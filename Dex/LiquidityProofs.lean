import Dex.SwapProofs
import Verity.Proofs.Stdlib.Math

/-!
# L4: burns pay out a proportional share, bounded by the pool's balances

`erc20Read_frame`: a token read (`balanceOf`) is a static call, so it keeps the pool's
storage and address whatever the token answers. `isqrt_state`: the pool's square root (a
256-step loop) only computes.

L5 (`mint_first_locks_min_liquidity`): the first mint locks `MIN_LIQUIDITY` shares.
-/

open Verity Contracts Dex

namespace Dex.ProofKit

/-- `mulDiv512Down` rounds down: `floor(a * b / c) * c ≤ a * b` (0 on overflow). -/
theorem mulDiv512Down_mul_le (a b c : Uint256) :
    (Verity.Stdlib.Math.mulDiv512Down a b c).val * c.val ≤ a.val * b.val := by
  unfold Verity.Stdlib.Math.mulDiv512Down
  split
  · rename_i r hr
    exact Verity.Proofs.Stdlib.Math.mulDiv512Down?_mul_le a b c r hr
  · simp

/-- A share `a ≤ c` of `b` is at most `b`. -/
theorem mulDiv512Down_le (a b c : Uint256) (hc : 0 < c.val) (hac : a.val ≤ c.val) :
    (Verity.Stdlib.Math.mulDiv512Down a b c).val ≤ b.val := by
  have h1 := mulDiv512Down_mul_le a b c
  have h2 : a.val * b.val ≤ b.val * c.val := by
    rw [Nat.mul_comm b.val]; exact Nat.mul_le_mul_right _ hac
  exact Nat.le_of_mul_le_mul_right (Nat.le_trans h1 h2) hc

/-- A loop whose step only computes leaves the state unchanged. -/
theorem loopList_state {σ : Type} (xs : List Nat) (init : σ) (body : Nat → σ → Contract σ)
    (hbody : ∀ i a s, ∃ b, body i a s = .success b s) (s : ContractState) :
    ∃ r, Contracts.loopList xs init body s = .success r s := by
  induction xs generalizing init with
  | nil => exact ⟨init, rfl⟩
  | cons x xs ih =>
    obtain ⟨b, hb⟩ := hbody x init s
    obtain ⟨r, hr⟩ := ih b
    refine ⟨r, ?_⟩
    simp only [Contracts.loopList, List.foldlM] at hr ⊢
    show Verity.bind (body x init) _ s = _
    simp only [Verity.bind, hb]
    exact hr

theorem loopList_state' {σ : Type} {xs : List Nat} {init : σ} {body : Nat → σ → Contract σ}
    {s s' : ContractState} {r : σ}
    (h : Contracts.loopList xs init body s = .success r s')
    (hbody : ∀ i a s, ∃ b, body i a s = .success b s) : s' = s := by
  obtain ⟨r', hr⟩ := loopList_state xs init body hbody s
  rw [hr] at h
  injection h with _ h
  exact h.symm

/-- `isqrt` only computes: on success the state is unchanged. -/
theorem isqrt_state (n r : Uint256) (s s' : ContractState)
    (h : Dex.Pool.isqrt n s = .success r s') : s' = s := by
  have tail : ∀ (z : Uint256) (s1 : ContractState),
      (Verity.bind (Pure.pure PUnit.unit) fun _ => Verity.bind
        (require (decide (EVM.Uint256.mul z z ≤ n)) "isqrt: too large") fun _ =>
        Verity.bind (require (decide (EVM.Uint256.sub n (EVM.Uint256.mul z z) ≤
          EVM.Uint256.mul 2 z)) "isqrt: too small") fun _ => Pure.pure z) s1 =
        .success r s' → s' = s1 := by
    intro z s1 hb
    obtain ⟨_, _, hp, hb⟩ := bind_success hb
    obtain ⟨_, _, hq, hb⟩ := bind_success hb
    obtain ⟨-, h1⟩ := require_success hq
    obtain ⟨_, _, hq, hb⟩ := bind_success hb
    obtain ⟨-, h2⟩ := require_success hq
    injection hp with _ hp
    injection hb with _ hb
    rw [← hb, h2, h1, ← hp]
  unfold Dex.Pool.isqrt at h
  simp only [Bind.bind] at h
  split at h
  · obtain ⟨zx, sL, hL, hk⟩ := bind_success h
    have hsL := loopList_state' hL (fun i a s => by
      obtain ⟨z, x⟩ := a
      split <;> exact ⟨_, rfl⟩)
    subst hsL
    exact tail zx.1 _ hk
  · split at h
    · exact tail 1 s h
    · exact tail 0 s h

/-- A token read keeps the caller's storage words and address, for every adversary. -/
theorem erc20Read_frame
    {adv : Compiler.CompilationModel.DenoteExternalCalls.AdversaryModel} {name : String}
    {token : Address}
    {args : List Uint256} {s s' : ContractState} {v : Uint256}
    (h : erc20Read adv name token args s = .success v s') :
    s'.storageWords = s.storageWords ∧ s'.thisAddress = s.thisAddress := by
  unfold erc20Read at h
  have hst := Compiler.CompilationModel.DenoteExternalCalls.externalCall_staticcall adv
    (linkedCallSite name args 1 .staticcall token.toNat 0 [Verity.addressToWord token]) s rfl
  revert hst
  generalize hr : (commonExternalCall adv
    (linkedCallSite name args 1 .staticcall token.toNat 0 [Verity.addressToWord token])).run s = r
    at h
  intro hst
  have hw : r.snd.storageWords = s.storageWords := by
    rw [← hr]; have h1 := congrArg ContractState.storageWords hst; exact h1
  have ha : r.snd.thisAddress = s.thisAddress := by
    rw [← hr]; have h1 := congrArg ContractState.thisAddress hst; exact h1
  rcases r with ⟨res, post⟩ | ⟨msg, post⟩
  · split at h
    · rename_i heq
      injection heq with _ hp
      injection h with _ h
      subst hp h
      exact ⟨hw, ha⟩
    all_goals simp at h
  · simp at h

end Dex.ProofKit

open Dex.ProofKit in
/-- L4: a successful burn pays `floor(liquidity * balance / supply)` of each token, where
`liquidity` is the pool's own LP balance and `supply` the LP supply before the burn, and
`balance` the pool's token balance it measured; each payout is positive, and at most that
balance when the burnt shares do not exceed the supply. Holds for every token behaviour. -/
theorem burn_proportional (ctx : ExecutableCallContext) (recipient : Address)
    (s s' : ContractState) (v : Uint256 × Uint256)
    (h : Pool.burn ctx recipient s = .success v s') :
    let liq := s.storageMap 6 s.thisAddress
    let supply := s.storage 5
    ∃ b0 b1 : Uint256,
      v = (Verity.Stdlib.Math.mulDiv512Down liq b0 supply,
        Verity.Stdlib.Math.mulDiv512Down liq b1 supply) ∧
      0 < supply.val ∧ 0 < v.1.val ∧ 0 < v.2.val := by
  intro liq supply
  unfold Pool.burn Verity.Core.NonReentrantGuard.guarded at h
  split at h
  · split at h
    · rename_i a s'' hbody
      injection h with ha _
      subst ha
      replace hbody := Contract.eq_of_run_success hbody
      simp only [Bind.bind] at hbody
      obtain ⟨t0, _, h1, hbody⟩ := bind_success hbody
      obtain ⟨t1, _, h2, hbody⟩ := bind_success hbody
      obtain ⟨me, _, h3, hbody⟩ := bind_success hbody
      obtain ⟨b0, _, h4, hbody⟩ := bind_success hbody
      obtain ⟨b1, _, h5, hbody⟩ := bind_success hbody
      obtain ⟨l, _, h6, hbody⟩ := bind_success hbody
      obtain ⟨sup, _, h7, hbody⟩ := bind_success hbody
      obtain ⟨_, _, hq, hbody⟩ := bind_success hbody
      obtain ⟨hsp, hs8⟩ := require_success hq
      obtain ⟨_, _, hq, hbody⟩ := bind_success hbody
      obtain ⟨ha0, hs9⟩ := require_success hq
      obtain ⟨_, _, hq, hbody⟩ := bind_success hbody
      obtain ⟨ha1, hs10⟩ := require_success hq
      iterate 13 (obtain ⟨_, _, -, hbody⟩ := bind_success hbody)
      simp only [Verity.pure, Pure.pure] at hbody
      injection hbody with hv _
      simp only [getStorageAddr, Contracts.contractAddress, getMapping, getStorage,
        Pool.token0, Pool.token1, Pool.balances, Pool.totalSupply] at h1 h2 h3 h6 h7
      injection h1 with _ h1
      injection h2 with _ h2
      injection h3 with hme h3
      injection h6 with hl h6
      injection h7 with hsup h7
      obtain ⟨hw4, ha4⟩ := erc20Read_frame h4
      obtain ⟨hw5, ha5⟩ := erc20Read_frame h5
      subst h1 h2 h3 h6 h7
      have hl' : l = liq := by
        rw [← hl, ← hme]
        simp only [ContractState.readMap, ContractState.storageMap, liq] at *
        rw [hw5, hw4]; rfl
      have hsup' : sup = supply := by
        rw [← hsup]
        simp only [ContractState.readSlot, ContractState.storage, supply] at *
        rw [hw5, hw4]; rfl
      subst hl' hsup'
      refine ⟨b0, b1, hv.symm, of_decide_eq_true hsp, ?_, ?_⟩
      · rw [← hv]; exact of_decide_eq_true ha0
      · rw [← hv]; exact of_decide_eq_true ha1
    · simp at h
  · simp at h

open Dex.ProofKit in
/-- L4 bounds: each burn payout is the rounded-down share `liquidity / supply` of the
measured balance, and at most that balance when `liquidity ≤ supply`. -/
theorem burn_payout_le (ctx : ExecutableCallContext) (recipient : Address)
    (s s' : ContractState) (v : Uint256 × Uint256)
    (h : Pool.burn ctx recipient s = .success v s') :
    let liq := s.storageMap 6 s.thisAddress
    let supply := s.storage 5
    ∃ b0 b1 : Uint256,
      v.1.val * supply.val ≤ liq.val * b0.val ∧ v.2.val * supply.val ≤ liq.val * b1.val ∧
      (liq.val ≤ supply.val → v.1.val ≤ b0.val ∧ v.2.val ≤ b1.val) := by
  intro liq supply
  obtain ⟨b0, b1, hv, hsup, -, -⟩ := burn_proportional ctx recipient s s' v h
  subst hv
  exact ⟨b0, b1, mulDiv512Down_mul_le _ _ _, mulDiv512Down_mul_le _ _ _,
    fun hle => ⟨mulDiv512Down_le _ _ _ hsup hle, mulDiv512Down_le _ _ _ hsup hle⟩⟩

open Dex.ProofKit in
/-- L5: the first mint (empty supply) locks `MIN_LIQUIDITY = 1000` shares at the zero
address and sets the supply to those 1000 plus the minted shares, which are positive. -/
theorem mint_first_locks_min_liquidity (ctx : ExecutableCallContext) (recipient : Address)
    (s s' : ContractState) (v : Uint256) (hsup : s.storage 5 = 0)
    (hrcpt : recipient ≠ zeroAddress) (h : Pool.mint ctx recipient s = .success v s') :
    s'.storage 5 = EVM.Uint256.add 1000 v ∧
      s'.storageMap 6 zeroAddress = EVM.Uint256.add (s.storageMap 6 zeroAddress) 1000 ∧
      0 < v.val := by
  unfold Pool.mint Verity.Core.NonReentrantGuard.guarded at h
  split at h
  · split at h
    · rename_i a s'' hbody
      injection h with ha hs'
      subst ha hs'
      replace hbody := Contract.eq_of_run_success hbody
      simp only [Bind.bind] at hbody
      obtain ⟨_, _, h1, hbody⟩ := bind_success hbody
      obtain ⟨_, _, h2, hbody⟩ := bind_success hbody
      obtain ⟨_, _, h3, hbody⟩ := bind_success hbody
      obtain ⟨_, _, h4, hbody⟩ := bind_success hbody
      obtain ⟨_, _, h5, hbody⟩ := bind_success hbody
      obtain ⟨_, _, hq, hbody⟩ := bind_success hbody
      obtain ⟨-, hs6⟩ := require_success hq
      obtain ⟨_, _, hq, hbody⟩ := bind_success hbody
      obtain ⟨-, hs7⟩ := require_success hq
      obtain ⟨_, _, h8, hbody⟩ := bind_success hbody
      obtain ⟨_, _, h9, hbody⟩ := bind_success hbody
      obtain ⟨_, _, hq, hbody⟩ := bind_success hbody
      obtain ⟨-, hs10⟩ := require_success hq
      obtain ⟨_, _, hq, hbody⟩ := bind_success hbody
      obtain ⟨-, hs11⟩ := require_success hq
      obtain ⟨sup, _, h12, hb12⟩ := bind_success hbody
      simp only [getStorageAddr, Contracts.contractAddress, getStorage, Pool.token0,
        Pool.token1, Pool.reserve0, Pool.reserve1, Pool.totalSupply] at h1 h2 h3 h8 h9 h12
      injection h1 with _ h1
      injection h2 with _ h2
      injection h3 with _ h3
      injection h8 with _ h8
      injection h9 with _ h9
      injection h12 with hsupR h12
      obtain ⟨hw4, -⟩ := erc20Read_frame h4
      obtain ⟨hw5, -⟩ := erc20Read_frame h5
      subst h1 h2 h3 h8 h9 h12 hs6 hs7 hs10 hs11
      have hsup0 : sup = 0 := by
        rw [← hsupR, ← hsup]
        simp only [ContractState.readSlot, ContractState.storage]
        rw [hw5, hw4]; rfl
      split at hb12
      · obtain ⟨root, _, c1, c2⟩ := bind_success hb12
        have hi := isqrt_state _ _ _ _ c1
        obtain ⟨_, _, hq, c3⟩ := bind_success c2
        obtain ⟨-, hr1⟩ := require_success hq
        obtain ⟨lockedBal, _, c4, c5⟩ := bind_success c3
        obtain ⟨_, _, c6, c7⟩ := bind_success c5
        obtain ⟨_, _, c8, c9⟩ := bind_success c7
        obtain ⟨_, _, hq, c10⟩ := bind_success c9
        obtain ⟨hliq, hr2⟩ := require_success hq
        obtain ⟨supplyNow, _, c11, c12⟩ := bind_success c10
        obtain ⟨_, _, c13, c14⟩ := bind_success c12
        obtain ⟨toBal, _, c15, c16⟩ := bind_success c14
        obtain ⟨_, _, c17, c18⟩ := bind_success c16
        obtain ⟨_, _, c19, c20⟩ := bind_success c18
        obtain ⟨_, _, c21, c22⟩ := bind_success c20
        obtain ⟨_, _, c23, c24⟩ := bind_success c22
        obtain ⟨_, _, c25, c26⟩ := bind_success c24
        obtain ⟨_, _, c27, c28⟩ := bind_success c26
        simp only [getMapping, setMapping, setStorage, getStorage, msgSender, emit,
          Pool.balances, Pool.totalSupply, Pool.reserve0, Pool.reserve1, Verity.pure,
          Pure.pure] at c4 c6 c8 c11 c13 c15 c17 c19 c21 c23 c25 c27 c28
        injection c4 with hlb c4
        injection c6 with _ c6
        injection c8 with _ c8
        injection c11 with hsn c11
        injection c13 with _ c13
        injection c15 with _ c15
        injection c17 with _ c17
        injection c19 with _ c19
        injection c21 with _ c21
        injection c23 with _ c23
        injection c25 with _ c25
        injection c27 with _ c27
        injection c28 with hv c28
        subst hi hr1 c4 c6 c8 hr2 c11 c13 c15 c17 c19 c21 c23 c25 c27 c28 hv hsn hlb
        refine ⟨?_, ?_, of_decide_eq_true hliq⟩
        · simp [ContractState.storage, ContractState.writeSlot, ContractState.writeMap,
            ContractState.readSlot, Verity.Core.NonReentrantGuard.setLock,
            ContractState.writeTransient]
        · simp only [ContractState.storageMap, ContractState.writeSlot, ContractState.writeMap,
            ContractState.readMap, Verity.Core.NonReentrantGuard.setLock,
            ContractState.writeTransient]
          simp [hw5, hw4, Verity.Core.NonReentrantGuard.setLock, ContractState.writeTransient]
          exact fun h0 => absurd h0.symm hrcpt
      · rename_i hne
        simp [hsup0] at hne
    · simp at h
  · simp at h

open Dex.ProofKit in
/-- L2 for `mint`: the minted shares `v > 0` go to the recipient, no other holder changes
except the zero address on the first mint, and the supply grows by exactly what the
balances grow by (first mint: `1000 + v`, with 1000 locked at the zero address). -/
theorem mint_lp_accounting (ctx : ExecutableCallContext) (recipient : Address)
    (s s' : ContractState) (v : Uint256) (hrcpt : recipient ≠ zeroAddress)
    (h : Pool.mint ctx recipient s = .success v s') :
    0 < v.val ∧
      s'.storageMap 6 recipient = EVM.Uint256.add (s.storageMap 6 recipient) v ∧
      (∀ a, a ≠ recipient → a ≠ zeroAddress → s'.storageMap 6 a = s.storageMap 6 a) ∧
      (s.storage 5 = 0 →
          s'.storage 5 = EVM.Uint256.add 1000 v ∧
            s'.storageMap 6 zeroAddress = EVM.Uint256.add (s.storageMap 6 zeroAddress) 1000) ∧
      (s.storage 5 ≠ 0 →
          s'.storage 5 = EVM.Uint256.add (s.storage 5) v ∧
            s'.storageMap 6 zeroAddress = s.storageMap 6 zeroAddress) := by
  unfold Pool.mint Verity.Core.NonReentrantGuard.guarded at h
  split at h
  · split at h
    · rename_i a s'' hbody
      injection h with ha hs'
      subst ha hs'
      replace hbody := Contract.eq_of_run_success hbody
      simp only [Bind.bind] at hbody
      obtain ⟨_, _, h1, hbody⟩ := bind_success hbody
      obtain ⟨_, _, h2, hbody⟩ := bind_success hbody
      obtain ⟨_, _, h3, hbody⟩ := bind_success hbody
      obtain ⟨_, _, h4, hbody⟩ := bind_success hbody
      obtain ⟨_, _, h5, hbody⟩ := bind_success hbody
      obtain ⟨_, _, hq, hbody⟩ := bind_success hbody
      obtain ⟨-, hs6⟩ := require_success hq
      obtain ⟨_, _, hq, hbody⟩ := bind_success hbody
      obtain ⟨-, hs7⟩ := require_success hq
      obtain ⟨_, _, h8, hbody⟩ := bind_success hbody
      obtain ⟨_, _, h9, hbody⟩ := bind_success hbody
      obtain ⟨_, _, hq, hbody⟩ := bind_success hbody
      obtain ⟨-, hs10⟩ := require_success hq
      obtain ⟨_, _, hq, hbody⟩ := bind_success hbody
      obtain ⟨-, hs11⟩ := require_success hq
      obtain ⟨sup, _, h12, hb12⟩ := bind_success hbody
      simp only [getStorageAddr, Contracts.contractAddress, getStorage, Pool.token0,
        Pool.token1, Pool.reserve0, Pool.reserve1, Pool.totalSupply] at h1 h2 h3 h8 h9 h12
      injection h1 with _ h1
      injection h2 with _ h2
      injection h3 with _ h3
      injection h8 with _ h8
      injection h9 with _ h9
      injection h12 with hsupR h12
      obtain ⟨hw4, -⟩ := erc20Read_frame h4
      obtain ⟨hw5, -⟩ := erc20Read_frame h5
      subst h1 h2 h3 h8 h9 h12 hs6 hs7 hs10 hs11
      have hsupE : sup = s.storage 5 := by
        rw [← hsupR]
        simp only [ContractState.readSlot, ContractState.storage]
        rw [hw5, hw4]; rfl
      have hr0 : recipient ≠ 0 := hrcpt
      split at hb12
      · rename_i hz
        have hs0 : s.storage 5 = 0 := by rw [← hsupE]; simpa using hz
        obtain ⟨root, _, c1, c2⟩ := bind_success hb12
        have hi := isqrt_state _ _ _ _ c1
        obtain ⟨_, _, hq, c3⟩ := bind_success c2
        obtain ⟨-, hr1⟩ := require_success hq
        obtain ⟨lockedBal, _, c4, c5⟩ := bind_success c3
        obtain ⟨_, _, c6, c7⟩ := bind_success c5
        obtain ⟨_, _, c8, c9⟩ := bind_success c7
        obtain ⟨_, _, hq, c10⟩ := bind_success c9
        obtain ⟨hliq, hr2⟩ := require_success hq
        obtain ⟨supplyNow, _, c11, c12⟩ := bind_success c10
        obtain ⟨_, _, c13, c14⟩ := bind_success c12
        obtain ⟨toBal, _, c15, c16⟩ := bind_success c14
        obtain ⟨_, _, c17, c18⟩ := bind_success c16
        obtain ⟨_, _, c19, c20⟩ := bind_success c18
        obtain ⟨_, _, c21, c22⟩ := bind_success c20
        obtain ⟨_, _, c23, c24⟩ := bind_success c22
        obtain ⟨_, _, c25, c26⟩ := bind_success c24
        obtain ⟨_, _, c27, c28⟩ := bind_success c26
        simp only [getMapping, setMapping, setStorage, getStorage, msgSender, emit,
          Pool.balances, Pool.totalSupply, Pool.reserve0, Pool.reserve1, Verity.pure,
          Pure.pure] at c4 c6 c8 c11 c13 c15 c17 c19 c21 c23 c25 c27 c28
        injection c4 with hlb c4
        injection c6 with _ c6
        injection c8 with _ c8
        injection c11 with hsn c11
        injection c13 with _ c13
        injection c15 with htb c15
        injection c17 with _ c17
        injection c19 with _ c19
        injection c21 with _ c21
        injection c23 with _ c23
        injection c25 with _ c25
        injection c27 with _ c27
        injection c28 with hv c28
        subst hi hr1 c4 c6 c8 hr2 c11 c13 c15 c17 c19 c21 c23 c25 c27 c28 hv hsn hlb htb
        refine ⟨of_decide_eq_true hliq, ?_, ?_, fun _ => ⟨?_, ?_⟩, fun hne => absurd hs0 hne⟩
        · simp only [ContractState.storageMap, ContractState.writeSlot, ContractState.writeMap,
            ContractState.readMap, Verity.Core.NonReentrantGuard.setLock,
            ContractState.writeTransient]
          simp [hw5, hw4, Verity.Core.NonReentrantGuard.setLock, ContractState.writeTransient,
            hr0]
        · intro x hx hxz
          have hx0 : x ≠ 0 := hxz
          simp only [ContractState.storageMap, ContractState.writeSlot, ContractState.writeMap,
            ContractState.readMap, Verity.Core.NonReentrantGuard.setLock,
            ContractState.writeTransient]
          simp [hw5, hw4, Verity.Core.NonReentrantGuard.setLock, ContractState.writeTransient,
            hx, hx0]
        · simp [ContractState.storage, ContractState.writeSlot, ContractState.writeMap,
            ContractState.readSlot, Verity.Core.NonReentrantGuard.setLock,
            ContractState.writeTransient]
        · simp only [ContractState.storageMap, ContractState.writeSlot, ContractState.writeMap,
            ContractState.readMap, Verity.Core.NonReentrantGuard.setLock,
            ContractState.writeTransient]
          simp [hw5, hw4, Verity.Core.NonReentrantGuard.setLock, ContractState.writeTransient]
          exact fun h0 => absurd h0.symm hrcpt
      · rename_i hz
        have hs0 : s.storage 5 ≠ 0 := by rw [← hsupE]; simpa using hz
        obtain ⟨_, _, c8, c9⟩ := bind_success hb12
        obtain ⟨_, _, hq, c10⟩ := bind_success c9
        obtain ⟨hliq, hr2⟩ := require_success hq
        obtain ⟨supplyNow, _, c11, c12⟩ := bind_success c10
        obtain ⟨_, _, c13, c14⟩ := bind_success c12
        obtain ⟨toBal, _, c15, c16⟩ := bind_success c14
        obtain ⟨_, _, c17, c18⟩ := bind_success c16
        obtain ⟨_, _, c19, c20⟩ := bind_success c18
        obtain ⟨_, _, c21, c22⟩ := bind_success c20
        obtain ⟨_, _, c23, c24⟩ := bind_success c22
        obtain ⟨_, _, c25, c26⟩ := bind_success c24
        obtain ⟨_, _, c27, c28⟩ := bind_success c26
        simp only [getMapping, setMapping, setStorage, getStorage, msgSender, emit,
          Pool.balances, Pool.totalSupply, Pool.reserve0, Pool.reserve1, Verity.pure,
          Pure.pure] at c8 c11 c13 c15 c17 c19 c21 c23 c25 c27 c28
        injection c8 with _ c8
        injection c11 with hsn c11
        injection c13 with _ c13
        injection c15 with htb c15
        injection c17 with _ c17
        injection c19 with _ c19
        injection c21 with _ c21
        injection c23 with _ c23
        injection c25 with _ c25
        injection c27 with _ c27
        injection c28 with hv c28
        subst c8 hr2 c11 c13 c15 c17 c19 c21 c23 c25 c27 c28 hv hsn htb
        refine ⟨of_decide_eq_true hliq, ?_, ?_, fun h0 => absurd h0 hs0, fun _ => ⟨?_, ?_⟩⟩
        · simp only [ContractState.storageMap, ContractState.writeSlot, ContractState.writeMap,
            ContractState.readMap, Verity.Core.NonReentrantGuard.setLock,
            ContractState.writeTransient]
          simp [hw5, hw4, Verity.Core.NonReentrantGuard.setLock, ContractState.writeTransient]
        · intro x hx _
          simp only [ContractState.storageMap, ContractState.writeSlot, ContractState.writeMap,
            ContractState.readMap, Verity.Core.NonReentrantGuard.setLock,
            ContractState.writeTransient]
          simp [hw5, hw4, Verity.Core.NonReentrantGuard.setLock, ContractState.writeTransient,
            hx]
        · simp only [ContractState.storage, ContractState.writeSlot, ContractState.writeMap,
            ContractState.readSlot, Verity.Core.NonReentrantGuard.setLock,
            ContractState.writeTransient]
          simp [hw5, hw4, Verity.Core.NonReentrantGuard.setLock, ContractState.writeTransient]
        · simp only [ContractState.storageMap, ContractState.writeMap,
            ContractState.readMap, Verity.Core.NonReentrantGuard.setLock,
            ContractState.writeTransient]
          simp [hw5, hw4, Verity.Core.NonReentrantGuard.setLock, ContractState.writeTransient]
          exact fun h0 => absurd h0.symm hrcpt
    · simp at h
  · simp at h

namespace Dex.ProofKit

open Compiler.CompilationModel.DenoteExternalCalls in
/-- A token transfer leaves the pool's storage unchanged when the adversary's committed
transitions do (no reentrant write into the pool, which the lock enforces on chain). -/
theorem erc20Write_storage_frame {adv : AdversaryModel} {name : String} {token : Address}
    {args : List Uint256} {s s' : ContractState} {u : Unit}
    (hadv : ∀ site w, (adv.stateTransition site w).storageWords = w.storageWords)
    (h : erc20Write adv name token args s = .success u s') :
    s'.storageWords = s.storageWords := by
  unfold erc20Write at h
  have hpost : ((commonExternalCall adv
      (linkedCallSite name args 0 .call token.toNat)).run s).snd.storageWords = s.storageWords := by
    rw [commonExternalCall, externalCall_run]
    simp only [ContractResult.snd, denoteCallJournaled, denoteCall]
    split <;> simp [hadv]
  revert hpost
  generalize (commonExternalCall adv (linkedCallSite name args 0 .call token.toNat)).run s = r at h
  intro hpost
  rcases r with ⟨res, post⟩ | ⟨msg, post⟩
  · simp only [ContractResult.snd] at hpost
    split at h
    · rename_i heq
      injection heq with _ hp
      subst hp
      split at h
      · split at h
        · simp at h
        · injection h with _ h; subst h; exact hpost
      · split at h
        · injection h with _ h; subst h; exact hpost
        · simp at h
      · simp at h
    all_goals simp at h
  · simp at h

end Dex.ProofKit

open Dex.ProofKit in
/-- L2 for `burn`: the pool's own LP balance (the shares sent to it) is zeroed, the supply
drops by exactly that balance, and no other holder changes. Assumes the token calls do not
write the pool's storage (on chain: any reentrant call into the pool reverts on its lock). -/
theorem burn_lp_accounting (ctx : ExecutableCallContext) (recipient : Address)
    (s s' : ContractState) (v : Uint256 × Uint256)
    (hadv : ∀ site w, (ctx.adversary.stateTransition site w).storageWords = w.storageWords)
    (h : Pool.burn ctx recipient s = .success v s') :
    s'.storageMap 6 s.thisAddress = 0 ∧
      s'.storage 5 = EVM.Uint256.sub (s.storage 5) (s.storageMap 6 s.thisAddress) ∧
      ∀ a, a ≠ s.thisAddress → s'.storageMap 6 a = s.storageMap 6 a := by
  unfold Pool.burn Verity.Core.NonReentrantGuard.guarded at h
  split at h
  · split at h
    · rename_i a s'' hbody
      injection h with _ hs'
      subst hs'
      replace hbody := Contract.eq_of_run_success hbody
      simp only [Bind.bind] at hbody
      obtain ⟨t0, _, h1, hbody⟩ := bind_success hbody
      obtain ⟨t1, _, h2, hbody⟩ := bind_success hbody
      obtain ⟨me, _, h3, hbody⟩ := bind_success hbody
      obtain ⟨b0, _, h4, hbody⟩ := bind_success hbody
      obtain ⟨b1, _, h5, hbody⟩ := bind_success hbody
      obtain ⟨l, _, h6, hbody⟩ := bind_success hbody
      obtain ⟨sup, _, h7, hbody⟩ := bind_success hbody
      obtain ⟨_, _, hq, hbody⟩ := bind_success hbody
      obtain ⟨-, hs8⟩ := require_success hq
      obtain ⟨_, _, hq, hbody⟩ := bind_success hbody
      obtain ⟨-, hs9⟩ := require_success hq
      obtain ⟨_, _, hq, hbody⟩ := bind_success hbody
      obtain ⟨-, hs10⟩ := require_success hq
      obtain ⟨_, S1, c1, hbody⟩ := bind_success hbody
      obtain ⟨_, S2, c2, hbody⟩ := bind_success hbody
      obtain ⟨_, S3, c3, hbody⟩ := bind_success hbody
      obtain ⟨_, S4, c4, hbody⟩ := bind_success hbody
      obtain ⟨_, S5, c5, hbody⟩ := bind_success hbody
      obtain ⟨_, S6, c6, hbody⟩ := bind_success hbody
      obtain ⟨_, S7, hq, hbody⟩ := bind_success hbody
      obtain ⟨-, hs7⟩ := require_success hq
      obtain ⟨_, S8, hq, hbody⟩ := bind_success hbody
      obtain ⟨-, hs8'⟩ := require_success hq
      obtain ⟨_, S9, c9, hbody⟩ := bind_success hbody
      obtain ⟨_, S10, c10, hbody⟩ := bind_success hbody
      obtain ⟨_, S11, c11, hbody⟩ := bind_success hbody
      obtain ⟨_, S12, c12, hbody⟩ := bind_success hbody
      obtain ⟨_, S13, c13, hbody⟩ := bind_success hbody
      simp only [getStorageAddr, Contracts.contractAddress, getMapping, getStorage,
        Pool.token0, Pool.token1, Pool.balances, Pool.totalSupply] at h1 h2 h3 h6 h7
      injection h1 with _ h1
      injection h2 with _ h2
      injection h3 with hme h3
      injection h6 with hl h6
      injection h7 with hsup h7
      obtain ⟨hw4, -⟩ := erc20Read_frame h4
      obtain ⟨hw5, -⟩ := erc20Read_frame h5
      obtain ⟨hw15, -⟩ := erc20Read_frame c5
      obtain ⟨hw16, -⟩ := erc20Read_frame c6
      unfold safeTransfer at c3 c4
      have hw13 := erc20Write_storage_frame hadv c3
      have hw14 := erc20Write_storage_frame hadv c4
      simp only [setMapping, setStorage, msgSender, emit, Pool.balances, Pool.totalSupply,
        Pool.reserve0, Pool.reserve1, Verity.pure, Pure.pure] at c1 c2 c9 c10 c11 c12 c13 hbody
      injection c1 with _ c1
      injection c2 with _ c2
      injection c9 with _ c9
      injection c10 with _ c10
      injection c11 with _ c11
      injection c12 with _ c12
      injection c13 with _ c13
      injection hbody with _ hbody
      subst h1 h2 h3 h6 h7 hs8 hs9 hs10 c1 c2 hs7 hs8' c9 c10 c11 c12 c13 hbody
      subst hme hl hsup
      refine ⟨?_, ?_, fun x hx => ?_⟩
      all_goals simp only [ContractState.storageMap, ContractState.storage,
        Verity.Core.NonReentrantGuard.setLock, ContractState.writeTransient,
        ContractState.writeSlot, hw16, hw15, hw14, hw13]
      all_goals simp [ContractState.writeMap, ContractState.readMap,
        ContractState.readSlot, ContractState.storageMap, ContractState.storage, hw5, hw4,
        Verity.Core.NonReentrantGuard.setLock, ContractState.writeTransient]
      exact fun h0 => absurd h0 hx
    · simp at h
  · simp at h

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
`balance` the pool's reported token balance. The reads are sequential and anchored to the
locked pre-state. Each payout is positive. Holds for every token behaviour. -/
theorem burn_proportional_observed (ctx : ExecutableCallContext) (recipient : Address)
    (s s' : ContractState) (v : Uint256 × Uint256)
    (h : Pool.burn ctx recipient s = .success v s') :
    let liq := s.storageMap 6 s.thisAddress
    let supply := s.storage 5
    ∃ (b0 b1 : Uint256) (mid last : ContractState),
      balanceOf (s.storageAddr 1) s.thisAddress ctx.adversary
        (Verity.Core.NonReentrantGuard.setLock 9 1 s) = .success b0 mid ∧
      balanceOf (s.storageAddr 2) s.thisAddress ctx.adversary mid = .success b1 last ∧
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
      injection h1 with ht0 h1
      injection h2 with ht1 h2
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
      have read0 := h4
      have read1 := h5
      subst ht0 ht1 hme
      rw [externalArgAddress_address, externalArgAddress_address, setLock_readAddrSlot]
        at read0 read1
      refine ⟨b0, b1, _, _, read0, read1, hv.symm, of_decide_eq_true hsp, ?_, ?_⟩
      · rw [← hv]; exact of_decide_eq_true ha0
      · rw [← hv]; exact of_decide_eq_true ha1
    · simp at h
  · simp at h

/-- Compatibility corollary; `burn_proportional_observed` links the balances to execution. -/
theorem burn_proportional (ctx : ExecutableCallContext) (recipient : Address)
    (s s' : ContractState) (v : Uint256 × Uint256)
    (h : Pool.burn ctx recipient s = .success v s') :
    let liq := s.storageMap 6 s.thisAddress
    let supply := s.storage 5
    ∃ b0 b1 : Uint256,
      v = (Verity.Stdlib.Math.mulDiv512Down liq b0 supply,
        Verity.Stdlib.Math.mulDiv512Down liq b1 supply) ∧
      0 < supply.val ∧ 0 < v.1.val ∧ 0 < v.2.val := by
  obtain ⟨b0, b1, _, _, _, _, hp⟩ := burn_proportional_observed ctx recipient s s' v h
  exact ⟨b0, b1, hp⟩

open Dex.ProofKit in
/-- L4 bounds on the actual sequential observations from the locked pre-state. -/
theorem burn_payout_le_observed (ctx : ExecutableCallContext) (recipient : Address)
    (s s' : ContractState) (v : Uint256 × Uint256)
    (h : Pool.burn ctx recipient s = .success v s') :
    ∃ (b0 b1 : Uint256) (mid last : ContractState),
      balanceOf (s.storageAddr 1) s.thisAddress ctx.adversary
        (Verity.Core.NonReentrantGuard.setLock 9 1 s) = .success b0 mid ∧
      balanceOf (s.storageAddr 2) s.thisAddress ctx.adversary mid = .success b1 last ∧
      v.1.val * (s.storage 5).val ≤ (s.storageMap 6 s.thisAddress).val * b0.val ∧
      v.2.val * (s.storage 5).val ≤ (s.storageMap 6 s.thisAddress).val * b1.val ∧
      ((s.storageMap 6 s.thisAddress).val ≤ (s.storage 5).val →
        v.1.val ≤ b0.val ∧ v.2.val ≤ b1.val) := by
  obtain ⟨b0, b1, mid, last, h0, h1, hv, hsup, _, _⟩ :=
    burn_proportional_observed ctx recipient s s' v h
  subst hv
  exact ⟨b0, b1, mid, last, h0, h1, mulDiv512Down_mul_le _ _ _, mulDiv512Down_mul_le _ _ _,
    fun hle => ⟨mulDiv512Down_le _ _ _ hsup hle, mulDiv512Down_le _ _ _ hsup hle⟩⟩

open Dex.ProofKit in
/-- Compatibility bounds: each burn payout is the rounded-down share `liquidity / supply` of the
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
        obtain ⟨_, _, hqs, c12⟩ := bind_success c12
        obtain ⟨hnowrap, hsq⟩ := require_success hqs
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
        subst hi hr1 c4 c6 c8 hr2 c11 c13 c15 c17 c19 c21 c23 c25 c27 c28 hv hsn hlb hsq
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
except the zero address on the first mint, and supply and balances change by the same
modular additions (first mint: `1000 + v`, with 1000 credited to the zero address).
Integer growth requires additional no-overflow bounds. -/
theorem mint_lp_accounting (ctx : ExecutableCallContext) (recipient : Address)
    (s s' : ContractState) (v : Uint256) (hrcpt : recipient ≠ zeroAddress)
    (h : Pool.mint ctx recipient s = .success v s') :
    0 < v.val ∧
      s'.storageMap 6 recipient = EVM.Uint256.add (s.storageMap 6 recipient) v ∧
      (∀ a, a ≠ recipient → a ≠ zeroAddress → s'.storageMap 6 a = s.storageMap 6 a) ∧
      (s.storage 5 = 0 →
          s'.storage 5 = EVM.Uint256.add 1000 v ∧
            s'.storageMap 6 zeroAddress = EVM.Uint256.add (s.storageMap 6 zeroAddress) 1000 ∧
            (1000 : Uint256).val ≤ (s'.storage 5).val) ∧
      (s.storage 5 ≠ 0 →
          s'.storage 5 = EVM.Uint256.add (s.storage 5) v ∧
            s'.storageMap 6 zeroAddress = s.storageMap 6 zeroAddress ∧
            (s.storage 5).val ≤ (s'.storage 5).val) := by
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
        obtain ⟨_, _, hqs, c12⟩ := bind_success c12
        obtain ⟨hnowrap, hsq⟩ := require_success hqs
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
        subst hi hr1 c4 c6 c8 hr2 c11 c13 c15 c17 c19 c21 c23 c25 c27 c28 hv hsn hlb htb hsq
        refine ⟨of_decide_eq_true hliq, ?_, ?_, fun _ => ⟨?_, ?_, ?_⟩, fun hne => absurd hs0 hne⟩
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
        · have hw := of_decide_eq_true hnowrap
          simp [ContractState.storage, ContractState.writeSlot, ContractState.writeMap,
            ContractState.readSlot, Verity.Core.NonReentrantGuard.setLock,
            ContractState.writeTransient, hw5, hw4] at hw ⊢
          exact hw
      · rename_i hz
        have hs0 : s.storage 5 ≠ 0 := by rw [← hsupE]; simpa using hz
        obtain ⟨_, _, c8, c9⟩ := bind_success hb12
        obtain ⟨_, _, hq, c10⟩ := bind_success c9
        obtain ⟨hliq, hr2⟩ := require_success hq
        obtain ⟨supplyNow, _, c11, c12⟩ := bind_success c10
        obtain ⟨_, _, hqs, c12⟩ := bind_success c12
        obtain ⟨hnowrap, hsq⟩ := require_success hqs
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
        subst c8 hr2 c11 c13 c15 c17 c19 c21 c23 c25 c27 c28 hv hsn htb hsq
        refine ⟨of_decide_eq_true hliq, ?_, ?_, fun h0 => absurd h0 hs0, fun _ => ⟨?_, ?_, ?_⟩⟩
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
        · have hw := of_decide_eq_true hnowrap
          simp [ContractState.storage, ContractState.writeSlot, ContractState.writeMap,
            ContractState.readSlot, Verity.Core.NonReentrantGuard.setLock,
            ContractState.writeTransient, hw5, hw4] at hw ⊢
          exact hw
    · simp at h
  · simp at h

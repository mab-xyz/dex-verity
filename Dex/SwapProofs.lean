import Dex.Pool
import Verity.Proofs.Stdlib.Automation
import Verity.Core.Model.NonReentrantGuard

/-!
# L3: swaps never decrease the constant product

`swap_k_nondecreasing`: a successful `Pool.swap` keeps both reserves below 2^112 and does
not decrease `reserve0 * reserve1`, for every behaviour of the token contracts
(`ctx.adversary`) and whatever balances the pool reads. The proof walks the success path
with two inversion lemmas (`bind_success`, `require_success`), then turns the pool's
256-bit fee-adjusted k-check into the exact inequality (`k_of_check`): below 2^112 no
product in the check can wrap.
-/

open Verity Contracts Dex

namespace Dex.ProofKit

theorem bind_success {α β : Type} {m : Contract α} {f : α → Contract β}
    {s s' : ContractState} {b : β}
    (h : Verity.bind m f s = .success b s') :
    ∃ a s1, m s = .success a s1 ∧ f a s1 = .success b s' := by
  unfold Verity.bind at h
  cases hm : m s
  · rename_i a s1
    rw [hm] at h
    exact ⟨a, s1, rfl, h⟩
  · rw [hm] at h
    simp at h

theorem require_success {c : Bool} {msg : String} {s s' : ContractState} {u : Unit}
    (h : Verity.require c msg s = .success u s') : c = true ∧ s' = s := by
  unfold Verity.require at h
  split at h <;> simp_all



/-- The amount that arrived, as `settle` computes it (`b - (r - out)` or 0) never exceeds `b`. -/
theorem input_le (b r out : Uint256) :
    (if b > EVM.Uint256.sub r out then EVM.Uint256.sub b (EVM.Uint256.sub r out) else 0).val
      ≤ b.val := by
  split
  · rename_i hgt
    have hle : (EVM.Uint256.sub r out).val ≤ b.val := le_of_lt hgt
    have := Verity.Core.Uint256.sub_eq_of_le hle
    simp only [EVM.Uint256.sub] at this ⊢
    show (Verity.Core.Uint256.sub b (Verity.Core.Uint256.sub r out)).val ≤ b.val
    rw [show Verity.Core.Uint256.sub b (Verity.Core.Uint256.sub r out) = b - Verity.Core.Uint256.sub r out from rfl, this]
    omega
  · simp

/-- Fee-adjusted balance `b*1000 - in*3`, exactly, when `b < 2^112` and `in ≤ b`. -/
theorem adj_val (b i : Uint256) (hb : b.val < 2 ^ 112) (hi : i.val ≤ b.val) :
    (EVM.Uint256.sub (EVM.Uint256.mul b 1000) (EVM.Uint256.mul i 3)).val = b.val * 1000 - i.val * 3 := by
  have h1000 : (EVM.Uint256.mul b 1000).val = b.val * 1000 :=
    Verity.Core.Uint256.mulNoWrap (by
      rw [show (1000 : Verity.Core.Uint256).val = 1000 from rfl]
      unfold Verity.Core.Uint256.modulus Verity.Core.UINT256_MODULUS; omega)
  have h3 : (EVM.Uint256.mul i 3).val = i.val * 3 :=
    Verity.Core.Uint256.mulNoWrap (by
      rw [show (3 : Verity.Core.Uint256).val = 3 from rfl]
      unfold Verity.Core.Uint256.modulus Verity.Core.UINT256_MODULUS; omega)
  have hle : (EVM.Uint256.mul i 3).val ≤ (EVM.Uint256.mul b 1000).val := by omega
  have := Verity.Core.Uint256.sub_eq_of_le hle
  show (Verity.Core.Uint256.sub (EVM.Uint256.mul b 1000) (EVM.Uint256.mul i 3)).val = _
  rw [show Verity.Core.Uint256.sub (EVM.Uint256.mul b 1000) (EVM.Uint256.mul i 3) =
    EVM.Uint256.mul b 1000 - EVM.Uint256.mul i 3 from rfl, this, h1000, h3]

set_option maxRecDepth 8000 in
/-- The pool's 256-bit k-check implies the exact product inequality when every reserve and
balance is below 2^112 (so no product wraps) and each input is at most its balance. -/
theorem k_of_check (r0 r1 b0 b1 i0 i1 : Uint256)
    (hr0 : r0.val < 2 ^ 112) (hr1 : r1.val < 2 ^ 112)
    (hb0 : b0.val < 2 ^ 112) (hb1 : b1.val < 2 ^ 112)
    (hi0 : i0.val ≤ b0.val) (hi1 : i1.val ≤ b1.val)
    (hk : EVM.Uint256.mul (EVM.Uint256.sub (EVM.Uint256.mul b0 1000) (EVM.Uint256.mul i0 3))
            (EVM.Uint256.sub (EVM.Uint256.mul b1 1000) (EVM.Uint256.mul i1 3)) ≥
          EVM.Uint256.mul (EVM.Uint256.mul r0 r1) 1000000) :
    r0.val * r1.val ≤ b0.val * b1.val := by
  have ha0 := adj_val b0 i0 hb0 hi0
  have ha1 := adj_val b1 i1 hb1 hi1
  have hmodulus : Verity.Core.Uint256.modulus = 2 ^ 256 := by
    unfold Verity.Core.Uint256.modulus Verity.Core.UINT256_MODULUS; rfl
  have hadj : (EVM.Uint256.mul (EVM.Uint256.sub (EVM.Uint256.mul b0 1000) (EVM.Uint256.mul i0 3))
      (EVM.Uint256.sub (EVM.Uint256.mul b1 1000) (EVM.Uint256.mul i1 3))).val =
      (b0.val * 1000 - i0.val * 3) * (b1.val * 1000 - i1.val * 3) := by
    rw [Verity.Core.Uint256.mulNoWrap, ha0, ha1]
    rw [ha0, ha1, hmodulus]
    have hs0 : b0.val * 1000 - i0.val * 3 < 2 ^ 122 := by omega
    have hs1 : b1.val * 1000 - i1.val * 3 < 2 ^ 122 := by omega
    calc (b0.val * 1000 - i0.val * 3) * (b1.val * 1000 - i1.val * 3)
        < 2 ^ 122 * 2 ^ 122 := Nat.mul_lt_mul'' hs0 hs1
      _ ≤ 2 ^ 256 := by norm_num
  have hrr : (EVM.Uint256.mul r0 r1).val = r0.val * r1.val :=
    Verity.Core.Uint256.mulNoWrap (by
      rw [hmodulus]
      calc r0.val * r1.val < 2 ^ 112 * 2 ^ 112 := Nat.mul_lt_mul'' hr0 hr1
        _ ≤ 2 ^ 256 := by norm_num)
  have hk6 : (EVM.Uint256.mul (EVM.Uint256.mul r0 r1) 1000000).val = r0.val * r1.val * 1000000 := by
    rw [Verity.Core.Uint256.mulNoWrap, hrr]
    · rfl
    · rw [hrr, show (1000000 : Verity.Core.Uint256).val = 1000000 from rfl, hmodulus]
      calc r0.val * r1.val * 1000000 < 2 ^ 112 * 2 ^ 112 * 2 ^ 20 :=
            Nat.mul_lt_mul'' (Nat.mul_lt_mul'' hr0 hr1) (by norm_num)
        _ ≤ 2 ^ 256 := by norm_num
  have hk' : r0.val * r1.val * 1000000 ≤
      (b0.val * 1000 - i0.val * 3) * (b1.val * 1000 - i1.val * 3) := by
    rw [← hk6, ← hadj]; exact hk
  have h0 : b0.val * 1000 - i0.val * 3 ≤ b0.val * 1000 := Nat.sub_le _ _
  have h1 : b1.val * 1000 - i1.val * 3 ≤ b1.val * 1000 := Nat.sub_le _ _
  nlinarith [Nat.mul_le_mul h0 h1]

set_option maxRecDepth 8000 in
/-- L3 (core): if `settle` succeeds, the new reserves (slots 3, 4) are below 2^112 and their
product is at least the product of the reserves it was given (also below 2^112), whatever
the token balances it read. -/
theorem settle_k_nondecreasing (ctx : ExecutableCallContext) (r0 r1 out0 out1 : Uint256)
    (t0 t1 rcpt : Address) (s s' : ContractState) (hr0 : r0.val < 2 ^ 112)
    (hr1 : r1.val < 2 ^ 112)
    (h : Pool.settle ctx r0 r1 out0 out1 t0 t1 rcpt s = .success () s') :
    (s'.storage 3).val < 2 ^ 112 ∧ (s'.storage 4).val < 2 ^ 112 ∧
      r0.val * r1.val ≤ (s'.storage 3).val * (s'.storage 4).val := by
  unfold Pool.settle at h
  simp only [Bind.bind] at h
  obtain ⟨me, s1, -, h⟩ := bind_success h
  obtain ⟨b0, s2, -, h⟩ := bind_success h
  obtain ⟨b1, s3, -, h⟩ := bind_success h
  obtain ⟨_, s4, hq, h⟩ := bind_success h
  obtain ⟨hb0, -⟩ := require_success hq
  obtain ⟨_, s5, hq, h⟩ := bind_success h
  obtain ⟨hb1, -⟩ := require_success hq
  obtain ⟨_, s6, hq, h⟩ := bind_success h
  obtain ⟨-, -⟩ := require_success hq
  obtain ⟨_, s7, hq, h⟩ := bind_success h
  obtain ⟨hk, -⟩ := require_success hq
  obtain ⟨_, s8, -, h⟩ := bind_success h
  obtain ⟨_, s9, -, h⟩ := bind_success h
  obtain ⟨_, s10, -, h⟩ := bind_success h
  obtain ⟨_, s11, hw0, h⟩ := bind_success h
  simp only [setStorage, Pool.reserve0, Pool.reserve1] at hw0 h
  injection hw0 with _ hw0
  injection h with _ h
  subst hw0 h
  have hcap : (5192296858534827628530496329220096 : Uint256).val = 2 ^ 112 := rfl
  have hb0' : b0.val < 2 ^ 112 := by
    have := of_decide_eq_true hb0; rw [← hcap]; exact this
  have hb1' : b1.val < 2 ^ 112 := by
    have := of_decide_eq_true hb1; rw [← hcap]; exact this
  simp only [ContractState.storage, ContractState.writeSlot] at *
  refine ⟨by simpa using hb0', by simpa using hb1', ?_⟩
  simp only [decide_eq_true_eq] at hk
  have := k_of_check r0 r1 b0 b1 _ _ hr0 hr1 hb0' hb1' (input_le b0 r0 out0) (input_le b1 r1 out1) hk
  simpa using this

/-- Reserve-cap invariant for `sync`: after a successful sync both reserves are below 2^112
(the bound `swap_k_nondecreasing` needs), whatever the token contracts report. -/
theorem sync_preserves_reserve_cap (ctx : ExecutableCallContext) (s s' : ContractState)
    (h : Pool.sync ctx s = .success () s') :
    (s'.storage 3).val < 2 ^ 112 ∧ (s'.storage 4).val < 2 ^ 112 := by
  unfold Pool.sync Verity.Core.NonReentrantGuard.guarded at h
  split at h
  · split at h
    · rename_i a s'' hbody
      injection h with _ hs'
      subst hs'
      replace hbody := Contract.eq_of_run_success hbody
      simp only [Bind.bind] at hbody
      obtain ⟨_, _, -, hbody⟩ := bind_success hbody
      obtain ⟨_, _, -, hbody⟩ := bind_success hbody
      obtain ⟨_, _, -, hbody⟩ := bind_success hbody
      obtain ⟨b0, _, -, hbody⟩ := bind_success hbody
      obtain ⟨b1, _, -, hbody⟩ := bind_success hbody
      obtain ⟨_, _, hq, hbody⟩ := bind_success hbody
      obtain ⟨hb0, -⟩ := require_success hq
      obtain ⟨_, _, hq, hbody⟩ := bind_success hbody
      obtain ⟨hb1, -⟩ := require_success hq
      obtain ⟨_, _, -, hbody⟩ := bind_success hbody
      obtain ⟨_, _, hw0, hbody⟩ := bind_success hbody
      simp only [setStorage, Pool.reserve0, Pool.reserve1] at hw0 hbody
      injection hw0 with _ hw0
      injection hbody with _ hbody
      subst hw0 hbody
      have hcap : (5192296858534827628530496329220096 : Uint256).val = 2 ^ 112 := rfl
      have hb0' : b0.val < 2 ^ 112 := by
        have := of_decide_eq_true hb0; rw [← hcap]; exact this
      have hb1' : b1.val < 2 ^ 112 := by
        have := of_decide_eq_true hb1; rw [← hcap]; exact this
      have hstor : ∀ (x : ContractState) n,
          (Verity.Core.NonReentrantGuard.setLock 9 0 x).storage n = x.storage n := fun _ _ => rfl
      rw [hstor, hstor]
      simp only [ContractState.storage, ContractState.writeSlot] at *
      exact ⟨by simpa using hb0', by simpa using hb1'⟩
    · simp at h
  · simp at h

/-- An address argument passes to an external call unchanged. -/
theorem externalArgAddress_address (a : Address) : externalArgAddress a = a := by
  simp only [externalArgAddress, externalArgWord, ExternalArg.toWords, List.head?_cons,
    Option.getD_some, wordToAddress]
  apply Core.Address.toNat_injective
  have h1 := Core.Address.val_lt_modulus a
  have h2 : a.toNat < Core.Uint256.modulus := lt_trans h1 (by decide)
  simp [Core.Address.toNat_ofNat, Nat.mod_eq_of_lt h2]
  exact Nat.mod_eq_of_lt h1

/-- Taking the reentrancy lock (transient storage) leaves address slots unchanged. -/
theorem setLock_readAddrSlot (s : ContractState) (n : Nat) :
    (Verity.Core.NonReentrantGuard.setLock 9 1 s).readAddrSlot n = s.storageAddr n := by
  simp [Verity.Core.NonReentrantGuard.setLock, ContractState.readAddrSlot,
    ContractState.writeTransient, ContractState.storageAddr]

/-- L9: after a successful `sync`, each reserve is the value its token returned to
`balanceOf(pool)`. The reads start at the locked pre-state and execute sequentially,
for every adversary (every token behaviour). -/
theorem sync_reserves_observed (ctx : ExecutableCallContext) (s s' : ContractState)
    (h : Pool.sync ctx s = .success () s') :
    ∃ mid last,
      balanceOf (s.storageAddr 1) s.thisAddress ctx.adversary
        (Verity.Core.NonReentrantGuard.setLock 9 1 s) = .success (s'.storage 3) mid ∧
      balanceOf (s.storageAddr 2) s.thisAddress ctx.adversary mid = .success (s'.storage 4) last := by
  unfold Pool.sync Verity.Core.NonReentrantGuard.guarded at h
  split at h
  · split at h
    · rename_i a s'' hbody
      injection h with _ hs'
      subst hs'
      replace hbody := Contract.eq_of_run_success hbody
      simp only [Bind.bind] at hbody
      obtain ⟨t0, s1, ht0, hbody⟩ := bind_success hbody
      obtain ⟨t1, s2, ht1, hbody⟩ := bind_success hbody
      obtain ⟨me, s3, hme, hbody⟩ := bind_success hbody
      obtain ⟨b0, s4, hb0r, hbody⟩ := bind_success hbody
      obtain ⟨b1, s5, hb1r, hbody⟩ := bind_success hbody
      obtain ⟨_, _, -, hbody⟩ := bind_success hbody
      obtain ⟨_, _, -, hbody⟩ := bind_success hbody
      obtain ⟨_, _, -, hbody⟩ := bind_success hbody
      obtain ⟨_, _, hw0, hbody⟩ := bind_success hbody
      simp only [setStorage, Pool.reserve0, Pool.reserve1] at hw0 hbody
      injection hw0 with _ hw0
      injection hbody with _ hbody
      subst hw0 hbody
      simp only [getStorageAddr, Pool.token0, Pool.token1] at ht0 ht1
      injection ht0 with ht0 hs1
      injection ht1 with ht1 hs2
      simp only [Contracts.contractAddress] at hme
      injection hme with hme hs3
      subst hs1 hs2 hs3 ht0 ht1 hme
      have hstor : ∀ (x : ContractState) n,
          (Verity.Core.NonReentrantGuard.setLock 9 0 x).storage n = x.storage n := fun _ _ => rfl
      rw [hstor, hstor]
      have h3 : ∀ (w : ContractState), ((w.writeSlot 3 b0).writeSlot 4 b1).storage 3 = b0 :=
        fun _ => by simp [ContractState.storage, ContractState.writeSlot]
      have h4 : ∀ (w : ContractState), ((w.writeSlot 3 b0).writeSlot 4 b1).storage 4 = b1 :=
        fun _ => by simp [ContractState.storage, ContractState.writeSlot]
      rw [h3, h4]
      rw [externalArgAddress_address, externalArgAddress_address, setLock_readAddrSlot]
        at hb0r hb1r
      exact ⟨_, _, hb0r, hb1r⟩
    · simp at h
  · simp at h

/-- Compatibility corollary; use `sync_reserves_observed` for anchored, sequential reads. -/
theorem sync_reserves_eq_reported (ctx : ExecutableCallContext) (s s' : ContractState)
    (h : Pool.sync ctx s = .success () s') :
    ∃ sA sA' sB sB',
      balanceOf (s.storageAddr 1) s.thisAddress ctx.adversary sA = .success (s'.storage 3) sA' ∧
      balanceOf (s.storageAddr 2) s.thisAddress ctx.adversary sB = .success (s'.storage 4) sB' := by
  obtain ⟨mid, last, h0, h1⟩ := sync_reserves_observed ctx s s' h
  exact ⟨_, mid, mid, last, h0, h1⟩

/-- Reserve-cap invariant for `mint`: after a successful mint both reserves are below
2^112, on the first-deposit path and on later deposits alike. -/
theorem mint_preserves_reserve_cap (ctx : ExecutableCallContext) (recipient : Address)
    (s s' : ContractState) (v : Uint256) (h : Pool.mint ctx recipient s = .success v s') :
    (s'.storage 3).val < 2 ^ 112 ∧ (s'.storage 4).val < 2 ^ 112 := by
  unfold Pool.mint Verity.Core.NonReentrantGuard.guarded at h
  split at h
  · split at h
    · rename_i a s'' hbody
      injection h with _ hs'
      subst hs'
      replace hbody := Contract.eq_of_run_success hbody
      simp only [Bind.bind] at hbody
      obtain ⟨_, _, -, hbody⟩ := bind_success hbody
      obtain ⟨_, _, -, hbody⟩ := bind_success hbody
      obtain ⟨_, _, -, hbody⟩ := bind_success hbody
      obtain ⟨b0, _, -, hbody⟩ := bind_success hbody
      obtain ⟨b1, _, -, hbody⟩ := bind_success hbody
      obtain ⟨_, _, hq, hbody⟩ := bind_success hbody
      obtain ⟨hb0, -⟩ := require_success hq
      obtain ⟨_, _, hq, hbody⟩ := bind_success hbody
      obtain ⟨hb1, -⟩ := require_success hq
      obtain ⟨_, _, -, hbody⟩ := bind_success hbody
      obtain ⟨_, _, -, hbody⟩ := bind_success hbody
      obtain ⟨_, _, -, hbody⟩ := bind_success hbody
      obtain ⟨_, _, -, hbody⟩ := bind_success hbody
      obtain ⟨_, _, -, hbody⟩ := bind_success hbody
      have hcap : (5192296858534827628530496329220096 : Uint256).val = 2 ^ 112 := rfl
      have hb0' : b0.val < 2 ^ 112 := by
        have := of_decide_eq_true hb0; rw [← hcap]; exact this
      have hb1' : b1.val < 2 ^ 112 := by
        have := of_decide_eq_true hb1; rw [← hcap]; exact this
      have hstor : ∀ (x : ContractState) n,
          (Verity.Core.NonReentrantGuard.setLock 9 0 x).storage n = x.storage n := fun _ _ => rfl
      rw [hstor, hstor]
      -- both branches end in the shared tail, whose last two steps write b0, b1
      split at hbody
      · iterate 5 (obtain ⟨_, _, -, hbody⟩ := bind_success hbody)
        iterate 8 (obtain ⟨_, _, -, hbody⟩ := bind_success hbody)
        obtain ⟨_, _, hw0, hbody⟩ := bind_success hbody
        obtain ⟨_, _, hw1, hbody⟩ := bind_success hbody
        simp only [setStorage, Pool.reserve0, Pool.reserve1, Verity.pure, Pure.pure] at hw0 hw1 hbody
        injection hw0 with _ hw0
        injection hw1 with _ hw1
        injection hbody with _ hbody
        subst hw0 hw1 hbody
        simp only [ContractState.storage, ContractState.writeSlot]
        exact ⟨by simpa using hb0', by simpa using hb1'⟩
      · iterate 1 (obtain ⟨_, _, -, hbody⟩ := bind_success hbody)
        iterate 8 (obtain ⟨_, _, -, hbody⟩ := bind_success hbody)
        obtain ⟨_, _, hw0, hbody⟩ := bind_success hbody
        obtain ⟨_, _, hw1, hbody⟩ := bind_success hbody
        simp only [setStorage, Pool.reserve0, Pool.reserve1, Verity.pure, Pure.pure] at hw0 hw1 hbody
        injection hw0 with _ hw0
        injection hw1 with _ hw1
        injection hbody with _ hbody
        subst hw0 hw1 hbody
        simp only [ContractState.storage, ContractState.writeSlot]
        exact ⟨by simpa using hb0', by simpa using hb1'⟩
    · simp at h
  · simp at h

/-- Reserve-cap invariant for `burn`: after a successful burn both reserves are below 2^112,
whatever the tokens report after the payouts. -/
theorem burn_preserves_reserve_cap (ctx : ExecutableCallContext) (recipient : Address)
    (s s' : ContractState) (v : Uint256 × Uint256)
    (h : Pool.burn ctx recipient s = .success v s') :
    (s'.storage 3).val < 2 ^ 112 ∧ (s'.storage 4).val < 2 ^ 112 := by
  unfold Pool.burn Verity.Core.NonReentrantGuard.guarded at h
  split at h
  · split at h
    · rename_i a s'' hbody
      injection h with _ hs'
      subst hs'
      replace hbody := Contract.eq_of_run_success hbody
      simp only [Bind.bind] at hbody
      iterate 14 (obtain ⟨_, _, -, hbody⟩ := bind_success hbody)
      obtain ⟨b0, _, -, hbody⟩ := bind_success hbody
      obtain ⟨b1, _, -, hbody⟩ := bind_success hbody
      obtain ⟨_, _, hq, hbody⟩ := bind_success hbody
      obtain ⟨hb0, -⟩ := require_success hq
      obtain ⟨_, _, hq, hbody⟩ := bind_success hbody
      obtain ⟨hb1, -⟩ := require_success hq
      iterate 3 (obtain ⟨_, _, -, hbody⟩ := bind_success hbody)
      obtain ⟨_, _, hw0, hbody⟩ := bind_success hbody
      obtain ⟨_, _, hw1, hbody⟩ := bind_success hbody
      simp only [setStorage, Pool.reserve0, Pool.reserve1, Verity.pure, Pure.pure] at hw0 hw1 hbody
      injection hw0 with _ hw0
      injection hw1 with _ hw1
      injection hbody with _ hbody
      subst hw0 hw1 hbody
      have hcap : (5192296858534827628530496329220096 : Uint256).val = 2 ^ 112 := rfl
      have hb0' : b0.val < 2 ^ 112 := by
        have := of_decide_eq_true hb0; rw [← hcap]; exact this
      have hb1' : b1.val < 2 ^ 112 := by
        have := of_decide_eq_true hb1; rw [← hcap]; exact this
      have hstor : ∀ (x : ContractState) n,
          (Verity.Core.NonReentrantGuard.setLock 9 0 x).storage n = x.storage n := fun _ _ => rfl
      rw [hstor, hstor]
      simp only [ContractState.storage, ContractState.writeSlot]
      exact ⟨by simpa using hb0', by simpa using hb1'⟩
    · simp at h
  · simp at h

end Dex.ProofKit

open Dex.ProofKit in
set_option maxRecDepth 8000 in
/-- L3: a successful swap keeps both reserves below 2^112 and never decreases
`reserve0 * reserve1`, for every behaviour of the token contracts (`ctx.adversary`),
provided the reserves start below 2^112 (an invariant every reserve write maintains). -/
theorem swap_k_nondecreasing (ctx : ExecutableCallContext) (out0 out1 : Uint256)
    (rcpt : Address) (s s' : ContractState)
    (hr0 : (s.storage 3).val < 2 ^ 112) (hr1 : (s.storage 4).val < 2 ^ 112)
    (h : Pool.swap ctx out0 out1 rcpt s = .success () s') :
    (s'.storage 3).val < 2 ^ 112 ∧ (s'.storage 4).val < 2 ^ 112 ∧
      (s.storage 3).val * (s.storage 4).val ≤ (s'.storage 3).val * (s'.storage 4).val := by
  unfold Pool.swap Verity.Core.NonReentrantGuard.guarded at h
  split at h
  · split at h
    · rename_i a s'' hbody
      injection h with _ hs'
      subst hs'
      replace hbody := Contract.eq_of_run_success hbody
      simp only [Bind.bind] at hbody
      obtain ⟨_, sA, hq, hbody⟩ := bind_success hbody
      obtain ⟨-, hsA⟩ := require_success hq
      obtain ⟨r0, sB, hg0, hbody⟩ := bind_success hbody
      obtain ⟨r1, sC, hg1, hbody⟩ := bind_success hbody
      simp only [getStorage, Pool.reserve0, Pool.reserve1] at hg0 hg1
      injection hg0 with hr0v hsB
      injection hg1 with hr1v hsC
      obtain ⟨_, sD, hq, hbody⟩ := bind_success hbody
      obtain ⟨-, hsD⟩ := require_success hq
      obtain ⟨_, sE, hq, hbody⟩ := bind_success hbody
      obtain ⟨-, hsE⟩ := require_success hq
      obtain ⟨t0, sF, hgt0, hbody⟩ := bind_success hbody
      obtain ⟨t1, sG, hgt1, hbody⟩ := bind_success hbody
      obtain ⟨_, sH, hq, hbody⟩ := bind_success hbody
      obtain ⟨-, hsH⟩ := require_success hq
      obtain ⟨_, sI, hq, hbody⟩ := bind_success hbody
      obtain ⟨-, hsI⟩ := require_success hq
      -- the reserves handed to `settle` are the stored ones (the lock only touches
      -- transient storage)
      have hr0s : r0 = s.storage 3 := by
        rw [← hr0v, hsA]; rfl
      have hr1s : r1 = s.storage 4 := by
        rw [← hr1v, ← hsB, hsA]; rfl
      -- the final state is `settle`'s, whichever payouts ran
      have hset : ∃ sJ, Pool.settle ctx r0 r1 out0 out1 t0 t1 rcpt sJ = .success a s'' := by
        split at hbody <;> (try obtain ⟨_, _, -, hbody⟩ := bind_success hbody) <;>
          split at hbody <;>
          (try obtain ⟨_, _, -, hbody⟩ := bind_success hbody) <;> exact ⟨_, hbody⟩
      obtain ⟨sJ, hset⟩ := hset
      have hstor : ∀ n, (Verity.Core.NonReentrantGuard.setLock 9 0 s'').storage n = s''.storage n :=
        fun _ => rfl
      rw [hstor 3, hstor 4]
      rw [hr0s, hr1s] at hset
      exact settle_k_nondecreasing _ _ _ _ _ _ _ _ _ _ hr0 hr1 hset
    · simp at h
  · simp at h

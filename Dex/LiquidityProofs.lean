import Dex.SwapProofs
import Verity.Proofs.Stdlib.Math

/-!
# L4: burns pay out a proportional share, bounded by the pool's balances

`erc20Read_frame`: a token read (`balanceOf`) is a static call, so it keeps the pool's
storage and address whatever the token answers.
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

/-- A token read keeps the caller's storage words and address, for every adversary. -/
theorem erc20Read_frame {adv : Compiler.CompilationModel.DenoteExternalCalls.AdversaryModel} {name : String} {token : Address}
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

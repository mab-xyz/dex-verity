import Dex.LiquidityProofs

/-! Consumer checks: observations start at the actual locked pre-state and chain.
The old existential statements cannot discharge these specifications. -/
open Verity Contracts Dex

example (ctx : ExecutableCallContext) (s s' : ContractState)
    (h : Pool.sync ctx s = .success () s') :
    ∃ mid last,
      balanceOf (s.storageAddr 1) s.thisAddress ctx.adversary
        (Core.NonReentrantGuard.setLock 9 1 s) = .success (s'.storage 3) mid ∧
      balanceOf (s.storageAddr 2) s.thisAddress ctx.adversary mid =
        .success (s'.storage 4) last :=
  Dex.ProofKit.sync_reserves_observed ctx s s' h

example (ctx : ExecutableCallContext) (recipient : Address)
    (s s' : ContractState) (v : Uint256 × Uint256)
    (h : Pool.burn ctx recipient s = .success v s') :
    ∃ b0 b1 mid last,
      balanceOf (s.storageAddr 1) s.thisAddress ctx.adversary
        (Core.NonReentrantGuard.setLock 9 1 s) = .success b0 mid ∧
      balanceOf (s.storageAddr 2) s.thisAddress ctx.adversary mid = .success b1 last ∧
      v.1.val * (s.storage 5).val ≤ (s.storageMap 6 s.thisAddress).val * b0.val ∧
      v.2.val * (s.storage 5).val ≤ (s.storageMap 6 s.thisAddress).val * b1.val ∧
      ((s.storageMap 6 s.thisAddress).val ≤ (s.storage 5).val →
        v.1.val ≤ b0.val ∧ v.2.val ≤ b1.val) :=
  burn_payout_le_observed ctx recipient s s' v h

#print axioms Dex.ProofKit.sync_reserves_observed
#print axioms burn_proportional_observed
#print axioms burn_payout_le_observed

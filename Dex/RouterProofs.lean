import Dex.Router
import Verity.Core.Model.NonReentrantGuard

/-!
# Router properties

R1: every router entry point reverts, without effect, once the block timestamp is past
the caller's deadline — before any token moves or external call.
-/

namespace Dex.RouterProofs

open Verity Contracts Dex

/-- Shared shape: a guarded body whose first action is `require (now ≤ deadline)`. -/
private theorem guarded_deadline_reverts {α : Type} (lockSlot : Nat) (deadline : Uint256)
    (rest : Contract α) (s : ContractState) (hlate : s.blockTimestamp > deadline) :
    ∃ msg, Verity.Core.NonReentrantGuard.guarded lockSlot
        (Verity.bind Contracts.blockTimestamp fun now =>
          Verity.bind (Verity.require (decide (now ≤ deadline)) "Router: EXPIRED") fun _ => rest) s =
      ContractResult.revert msg s := by
  unfold Verity.Core.NonReentrantGuard.guarded
  by_cases hlock : s.transientStorage lockSlot = 0
  · have hlt : deadline.val < s.blockTimestamp.val := hlate
    have hnot : ¬ (s.blockTimestamp.val ≤ deadline.val) := by omega
    simp [hlock, Verity.bind, Verity.require, Contract.run, Contracts.blockTimestamp,
      Verity.blockTimestamp, ContractState.writeTransient,
      Verity.Core.NonReentrantGuard.setLock, hnot]
  · simp [hlock]

/-- R1 for `swapExactIn`. -/
theorem swapExactIn_reverts_after_deadline (ctx : ExecutableCallContext)
    (amountIn amountOutMin : Uint256) (tokenIn tokenOut recipient : Address)
    (deadline : Uint256) (s : ContractState) (hlate : s.blockTimestamp > deadline) :
    ∃ msg, Router.swapExactIn ctx amountIn amountOutMin tokenIn tokenOut recipient deadline s =
      ContractResult.revert msg s := by
  unfold Router.swapExactIn
  exact guarded_deadline_reverts 1 deadline _ s hlate

/-- R1 for `addLiquidity`. -/
theorem addLiquidity_reverts_after_deadline (ctx : ExecutableCallContext)
    (tokenA tokenB : Address) (aDesired bDesired aMin bMin : Uint256) (recipient : Address)
    (deadline : Uint256) (s : ContractState) (hlate : s.blockTimestamp > deadline) :
    ∃ msg, Router.addLiquidity ctx tokenA tokenB aDesired bDesired aMin bMin recipient deadline s =
      ContractResult.revert msg s := by
  unfold Router.addLiquidity
  exact guarded_deadline_reverts 1 deadline _ s hlate

/-- R1 for `removeLiquidity`. -/
theorem removeLiquidity_reverts_after_deadline (ctx : ExecutableCallContext)
    (tokenA tokenB : Address) (liquidity aMin bMin : Uint256) (recipient : Address)
    (deadline : Uint256) (s : ContractState) (hlate : s.blockTimestamp > deadline) :
    ∃ msg, Router.removeLiquidity ctx tokenA tokenB liquidity aMin bMin recipient deadline s =
      ContractResult.revert msg s := by
  unfold Router.removeLiquidity
  exact guarded_deadline_reverts 1 deadline _ s hlate

end Dex.RouterProofs

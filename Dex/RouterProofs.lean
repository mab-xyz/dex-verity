import Dex.Router
import Verity.Core.Model.NonReentrantGuard
import Dex.SwapProofs

/-!
# Router properties

R1: every router entry point reverts, without effect, once the block timestamp is past
the caller's deadline — before any token moves or external call.
R2: a successful `swapExactIn` returns at least `amountOutMin`, whatever the factory,
pool and tokens answer.
R4: a successful `removeLiquidity` returns at least the caller's minimum of each token.
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

open Dex.ProofKit in
/-- R2: if `swapExactIn` succeeds, the output it reports (and asked the pool for) is at least
`amountOutMin`. -/
theorem swapExactIn_respects_min (ctx : ExecutableCallContext)
    (amountIn amountOutMin : Uint256) (tokenIn tokenOut recipient : Address)
    (deadline : Uint256) (s s' : ContractState) (v : Uint256)
    (h : Router.swapExactIn ctx amountIn amountOutMin tokenIn tokenOut recipient deadline s =
      .success v s') :
    amountOutMin ≤ v := by
  unfold Router.swapExactIn Verity.Core.NonReentrantGuard.guarded at h
  split at h
  · split at h
    · rename_i a s'' hbody
      injection h with ha _
      subst ha
      replace hbody := Contract.eq_of_run_success hbody
      simp only [Bind.bind] at hbody
      iterate 3 (obtain ⟨_, _, -, hbody⟩ := bind_success hbody)
      obtain ⟨⟨r0, r1⟩, _, -, hbody⟩ := bind_success hbody
      iterate 4 (obtain ⟨_, _, -, hbody⟩ := bind_success hbody)
      obtain ⟨_, _, hq, hbody⟩ := bind_success hbody
      obtain ⟨hmin, -⟩ := require_success hq
      iterate 3 (obtain ⟨_, _, -, hbody⟩ := bind_success hbody)
      simp only [Verity.pure, Pure.pure] at hbody
      injection hbody with hv _
      rw [← hv]
      exact of_decide_eq_true hmin
    · simp at h
  · simp at h

open Dex.ProofKit in
/-- R4: if `removeLiquidity` succeeds, the amounts of token A and token B it returns are at
least `amountAMin` and `amountBMin`, whatever the pool pays out. -/
theorem removeLiquidity_respects_mins (ctx : ExecutableCallContext)
    (tokenA tokenB : Address) (liquidity amountAMin amountBMin : Uint256) (recipient : Address)
    (deadline : Uint256) (s s' : ContractState) (v : Uint256 × Uint256)
    (h : Router.removeLiquidity ctx tokenA tokenB liquidity amountAMin amountBMin recipient
      deadline s = .success v s') :
    amountAMin ≤ v.1 ∧ amountBMin ≤ v.2 := by
  unfold Router.removeLiquidity Verity.Core.NonReentrantGuard.guarded at h
  split at h
  · split at h
    · rename_i a s'' hbody
      injection h with ha _
      subst ha
      replace hbody := Contract.eq_of_run_success hbody
      simp only [Bind.bind] at hbody
      iterate 5 (obtain ⟨_, _, -, hbody⟩ := bind_success hbody)
      obtain ⟨⟨x0, x1⟩, _, -, hbody⟩ := bind_success hbody
      obtain ⟨_, _, hq, hbody⟩ := bind_success hbody
      obtain ⟨hA, -⟩ := require_success hq
      obtain ⟨_, _, hq, hbody⟩ := bind_success hbody
      obtain ⟨hB, -⟩ := require_success hq
      simp only [Verity.pure, Pure.pure] at hbody
      injection hbody with hv _
      rw [← hv]
      exact ⟨of_decide_eq_true hA, of_decide_eq_true hB⟩
    · simp at h
  · simp at h

end Dex.RouterProofs

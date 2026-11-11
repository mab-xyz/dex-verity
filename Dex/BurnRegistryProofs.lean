import Dex.LiquidityProofs

/-!
# Burn under reentrancy (L2 for `burn`)

`burn` pays out through two token calls. In Verity's model a mutable external call may run
any sequence of the pool's own entry points (`CallbackBounded Pool.entrypointRegistry`).
`SupplyLocked c` (supply `= c`, lock held) is preserved by every entry point: the guarded
ones revert under the lock, the others never write the supply. So the supply `burn` writes
before its token calls is the one it ends with.
-/
open Verity Contracts Dex
open Compiler.CompilationModel.DenoteExternalCalls

namespace Dex.BurnRegistry

-- The eight unguarded entry-point obligations share one `simp` set; each uses part of it.
set_option linter.unusedSimpArgs false

/-- While the lock is held, the LP supply is `c`. -/
def SupplyLocked (c : Uint256) (w : ContractState) : Prop :=
  LockedInv (fun w => w.storage 5 = c) 9 w

theorem supplyLocked_frame (c : Uint256) (w : ContractState) (cs : List ExternalCall)
    (r : List Nat) (h : SupplyLocked c w) :
    SupplyLocked c { w with calls := cs, returndata := r } := h

/-- A token transfer preserves any invariant the registry preserves. -/
theorem erc20Write_preserves {Inv : ContractState → Prop} {entrypoints : EntrypointRegistry}
    {adv : AdversaryModel} {name : String} {token : Address} {args : List Uint256}
    {s s' : ContractState} {u : Unit}
    (hbound : CallbackBounded entrypoints adv) (hreg : RegistryPreserves Inv entrypoints adv)
    (hframe : ∀ w cs r, Inv w → Inv { w with calls := cs, returndata := r })
    (hInv : Inv s) (h : erc20Write adv name token args s = .success u s') : Inv s' := by
  unfold erc20Write at h
  have hpost : Inv ((commonExternalCall adv
      (linkedCallSite name args 0 .call token.toNat)).run s).snd := by
    rw [commonExternalCall, externalCall_run]
    simp only [ContractResult.snd, denoteCallJournaled]
    exact hframe _ _ _ (hbound.denoteCall_preserves_registry Inv entrypoints hreg _
      { world := s, gasRemaining := _ } hInv)
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

theorem mint_entrypoint_preserves (c : Uint256) (adv : AdversaryModel) :
    RegistryPreserves (SupplyLocked c) Pool.mint_entrypoint adv := by
  rintro g ⟨ctx, resolve, x0, _hcalldata, _hval, rfl⟩
  rw [Pool.mint_registry_eq]
  exact guarded_callback_preserves_locked _ 9 ctx _

theorem burn_entrypoint_preserves (c : Uint256) (adv : AdversaryModel) :
    RegistryPreserves (SupplyLocked c) Pool.burn_entrypoint adv := by
  rintro g ⟨ctx, resolve, x0, _hcalldata, _hval, rfl⟩
  rw [Pool.burn_registry_eq]
  exact guarded_callback_preserves_locked _ 9 ctx _

theorem swap_entrypoint_preserves (c : Uint256) (adv : AdversaryModel) :
    RegistryPreserves (SupplyLocked c) Pool.swap_entrypoint adv := by
  rintro g ⟨ctx, resolve, x0, x1, x2, _hcalldata, _hval, rfl⟩
  rw [Pool.swap_registry_eq]
  exact guarded_callback_preserves_locked _ 9 ctx _

theorem sync_entrypoint_preserves (c : Uint256) (adv : AdversaryModel) :
    RegistryPreserves (SupplyLocked c) Pool.sync_entrypoint adv := by
  rintro g ⟨ctx, resolve, _hcalldata, _hval, rfl⟩
  rw [Pool.sync_registry_eq]
  exact guarded_callback_preserves_locked _ 9 ctx _

theorem initPool_entrypoint_preserves (c : Uint256) (adv : AdversaryModel) :
    RegistryPreserves (SupplyLocked c) Pool.initPool_entrypoint adv := by
  rintro g ⟨ctx, resolve, x0, x1, _hcalldata, _hval, rfl⟩
  rw [Pool.initPool_registry_eq]
  apply callbackContractTransition_preserves
  intro s a s' ⟨hsup, hlock⟩ hrun
  simp [Pool.initPool, Contract.run, Verity.bind, Bind.bind, msgSender, setMapping2, setMapping, getMapping, getMapping2,
    getStorage, getStorageAddr, setStorage, setStorageAddr, Verity.require, Pool.allowances, Pool.balances,
    Pool.totalSupply, Pool.reserve0, Pool.reserve1, Pool.factory, Pool.token0, Pool.token1, Pool.initialized,
    Verity.pure, Pure.pure, emit, emitEvent, EventArg.toWord, List.mapM, List.mapM.loop] at hrun
  all_goals (repeat' (split_ifs at hrun <;> simp at hrun))
  all_goals (try (obtain ⟨-, rfl⟩ := hrun))
  all_goals simp_all [SupplyLocked, LockedInv, restoreCallbackContext, ContractState.storage,
    ContractState.writeMap2, ContractState.writeMap, ContractState.writeSlot,
    ContractState.writeAddrSlot, ContractState.transientStorage]

theorem getReserves_entrypoint_preserves (c : Uint256) (adv : AdversaryModel) :
    RegistryPreserves (SupplyLocked c) Pool.getReserves_entrypoint adv := by
  rintro g ⟨ctx, resolve, _hcalldata, _hval, rfl⟩
  rw [Pool.getReserves_registry_eq]
  apply callbackContractTransition_preserves
  intro s a s' ⟨hsup, hlock⟩ hrun
  simp [Pool.getReserves, Contract.run, Verity.bind, Bind.bind, msgSender, setMapping2, setMapping, getMapping, getMapping2,
    getStorage, getStorageAddr, setStorage, setStorageAddr, Verity.require, Pool.allowances, Pool.balances,
    Pool.totalSupply, Pool.reserve0, Pool.reserve1, Pool.factory, Pool.token0, Pool.token1, Pool.initialized,
    Verity.pure, Pure.pure, emit, emitEvent, EventArg.toWord, List.mapM, List.mapM.loop] at hrun
  all_goals (try (obtain ⟨-, rfl⟩ := hrun))
  all_goals simp_all [SupplyLocked, LockedInv, restoreCallbackContext, ContractState.storage,
    ContractState.writeMap2, ContractState.writeMap, ContractState.writeSlot,
    ContractState.writeAddrSlot, ContractState.transientStorage]

theorem lpBalanceOf_entrypoint_preserves (c : Uint256) (adv : AdversaryModel) :
    RegistryPreserves (SupplyLocked c) Pool.lpBalanceOf_entrypoint adv := by
  rintro g ⟨ctx, resolve, x0, _hcalldata, _hval, rfl⟩
  rw [Pool.lpBalanceOf_registry_eq]
  apply callbackContractTransition_preserves
  intro s a s' ⟨hsup, hlock⟩ hrun
  simp [Pool.lpBalanceOf, Contract.run, Verity.bind, Bind.bind, msgSender, setMapping2, setMapping, getMapping, getMapping2,
    getStorage, getStorageAddr, setStorage, setStorageAddr, Verity.require, Pool.allowances, Pool.balances,
    Pool.totalSupply, Pool.reserve0, Pool.reserve1, Pool.factory, Pool.token0, Pool.token1, Pool.initialized,
    Verity.pure, Pure.pure, emit, emitEvent, EventArg.toWord, List.mapM, List.mapM.loop] at hrun
  all_goals (try (obtain ⟨-, rfl⟩ := hrun))
  all_goals simp_all [SupplyLocked, LockedInv, restoreCallbackContext, ContractState.storage,
    ContractState.writeMap2, ContractState.writeMap, ContractState.writeSlot,
    ContractState.writeAddrSlot, ContractState.transientStorage]

theorem lpAllowance_entrypoint_preserves (c : Uint256) (adv : AdversaryModel) :
    RegistryPreserves (SupplyLocked c) Pool.lpAllowance_entrypoint adv := by
  rintro g ⟨ctx, resolve, x0, x1, _hcalldata, _hval, rfl⟩
  rw [Pool.lpAllowance_registry_eq]
  apply callbackContractTransition_preserves
  intro s a s' ⟨hsup, hlock⟩ hrun
  simp [Pool.lpAllowance, Contract.run, Verity.bind, Bind.bind, msgSender, setMapping2, setMapping, getMapping, getMapping2,
    getStorage, getStorageAddr, setStorage, setStorageAddr, Verity.require, Pool.allowances, Pool.balances,
    Pool.totalSupply, Pool.reserve0, Pool.reserve1, Pool.factory, Pool.token0, Pool.token1, Pool.initialized,
    Verity.pure, Pure.pure, emit, emitEvent, EventArg.toWord, List.mapM, List.mapM.loop] at hrun
  all_goals (try (obtain ⟨-, rfl⟩ := hrun))
  all_goals simp_all [SupplyLocked, LockedInv, restoreCallbackContext, ContractState.storage,
    ContractState.writeMap2, ContractState.writeMap, ContractState.writeSlot,
    ContractState.writeAddrSlot, ContractState.transientStorage]

theorem lpTotalSupply_entrypoint_preserves (c : Uint256) (adv : AdversaryModel) :
    RegistryPreserves (SupplyLocked c) Pool.lpTotalSupply_entrypoint adv := by
  rintro g ⟨ctx, resolve, _hcalldata, _hval, rfl⟩
  rw [Pool.lpTotalSupply_registry_eq]
  apply callbackContractTransition_preserves
  intro s a s' ⟨hsup, hlock⟩ hrun
  simp [Pool.lpTotalSupply, Contract.run, Verity.bind, Bind.bind, msgSender, setMapping2, setMapping, getMapping, getMapping2,
    getStorage, getStorageAddr, setStorage, setStorageAddr, Verity.require, Pool.allowances, Pool.balances,
    Pool.totalSupply, Pool.reserve0, Pool.reserve1, Pool.factory, Pool.token0, Pool.token1, Pool.initialized,
    Verity.pure, Pure.pure, emit, emitEvent, EventArg.toWord, List.mapM, List.mapM.loop] at hrun
  all_goals (try (obtain ⟨-, rfl⟩ := hrun))
  all_goals simp_all [SupplyLocked, LockedInv, restoreCallbackContext, ContractState.storage,
    ContractState.writeMap2, ContractState.writeMap, ContractState.writeSlot,
    ContractState.writeAddrSlot, ContractState.transientStorage]

theorem approve_entrypoint_preserves (c : Uint256) (adv : AdversaryModel) :
    RegistryPreserves (SupplyLocked c) Pool.approve_entrypoint adv := by
  rintro g ⟨ctx, resolve, x0, x1, _hcalldata, _hval, rfl⟩
  rw [Pool.approve_registry_eq]
  apply callbackContractTransition_preserves
  intro s a s' ⟨hsup, hlock⟩ hrun
  simp [Pool.approve, Contract.run, Verity.bind, Bind.bind, msgSender, setMapping2, setMapping, getMapping, getMapping2,
    getStorage, getStorageAddr, setStorage, setStorageAddr, Verity.require, Pool.allowances, Pool.balances,
    Pool.totalSupply, Pool.reserve0, Pool.reserve1, Pool.factory, Pool.token0, Pool.token1, Pool.initialized,
    Verity.pure, Pure.pure, emit, emitEvent, EventArg.toWord, List.mapM, List.mapM.loop] at hrun
  all_goals (try (obtain ⟨-, rfl⟩ := hrun))
  all_goals simp_all [SupplyLocked, LockedInv, restoreCallbackContext, ContractState.storage,
    ContractState.writeMap2, ContractState.writeMap, ContractState.writeSlot,
    ContractState.writeAddrSlot, ContractState.transientStorage]

theorem transfer_entrypoint_preserves (c : Uint256) (adv : AdversaryModel) :
    RegistryPreserves (SupplyLocked c) Pool.transfer_entrypoint adv := by
  rintro g ⟨ctx, resolve, x0, x1, _hcalldata, _hval, rfl⟩
  rw [Pool.transfer_registry_eq]
  apply callbackContractTransition_preserves
  intro s a s' ⟨hsup, hlock⟩ hrun
  simp [Pool.transfer, Contract.run, Verity.bind, Bind.bind, msgSender, setMapping2, setMapping, getMapping, getMapping2,
    getStorage, getStorageAddr, setStorage, setStorageAddr, Verity.require, Pool.allowances, Pool.balances,
    Pool.totalSupply, Pool.reserve0, Pool.reserve1, Pool.factory, Pool.token0, Pool.token1, Pool.initialized,
    Verity.pure, Pure.pure, emit, emitEvent, EventArg.toWord, List.mapM, List.mapM.loop] at hrun
  all_goals (repeat' (split_ifs at hrun <;> simp at hrun))
  all_goals (try (obtain ⟨-, rfl⟩ := hrun))
  all_goals simp_all [SupplyLocked, LockedInv, restoreCallbackContext, ContractState.storage,
    ContractState.writeMap2, ContractState.writeMap, ContractState.writeSlot,
    ContractState.writeAddrSlot, ContractState.transientStorage]

theorem transferFrom_entrypoint_preserves (c : Uint256) (adv : AdversaryModel) :
    RegistryPreserves (SupplyLocked c) Pool.transferFrom_entrypoint adv := by
  rintro g ⟨ctx, resolve, x0, x1, x2, _hcalldata, _hval, rfl⟩
  rw [Pool.transferFrom_registry_eq]
  apply callbackContractTransition_preserves
  intro s a s' ⟨hsup, hlock⟩ hrun
  simp [Pool.transferFrom, Contract.run, Verity.bind, Bind.bind, msgSender, setMapping2, setMapping, getMapping, getMapping2,
    getStorage, getStorageAddr, setStorage, setStorageAddr, Verity.require, Pool.allowances, Pool.balances,
    Pool.totalSupply, Pool.reserve0, Pool.reserve1, Pool.factory, Pool.token0, Pool.token1, Pool.initialized,
    Verity.pure, Pure.pure, emit, emitEvent, EventArg.toWord, List.mapM, List.mapM.loop] at hrun
  all_goals (repeat' (split_ifs at hrun <;> simp at hrun))
  all_goals (try (obtain ⟨-, rfl⟩ := hrun))
  all_goals simp_all [SupplyLocked, LockedInv, restoreCallbackContext, ContractState.storage,
    ContractState.writeMap2, ContractState.writeMap, ContractState.writeSlot,
    ContractState.writeAddrSlot, ContractState.transientStorage]

theorem registry_preserves (c : Uint256) (adv : AdversaryModel) :
    RegistryPreserves (SupplyLocked c) Pool.entrypointRegistry adv :=
  Pool.entrypointRegistry_preserves _ adv (initPool_entrypoint_preserves c adv)
    (getReserves_entrypoint_preserves c adv) (lpBalanceOf_entrypoint_preserves c adv)
    (lpAllowance_entrypoint_preserves c adv) (lpTotalSupply_entrypoint_preserves c adv)
    (approve_entrypoint_preserves c adv) (transfer_entrypoint_preserves c adv)
    (transferFrom_entrypoint_preserves c adv) (mint_entrypoint_preserves c adv)
    (burn_entrypoint_preserves c adv) (swap_entrypoint_preserves c adv)
    (sync_entrypoint_preserves c adv)

open Dex.ProofKit in
/-- L2 for `burn`: the supply drops by exactly the pool's own LP balance (the shares sent to
it), for every adversary whose reentrant calls are calls into the pool's entry points
(`CallbackBounded`). Holds although the token calls may re-enter `transfer`,
`transferFrom` or `approve`: none of them writes the supply, and every entry point that
does is under the lock `burn` holds. LP balances themselves can move during those calls,
so the theorem says nothing about them. -/
theorem burn_supply_drops_by_burned (ctx : ExecutableCallContext) (recipient : Address)
    (s s' : ContractState) (v : Uint256 × Uint256)
    (hbound : CallbackBounded Pool.entrypointRegistry ctx.adversary)
    (h : Pool.burn ctx recipient s = .success v s') :
    s'.storage 5 = EVM.Uint256.sub (s.storage 5) (s.storageMap 6 s.thisAddress) := by
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
      have hreg := registry_preserves (EVM.Uint256.sub (s.storage 5)
        (s.storageMap 6 s.thisAddress)) ctx.adversary
      have hS3 := erc20Write_preserves hbound hreg (supplyLocked_frame _) (by
        refine ⟨?_, ?_⟩
        · simp [ContractState.storage, ContractState.writeSlot, ContractState.writeMap,
            ContractState.readMap, ContractState.readSlot, ContractState.storageMap, hw5, hw4,
            Verity.Core.NonReentrantGuard.setLock, ContractState.writeTransient]
        · simp [ContractState.transientStorage, ContractState.writeSlot, ContractState.writeMap,
            hw5, hw4, Verity.Core.NonReentrantGuard.setLock, ContractState.writeTransient]
          decide) c3
      have hS4 := erc20Write_preserves hbound hreg (supplyLocked_frame _) hS3 c4
      obtain ⟨hsup4, -⟩ := hS4
      simp only [ContractState.storage, Verity.Core.NonReentrantGuard.setLock,
        ContractState.writeTransient, ContractState.writeSlot, hw16, hw15]
      simpa [ContractState.storage] using hsup4
    · simp at h
  · simp at h

end Dex.BurnRegistry

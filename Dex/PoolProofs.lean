import Dex.Pool
import Verity.Proofs.Stdlib.Automation
import Verity.Specs.Common.Sum

/-!
# Pool properties

Properties of `Dex.Pool` over Verity's EDSL semantics (the same code the compiler lowers to
the EVM bytecode tested in `test/`). Storage layout: factory 0, token0 1, token1 2,
reserve0 3, reserve1 4, totalSupply 5, balances 6, allowances 7, initialized 8, lock 9.
-/

namespace Dex.PoolProofs

open Verity
open Contracts
open Dex
open Verity.Proofs.Stdlib.Automation (address_beq_false_of_ne)
open Verity.Specs.Common (sumBalancesNat sumBalancesNat_transfer_conserved)
open Verity.Stdlib.Math (MAX_UINT256)

/-- L1a: only the factory can initialise the pool. -/
theorem initPool_reverts_when_not_factory (s : ContractState) (t0 t1 : Address)
    (h : s.sender ≠ s.storageAddr 0) :
    ∃ msg, (Pool.initPool t0 t1).run s = ContractResult.revert msg s := by
  simp only [Pool.initPool, Pool.factory, Pool.initialized, Pool.token0, Pool.token1,
    msgSender, getStorageAddr, getStorage, setStorage, setStorageAddr,
    Verity.require, Verity.bind, Bind.bind, Contract.run]
  simp [address_beq_false_of_ne s.sender (s.storageAddr 0) h, ContractState.readAddrSlot]

/-- L1b: the pool can be initialised only once. -/
theorem initPool_reverts_when_initialized (s : ContractState) (t0 t1 : Address)
    (hf : s.sender = s.storageAddr 0) (hi : s.storage 8 ≠ 0) :
    ∃ msg, (Pool.initPool t0 t1).run s = ContractResult.revert msg s := by
  simp only [Pool.initPool, Pool.factory, Pool.initialized, Pool.token0, Pool.token1,
    msgSender, getStorageAddr, getStorage, setStorage, setStorageAddr,
    Verity.require, Verity.bind, Bind.bind, Contract.run]
  simp [hf, hi, ContractState.readAddrSlot, ContractState.readSlot]

/-- L1c: the first initialisation by the factory succeeds… -/
theorem initPool_succeeds (s : ContractState) (t0 t1 : Address)
    (hf : s.sender = s.storageAddr 0) (hi : s.storage 8 = 0) :
    (Pool.initPool t0 t1).run s =
      ContractResult.success () ((Pool.initPool t0 t1).runState s) := by
  simp [Pool.initPool, Pool.factory, Pool.initialized, Pool.token0, Pool.token1,
    msgSender, getStorageAddr, getStorage, setStorage, setStorageAddr,
    Verity.require, Verity.bind, Bind.bind, Contract.run, Contract.runState,
    hf, hi, ContractState.readAddrSlot, ContractState.readSlot]

/-- …records both tokens… -/
theorem initPool_records_tokens (s : ContractState) (t0 t1 : Address)
    (hf : s.sender = s.storageAddr 0) (hi : s.storage 8 = 0) :
    ((Pool.initPool t0 t1).runState s).storageAddr 1 = t0 ∧
      ((Pool.initPool t0 t1).runState s).storageAddr 2 = t1 := by
  simp [Pool.initPool, Pool.factory, Pool.initialized, Pool.token0, Pool.token1,
    msgSender, getStorageAddr, getStorage, setStorage, setStorageAddr,
    Verity.require, Verity.bind, Bind.bind, Contract.runState,
    hf, hi, ContractState.readAddrSlot, ContractState.readSlot,
    ContractState.writeAddrSlot, ContractState.writeSlot, ContractState.storageAddr]

/-- …and marks the pool initialised, so every later `initPool` reverts (L1b). -/
theorem initPool_marks_initialized (s : ContractState) (t0 t1 : Address)
    (hf : s.sender = s.storageAddr 0) (hi : s.storage 8 = 0) :
    ((Pool.initPool t0 t1).runState s).storage 8 ≠ 0 := by
  have hi' : s.storageWords (StorageKey.slot 8) = 0 := hi
  simp [hi', Pool.initPool, Pool.factory, Pool.initialized, Pool.token0, Pool.token1,
    msgSender, getStorageAddr, getStorage, setStorage, setStorageAddr,
    Verity.require, Verity.bind, Bind.bind, Contract.runState,
    hf, ContractState.readAddrSlot, ContractState.readSlot,
    ContractState.writeAddrSlot, ContractState.writeSlot, ContractState.storage]
  decide

/-! ## L2: LP-share conservation -/

/-- `transfer` with enough balance succeeds. -/
theorem transfer_succeeds (s : ContractState) (dst : Address) (amount : Uint256)
    (hbal : s.storageMap 6 s.sender ≥ amount) :
    ∃ s', (Pool.transfer dst amount).run s = ContractResult.success true s' := by
  have hbal' : amount.val ≤ (s.storageMap 6 s.sender).val := hbal
  verity_unfold Pool.transfer
  simp [Pool.balances, ContractState.readMap, ContractState.writeMap, hbal',
    Contract.run, emitEvent]

/-- After a successful `transfer` to another address, the sender lost `amount`, the
recipient gained it, and every other LP balance is unchanged. -/
theorem transfer_balances (s : ContractState) (dst : Address) (amount : Uint256)
    (hne : s.sender ≠ dst) (hbal : s.storageMap 6 s.sender ≥ amount) (a : Address) :
    ((Pool.transfer dst amount).runState s).storageMap 6 a =
      (if a == dst then EVM.Uint256.add (s.storageMap 6 dst) amount
       else if a == s.sender then EVM.Uint256.sub (s.storageMap 6 s.sender) amount
       else s.storageMap 6 a) := by
  have hbal' : amount.val ≤ (s.storageMap 6 s.sender).val := hbal
  have hbal'' : amount.val ≤ (s.storageWords (StorageKey.map 6 s.sender)).val := hbal'
  verity_unfold Pool.transfer
  simp [Pool.balances, ContractState.readMap, ContractState.writeMap, hbal', hbal'',
    Contract.runState, emitEvent, ContractState.storageMap, msgSender, getMapping, setMapping,
    Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure]
  by_cases h1 : a = dst <;> by_cases h2 : a = s.sender <;> simp_all [Ne.symm hne]

/-- L2 for `transfer`: the sum of LP balances over any tracked set of holders that contains
both parties is unchanged (shares move, none are created or destroyed). The no-overflow
hypothesis on the recipient follows from the supply invariant `NoSupplyOverflow`. -/
theorem transfer_conserves_lp_sum (s : ContractState) (dst : Address) (amount : Uint256)
    (addrs : Verity.Core.FiniteAddressSet)
    (hne : s.sender ≠ dst) (hbal : s.storageMap 6 s.sender ≥ amount)
    (hs : s.sender ∈ addrs.addresses.elements) (hd : dst ∈ addrs.addresses.elements)
    (hadd : (s.storageMap 6 dst).val + amount.val ≤ MAX_UINT256) :
    sumBalancesNat 6 addrs ((Pool.transfer dst amount).runState s).storageMap =
      sumBalancesNat 6 addrs s.storageMap := by
  have hsub : amount.val ≤ (s.storageMap 6 s.sender).val := hbal
  have hcons := sumBalancesNat_transfer_conserved («slot» := 6) (balances := s.storageMap)
    (amount := amount) hs hd hne hsub hadd
  rw [← hcons]
  unfold sumBalancesNat
  congr 1
  funext acc a
  rw [transfer_balances s dst amount hne hbal a]
  simp

end Dex.PoolProofs

import Dex.NatAccountingProofs

/-! Executable arithmetic boundary controls against Pool.mint, with independent Nat
quotients as reference. These arbitrary pre-states are not reachability claims. -/
open Verity Contracts Dex
open Compiler.CompilationModel.DenoteExternalCalls

namespace Dex.AccountingChecks

private def state (supply : Nat) : ContractState :=
  let empty : ContractState := {
    storageWords := fun _ => 0
    storageArray := fun _ => []
    sender := 7
    thisAddress := 8
    msgValue := 0
    blockTimestamp := 0
    knownAddresses := fun _ => .empty }
  let funded := ((empty.writeSlot 3 1).writeSlot 4 1).writeSlot 5 (Core.Uint256.ofNat supply)
  funded.writeMap 6 7 (Core.Uint256.ofNat supply)

private def ctx (balance : Nat := 2) : ExecutableCallContext := .ofAdversary {
  stateTransition := fun _ s => s
  result := fun site _ => .success [if site.kind == .staticcall then balance else 1]
  gasUsed := fun _ _ => 0 }

private def mintCheck (supply : Nat) (exact : Bool) : Bool :=
  match Pool.mint (ctx 2) 7 (state supply) with
  | .revert _ _ => false
  | .success v post =>
    let expected := (2 - 1) * supply / 1
    v.val == expected &&
      (post.storage 5).val == (supply + expected) % (2^256) &&
      (post.storageMap 6 7).val == (supply + expected) % (2^256) &&
      ((post.storage 5).val == supply + expected) == exact

-- Positive control, last even sum below modulus, first overflowing sum.
#guard mintCheck 10000 true
#guard mintCheck (2^255 - 1) true
#guard mintCheck (2^255) false

private def firstMintCheck : Bool :=
  let initial := ((state 0).writeSlot 3 0).writeSlot 4 0
  match Pool.mint (ctx 2000) 7 initial with
  | .revert _ _ => false
  | .success v post =>
    v.val == 1000 && (post.storage 5).val == 2000 &&
      (post.storageMap 6 zeroAddress).val == 1000 &&
      (post.storageMap 6 7).val == 1000

#guard firstMintCheck

private def burnCheck (supply liq : Nat) (exact : Bool) : Bool :=
  let initial := (state supply).writeMap 6 8 (Core.Uint256.ofNat liq)
  match Pool.burn (ctx 2) 7 initial with
  | .revert _ _ => false
  | .success v post =>
    v.1.val == liq * 2 / supply && v.2.val == liq * 2 / supply &&
      (post.storage 5).val == (supply + 2^256 - liq) % (2^256) &&
      ((post.storage 5).val + liq == supply) == exact

-- Positive control, equality boundary, and underflow on an inconsistent ledger.
#guard burnCheck 10 5 true
#guard burnCheck 2 2 true
#guard burnCheck 1 2 false

end Dex.AccountingChecks

-- Consumer specifications: exact addition/subtraction, not modular equality.
example (ctx : ExecutableCallContext) (recipient : Address)
    (s s' : ContractState) (v : Uint256 × Uint256)
    (hb : CallbackBounded Pool.entrypointRegistry ctx.adversary)
    (h : Pool.burn ctx recipient s = .success v s') :
    ((s'.storage 5).val + (s.storageMap 6 s.thisAddress).val = (s.storage 5).val ↔
      (s.storageMap 6 s.thisAddress).val ≤ (s.storage 5).val) :=
  Dex.NatAccounting.burn_supply_exact_iff ctx recipient s s' v hb h

example (ctx : ExecutableCallContext) (recipient : Address)
    (s s' : ContractState) (v : Uint256) (hr : recipient ≠ zeroAddress)
    (h : Pool.mint ctx recipient s = .success v s') :
    ((s'.storage 5).val = (Dex.NatAccounting.mintBase s).val + v.val ↔
      (Dex.NatAccounting.mintBase s).val + v.val < Core.Uint256.modulus) :=
  Dex.NatAccounting.mint_supply_exact_iff ctx recipient s s' v hr h

#print axioms Dex.NatAccounting.mint_supply_exact_iff
#print axioms Dex.NatAccounting.burn_supply_exact_iff
#print axioms Dex.NatAccounting.mint_lp_accounting_nat
#print axioms Dex.NatAccounting.burn_supply_drops_nat

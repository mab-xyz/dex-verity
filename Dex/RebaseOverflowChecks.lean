import Dex.NatAccountingProofs

/-! Reachable executable witness under changing token balances. Only constructor,
initPool, mint and sync mutate pool state. The EVM counterpart uses actual rebasing
token storage, not invented balanceOf responses or direct pool storage writes. -/
open Verity Contracts Dex

namespace Dex.RebaseOverflowChecks

private def initial : ContractState := {
  storageWords := fun _ => 0
  storageArray := fun _ => []
  sender := 7
  thisAddress := 8
  msgValue := 0
  blockTimestamp := 0
  knownAddresses := fun _ => .empty }

private def ctx (balance : Nat) : ExecutableCallContext := .ofAdversary {
  stateTransition := fun _ s => s
  result := fun _ _ => .success [balance]
  gasUsed := fun _ _ => 0 }

private def step (r : ContractResult α) : Except String (α × ContractState) :=
  match r with
  | .success a s => .ok (a, s)
  | .revert msg _ => .error msg

private def check (p : Bool) (message : String) : Except String Unit :=
  if p then .ok () else .error message

private def ledger (s : ContractState) (supply : Nat) : Bool :=
  (s.storage 5).val == supply && (s.storageMap 6 7).val == supply - 1000 &&
    (s.storageMap 6 zeroAddress).val == 1000

private def grow (s : ContractState) (balance minted : Nat) : Except String ContractState := do
  let (_, s) ← step (Pool.sync (ctx 1) s)
  check ((s.storage 3).val == 1 && (s.storage 4).val == 1) "sync reserves"
  let (v, s) ← step (Pool.mint (ctx balance) 7 s)
  check (v.val == minted) "minted amount"
  check ((s.storage 3).val == balance && (s.storage 4).val == balance &&
    balance < 2^112) "mint reserves"
  return s

private def witness : Except String Unit := do
  let (_, s) ← step (Pool.constructor initial)
  let (_, s) ← step (Pool.initPool 1 2 s)
  check (s.storageAddr 0 == 7 && s.storageAddr 1 == 1 && s.storageAddr 2 == 2 &&
    s.storage 8 == 1) "initialization"
  let (v, s) ← step (Pool.mint (ctx (2^100)) 7 s)
  check (v.val == 2^100 - 1000 && ledger s (2^100)) "first mint"
  let s ← grow s (2^100) (2^200 - 2^100)
  check (ledger s (2^200)) "second mint"
  let s ← grow s (2^55) (2^255 - 2^200)
  check (ledger s (2^255)) "third mint"
  let s ← grow s 2 (2^255)
  check ((s.storage 5).val == 0 && (s.storageMap 6 7).val == 2^256 - 1000 &&
    (s.storageMap 6 zeroAddress).val == 1000) "reachable overflow"

-- Independent unbounded-integer reference, including the first overflowing boundary.
#guard 2^100 * 2^100 = (2^200 : Nat)
#guard 2^200 * 2^55 = (2^255 : Nat)
#guard 2^255 < (2^256 : Nat)
#guard ¬ (2^255 + 2^255 < (2^256 : Nat))
#guard witness == .ok ()

end Dex.RebaseOverflowChecks

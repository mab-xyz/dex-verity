import Mathlib.Tactic

/-!
# Constant-product AMM math

The formulas the DEX contracts compute, as functions on `Nat` (no wrapping), and their
properties. `Dex.Pool`/`Dex.Router` evaluate the same formulas on `Uint256` with
overflow-checked or 512-bit arithmetic; the contract proofs relate the two.

* `getAmountOut a rIn rOut`: output of an exact-in swap with a 0.3% fee.
* `getAmountIn out rIn rOut`: input needed for an exact-out swap.
* `quote a rA rB`: the amount of B worth `a` of A at the current price.
* `kCheck`: the pool's post-swap invariant, fee-adjusted balances against old reserves.
-/

namespace Dex.Math

/-- Fee numerator and denominator: 997/1000, i.e. a 0.3% fee on the input. -/
def feeNum : Nat := 997
def feeDen : Nat := 1000

/-- Output amount for `amountIn` against reserves `rIn`, `rOut`. -/
def getAmountOut (amountIn rIn rOut : Nat) : Nat :=
  amountIn * feeNum * rOut / (rIn * feeDen + amountIn * feeNum)

/-- Input amount needed to receive `amountOut` (rounded up by one). -/
def getAmountIn (amountOut rIn rOut : Nat) : Nat :=
  rIn * amountOut * feeDen / ((rOut - amountOut) * feeNum) + 1

/-- Amount of B equivalent to `amountA` of A at price `rB / rA`. -/
def quote (amountA rA rB : Nat) : Nat :=
  amountA * rB / rA

/-- The pool's swap acceptance condition: with balances `b0, b1` after the transfers and
`in0, in1` the amounts received, the fee-adjusted product must not fall below the old one. -/
def kCheck (r0 r1 b0 b1 in0 in1 : Nat) : Prop :=
  r0 * r1 * (feeDen * feeDen) ≤ (b0 * feeDen - in0 * (feeDen - feeNum)) *
    (b1 * feeDen - in1 * (feeDen - feeNum))

/-- P2: an exact-in swap never drains the output reserve. -/
theorem getAmountOut_lt_reserve {amountIn rIn rOut : Nat}
    (hrIn : 0 < rIn) (hrOut : 0 < rOut) :
    getAmountOut amountIn rIn rOut < rOut := by
  unfold getAmountOut feeNum feeDen
  have hden : 0 < rIn * 1000 + amountIn * 997 := by positivity
  rw [Nat.div_lt_iff_lt_mul hden]
  nlinarith [mul_pos hrIn hrOut]

/-- Floor division is monotone under the rational order `x/y ≤ z/w`. -/
theorem div_le_div_of_cross {x y z w : Nat} (hy : 0 < y) (hw : 0 < w)
    (h : x * w ≤ z * y) : x / y ≤ z / w := by
  rw [Nat.le_div_iff_mul_le hw]
  have hq : x / y * y ≤ x := Nat.div_mul_le_self x y
  have : x / y * w * y ≤ z * y := by
    calc x / y * w * y = (x / y * y) * w := by ring
      _ ≤ x * w := Nat.mul_le_mul_right w hq
      _ ≤ z * y := h
  exact Nat.le_of_mul_le_mul_right this hy

/-- P3: more input never gives less output. -/
theorem getAmountOut_mono {a b rIn rOut : Nat} (hrIn : 0 < rIn) (hab : a ≤ b) :
    getAmountOut a rIn rOut ≤ getAmountOut b rIn rOut := by
  unfold getAmountOut feeNum feeDen
  apply div_le_div_of_cross (by positivity) (by positivity)
  -- a*997*R*(K + b*997) ≤ b*997*R*(K + a*997) with K = rIn*1000
  have : a * 997 * rOut * (rIn * 1000) ≤ b * 997 * rOut * (rIn * 1000) := by
    gcongr
  nlinarith [this]

/-- P4: paying `amountIn` and taking `getAmountOut amountIn` passes the pool's k-check. -/
theorem kCheck_getAmountOut {amountIn rIn rOut : Nat} (hrIn : 0 < rIn) :
    kCheck rIn rOut (rIn + amountIn) (rOut - getAmountOut amountIn rIn rOut) amountIn 0 := by
  unfold kCheck
  set out := getAmountOut amountIn rIn rOut with hout
  have hD : 0 < rIn * feeDen + amountIn * feeNum := by
    unfold feeDen feeNum; positivity
  -- out * D ≤ amountIn * 997 * rOut
  have hfloor : out * (rIn * feeDen + amountIn * feeNum) ≤ amountIn * feeNum * rOut := by
    rw [hout]; unfold getAmountOut; exact Nat.div_mul_le_self _ _
  have hle : out ≤ rOut := by
    by_cases hr : rOut = 0
    · subst hr; simp [hout, getAmountOut]
    · exact (getAmountOut_lt_reserve hrIn (Nat.pos_of_ne_zero hr)).le
  unfold feeDen feeNum at *
  have h1 : (rIn + amountIn) * 1000 - amountIn * (1000 - 997) = rIn * 1000 + amountIn * 997 := by
    omega
  rw [h1, Nat.zero_mul, Nat.sub_zero]
  obtain ⟨k, hk⟩ : ∃ k, rOut = out + k := ⟨rOut - out, by omega⟩
  have hfloor' : out * (rIn * 1000 + amountIn * 997) ≤ amountIn * 997 * (out + k) := by
    rw [← hk]; exact hfloor
  have hsub : out + k - out = k := Nat.add_sub_cancel_left out k
  rw [hk, hsub]
  -- rIn*1000*out ≤ amountIn*997*k, from the floor bound
  nlinarith [hfloor']

/-- P5: `quote` never overstates the equivalent amount. -/
theorem quote_mul_le {amountA rA rB : Nat} : quote amountA rA rB * rA ≤ amountA * rB :=
  Nat.div_mul_le_self _ _

end Dex.Math

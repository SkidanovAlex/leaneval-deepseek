import Mathlib
import Submission.HvdH.Interfaces

/-!
# Area Recursion: real-valued packaging of the parameter functions

This module fixes the vocabulary used by the Recursion area.  Everything is a
`ℝ`-valued shadow of the (paper §5.1) parameter functions `bpar, ppar, apar,
kTpar, Tpar, rpar` and of `Nat.size`, together with the two estimates (one for
the transform term, one for the resampling term) into which the recursion
inequality of Corollary 5.5 splits.
-/

set_option autoImplicit false

namespace Work.Recursion

open HvdH

noncomputable section

/-- `d = 1729` as a real number. -/
def rD : ℝ := ((HvdH.D : ℕ) : ℝ)

/-- `b = ⌈log₂ n⌉` as a real number. -/
def rB (n : ℕ) : ℝ := ((HvdH.bpar n : ℕ) : ℝ)

/-- `p = 6b` as a real number. -/
def rP (n : ℕ) : ℝ := ((HvdH.ppar n : ℕ) : ℝ)

/-- `α` as a real number. -/
def rA (n : ℕ) : ℝ := ((HvdH.apar n : ℕ) : ℝ)

/-- `k_T` as a real number. -/
def rK (n : ℕ) : ℝ := ((HvdH.kTpar n : ℕ) : ℝ)

/-- `T = 2^{k_T}` as a real number. -/
def rT (n : ℕ) : ℝ := ((HvdH.Tpar n : ℕ) : ℝ)

/-- `r = 2^{⌈k_T/d⌉}` as a real number. -/
def rR (n : ℕ) : ℝ := ((HvdH.rpar n : ℕ) : ℝ)

/-- `Nat.size m` as a real number. -/
def rS (m : ℕ) : ℝ := ((m.size : ℕ) : ℝ)

/-- `Nat.sqrt m` as a real number. -/
def rQ (m : ℕ) : ℝ := ((Nat.sqrt m : ℕ) : ℝ)

/-- **Transform estimate.**  With `CmOf C m = C * (m * size m + 1)`, the first summand of
`mainCost` is `12 * (T/r) * C * (3 r p * size (3 r p) + 1)`; this says that (after cancelling
`C`) it is at most `(1 - 1/(2d)) * n * size n`. -/
def Est1 (n : ℕ) : Prop :=
  12 * (rT n / rR n) * ((3 * rR n * rP n) * rS (3 * rpar n * ppar n) + 1)
    ≤ (1 - 1 / (2 * rD)) * ((n : ℝ) * rS n)

/-- **Resampling estimate.**  The second summand of `mainCost` (after cancelling `C`) is at most
`(1/(8d)) * n * size n`. -/
def Est2 (K : ℕ) (n : ℕ) : Prop :=
  (K : ℝ) * rT n * (rQ (ppar n) + 1) * rA n * (((K : ℝ) * rP n) * rS (K * ppar n) + 1)
    ≤ (1 / (8 * rD)) * ((n : ℝ) * rS n)

/-- Hypotheses (all of them elementary estimates on the parameters) from which `Est1` follows by
elementary arithmetic. -/
def Est1Hyp (n : ℕ) : Prop :=
  1 ≤ rB n ∧ 1 ≤ rR n ∧
  rT n * rB n < 8 * (n : ℝ) ∧
  rS (3 * rpar n * ppar n) ≤ rK n / rD + Real.logb 2 (18 * rB n) + 3 ∧
  rK n ≤ Real.logb 2 (n : ℝ) + 3 ∧
  Real.logb 2 (n : ℝ) ≤ rS n ∧
  1728 * ((Real.logb 2 (n : ℝ) + 3) / rD + Real.logb 2 (18 * rB n) + 3) + 96
    ≤ (1 - 1 / (2 * rD)) * Real.logb 2 (n : ℝ)

/-- Hypotheses from which `Est2` follows by elementary arithmetic. -/
def Est2Hyp (K : ℕ) (n : ℕ) : Prop :=
  1 ≤ K ∧ 1 ≤ rB n ∧
  rT n * rB n < 8 * (n : ℝ) ∧
  rQ (ppar n) + 1 ≤ 4 * Real.sqrt (rB n) ∧
  rA n ≤ ((12 * rD ^ 2) ^ ((1 : ℝ) / 4) + 1) * (rB n) ^ ((1 : ℝ) / 4) ∧
  rS (K * ppar n) ≤ Real.logb 2 ((K : ℝ) * rP n) + 1 ∧
  Real.logb 2 (n : ℝ) ≤ rS n ∧
  192 * ((12 * rD ^ 2) ^ ((1 : ℝ) / 4) + 1) * (K : ℝ) ^ 2 * (rB n) ^ ((3 : ℝ) / 4)
      * (Real.logb 2 (6 * (K : ℝ) * rB n) + 2) ≤ (1 / (8 * rD)) * Real.logb 2 (n : ℝ)

end

end Work.Recursion

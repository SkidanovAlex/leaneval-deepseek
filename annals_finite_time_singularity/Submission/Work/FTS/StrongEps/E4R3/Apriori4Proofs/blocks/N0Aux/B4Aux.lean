/-
# `N0Aux.B4Aux` — small helpers for the level-`4` clause

Real-power bookkeeping for `α ∈ (0,1]` and the identification `(Xn f)² = HkSq α 4 f`, used in
`N0Aux.B4`.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.Vocab

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux

set_option autoImplicit false

/-- `(Xn α f)² = HkSq α 4 f`. -/
theorem xn_sq {α : ℝ} (f : ℝ → ℝ → ℝ) :
    (Work.FTS.Nonlin.Xn α f) ^ 2 = Work.Spaces.HkSq α 4 f := by
  rw [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 f)]

/-- `HkSq α 4 f = (Xn α f)²`. -/
theorem sq_xn {α : ℝ} (f : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α 4 f = (Work.FTS.Nonlin.Xn α f) ^ 2 := (xn_sq f).symm

/-- `α^a · α^b = α^{a+b}` for `α > 0`. -/
theorem rpow_mul_add {α : ℝ} (hα : 0 < α) (a b : ℝ) : α ^ a * α ^ b = α ^ (a + b) :=
  (Real.rpow_add hα a b).symm

/-- `(α^{-1/2})² = α^{-1}`. -/
theorem rpow_neg_half_sq {α : ℝ} (hα : 0 < α) :
    (α ^ (-(1 / 2 : ℝ))) ^ 2 = α ^ (-(1 : ℝ)) := by
  rw [← Real.rpow_natCast (α ^ (-(1 / 2 : ℝ))) 2, ← Real.rpow_mul hα.le]
  norm_num

/-- For `α ∈ (0,1]`, `α^s ≤ 1` for `s ≥ 0`, and `α^k * α^s = α^{k+s}`. -/
theorem rpow_le_one_of_nonneg {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {s : ℝ} (hs : 0 ≤ s) :
    α ^ s ≤ 1 := Real.rpow_le_one hα.le hα1 hs

/-- `α^a · α^b · α^c = α^{a+b+c}` for `α > 0`. -/
theorem rpow_three {α : ℝ} (hα : 0 < α) (a b c : ℝ) :
    α ^ a * α ^ b * α ^ c = α ^ (a + b + c) := by
  rw [rpow_mul_add hα, rpow_mul_add hα]

/-- `α^a · α^b · α^c · α^d = α^{a+b+c+d}` for `α > 0`. -/
theorem rpow_four {α : ℝ} (hα : 0 < α) (a b c d : ℝ) :
    α ^ a * α ^ b * α ^ c * α ^ d = α ^ (a + b + c + d) := by
  rw [rpow_mul_add hα, rpow_mul_add hα, rpow_mul_add hα]

/-- `(α^{-1/2})² = α^{-1} = α⁻¹`. -/
theorem neg_half_sq {α : ℝ} (hα : 0 < α) : (α ^ (-(1 / 2 : ℝ))) ^ 2 = α⁻¹ := by
  rw [rpow_neg_half_sq hα, Real.rpow_neg_one]

/-- `α^{k} = α^k` for a natural `k`, in the `rpow` form. -/
theorem rpow_nat {α : ℝ} (k : ℕ) : α ^ (k : ℝ) = α ^ k := Real.rpow_natCast α k

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux

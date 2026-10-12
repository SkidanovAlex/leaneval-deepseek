import Mathlib.Algebra.Order.Star.Real
import Submission.Work.UBBInputs3.MatLoc.Util
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.UBBInputs3.MatLoc.ProfileSupport` — support and positivity of the profile

The triangle profile `tri p` is supported on `[-p,p]`, so the normalised profile `prof p`
vanishes outside that window.  These are the facts used to deduce the window condition on
`winVec p ψ m` from the nonvanishing of `prof p (j-m)`.
-/

noncomputable section

open scoped BigOperators
open Finset

namespace Work.UBBInputs3

/-- `tri p 0 = p+1`. -/
theorem tri_zero (p : ℕ) : tri p 0 = (p : ℝ) + 1 := by
  unfold tri
  have h : |((0 : ℤ) : ℝ)| = 0 := by simp
  rw [h, sub_zero]
  exact max_eq_right (by positivity)

/-- `tri p s = 0` when `p+1 ≤ |s|`. -/
theorem tri_eq_zero_of_le_abs {p : ℕ} {s : ℤ} (h : (p : ℝ) + 1 ≤ |(s : ℝ)|) :
    tri p s = 0 := by
  unfold tri
  rw [max_eq_left]
  linarith

/-- `tri p s = 0` when `|s| > p`, for integer `s`. -/
theorem tri_eq_zero_of_lt_abs {p : ℕ} {s : ℤ} (h : (p : ℤ) < |s|) : tri p s = 0 := by
  refine tri_eq_zero_of_le_abs ?_
  have h' : (p : ℤ) + 1 ≤ |s| := by omega
  exact_mod_cast h'

/-- `prof p s = 0` when `|s| > p`. -/
theorem prof_eq_zero_of_lt_abs {p : ℕ} {s : ℤ} (h : (p : ℤ) < |s|) : prof p s = 0 := by
  unfold prof
  rw [tri_eq_zero_of_lt_abs h, zero_div]

/-- `|s| ≤ p` whenever `prof p s ≠ 0`. -/
theorem abs_le_of_prof_ne_zero {p : ℕ} {s : ℤ} (h : prof p s ≠ 0) : |s| ≤ (p : ℤ) := by
  by_contra hc
  push_neg at hc
  exact h (prof_eq_zero_of_lt_abs hc)

/-- The triangle mass is positive. -/
theorem triMass_pos (p : ℕ) : 0 < triMass p := by
  have h0 : 0 ∈ Finset.Icc (-(p : ℤ)) (p : ℤ) := by
    simp only [Finset.mem_Icc]
    omega
  have := Finset.single_le_sum (f := fun s => (tri p s) ^ 2) (fun s _ => sq_nonneg _) h0
  rw [tri_zero] at this
  have : (0:ℝ) < ((p : ℝ) + 1) ^ 2 := by positivity
  unfold triMass
  linarith

/-- `prof p` is nonnegative. -/
theorem prof_nonneg (p : ℕ) (s : ℤ) : 0 ≤ prof p s := by
  unfold prof
  have := triMass_pos p
  exact div_nonneg (le_max_left _ _) (Real.sqrt_nonneg _)

/-- `prof p 0 ≠ 0`. -/
theorem prof_zero_ne_zero (p : ℕ) : prof p 0 ≠ 0 := by
  unfold prof
  have hm : 0 < triMass p := triMass_pos p
  have h1 : tri p 0 ≠ 0 := by rw [tri_zero]; positivity
  have h2 : Real.sqrt (triMass p) ≠ 0 := by
    simp [Real.sqrt_eq_zero_of_nonpos, le_of_lt hm, ne_of_gt (Real.sqrt_pos_of_pos hm)]
  exact div_ne_zero h1 h2

/-- The deficit is nonnegative. -/
theorem gamma_nonneg (p : ℕ) (k : ℤ) : 0 ≤ gamma p k := by
  unfold gamma
  have : 0 ≤ ∑ s ∈ Finset.Icc (-(p : ℤ) - |k|) ((p : ℤ) + |k|),
      (prof p (s + k) - prof p s) ^ 2 := Finset.sum_nonneg (fun s _ => sq_nonneg _)
  linarith

end Work.UBBInputs3

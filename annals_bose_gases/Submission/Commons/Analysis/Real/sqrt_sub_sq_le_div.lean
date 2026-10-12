import Mathlib.Algebra.Order.Star.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.Analysis.Real

theorem sqrt_sub_sq_le_div {A B : ℝ} (hA : 0 < A) (hB : |B| ≤ A) :
    A - Real.sqrt (A ^ 2 - B ^ 2) ≤ B ^ 2 / A := by
  have hAsq : B ^ 2 ≤ A ^ 2 := by
    have h : |B| ≤ |A| := by rwa [abs_of_pos hA]
    exact sq_le_sq.mpr h
  have hnonneg : 0 ≤ A ^ 2 - B ^ 2 := by linarith
  set s := Real.sqrt (A ^ 2 - B ^ 2) with hs
  have hsq : s ^ 2 = A ^ 2 - B ^ 2 := by
    rw [hs]
    exact Real.sq_sqrt hnonneg
  have hsn : 0 ≤ s := Real.sqrt_nonneg _
  have hsle : s ≤ A := by
    have h1 : |s| ≤ |A| := sq_le_sq.mp (by nlinarith [hsq, sq_nonneg B])
    rwa [abs_of_nonneg hsn, abs_of_pos hA] at h1
  rw [le_div_iff₀ hA]
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hsn (sub_nonpos.mpr hsle), hsq]

end Commons.Analysis.Real
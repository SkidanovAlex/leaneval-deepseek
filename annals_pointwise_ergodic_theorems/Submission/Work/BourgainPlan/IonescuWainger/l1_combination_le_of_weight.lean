import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.tsum_norm_sq_sum_of_orthogonal

open scoped BigOperators lp

namespace Work.BourgainPlan.IonescuWainger

/-- For `C ≥ 0`, `(C²)^{1/2} = C`.  (Elementary scaffolding for the weighted Cauchy–Schwarz.) -/
theorem rpow_half_of_sq {C : ℝ} (hC : 0 ≤ C) : (C ^ 2) ^ ((1 : ℝ) / 2) = C := by
  calc (C ^ 2) ^ ((1 : ℝ) / 2) = Real.sqrt (C ^ 2) := (Real.sqrt_eq_rpow (C ^ 2)).symm
    _ = C := Real.sqrt_sq hC

/-- For `C ≥ 0`, if `A ≤ C²` then `A^{1/2} ≤ C`. -/
theorem rpow_half_le_of_le_sq {A C : ℝ} (hC : 0 ≤ C) (h : A ≤ C ^ 2) :
    A ^ ((1 : ℝ) / 2) ≤ C := by
  calc A ^ ((1 : ℝ) / 2) = Real.sqrt A := (Real.sqrt_eq_rpow A).symm
    _ ≤ Real.sqrt (C ^ 2) := Real.sqrt_le_sqrt h
    _ = C := Real.sqrt_sq hC

/-- For `C, D ≥ 0`, if `B ≤ C² · D` then `B^{1/2} ≤ C · D^{1/2}`. -/
theorem rpow_half_le_sq_mul {B C D : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (h : B ≤ C ^ 2 * D) : B ^ ((1 : ℝ) / 2) ≤ C * D ^ ((1 : ℝ) / 2) := by
  calc B ^ ((1 : ℝ) / 2) ≤ (C ^ 2 * D) ^ ((1 : ℝ) / 2) :=
        Real.rpow_le_rpow hB h (by norm_num)
    _ = (C ^ 2) ^ ((1 : ℝ) / 2) * D ^ ((1 : ℝ) / 2) := Real.mul_rpow (sq_nonneg C) hD
    _ = C * D ^ ((1 : ℝ) / 2) := by rw [rpow_half_of_sq hC]

end Work.BourgainPlan.IonescuWainger

import Mathlib
import Submission.Work.Holonomy3.defs

namespace Work.Holonomy3

theorem scale_coeff_bound (q : ℕ) (hq : 0 < q) (C A : ℝ) (hA : 1 ≤ A) (hC : 0 < C) (hCq : C ≤ (q : ℝ)) (f : PowerSeries ℚ) (hgr : ∀ n : ℕ, ‖((PowerSeries.coeff n f : ℚ) : ℝ)‖ ≤ C * A ^ n) (n : ℕ) : ‖((PowerSeries.coeff n ((q : ℚ)⁻¹ • f) : ℚ) : ℝ)‖ ≤ A ^ n := by
  have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hA0 : (0:ℝ) ≤ A := le_trans zero_le_one hA
  have hcoeff : PowerSeries.coeff n ((q : ℚ)⁻¹ • f) = (q:ℚ)⁻¹ * PowerSeries.coeff n f := by
    rw [PowerSeries.coeff_smul, smul_eq_mul, mul_comm]
  have h2 : ((q:ℝ))⁻¹ * C ≤ 1 := by
    have h3 : ((q:ℝ))⁻¹ * C ≤ ((q:ℝ))⁻¹ * (q:ℝ) :=
      mul_le_mul_of_nonneg_left hCq (inv_nonneg.mpr hqR.le)
    rwa [inv_mul_cancel₀ hqR.ne'] at h3
  rw [hcoeff]
  simp only [Rat.cast_mul, Rat.cast_inv, Rat.cast_natCast]
  rw [norm_mul, Real.norm_of_nonneg (inv_nonneg.mpr hqR.le)]
  calc ((q:ℝ))⁻¹ * ‖((PowerSeries.coeff n f : ℚ) : ℝ)‖
      ≤ ((q:ℝ))⁻¹ * (C * A ^ n) :=
        mul_le_mul_of_nonneg_left (hgr n) (inv_nonneg.mpr hqR.le)
    _ = (((q:ℝ))⁻¹ * C) * A ^ n := by ring
    _ ≤ 1 * A ^ n := mul_le_mul_of_nonneg_right h2 (pow_nonneg hA0 n)
    _ = A ^ n := one_mul _

end Work.Holonomy3

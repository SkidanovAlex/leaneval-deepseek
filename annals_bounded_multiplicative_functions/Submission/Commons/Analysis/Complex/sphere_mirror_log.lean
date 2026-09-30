import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Commons.Analysis.Complex

open scoped ComplexConjugate

/-- Mirror/inversion identity: if `‖z - a‖ = R`, the distance from `z` to the
mirror image `u' = a + R² / conj(u - a)` of `u` satisfies
`‖z - u'‖ * ‖u - a‖ = ‖z - u‖ * R`. -/
lemma sphere_mirror_norm_aux {a u z : ℂ} {R : ℝ} (hz : ‖z - a‖ = R) (hu : u ≠ a) :
    ‖z - (a + ((R * R : ℝ) : ℂ) * ((starRingEnd ℂ) (u - a))⁻¹)‖ * ‖u - a‖ =
      ‖z - u‖ * R := by
  have hnu_ne : ‖u - a‖ ≠ 0 := by
    exact ne_of_gt (norm_pos_iff.mpr (sub_ne_zero.mpr hu))
  have hw_star_eq : (z - a) * (starRingEnd ℂ) (z - a) = ((R * R : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]
    simp [pow_two]
  have hzU : z - (a + ((R * R : ℝ) : ℂ) * ((starRingEnd ℂ) (u - a))⁻¹) =
      (z - a) - ((R * R : ℝ) : ℂ) * ((starRingEnd ℂ) (u - a))⁻¹ := by ring
  have hmain : (z - a) - ((R * R : ℝ) : ℂ) * ((starRingEnd ℂ) (u - a))⁻¹ =
      (z - a) * (starRingEnd ℂ) ((u - a - (z - a)) / (u - a)) := by
    calc
      (z - a) - ((R * R : ℝ) : ℂ) * ((starRingEnd ℂ) (u - a))⁻¹
          = (z - a) - (z - a) * (starRingEnd ℂ) (z - a) * ((starRingEnd ℂ) (u - a))⁻¹ := by
              rw [← hw_star_eq]
      _ = (z - a) * (1 - (starRingEnd ℂ) (z - a) * ((starRingEnd ℂ) (u - a))⁻¹) := by ring
      _ = (z - a) * (1 - (starRingEnd ℂ) ((z - a) / (u - a))) := by
              congr 1
              rw [← div_eq_mul_inv, ← map_div₀ (starRingEnd ℂ) (z - a) (u - a)]
      _ = (z - a) * (starRingEnd ℂ) (1 - (z - a) / (u - a)) := by
              congr 1
              rw [map_sub (starRingEnd ℂ) 1 ((z - a) / (u - a))]
              simp
      _ = (z - a) * (starRingEnd ℂ) ((u - a - (z - a)) / (u - a)) := by
              congr 1
              congr 1
              field_simp
  have hnorm_norm : ‖(z - a) - ((R * R : ℝ) : ℂ) * ((starRingEnd ℂ) (u - a))⁻¹‖ =
      ‖z - a‖ * ‖u - z‖ * ‖u - a‖⁻¹ := by
    rw [hmain]
    calc
      ‖(z - a) * (starRingEnd ℂ) ((u - a - (z - a)) / (u - a))‖
          = ‖z - a‖ * ‖(starRingEnd ℂ) ((u - a - (z - a)) / (u - a))‖ := by
              rw [norm_mul]
      _ = ‖z - a‖ * ‖((u - a - (z - a)) / (u - a))‖ := by
              rw [Complex.norm_conj]
      _ = ‖z - a‖ * (‖u - a - (z - a)‖ / ‖u - a‖) := by
              rw [norm_div]
      _ = ‖z - a‖ * ‖u - z‖ * ‖u - a‖⁻¹ := by
              have huz : u - a - (z - a) = u - z := by ring
              rw [huz, div_eq_mul_inv]
              ring
  calc
    ‖z - (a + ((R * R : ℝ) : ℂ) * ((starRingEnd ℂ) (u - a))⁻¹)‖ * ‖u - a‖
        = ‖(z - a) - ((R * R : ℝ) : ℂ) * ((starRingEnd ℂ) (u - a))⁻¹‖ * ‖u - a‖ := by
            rw [hzU]
    _ = ‖z - a‖ * ‖u - z‖ := by
            rw [hnorm_norm]
            field_simp [hnu_ne]
    _ = ‖z - u‖ * R := by
            rw [hz, norm_sub_rev u z]
            ring

/-- The logarithmic mirror identity: for `z` on the circle `‖w - a‖ = R`, the
distances from `z` to a point `u ≠ a` and to its mirror image
`u' = a + R² / conj(u - a)` are related by
`log ‖z - u‖ = log ‖z - u'‖ + log (‖u - a‖ / R)`. -/
theorem sphere_mirror_log {a u z : ℂ} {R : ℝ} (hR : 0 < R) (hz : ‖z - a‖ = R)
    (hu : u ≠ a) (hzu : z ≠ u) :
    Real.log ‖z - u‖ =
      Real.log ‖z - (a + ((R * R : ℝ) : ℂ) * ((starRingEnd ℂ) (u - a))⁻¹)‖ +
        Real.log (‖u - a‖ / R) := by
  set U : ℂ := a + ((R * R : ℝ) : ℂ) * ((starRingEnd ℂ) (u - a))⁻¹ with hU
  have hnorm : ‖z - U‖ * ‖u - a‖ = ‖z - u‖ * R := by
    have hzU : z - U = z - (a + ((R * R : ℝ) : ℂ) * ((starRingEnd ℂ) (u - a))⁻¹) := by
      rw [hU]
    rw [hzU]
    exact sphere_mirror_norm_aux hz hu
  have hnz_ne : ‖z - u‖ ≠ 0 := by
    exact ne_of_gt (norm_pos_iff.mpr (sub_ne_zero.mpr hzu))
  have hnu_ne : ‖u - a‖ ≠ 0 := by
    exact ne_of_gt (norm_pos_iff.mpr (sub_ne_zero.mpr hu))
  have hR_ne : R ≠ 0 := ne_of_gt hR
  have hnU_ne : ‖z - U‖ ≠ 0 := by
    intro h0
    have hmul0 : ‖z - U‖ * ‖u - a‖ = 0 := by simp [h0]
    rw [hnorm] at hmul0
    exact (mul_ne_zero hnz_ne hR_ne) hmul0
  have hlogmul : Real.log (‖z - U‖ * ‖u - a‖) = Real.log (‖z - u‖ * R) := by
    rw [hnorm]
  have hlogs : Real.log ‖z - U‖ + Real.log ‖u - a‖ = Real.log ‖z - u‖ + Real.log R := by
    rw [Real.log_mul hnU_ne hnu_ne, Real.log_mul hnz_ne hR_ne] at hlogmul
    exact hlogmul
  have hlogdiv : Real.log (‖u - a‖ / R) = Real.log ‖u - a‖ - Real.log R :=
    Real.log_div hnu_ne hR_ne
  rw [hlogdiv]
  linarith

end Commons.Analysis.Complex
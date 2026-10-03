import Mathlib

namespace Work.FIArea5.S16Hecke

open MeasureTheory Set

/-- Change of variables `u = 1 / (B * v)` for integrals over `(0, ∞)`:
the substitution `v ↦ (B * v)⁻¹` is an involutive bijection of `Ioi 0` whose derivative
has absolute value `(B * v ^ 2)⁻¹`. -/
theorem integral_inv_scale (G : ℝ → ℂ) {B : ℝ} (hB : 0 < B) :
    (∫ v in Set.Ioi (0 : ℝ), G (1 / (B * v)) * (((B * v ^ 2)⁻¹ : ℝ) : ℂ)) = ∫ u in Set.Ioi (0 : ℝ), G u := by
  simp only [one_div]
  have hderiv : ∀ v ∈ Set.Ioi (0:ℝ),
      HasDerivWithinAt (fun w : ℝ => (B * w)⁻¹) (-(B * v ^ 2)⁻¹) (Set.Ioi 0) v := by
    intro v hv
    have hv0 : v ≠ 0 := ne_of_gt hv
    have hBv : B * v ≠ 0 := mul_ne_zero hB.ne' hv0
    have hinner : HasDerivAt (fun w : ℝ => B * w) B v := by
      simpa using (hasDerivAt_id v).const_mul B
    have h := hinner.inv hBv
    have heq : -(B * v ^ 2)⁻¹ = -B / (B * v) ^ 2 := by
      field_simp
    rw [heq]
    exact h.hasDerivWithinAt
  have hinj : InjOn (fun w : ℝ => (B * w)⁻¹) (Set.Ioi 0) := by
    intro u hu v hv huv
    have : B * u = B * v := inv_inj.mp huv
    exact mul_left_cancel₀ hB.ne' this
  have himage : (fun w : ℝ => (B * w)⁻¹) '' Set.Ioi 0 = Set.Ioi 0 := by
    ext u
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact inv_pos.mpr (mul_pos hB hv)
    · intro hu
      refine ⟨(B * u)⁻¹, inv_pos.mpr (mul_pos hB hu), ?_⟩
      field_simp
  have key := integral_image_eq_integral_abs_deriv_smul (s := Set.Ioi (0:ℝ))
    measurableSet_Ioi hderiv hinj G
  rw [himage] at key
  rw [key]
  refine setIntegral_congr_fun measurableSet_Ioi ?_
  intro v hv
  change G ((B * v)⁻¹) * (((B * v ^ 2)⁻¹ : ℝ) : ℂ) = |(-(B * v ^ 2)⁻¹)| • G ((B * v)⁻¹)
  have hvpos : 0 < B * v ^ 2 := mul_pos hB (pow_pos hv 2)
  have hfinv : (0:ℝ) < (B * v ^ 2)⁻¹ := inv_pos.mpr hvpos
  have habs : |(-(B * v ^ 2)⁻¹)| = (B * v ^ 2)⁻¹ := by
    rw [abs_neg, abs_of_pos hfinv]
  rw [habs, Complex.real_smul]
  exact mul_comm _ _

end Work.FIArea5.S16Hecke

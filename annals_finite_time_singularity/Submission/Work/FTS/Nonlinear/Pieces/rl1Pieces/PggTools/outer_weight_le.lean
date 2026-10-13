import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.H2.InvOneAddSq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The outer weight bound: `∫⁻ (1/z)·Φ^{1/2} ≤ √2 · √(∫ w·Φ)`

This is the radial Cauchy–Schwarz estimate behind the `rl¹`-rows of the nonlinearity: the
singular factor `1/z` of the outer region is split against the weight `w z = (1+z)²/z²`,

```
1/z · √(Φ z) = √(w z · Φ z) · (1+z)⁻¹          (z > 0),
```

so that `√(w z · Φ z)` is square-integrable exactly when `∫ w · Φ < ∞`, while the *second*
factor `(1+z)⁻¹` contributes only the universal constant
`(∫₀^∞ (1+z)⁻²)^{1/2} ≤ √2` (`Work.FTS.H2.InvOneAddSq`).  The proof is Hölder's inequality
in `L²` (`ENNReal.lintegral_mul_le_Lp_mul_Lq` with `p = q = 2`) applied to the two factors,
after converting the `ℝ≥0∞`-integral `∫⁻ ofReal (w·Φ)` of the first factor back into the real
integral `∫ w·Φ`.

The constant `√2` is not optimal (the sharp constant is `1 = (∫₀^∞ (1+z)⁻²)^{1/2}`), but the
statement only needs `√2`, and this is what the available weight lemma provides.
-/

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.rl1Pieces.PggTools

/-- `Work.Spaces.w` is nonnegative. -/
theorem outer_weight_w_nonneg (z : ℝ) : 0 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w]
  exact div_nonneg (sq_nonneg _) (sq_nonneg _)

/-- `Work.Spaces.w z = ((1+z)/z)²`, the form in which the square root is taken. -/
theorem outer_weight_w_eq (z : ℝ) : Work.Spaces.w z = ((1 + z) / z) ^ 2 := by
  rw [Work.Spaces.w, ← div_pow]

/-- `z ↦ Work.Spaces.w z` is measurable. -/
theorem outer_weight_w_measurable : Measurable (fun z : ℝ => Work.Spaces.w z) := by
  unfold Work.Spaces.w
  fun_prop

/-- The pointwise split of the radial singular factor: for `z > 0`,
`(1/z)·√(Φ z) = √(w z · Φ z)·(1+z)⁻¹`, expressed in `ℝ≥0∞` with `ENNReal.ofReal`. -/
theorem outer_weight_pointwise {Φ : ℝ → ℝ} (hΦnn : ∀ z, 0 ≤ Φ z) {z : ℝ} (hz : 0 < z) :
    ENNReal.ofReal z⁻¹ * (ENNReal.ofReal (Φ z)) ^ (1 / 2 : ℝ)
      = ENNReal.ofReal (Real.sqrt (Work.Spaces.w z * Φ z)) * ENNReal.ofReal ((1 + z)⁻¹) := by
  have h1 : (ENNReal.ofReal (Φ z)) ^ (1 / 2 : ℝ) = ENNReal.ofReal (Real.sqrt (Φ z)) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (hΦnn z) (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ← Real.sqrt_eq_rpow]
  have h2 : ENNReal.ofReal z⁻¹ * ENNReal.ofReal (Real.sqrt (Φ z))
      = ENNReal.ofReal (z⁻¹ * Real.sqrt (Φ z)) := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hz.le)]
  have hsqrt : Real.sqrt (Work.Spaces.w z * Φ z) = ((1 + z) / z) * Real.sqrt (Φ z) := by
    rw [outer_weight_w_eq z, Real.sqrt_mul (sq_nonneg ((1 + z) / z)) (Φ z),
      Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
  have h3 : z⁻¹ * Real.sqrt (Φ z) = Real.sqrt (Work.Spaces.w z * Φ z) * (1 + z)⁻¹ := by
    rw [hsqrt]
    field_simp
  rw [h1, h2, h3, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]

theorem outer_weight_le {Φ : ℝ → ℝ}
    (hΦnn : ∀ z, 0 ≤ Φ z)
    (hΦmeas : AEMeasurable Φ (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hΦint : MeasureTheory.IntegrableOn (fun z => Work.Spaces.w z * Φ z) (Set.Ioi 0)) :
    (∫⁻ z in Set.Ioi (0 : ℝ), ENNReal.ofReal z⁻¹ * (ENNReal.ofReal (Φ z)) ^ (1 / 2 : ℝ))
      ≤ ENNReal.ofReal (Real.sqrt 2 * Real.sqrt (∫ z in Set.Ioi (0 : ℝ), Work.Spaces.w z * Φ z)) := by
  -- the two `L²` factors
  have hAmeas : AEMeasurable (fun z : ℝ => ENNReal.ofReal (Real.sqrt (Work.Spaces.w z * Φ z)))
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    (outer_weight_w_measurable.aemeasurable.mul hΦmeas).sqrt.ennreal_ofReal
  have hBmeas : AEMeasurable (fun z : ℝ => ENNReal.ofReal ((1 + z)⁻¹))
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    (by fun_prop : Measurable (fun z : ℝ => ENNReal.ofReal ((1 + z)⁻¹))).aemeasurable
  -- Hölder in `L²`
  have hholder : (∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal (Real.sqrt (Work.Spaces.w z * Φ z)) * ENNReal.ofReal ((1 + z)⁻¹))
      ≤ (∫⁻ z in Set.Ioi (0 : ℝ),
            (ENNReal.ofReal (Real.sqrt (Work.Spaces.w z * Φ z))) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
        * (∫⁻ z in Set.Ioi (0 : ℝ), (ENNReal.ofReal ((1 + z)⁻¹)) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
      (p := 2) (q := 2) Real.HolderConjugate.two_two hAmeas hBmeas
    simpa only [Pi.mul_apply] using h
  -- nonnegativity of the `z`-integral
  have hI : 0 ≤ ∫ z in Set.Ioi (0 : ℝ), Work.Spaces.w z * Φ z :=
    MeasureTheory.integral_nonneg (fun z => mul_nonneg (outer_weight_w_nonneg z) (hΦnn z))
  -- the first factor's `L²`-integral is `∫ w · Φ`
  have hA2 : (∫⁻ z in Set.Ioi (0 : ℝ),
        (ENNReal.ofReal (Real.sqrt (Work.Spaces.w z * Φ z))) ^ (2 : ℝ))
      = ENNReal.ofReal (∫ z in Set.Ioi (0 : ℝ), Work.Spaces.w z * Φ z) := by
    have hpt2 : ∀ z, (ENNReal.ofReal (Real.sqrt (Work.Spaces.w z * Φ z))) ^ (2 : ℝ)
        = ENNReal.ofReal (Work.Spaces.w z * Φ z) := by
      intro z
      rw [ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 2),
        Real.rpow_two, Real.sq_sqrt (mul_nonneg (outer_weight_w_nonneg z) (hΦnn z))]
    rw [MeasureTheory.lintegral_congr_ae (Filter.Eventually.of_forall hpt2)]
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hΦint
      (Filter.Eventually.of_forall (fun z => mul_nonneg (outer_weight_w_nonneg z) (hΦnn z)))]
  have hA1 : (ENNReal.ofReal (∫ z in Set.Ioi (0 : ℝ), Work.Spaces.w z * Φ z)) ^ (1 / 2 : ℝ)
      = ENNReal.ofReal (Real.sqrt (∫ z in Set.Ioi (0 : ℝ), Work.Spaces.w z * Φ z)) := by
    rw [ENNReal.ofReal_rpow_of_nonneg hI (by norm_num : (0 : ℝ) ≤ 1 / 2), ← Real.sqrt_eq_rpow]
  -- the second factor's `L²`-integral is bounded by `2`
  have hBint : MeasureTheory.IntegrableOn (fun z : ℝ => ((1 + z)⁻¹) ^ 2) (Set.Ioi 0) := by
    simpa only [one_div] using Work.FTS.H2.InvOneAddSq.1
  have hBle : (∫ z in Set.Ioi (0 : ℝ), ((1 + z)⁻¹) ^ 2) ≤ 2 := by
    simpa only [one_div] using Work.FTS.H2.InvOneAddSq.2
  have hB2 : (∫⁻ z in Set.Ioi (0 : ℝ), (ENNReal.ofReal ((1 + z)⁻¹)) ^ (2 : ℝ))
      = ENNReal.ofReal (∫ z in Set.Ioi (0 : ℝ), ((1 + z)⁻¹) ^ 2) := by
    have hpt2 : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
        (ENNReal.ofReal ((1 + z)⁻¹)) ^ (2 : ℝ) = ENNReal.ofReal (((1 + z)⁻¹) ^ 2) := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
      have hz0 : (0 : ℝ) < z := Set.mem_Ioi.mp hz
      rw [ENNReal.ofReal_rpow_of_nonneg (inv_nonneg.mpr (by linarith : (0 : ℝ) ≤ 1 + z))
        (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_two]
    rw [MeasureTheory.lintegral_congr_ae hpt2]
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hBint
      (Filter.Eventually.of_forall (fun z => sq_nonneg _))]
  have hB2le : (ENNReal.ofReal (∫ z in Set.Ioi (0 : ℝ), ((1 + z)⁻¹) ^ 2)) ^ (1 / 2 : ℝ)
      ≤ ENNReal.ofReal (Real.sqrt 2) := by
    calc (ENNReal.ofReal (∫ z in Set.Ioi (0 : ℝ), ((1 + z)⁻¹) ^ 2)) ^ (1 / 2 : ℝ)
        ≤ (ENNReal.ofReal 2) ^ (1 / 2 : ℝ) :=
          ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hBle) (by norm_num)
      _ = ENNReal.ofReal (Real.sqrt 2) := by
          rw [ENNReal.ofReal_rpow_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)
              (by norm_num : (0 : ℝ) ≤ 1 / 2),
            ← Real.sqrt_eq_rpow]
  -- the pointwise split, a.e.
  have hcongr : (∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal z⁻¹ * (ENNReal.ofReal (Φ z)) ^ (1 / 2 : ℝ))
      = ∫⁻ z in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (Real.sqrt (Work.Spaces.w z * Φ z)) * ENNReal.ofReal ((1 + z)⁻¹) := by
    refine MeasureTheory.lintegral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
    exact outer_weight_pointwise hΦnn (Set.mem_Ioi.mp hz)
  calc (∫⁻ z in Set.Ioi (0 : ℝ), ENNReal.ofReal z⁻¹ * (ENNReal.ofReal (Φ z)) ^ (1 / 2 : ℝ))
      = ∫⁻ z in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (Real.sqrt (Work.Spaces.w z * Φ z)) * ENNReal.ofReal ((1 + z)⁻¹) := hcongr
    _ ≤ (∫⁻ z in Set.Ioi (0 : ℝ),
            (ENNReal.ofReal (Real.sqrt (Work.Spaces.w z * Φ z))) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
          * (∫⁻ z in Set.Ioi (0 : ℝ), (ENNReal.ofReal ((1 + z)⁻¹)) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := hholder
    _ = ENNReal.ofReal (Real.sqrt (∫ z in Set.Ioi (0 : ℝ), Work.Spaces.w z * Φ z))
          * (∫⁻ z in Set.Ioi (0 : ℝ), (ENNReal.ofReal ((1 + z)⁻¹)) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
        rw [hA2, hA1]
    _ = ENNReal.ofReal (Real.sqrt (∫ z in Set.Ioi (0 : ℝ), Work.Spaces.w z * Φ z))
          * (ENNReal.ofReal (∫ z in Set.Ioi (0 : ℝ), ((1 + z)⁻¹) ^ 2)) ^ (1 / 2 : ℝ) := by
        rw [hB2]
    _ ≤ ENNReal.ofReal (Real.sqrt (∫ z in Set.Ioi (0 : ℝ), Work.Spaces.w z * Φ z))
          * ENNReal.ofReal (Real.sqrt 2) := mul_le_mul_right hB2le _
    _ = ENNReal.ofReal (Real.sqrt 2 * Real.sqrt (∫ z in Set.Ioi (0 : ℝ), Work.Spaces.w z * Φ z)) := by
        rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
        congr 1
        ring

end Work.FTS.Nonlinear.Pieces.rl1Pieces.PggTools

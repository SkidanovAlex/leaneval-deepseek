import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner

/-!
# Adjointness of convolution against the (conjugate-linear) inner product

For a measurable weight `K : ℝ → ℂ` bounded by `B`, and integrable functions
`F G : ℝ → H` with values in a complex Hilbert space `H`, the convolution operator
`T_K F = (x ↦ ∫ y, K (x - y) • F y)` satisfies

`∫ x, ⟪(T_K F) x, G x⟫ = ∫ x, ⟪F x, (T_{K*} G) x⟫`,

where the adjoint kernel is `K* z = conj (K (-z))`; here it is written in the
equivalent form `conj (K (y - x))` inside the integral.

Both sides are the same product integral
`∫ z : ℝ × ℝ, conj (K (z.1 - z.2)) * ⟪F z.2, G z.1⟫` (up to Fubini and a change of
variables), which is the standard self-adjointness of convolution with respect to the
sesquilinear pairing `⟪·,·⟫`.
-/

namespace Commons.Analysis.Convolution

open MeasureTheory

/-- Inner product with a fixed vector commutes with the Bochner integral (left slot):

`⟪∫ x, φ x, v⟫ = ∫ x, ⟪φ x, v⟫`.  The map `w ↦ ⟪w, v⟫` is conjugate-linear over `ℂ`,
hence `ℝ`-linear and continuous, so this is `ContinuousLinearMap.integral_comp_comm`
applied to `conj ∘ innerSL v`. -/
theorem inner_integral_left {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {φ : ℝ → H} (hφ : Integrable φ) (v : H) :
    inner ℂ (∫ x, φ x) v = ∫ x, inner ℂ (φ x) v := by
  set T : H →L[ℝ] ℂ :=
    (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.comp
      ((innerSL ℂ v).restrictScalars ℝ) with hT
  have hTapply : ∀ w : H, T w = inner ℂ w v := by
    intro w
    have hr : ((innerSL ℂ v).restrictScalars ℝ) w = inner ℂ v w := by
      rw [show ((innerSL ℂ v).restrictScalars ℝ) w = (innerSL ℂ v) w from rfl]
      exact innerSL_apply_apply ℂ v w
    rw [hT]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
    change (Complex.conjCLE : ℂ → ℂ) (((innerSL ℂ v).restrictScalars ℝ) w) = inner ℂ w v
    rw [hr, Complex.conjCLE_apply]
    exact inner_conj_symm w v
  have h := ContinuousLinearMap.integral_comp_comm T hφ
  rw [show T (∫ x, φ x) = inner ℂ (∫ x, φ x) v from hTapply _] at h
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact (hTapply (φ x))

/-- Inner product with a fixed vector commutes with the Bochner integral (right slot):

`⟪v, ∫ x, φ x⟫ = ∫ x, ⟪v, φ x⟫`, as `innerSL ℂ v` is `ℂ`-linear and continuous. -/
theorem inner_integral_right {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {φ : ℝ → H} (hφ : Integrable φ) (v : H) :
    inner ℂ v (∫ x, φ x) = ∫ x, inner ℂ v (φ x) := by
  exact (ContinuousLinearMap.integral_comp_comm (innerSL ℂ v) hφ).symm

/-- The integrand `y ↦ K (x - y) • F y` is integrable, for a measurable weight bounded by `B`
and an integrable `F`. -/
theorem integrable_smul_sub_of_measurable_bounded {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (K : ℝ → ℂ) (B : ℝ) (hB : ∀ x, ‖K x‖ ≤ B) (hmeas : Measurable K)
    (F : ℝ → H) (hF : Integrable F) (x : ℝ) :
    Integrable (fun y : ℝ => K (x - y) • F y) := by
  have hmeasK : Measurable (fun y : ℝ => K (x - y)) :=
    hmeas.comp (continuous_const.sub continuous_id).measurable
  refine Integrable.mono' (hF.norm.const_mul B)
    (hmeasK.aestronglyMeasurable.smul hF.aestronglyMeasurable) ?_
  filter_upwards with y
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right (hB (x - y)) (norm_nonneg _)

/-- The integrand `y ↦ conj (K (y - x)) • G y` is integrable, for a measurable weight bounded
by `B` and an integrable `G`. -/
theorem integrable_star_smul_sub_of_measurable_bounded {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (K : ℝ → ℂ) (B : ℝ) (hB : ∀ x, ‖K x‖ ≤ B) (hmeas : Measurable K)
    (G : ℝ → H) (hG : Integrable G) (x : ℝ) :
    Integrable (fun y : ℝ => (starRingEnd ℂ) (K (y - x)) • G y) := by
  have hconjmeas : Measurable (fun y : ℝ => (starRingEnd ℂ) (K (y - x))) :=
    continuous_star.measurable.comp (hmeas.comp (continuous_id.sub continuous_const).measurable)
  refine Integrable.mono' (hG.norm.const_mul B)
    (hconjmeas.aestronglyMeasurable.smul hG.aestronglyMeasurable) ?_
  filter_upwards with y
  rw [norm_smul, Complex.norm_conj]
  exact mul_le_mul_of_nonneg_right (hB (y - x)) (norm_nonneg _)

/-- The product integrand `(x,y) ↦ conj (K (x - y)) * ⟪F y, G x⟫` is integrable
(with respect to the product measure), for a measurable weight bounded by `B` and integrable
`F`, `G`. -/
theorem integrable_uncurry_star_mul_inner {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (K : ℝ → ℂ) (B : ℝ) (hB : ∀ x, ‖K x‖ ≤ B) (hmeas : Measurable K)
    (F G : ℝ → H) (hF : Integrable F) (hG : Integrable G) :
    Integrable (fun z : ℝ × ℝ => (starRingEnd ℂ) (K (z.1 - z.2)) * inner ℂ (F z.2) (G z.1))
      (volume.prod volume) := by
  have hdom : Integrable (fun z : ℝ × ℝ => B * (‖G z.1‖ * ‖F z.2‖)) (volume.prod volume) :=
    (hG.norm.mul_prod hF.norm).const_mul B
  have hconjmeas : Measurable (fun z : ℝ × ℝ => (starRingEnd ℂ) (K (z.1 - z.2))) :=
    continuous_star.measurable.comp (hmeas.comp (continuous_fst.sub continuous_snd).measurable)
  have hinter : AEStronglyMeasurable (fun z : ℝ × ℝ => inner ℂ (F z.2) (G z.1))
      (volume.prod volume) :=
    (hF.aestronglyMeasurable.comp_quasiMeasurePreserving
      Measure.quasiMeasurePreserving_snd).inner
      (hG.aestronglyMeasurable.comp_quasiMeasurePreserving
        Measure.quasiMeasurePreserving_fst)
  refine Integrable.mono' hdom (hconjmeas.aestronglyMeasurable.mul hinter) ?_
  filter_upwards with z
  rw [norm_mul, Complex.norm_conj]
  have h1 : ‖inner ℂ (F z.2) (G z.1)‖ ≤ ‖F z.2‖ * ‖G z.1‖ := norm_inner_le_norm _ _
  have hKb : ‖K (z.1 - z.2)‖ ≤ B := hB _
  calc ‖K (z.1 - z.2)‖ * ‖inner ℂ (F z.2) (G z.1)‖
      ≤ ‖K (z.1 - z.2)‖ * (‖F z.2‖ * ‖G z.1‖) :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ ≤ B * (‖F z.2‖ * ‖G z.1‖) :=
        mul_le_mul_of_nonneg_right hKb (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = B * (‖G z.1‖ * ‖F z.2‖) := by ring

/-- **Adjointness of convolution with a measurable bounded kernel.**
For a measurable `K` bounded by `B` and integrable `F G : ℝ → H` into a complex Hilbert space,
`∫ x, ⟪(K ⋆ F) x, G x⟫ = ∫ x, ⟪F x, (K* ⋆ G) x⟫`, where the adjoint kernel is
`K* z = conj (K (-z))`, written here as `conj (K (y - x))`. -/
theorem integral_inner_convolution_eq_adjoint_meas {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (K : ℝ → ℂ) (B : ℝ) (hB : ∀ x, ‖K x‖ ≤ B) (hmeas : Measurable K) (F G : ℝ → H) (hF : MeasureTheory.Integrable F) (hG : MeasureTheory.Integrable G) : (∫ x : ℝ, inner ℂ (∫ y : ℝ, K (x - y) • F y) (G x)) = ∫ x : ℝ, inner ℂ (F x) (∫ y : ℝ, (starRingEnd ℂ) (K (y - x)) • G y) := by
  set f : ℝ → ℝ → ℂ := fun x y => (starRingEnd ℂ) (K (x - y)) * inner ℂ (F y) (G x) with hf
  have hinnerL : ∀ x, inner ℂ (∫ y : ℝ, K (x - y) • F y) (G x) = ∫ y : ℝ, f x y := by
    intro x
    rw [inner_integral_left (integrable_smul_sub_of_measurable_bounded K B hB hmeas F hF x) (G x)]
    apply integral_congr_ae
    filter_upwards with y
    rw [inner_smul_left]
  have hinnerR : ∀ x, inner ℂ (F x) (∫ y : ℝ, (starRingEnd ℂ) (K (y - x)) • G y) = ∫ y : ℝ, f y x := by
    intro x
    rw [inner_integral_right (integrable_star_smul_sub_of_measurable_bounded K B hB hmeas G hG x) (F x)]
    apply integral_congr_ae
    filter_upwards with y
    rw [inner_smul_right]
  have hL : (∫ x : ℝ, inner ℂ (∫ y : ℝ, K (x - y) • F y) (G x)) = ∫ x : ℝ, ∫ y : ℝ, f x y := by
    apply integral_congr_ae
    filter_upwards with x
    exact hinnerL x
  have hR : (∫ x : ℝ, inner ℂ (F x) (∫ y : ℝ, (starRingEnd ℂ) (K (y - x)) • G y)) = ∫ x : ℝ, ∫ y : ℝ, f y x := by
    apply integral_congr_ae
    filter_upwards with x
    exact hinnerR x
  have hfint : Integrable (fun z : ℝ × ℝ => f z.1 z.2) (volume.prod volume) :=
    integrable_uncurry_star_mul_inner K B hB hmeas F G hF hG
  rw [hL, hR]
  rw [integral_integral_swap hfint]

end Commons.Analysis.Convolution
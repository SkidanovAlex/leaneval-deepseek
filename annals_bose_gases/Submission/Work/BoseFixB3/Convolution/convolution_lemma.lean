import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.ConvolutionTaylor
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB3.Convolution.convolution_lemma`

The convolution estimate of Fournais--Solovej, `lem:Convolution`
(`Papers/fournais_solovej/final_v2.tex`, ~l. 845): for an even integrable
`f` supported in `ball 0 R` and `0 < ℓ`,

    |(f * χ_ℓ)(x) − χ_ℓ(x) · ∫ f| ≤ C (R/ℓ)² ∫ |f|,

where `χ_ℓ(z) = χ(ℓ⁻¹ • z)` and `conv3 f χ_ℓ x = ∫ y, f y · χ_ℓ(x − y)`.

The mathematical content (the second-order Taylor estimate for the smooth
compactly supported bump `χ`, together with the observation that the linear
term integrates to zero because `f` is even) is already formalised in the
corpus as `Submission.BoseGases.convolution_approx` (and
`Submission.BoseGases.chi_second_order_bound`), in the "difference" form
`∫ y, f y · (χ_ℓ(x−y) − χ_ℓ(x))`.  Here we do the bookkeeping that converts
that difference form into the `conv3`-minus-constant-times-`∫f` form of the
statement, and convert the support hypothesis about `tsupport` into the
pointwise vanishing hypothesis used there.
-/

namespace Work.BoseFixB3.Convolution

open MeasureTheory

theorem convolution_lemma :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : EuclideanSpace ℝ (Fin 3) → ℝ), MeasureTheory.Integrable f →
      (∀ x, f (-x) = f x) → ∀ {R ℓ : ℝ}, 0 < R → 0 < ℓ →
      tsupport f ⊆ Metric.ball 0 R → ∀ x : EuclideanSpace ℝ (Fin 3),
      |Submission.BoseGases.conv3 f (fun z => Submission.BoseGases.chi ((ℓ⁻¹) • z)) x
          - Submission.BoseGases.chi ((ℓ⁻¹) • x) * ∫ y, f y|
        ≤ C * (R / ℓ) ^ 2 * ∫ y, |f y| := by
  obtain ⟨C, hC0, hT⟩ := Submission.BoseGases.chi_second_order_bound
  refine ⟨C, hC0, ?_⟩
  intro f hf heven R ℓ hR hℓ hsupp x
  -- `tsupport f ⊆ ball 0 R` gives the pointwise vanishing used by `convolution_approx`.
  have hfsupp : ∀ z : EuclideanSpace ℝ (Fin 3), R ≤ ‖z‖ → f z = 0 := by
    intro z hz
    by_contra h
    have hzt : z ∈ tsupport f := subset_tsupport f (by simpa [Function.mem_support] using h)
    have hzb : z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R := hsupp hzt
    rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hzb
    linarith
  have hmain := Submission.BoseGases.convolution_approx (f := f) (ℓ := ℓ) (R := R) (Cχ := C)
    hℓ hT hf heven hfsupp (le_of_lt hR) x
  -- the two integrands are bounded by `(√chiNormSq)⁻¹ · f`
  have hMbound : ∀ z : EuclideanSpace ℝ (Fin 3),
      ‖Submission.BoseGases.chiScale ℓ z‖ ≤ (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ :=
    fun z => by simpa [Real.norm_eq_abs] using Submission.BoseGases.abs_chiScale_le ℓ z
  have hcont1 : Continuous (fun y : EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.chiScale ℓ (x - y)) :=
    (Submission.BoseGases.chiScale_continuous ℓ).comp (continuous_const.sub continuous_id)
  have hInt1 : MeasureTheory.Integrable (fun y : EuclideanSpace ℝ (Fin 3) =>
      f y * Submission.BoseGases.chiScale ℓ (x - y)) :=
    hf.mul_bdd (c := (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹) hcont1.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun y => hMbound (x - y)))
  have hInt2 : MeasureTheory.Integrable (fun y : EuclideanSpace ℝ (Fin 3) =>
      f y * Submission.BoseGases.chiScale ℓ x) :=
    hf.mul_bdd (c := (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹) aestronglyMeasurable_const
      (Filter.Eventually.of_forall (fun _ => hMbound x))
  -- `conv3` is the convolution against `chiScale ℓ`
  have h1 : Submission.BoseGases.conv3 f (fun z => Submission.BoseGases.chi ((ℓ⁻¹) • z)) x
      = ∫ y : EuclideanSpace ℝ (Fin 3), f y * Submission.BoseGases.chiScale ℓ (x - y) := rfl
  -- pull the constant `chiScale ℓ x` out of the integral
  have h2 : Submission.BoseGases.chi ((ℓ⁻¹) • x) * ∫ y : EuclideanSpace ℝ (Fin 3), f y
      = ∫ y : EuclideanSpace ℝ (Fin 3), f y * Submission.BoseGases.chiScale ℓ x := by
    rw [MeasureTheory.integral_mul_const]
    simp [Submission.BoseGases.chiScale, mul_comm]
  -- split the integral of the difference
  have h3 : (∫ y : EuclideanSpace ℝ (Fin 3), f y * Submission.BoseGases.chiScale ℓ (x - y))
        - ∫ y : EuclideanSpace ℝ (Fin 3), f y * Submission.BoseGases.chiScale ℓ x
      = ∫ y : EuclideanSpace ℝ (Fin 3),
          f y * (Submission.BoseGases.chiScale ℓ (x - y)
            - Submission.BoseGases.chiScale ℓ x) := by
    rw [← MeasureTheory.integral_sub hInt1 hInt2]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with y
    ring
  have key : Submission.BoseGases.conv3 f (fun z => Submission.BoseGases.chi ((ℓ⁻¹) • z)) x
        - Submission.BoseGases.chi ((ℓ⁻¹) • x) * ∫ y : EuclideanSpace ℝ (Fin 3), f y
      = ∫ y : EuclideanSpace ℝ (Fin 3),
          f y * (Submission.BoseGases.chiScale ℓ (x - y)
            - Submission.BoseGases.chiScale ℓ x) := by
    rw [h1, h2, ← h3]
  rw [key]
  exact hmain

end Work.BoseFixB3.Convolution

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Submission.Work.BoseRowsL.LatticeCoulomb.reductionDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsL.LatticeCoulomb.integrable_cosCosBall_prod`

The product-integrability of the continuum cos-cosine kernel: for integrable
`f₁ f₂ : E3 → ℝ`, the function

  `(z₁,z₂) ↦ f₁ z₁ · f₂ z₂ · cosCosBall K z₁ z₂`

is integrable for the product of the Lebesgue measures.

The mathematics is one-dimensional in nature: `cosCosBall K x y` is the integral of
`cos⟪p,x⟫cos⟪p,y⟫/(2‖p‖²)` over the ball `closedBall 0 K`, and since
`|cos⟪p,x⟫cos⟪p,y⟫| ≤ 1` it is bounded by the **finite** constant

  `C := ∫ p in closedBall 0 K, (2‖p‖²)⁻¹`,

`p ↦ (2‖p‖²)⁻¹` being integrable on a ball in dimension `3 > 2`
(`Work.BoseRowsL.LatticeCoulomb.integrableOn_inv_norm_sq`).  Hence
`|f₁ z₁ f₂ z₂ cosCosBall K z₁ z₂| ≤ C·|f₁ z₁|·|f₂ z₂|`, and the right-hand side is
integrable by `Integrable.mul_prod`.  The remaining ingredient is the (a.e.) strong
measurability of `(z₁,z₂) ↦ cosCosBall K z₁ z₂`, which follows from the parameterised
integral representation (`StronglyMeasurable.integral_prod_right`).
-/

noncomputable section

open scoped Real BigOperators Topology
open MeasureTheory Metric

namespace Work.BoseRowsL.LatticeCoulomb

set_option autoImplicit false

/-- The continuum cos-cosine kernel is bounded by the finite constant
`∫ p in closedBall 0 K, (2‖p‖²)⁻¹` (`3 > 2` is the borderline dimension). -/
private lemma norm_cosCosBall_le (K : ℝ) (x y : E3) :
    ‖cosCosBall K x y‖ ≤ ∫ p in Metric.closedBall (0 : E3) K, (2 * ‖p‖ ^ 2)⁻¹ := by
  have hs : MeasurableSet (Metric.closedBall (0 : E3) K) := measurableSet_closedBall
  have hpt : ∀ p : E3,
      ‖Real.cos (inner ℝ p x) * Real.cos (inner ℝ p y) / (2 * ‖p‖ ^ 2)‖ ≤ (2 * ‖p‖ ^ 2)⁻¹ := by
    intro p
    have hden : (0 : ℝ) ≤ 2 * ‖p‖ ^ 2 := by positivity
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg hden]
    calc |Real.cos (inner ℝ p x) * Real.cos (inner ℝ p y)| / (2 * ‖p‖ ^ 2)
        ≤ 1 / (2 * ‖p‖ ^ 2) := by
          apply div_le_div_of_nonneg_right _ hden
          calc |Real.cos (inner ℝ p x) * Real.cos (inner ℝ p y)|
              = |Real.cos (inner ℝ p x)| * |Real.cos (inner ℝ p y)| := abs_mul _ _
            _ ≤ 1 * 1 := mul_le_mul (Real.abs_cos_le_one _) (Real.abs_cos_le_one _)
                (abs_nonneg _) zero_le_one
            _ = 1 := by ring
      _ = (2 * ‖p‖ ^ 2)⁻¹ := by rw [inv_eq_one_div]
  have hmeas : Measurable (fun p : E3 =>
      Real.cos (inner ℝ p x) * Real.cos (inner ℝ p y) / (2 * ‖p‖ ^ 2)) := by fun_prop
  have hint : IntegrableOn (fun p : E3 =>
      ‖Real.cos (inner ℝ p x) * Real.cos (inner ℝ p y) / (2 * ‖p‖ ^ 2)‖)
      (Metric.closedBall (0 : E3) K) := by
    refine Integrable.mono' (integrableOn_inv_norm_sq K) hmeas.norm.aestronglyMeasurable ?_
    filter_upwards with p
    simpa [Real.norm_of_nonneg (norm_nonneg _)] using hpt p
  calc ‖cosCosBall K x y‖
      ≤ ∫ p in Metric.closedBall (0 : E3) K,
          ‖Real.cos (inner ℝ p x) * Real.cos (inner ℝ p y) / (2 * ‖p‖ ^ 2)‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ p in Metric.closedBall (0 : E3) K, (2 * ‖p‖ ^ 2)⁻¹ :=
        setIntegral_mono_on hint (integrableOn_inv_norm_sq K) hs (fun p _ => hpt p)

/-- The continuum cos-cosine kernel is (a.e.) strongly measurable as a function of the
pair of variables: it is a parameterised integral of a jointly measurable integrand. -/
private lemma aestronglyMeasurable_cosCosBall (K : ℝ) :
    AEStronglyMeasurable (fun z : E3 × E3 => cosCosBall K z.1 z.2)
      ((volume : Measure E3).prod (volume : Measure E3)) := by
  let F : (E3 × E3) → E3 → ℝ := fun z p => (Metric.closedBall (0 : E3) K).indicator
      (fun p => Real.cos (inner ℝ p z.1) * Real.cos (inner ℝ p z.2) / (2 * ‖p‖ ^ 2)) p
  have hkey : (fun z : E3 × E3 => cosCosBall K z.1 z.2)
      = fun z => ∫ p, F z p ∂(volume : Measure E3) := by
    funext z
    exact (integral_indicator measurableSet_closedBall).symm
  rw [hkey]
  have huncurry : Function.uncurry F
      = (Prod.snd ⁻¹' (Metric.closedBall (0 : E3) K)).indicator
        (fun w : (E3 × E3) × E3 =>
          Real.cos (inner ℝ w.2 w.1.1) * Real.cos (inner ℝ w.2 w.1.2) / (2 * ‖w.2‖ ^ 2)) := by
    funext w
    rfl
  have hmeas : StronglyMeasurable (Function.uncurry F) := by
    rw [huncurry]
    refine Measurable.stronglyMeasurable (Measurable.indicator ?_ ?_)
    · fun_prop
    · exact measurableSet_closedBall.preimage measurable_snd
  exact (hmeas.integral_prod_right).aestronglyMeasurable

theorem integrable_cosCosBall_prod (K : ℝ) {f₁ f₂ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hf1 : MeasureTheory.Integrable f₁) (hf2 : MeasureTheory.Integrable f₂) :
    MeasureTheory.Integrable
      (fun z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        f₁ z.1 * f₂ z.2 * Work.BoseRowsL.LatticeCoulomb.cosCosBall K z.1 z.2)
      ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))) := by
  set C : ℝ := ∫ p in Metric.closedBall (0 : E3) K, (2 * ‖p‖ ^ 2)⁻¹ with hCdef
  have hmaj : Integrable (fun z : E3 × E3 => C * (‖f₁ z.1‖ * ‖f₂ z.2‖))
      ((volume : Measure E3).prod (volume : Measure E3)) :=
    (hf1.norm.mul_prod hf2.norm).const_mul C
  refine hmaj.mono' ?_ ?_
  · exact ((hf1.mul_prod hf2).aestronglyMeasurable).mul (aestronglyMeasurable_cosCosBall K)
  · filter_upwards with z
    calc ‖f₁ z.1 * f₂ z.2 * cosCosBall K z.1 z.2‖
        = ‖f₁ z.1‖ * ‖f₂ z.2‖ * ‖cosCosBall K z.1 z.2‖ := by rw [norm_mul, norm_mul]
      _ ≤ ‖f₁ z.1‖ * ‖f₂ z.2‖ * C :=
          mul_le_mul_of_nonneg_left (norm_cosCosBall_le K z.1 z.2)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = C * (‖f₁ z.1‖ * ‖f₂ z.2‖) := by ring

end Work.BoseRowsL.LatticeCoulomb

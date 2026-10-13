/-
Copyright: work module for the Elgindi finite-time singularity project.

# Endpoint values of a `C²` slice, controlled by the two energies

`endpointValuesCore`: for `f` of class `C²` on `(0, π/2)` whose one-sided limits `F₀` (at `0⁺`)
and `F₁` (at `(π/2)⁻`) exist, and whose weighted `L²`-energies

  `A = ∫_{Iθ} f² · σ`,  `B = ∫_{Iθ} (f'')² · σ`,   `σ = sin(2θ)^{-η}`,

are finite, one has

  `F₀² + F₁² + (F₁ - F₀)² ≤ C (A + √(A B))`.

The route is the two-scale estimate `EndpointValues.endpointParamLeft` (and its mirror
`EndpointValues.endpointParamRight` for the right endpoint): at every scale `t ∈ (0, π/2)`

  `F² ≤ (2/3) t³ ∫ (f'')² + 72 t⁻¹ ∫ f²`,

which, after discarding the weight (`σ ≥ 1` on `Iθ`), gives `F² ≤ (2/3) t³ Y + 72 t⁻¹ X` with
`X = ∫ f²`, `Y = ∫ (f'')²`; the one-dimensional optimisation
`EndpointValues.endpointSqBound` then produces `F² ≤ 100 (X + √(XY))`, and `X ≤ A`, `Y ≤ B` give
the claim.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.EllipticEst.Core.sliceBoundaryLimit
import Submission.Work.EllipticEst.Core.derivIntegrableOfEnergy
import Submission.Work.EllipticEst.Core.i0Aux.EndpointDefs
import Submission.Work.EllipticEst.Core.i0Aux.EndpointValues.EndpointParamLeft
import Submission.Work.EllipticEst.Core.i0Aux.EndpointValues.endpointParamRight
import Submission.Work.EllipticEst.Core.i0Aux.EndpointValues.endpointSqBound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.Core.i0Aux

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

theorem endpointValuesCore : ∃ C : ℝ, 0 < C ∧ ∀ (f : ℝ → ℝ) (F₀ F₁ : ℝ),
    ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)) →
    Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds F₀) →
    Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds F₁) →
    MeasureTheory.IntegrableOn (fun θ : ℝ => (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
    F₀ ^ 2 + F₁ ^ 2 + (F₁ - F₀) ^ 2 ≤ C * ((∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      + Real.sqrt ((∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
          * (∫ θ in Work.Spaces.Iθ, (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ))) := by
  refine ⟨600, by norm_num, ?_⟩
  intro f F₀ F₁ hf hlim0 hlim1 hF _hD hDD
  have hsub : Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆ Set.Icc (0 : ℝ) (Real.pi / 2) :=
    Set.Ioo_subset_Icc_self
  -- restrict every integrability statement to the open interval
  have hFioo : IntegrableOn (fun θ : ℝ => (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      (Set.Ioo 0 (Real.pi / 2)) := hF.mono_set hsub
  have hDDioo : IntegrableOn (fun θ : ℝ => (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      (Set.Ioo 0 (Real.pi / 2)) := hDD.mono_set hsub
  -- continuity of `f` and of `f''` on the open interval
  have hcont0 : ContinuousOn f (Set.Ioo 0 (Real.pi / 2)) := hf.continuousOn
  have hcont2 : ContinuousOn (deriv (deriv f)) (Set.Ioo 0 (Real.pi / 2)) := by
    have h1 : ContDiffOn ℝ 1 (deriv f) (Set.Ioo 0 (Real.pi / 2)) :=
      hf.deriv_of_isOpen isOpen_Ioo (by norm_num)
    exact h1.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
  -- the weight dominates `1`, so the plain `L²`-norms are finite
  have hF2 : IntegrableOn (fun θ : ℝ => (f θ) ^ 2) (Set.Ioo 0 (Real.pi / 2)) := by
    refine Integrable.mono' hFioo ((hcont0.pow 2).aestronglyMeasurable measurableSet_Ioo) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
    show |(f θ) ^ 2| ≤ (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
    rw [abs_of_nonneg (sq_nonneg _)]
    exact le_mul_of_one_le_right (sq_nonneg _) (Work.EllipticEst.Core.one_le_thEta hθ)
  have hDD2 : IntegrableOn (fun θ : ℝ => (deriv (deriv f) θ) ^ 2) (Set.Ioo 0 (Real.pi / 2)) := by
    refine Integrable.mono' hDDioo ((hcont2.pow 2).aestronglyMeasurable measurableSet_Ioo) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
    show |(deriv (deriv f) θ) ^ 2| ≤ (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
    rw [abs_of_nonneg (sq_nonneg _)]
    exact le_mul_of_one_le_right (sq_nonneg _) (Work.EllipticEst.Core.one_le_thEta hθ)
  -- and the corresponding integral comparisons
  have hF2le : (∫ θ in Set.Ioo 0 (Real.pi / 2), (f θ) ^ 2)
      ≤ ∫ θ in Set.Ioo 0 (Real.pi / 2), (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ := by
    refine integral_mono_ae hF2 hFioo ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
    exact le_mul_of_one_le_right (sq_nonneg _) (Work.EllipticEst.Core.one_le_thEta hθ)
  have hDD2le : (∫ θ in Set.Ioo 0 (Real.pi / 2), (deriv (deriv f) θ) ^ 2)
      ≤ ∫ θ in Set.Ioo 0 (Real.pi / 2),
          (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ := by
    refine integral_mono_ae hDD2 hDDioo ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
    exact le_mul_of_one_le_right (sq_nonneg _) (Work.EllipticEst.Core.one_le_thEta hθ)
  -- the two energy constants of the statement
  set A := ∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ with hA
  set B := ∫ θ in Work.Spaces.Iθ, (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ with hB
  have hAioo : A = ∫ θ in Set.Ioo 0 (Real.pi / 2),
      (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ := by
    rw [hA, Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioo]
  have hBioo : B = ∫ θ in Set.Ioo 0 (Real.pi / 2),
      (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ := by
    rw [hB, Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioo]
  -- the two plain energies
  set X := ∫ θ in Set.Ioo 0 (Real.pi / 2), (f θ) ^ 2 with hX
  set Y := ∫ θ in Set.Ioo 0 (Real.pi / 2), (deriv (deriv f) θ) ^ 2 with hY
  have hXleA : X ≤ A := by rw [hX, hAioo]; exact hF2le
  have hYleB : Y ≤ B := by rw [hY, hBioo]; exact hDD2le
  have hX0 : 0 ≤ X := by
    rw [hX]
    exact setIntegral_nonneg measurableSet_Ioo (fun θ _ => sq_nonneg (f θ))
  have hY0 : 0 ≤ Y := by
    rw [hY]
    exact setIntegral_nonneg measurableSet_Ioo (fun θ _ => sq_nonneg (deriv (deriv f) θ))
  have hA0 : 0 ≤ A := le_trans hX0 hXleA
  -- the two-scale estimate at both endpoints
  have hparam0 : ∀ t : ℝ, 0 < t → t < Real.pi / 2 →
      F₀ ^ 2 ≤ (2 / 3) * t ^ 3 * Y + 72 * t⁻¹ * X := by
    intro t ht hta
    exact EndpointValues.endpointParamLeft f F₀ t ht hta hf hlim0 hDD2 hF2
  have hparam1 : ∀ t : ℝ, 0 < t → t < Real.pi / 2 →
      F₁ ^ 2 ≤ (2 / 3) * t ^ 3 * Y + 72 * t⁻¹ * X := by
    intro t ht hta
    exact EndpointValues.endpointParamRight f F₁ t ht hta hf hlim1 hDD2 hF2
  have hb0 : F₀ ^ 2 ≤ 100 * (X + Real.sqrt (X * Y)) :=
    EndpointValues.endpointSqBound hX0 hY0 hparam0
  have hb1 : F₁ ^ 2 ≤ 100 * (X + Real.sqrt (X * Y)) :=
    EndpointValues.endpointSqBound hX0 hY0 hparam1
  -- assemble
  have hsum : F₀ ^ 2 + F₁ ^ 2 + (F₁ - F₀) ^ 2 ≤ 600 * (A + Real.sqrt (A * B)) := by
    have hd : (F₁ - F₀) ^ 2 ≤ 2 * F₁ ^ 2 + 2 * F₀ ^ 2 := by
      nlinarith [sq_nonneg (F₁ + F₀)]
    have hXY : X * Y ≤ A * B := mul_le_mul hXleA hYleB hY0 hA0
    have hs : Real.sqrt (X * Y) ≤ Real.sqrt (A * B) := Real.sqrt_le_sqrt hXY
    have hsqrt0 : (0 : ℝ) ≤ Real.sqrt (X * Y) := Real.sqrt_nonneg _
    linarith [hb0, hb1, hd, hs, hA0, hsqrt0]
  simpa only [hA, hB] using hsum

end Work.EllipticEst.Core.i0Aux

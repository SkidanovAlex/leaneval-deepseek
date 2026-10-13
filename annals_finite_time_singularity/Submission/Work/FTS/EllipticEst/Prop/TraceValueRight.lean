import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.EllipticEst.Core.i0Aux.EndpointValues.endpointParamRight
import Submission.Work.EllipticEst.Core.i0Aux.EndpointValues.endpointSqBound
import Submission.Work.EllipticEst.Core.derivIntegrableOfEnergy
import Submission.Work.EllipticEst.Core.i0Aux.endpointValuesCore

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The right-endpoint trace value, controlled by the two weighted energies

For `f` of class `C²` on `(0, π/2)` whose one-sided limit `F₁` at `(π/2)⁻` exists and whose
weighted `L²`-energies `A = ∫_{Iθ} f² · σ`, `B = ∫_{Iθ} (f'')² · σ` are finite
(`σ = thEta θ = sin(2θ)^{-η}`, `η = 99/100`), one has `F₁² ≤ 100 (A + √(A B))`.

The proof is the right-endpoint half of `EndpointValues.endpointValuesCore`.  The two-scale
estimate `EndpointValues.endpointParamRight` gives, at every scale `t ∈ (0, π/2)`,
`F₁² ≤ (2/3) t³ ∫ (f'')² + 72 t⁻¹ ∫ f²` for the *unweighted* integrals over `(0, π/2)`; the
one-dimensional optimisation `EndpointValues.endpointSqBound` turns this into
`F₁² ≤ 100 (X + √(X Y))` with `X = ∫ f²`, `Y = ∫ (f'')²`, and finally `σ ≥ 1` on `Iθ`
(`Work.EllipticEst.Core.one_le_thEta`) gives `X ≤ A`, `Y ≤ B`, hence the claim with `C = 100`.
-/

namespace Work.FTS.EllipticEst.Prop

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

theorem TraceValueRight : ∃ C : ℝ, 0 < C ∧ ∀ (f : ℝ → ℝ) (F₁ : ℝ),
    ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)) →
    Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds F₁) →
    MeasureTheory.IntegrableOn (fun θ : ℝ => (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
    F₁ ^ 2 ≤ C * ((∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        + Real.sqrt ((∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
            * (∫ θ in Work.Spaces.Iθ, (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ))) := by
  refine ⟨100, by norm_num, ?_⟩
  intro f F₁ hf hlim1 hF hDD
  have hsub : Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆ Set.Icc (0 : ℝ) (Real.pi / 2) :=
    Set.Ioo_subset_Icc_self
  -- restrict every integrability statement to the open interval
  have hFioo : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      (Set.Ioo 0 (Real.pi / 2)) := hF.mono_set hsub
  have hDDioo : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      (Set.Ioo 0 (Real.pi / 2)) := hDD.mono_set hsub
  -- continuity of `f` and of `f''` on the open interval
  have hcont0 : ContinuousOn f (Set.Ioo 0 (Real.pi / 2)) := hf.continuousOn
  have hcont2 : ContinuousOn (deriv (deriv f)) (Set.Ioo 0 (Real.pi / 2)) := by
    have h1 : ContDiffOn ℝ 1 (deriv f) (Set.Ioo 0 (Real.pi / 2)) :=
      hf.deriv_of_isOpen isOpen_Ioo (by norm_num)
    exact h1.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
  -- the weight dominates `1`, so the plain `L²`-norms are finite
  have hF2 : MeasureTheory.IntegrableOn (fun θ : ℝ => (f θ) ^ 2)
      (Set.Ioo 0 (Real.pi / 2)) := by
    refine Integrable.mono' hFioo ((hcont0.pow 2).aestronglyMeasurable measurableSet_Ioo) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
    show |(f θ) ^ 2| ≤ (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
    rw [abs_of_nonneg (sq_nonneg _)]
    exact le_mul_of_one_le_right (sq_nonneg _) (Work.EllipticEst.Core.one_le_thEta hθ)
  have hDD2 : MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv (deriv f) θ) ^ 2)
      (Set.Ioo 0 (Real.pi / 2)) := by
    refine Integrable.mono' hDDioo ((hcont2.pow 2).aestronglyMeasurable measurableSet_Ioo) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
    show |(deriv (deriv f) θ) ^ 2| ≤ (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
    rw [abs_of_nonneg (sq_nonneg _)]
    exact le_mul_of_one_le_right (sq_nonneg _) (Work.EllipticEst.Core.one_le_thEta hθ)
  -- and the corresponding integral comparisons
  have hF2le : (∫ θ in Set.Ioo 0 (Real.pi / 2), (f θ) ^ 2)
      ≤ ∫ θ in Set.Ioo 0 (Real.pi / 2),
          (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ := by
    refine integral_mono_ae hF2 hFioo ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
    exact le_mul_of_one_le_right (sq_nonneg _) (Work.EllipticEst.Core.one_le_thEta hθ)
  have hDD2le : (∫ θ in Set.Ioo 0 (Real.pi / 2), (deriv (deriv f) θ) ^ 2)
      ≤ ∫ θ in Set.Ioo 0 (Real.pi / 2),
          (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ := by
    refine integral_mono_ae hDD2 hDDioo ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
    exact le_mul_of_one_le_right (sq_nonneg _) (Work.EllipticEst.Core.one_le_thEta hθ)
  -- the two weighted energies of the statement
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
  -- the two-scale estimate at the right endpoint
  have hparam1 : ∀ t : ℝ, 0 < t → t < Real.pi / 2 →
      F₁ ^ 2 ≤ (2 / 3) * t ^ 3 * Y + 72 * t⁻¹ * X := by
    intro t ht hta
    exact Work.EllipticEst.Core.i0Aux.EndpointValues.endpointParamRight f F₁ t ht hta
      hf hlim1 hDD2 hF2
  have hb1 : F₁ ^ 2 ≤ 100 * (X + Real.sqrt (X * Y)) :=
    Work.EllipticEst.Core.i0Aux.EndpointValues.endpointSqBound hX0 hY0 hparam1
  -- transfer to the weighted energies
  have hXY : X * Y ≤ A * B := mul_le_mul hXleA hYleB hY0 hA0
  have hs : Real.sqrt (X * Y) ≤ Real.sqrt (A * B) := Real.sqrt_le_sqrt hXY
  have hstep : 100 * (X + Real.sqrt (X * Y)) ≤ 100 * (A + Real.sqrt (A * B)) := by
    have h2 : X + Real.sqrt (X * Y) ≤ A + Real.sqrt (A * B) := add_le_add hXleA hs
    linarith
  have hfinal : F₁ ^ 2 ≤ 100 * (A + Real.sqrt (A * B)) := le_trans hb1 hstep
  simpa only [hA, hB] using hfinal

end Work.FTS.EllipticEst.Prop

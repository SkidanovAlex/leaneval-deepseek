import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.EllipticEst.Core.i0Aux.endpointValuesCore
import Submission.Work.EllipticEst.Core.i0Aux.traceVanishingInterp
import Submission.Work.EllipticEst.Core.sliceBoundaryLimit
import Submission.Work.EllipticEst.Core.i0Aux.EndpointValues.EndpointParamLeft
import Submission.Work.EllipticEst.Core.i0Aux.EndpointValues.endpointSqBound
import Submission.Work.FTS.EllipticEst.Prop.TraceLeftPieces.traceCore
import Submission.Work.FTS.EllipticEst.Prop.TraceLeftPieces.plainIntegrable
import Submission.Work.FTS.EllipticEst.Prop.TraceLeftPieces.ChiCutDefs
import Submission.Work.FTS.EllipticEst.Prop.TraceLeftPieces.CutBdd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Prop

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 1000000

/-- **The left trace bound.**  For a `C²` slice `f` of the angular variable with finite weighted
energies `A = ∫_{Iθ} f² σ`, `D = ∫_{Iθ} (f'')² σ` (`σ = sin(2θ)^{-η}`), the values of the left
traces `F₀ = lim_{θ→0⁺} f θ` and `L₀ = lim_{θ→0⁺} f'(θ)` are controlled by the two energies:

`max (F₀ L₀) 0 + F₀² ≤ C (A + √(A D))`.

The value term is the sharp endpoint (Agmon type) two-scale estimate
(`Core.i0Aux.EndpointValues.endpointParamLeft` + `endpointSqBound`); the product term comes from
an integration by parts against a fixed cutoff `χ` (`1` near `0`, `0` near `π/2`), see
`TraceLeftCore.prodTraceBound`:
`F₀ L₀ = -∫ (f'² χ + f χ' f' + f χ f'')`, and `∫ f χ' f'` is moved onto `f² χ''` by a second
integration by parts. -/
theorem traceBoundLeft : ∃ C : ℝ, 0 < C ∧ ∀ (f : ℝ → ℝ) (F₀ L₀ : ℝ),
    ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)) →
    Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds F₀) →
    Filter.Tendsto (deriv f) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds L₀) →
    MeasureTheory.IntegrableOn (fun θ : ℝ => (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
    max (F₀ * L₀) 0 + F₀ ^ 2
      ≤ C * ((∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
          + Real.sqrt ((∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
              * (∫ θ in Work.Spaces.Iθ, (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ))) := by
  -- the explicit cutoff and the bounds on its first two derivatives
  obtain ⟨K, hK1, hKbdd1, hKbdd2⟩ :=
    TraceLeftPieces.deriv_bdd_of_plateau TraceLeftPieces.chiCut
      (by linarith [Real.pi_pos] : Real.pi / 4 < 3 * Real.pi / 8)
      TraceLeftPieces.chiCut_contDiff (fun θ hθ => TraceLeftPieces.chiCut_eq_one hθ)
      (fun θ hθ => TraceLeftPieces.chiCut_eq_zero hθ)
  refine ⟨K / 2 + 1 + 100, by linarith, ?_⟩
  intro f F₀ L₀ hf hlim hlimL hA hA1 hD
  obtain ⟨hii, hjj, hkk, h12, h23⟩ := TraceLeftPieces.plainIntegrable f hf hA hA1 hD
  have hK0 : (0 : ℝ) ≤ K := le_trans zero_le_one hK1
  have hχcont2 : Continuous (deriv (deriv TraceLeftPieces.chiCut)) := by
    have h1 : ContDiff ℝ 1 (deriv TraceLeftPieces.chiCut) :=
      TraceLeftPieces.chiCut_contDiff.deriv' (n := 1)
    exact h1.continuous_deriv_one
  have hχd1 : ∀ θ : ℝ, HasDerivAt TraceLeftPieces.chiCut
      (deriv TraceLeftPieces.chiCut θ) θ :=
    fun θ => (TraceLeftPieces.chiCut_contDiff.differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hχd2 : ∀ θ : ℝ,
      HasDerivAt (deriv TraceLeftPieces.chiCut) (deriv (deriv TraceLeftPieces.chiCut) θ) θ := by
    intro θ
    have h1 : ContDiff ℝ 1 (deriv TraceLeftPieces.chiCut) :=
      TraceLeftPieces.chiCut_contDiff.deriv' (n := 1)
    exact (h1.differentiable (by norm_num)).differentiableAt.hasDerivAt
  -- the product term
  have hprod : F₀ * L₀ ≤ (K / 2) * (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * thEta θ)
      + Real.sqrt ((∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * thEta θ)
          * (∫ θ in Work.Spaces.Iθ, (deriv (deriv f) θ) ^ 2 * thEta θ)) :=
    TraceLeftCore.prodTraceBound f TraceLeftPieces.chiCut hf hχd1 hχd2
      (fun θ hθ => TraceLeftPieces.chiCut_eq_one hθ) (fun θ hθ => TraceLeftPieces.chiCut_eq_zero hθ)
      (fun θ hθ => TraceLeftPieces.chiCut_deriv_eq_zero_left hθ)
      (fun θ hθ => TraceLeftPieces.chiCut_deriv_eq_zero_right hθ)
      TraceLeftPieces.chiCut_nonneg TraceLeftPieces.chiCut_le_one hKbdd1 hKbdd2 hK0 hχcont2
      hlim hlimL hA hD hii hjj hkk h12 h23
  -- the value term, via the sharp two-scale endpoint estimate
  have hAioo : IntegrableOn (fun θ : ℝ => (f θ) ^ 2 * thEta θ) (Set.Ioo 0 (Real.pi / 2)) :=
    hA.mono_set (fun θ hθ => ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
  have hDioo : IntegrableOn (fun θ : ℝ => (deriv (deriv f) θ) ^ 2 * thEta θ)
      (Set.Ioo 0 (Real.pi / 2)) :=
    hD.mono_set (fun θ hθ => ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
  have hcont0 : ContinuousOn f (Set.Ioo 0 (Real.pi / 2)) := hf.continuousOn
  have hcont2 : ContinuousOn (deriv (deriv f)) (Set.Ioo 0 (Real.pi / 2)) :=
    ((hf.deriv_of_isOpen (m := 1) isOpen_Ioo (by norm_num)).continuousOn_deriv_of_isOpen
      isOpen_Ioo (le_refl 1))
  have hF2 : IntegrableOn (fun θ : ℝ => (f θ) ^ 2) (Set.Ioo 0 (Real.pi / 2)) := by
    refine Integrable.mono' hAioo ((hcont0.pow 2).aestronglyMeasurable measurableSet_Ioo) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact le_mul_of_one_le_right (sq_nonneg _) (TraceLeftCore.one_le_thEta_Ioo hθ)
  have hDD2 : IntegrableOn (fun θ : ℝ => (deriv (deriv f) θ) ^ 2) (Set.Ioo 0 (Real.pi / 2)) := by
    refine Integrable.mono' hDioo ((hcont2.pow 2).aestronglyMeasurable measurableSet_Ioo) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact le_mul_of_one_le_right (sq_nonneg _) (TraceLeftCore.one_le_thEta_Ioo hθ)
  have hX0 : 0 ≤ ∫ θ in Set.Ioo 0 (Real.pi / 2), (f θ) ^ 2 :=
    setIntegral_nonneg measurableSet_Ioo (fun θ _ => sq_nonneg _)
  have hY0 : 0 ≤ ∫ θ in Set.Ioo 0 (Real.pi / 2), (deriv (deriv f) θ) ^ 2 :=
    setIntegral_nonneg measurableSet_Ioo (fun θ _ => sq_nonneg _)
  have hparam : ∀ t : ℝ, 0 < t → t < Real.pi / 2 →
      F₀ ^ 2 ≤ (2 / 3) * t ^ 3 * (∫ θ in Set.Ioo 0 (Real.pi / 2), (deriv (deriv f) θ) ^ 2)
        + 72 * t⁻¹ * (∫ θ in Set.Ioo 0 (Real.pi / 2), (f θ) ^ 2) :=
    fun t ht hta => Work.EllipticEst.Core.i0Aux.EndpointValues.endpointParamLeft f F₀ t ht hta
      hf hlim hDD2 hF2
  have hb0 : F₀ ^ 2 ≤ 100 * ((∫ θ in Set.Ioo 0 (Real.pi / 2), (f θ) ^ 2)
      + Real.sqrt ((∫ θ in Set.Ioo 0 (Real.pi / 2), (f θ) ^ 2)
          * (∫ θ in Set.Ioo 0 (Real.pi / 2), (deriv (deriv f) θ) ^ 2))) :=
    Work.EllipticEst.Core.i0Aux.EndpointValues.endpointSqBound hX0 hY0 hparam
  have hXleA : (∫ θ in Set.Ioo 0 (Real.pi / 2), (f θ) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * thEta θ := by
    have h1 : (∫ θ in Set.Ioo 0 (Real.pi / 2), (f θ) ^ 2)
        ≤ ∫ θ in Set.Ioo 0 (Real.pi / 2), (f θ) ^ 2 * thEta θ := by
      refine integral_mono_ae hF2 hAioo ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
      exact le_mul_of_one_le_right (sq_nonneg _) (TraceLeftCore.one_le_thEta_Ioo hθ)
    have h2 : (∫ θ in Set.Ioo 0 (Real.pi / 2), (f θ) ^ 2 * thEta θ)
        = ∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * thEta θ := by
      rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioo]
    linarith
  have hYleD : (∫ θ in Set.Ioo 0 (Real.pi / 2), (deriv (deriv f) θ) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ, (deriv (deriv f) θ) ^ 2 * thEta θ := by
    have h1 : (∫ θ in Set.Ioo 0 (Real.pi / 2), (deriv (deriv f) θ) ^ 2)
        ≤ ∫ θ in Set.Ioo 0 (Real.pi / 2), (deriv (deriv f) θ) ^ 2 * thEta θ := by
      refine integral_mono_ae hDD2 hDioo ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
      exact le_mul_of_one_le_right (sq_nonneg _) (TraceLeftCore.one_le_thEta_Ioo hθ)
    have h2 : (∫ θ in Set.Ioo 0 (Real.pi / 2), (deriv (deriv f) θ) ^ 2 * thEta θ)
        = ∫ θ in Work.Spaces.Iθ, (deriv (deriv f) θ) ^ 2 * thEta θ := by
      rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioo]
    linarith
  have hF0 : F₀ ^ 2 ≤ 100 * ((∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * thEta θ)
      + Real.sqrt ((∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * thEta θ)
          * (∫ θ in Work.Spaces.Iθ, (deriv (deriv f) θ) ^ 2 * thEta θ))) := by
    have hXY : (∫ θ in Set.Ioo 0 (Real.pi / 2), (f θ) ^ 2)
          * (∫ θ in Set.Ioo 0 (Real.pi / 2), (deriv (deriv f) θ) ^ 2)
        ≤ (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * thEta θ)
          * (∫ θ in Work.Spaces.Iθ, (deriv (deriv f) θ) ^ 2 * thEta θ) :=
      mul_le_mul hXleA hYleD hY0 (le_trans hX0 hXleA)
    have hs := Real.sqrt_le_sqrt hXY
    have hsn : (0 : ℝ) ≤ Real.sqrt ((∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * thEta θ)
        * (∫ θ in Work.Spaces.Iθ, (deriv (deriv f) θ) ^ 2 * thEta θ)) := Real.sqrt_nonneg _
    nlinarith [hb0, hs, hXleA, hYleD, hsn]
  -- assemble
  set A := ∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * thEta θ with hAdef
  set D := ∫ θ in Work.Spaces.Iθ, (deriv (deriv f) θ) ^ 2 * thEta θ with hDdef
  have hA0 : 0 ≤ A := by
    rw [hAdef]
    refine MeasureTheory.setIntegral_nonneg (by
      rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) from rfl]
      exact measurableSet_Icc) ?_
    intro θ hθ
    exact mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ)
  have hsqrt0 : 0 ≤ Real.sqrt (A * D) := Real.sqrt_nonneg _
  have hmax : max (F₀ * L₀) 0 ≤ (K / 2) * A + Real.sqrt (A * D) :=
    max_le hprod (add_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ K / 2) hA0) hsqrt0)
  have hsum : max (F₀ * L₀) 0 + F₀ ^ 2 ≤ (K / 2 + 1 + 100) * (A + Real.sqrt (A * D)) := by
    have h1 : (K / 2) * A + Real.sqrt (A * D) + 100 * (A + Real.sqrt (A * D))
        ≤ (K / 2 + 1 + 100) * (A + Real.sqrt (A * D)) := by
      nlinarith [hA0, hsqrt0, hK0]
    linarith [hmax, hF0, h1]
  rw [hAdef, hDdef] at hsum
  rw [hAdef, hDdef]
  exact hsum

end Work.FTS.EllipticEst.Prop

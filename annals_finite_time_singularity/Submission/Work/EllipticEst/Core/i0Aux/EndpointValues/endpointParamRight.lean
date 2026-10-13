import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.EllipticEst.Core.i0Aux.EndpointDefs
import Submission.Work.EllipticEst.Core.i0Aux.EndpointValues.EndpointParamLeft
import Submission.Work.EllipticEst.Core.i0Aux.EndpointValues.reflectFacts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.Core.i0Aux.EndpointValues

/-- **The endpoint-value estimate at the right endpoint.**  The reflected function
`g θ = f (π/2 - θ)` satisfies the hypotheses of `endpointParamLeft` (with the same limit `F`),
and the reflection preserves both `L²`-norms on `Ioo 0 (π/2)`; hence the estimate is identical
in shape. -/
theorem endpointParamRight (f : ℝ → ℝ) (F t : ℝ)
    (ht : 0 < t) (hta : t < Real.pi / 2)
    (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    (hlim : Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds F))
    (h2 : MeasureTheory.IntegrableOn (fun x : ℝ => (deriv (deriv f) x) ^ 2)
      (Set.Ioo 0 (Real.pi / 2)))
    (h1 : MeasureTheory.IntegrableOn (fun x : ℝ => (f x) ^ 2)
      (Set.Ioo 0 (Real.pi / 2))) :
    F ^ 2 ≤ (2 / 3) * t ^ 3 * (∫ x in Set.Ioo 0 (Real.pi / 2), (deriv (deriv f) x) ^ 2)
      + 72 * t⁻¹ * (∫ x in Set.Ioo 0 (Real.pi / 2), (f x) ^ 2) := by
  obtain ⟨hintR, hintIR, hcdR, _hd1R, hd2R, hlimR⟩ := reflectFacts
  -- the reflected function
  set g : ℝ → ℝ := fun θ' => f (Real.pi / 2 - θ') with hg_eq
  have hg_cd : ContDiffOn ℝ 2 g (Set.Ioo 0 (Real.pi / 2)) := by
    simpa only [hg_eq] using hcdR f hf
  have hg_lim : Filter.Tendsto g (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds F) := by
    simpa only [hg_eq] using hlimR f F hlim
  -- pointwise identifications on the interval
  have hpt2 : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (deriv (deriv g) x) ^ 2 = (deriv (deriv f) (Real.pi / 2 - x)) ^ 2 := by
    intro x hx
    simpa only [hg_eq] using congrArg (fun y : ℝ => y ^ 2) (hd2R f hf x hx)
  have hpt1 : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (g x) ^ 2 = (f (Real.pi / 2 - x)) ^ 2 := by
    intro x _
    simp only [hg_eq]
  -- transfer of the two integrability hypotheses
  have hg_2 : MeasureTheory.IntegrableOn (fun x : ℝ => (deriv (deriv g) x) ^ 2)
      (Set.Ioo 0 (Real.pi / 2)) := by
    refine MeasureTheory.IntegrableOn.congr_fun
      (hintIR (fun y : ℝ => (deriv (deriv f) y) ^ 2) h2) ?_ measurableSet_Ioo
    intro x hx
    show (deriv (deriv f) (Real.pi / 2 - x)) ^ 2 = (deriv (deriv g) x) ^ 2
    exact (hpt2 x hx).symm
  have hg_1 : MeasureTheory.IntegrableOn (fun x : ℝ => (g x) ^ 2)
      (Set.Ioo 0 (Real.pi / 2)) := by
    refine MeasureTheory.IntegrableOn.congr_fun
      (hintIR (fun y : ℝ => (f y) ^ 2) h1) ?_ measurableSet_Ioo
    intro x hx
    show (f (Real.pi / 2 - x)) ^ 2 = (g x) ^ 2
    exact (hpt1 x hx).symm
  -- the estimate for the reflected function
  have hmain : F ^ 2
      ≤ (2 / 3) * t ^ 3 * (∫ x in Set.Ioo 0 (Real.pi / 2), (deriv (deriv g) x) ^ 2)
        + 72 * t⁻¹ * (∫ x in Set.Ioo 0 (Real.pi / 2), (g x) ^ 2) :=
    endpointParamLeft g F t ht hta hg_cd hg_lim hg_2 hg_1
  -- the two integrals are unchanged by the reflection
  have hIg1 : (∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2), (deriv (deriv g) x) ^ 2)
      = ∫ x in Set.Ioo 0 (Real.pi / 2), (deriv (deriv f) (Real.pi / 2 - x)) ^ 2 :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioo hpt2
  have hIg2 : (∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2), (deriv (deriv f) (Real.pi / 2 - x)) ^ 2)
      = ∫ x in Set.Ioo 0 (Real.pi / 2), (deriv (deriv f) x) ^ 2 := by
    simpa only using hintR (fun y : ℝ => (deriv (deriv f) y) ^ 2)
  have hIf1 : (∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2), (g x) ^ 2)
      = ∫ x in Set.Ioo 0 (Real.pi / 2), (f (Real.pi / 2 - x)) ^ 2 :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioo hpt1
  have hIf2 : (∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2), (f (Real.pi / 2 - x)) ^ 2)
      = ∫ x in Set.Ioo 0 (Real.pi / 2), (f x) ^ 2 := by
    simpa only using hintR (fun y : ℝ => (f y) ^ 2)
  have hIg : (∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2), (deriv (deriv g) x) ^ 2)
      = ∫ x in Set.Ioo 0 (Real.pi / 2), (deriv (deriv f) x) ^ 2 := hIg1.trans hIg2
  have hIf : (∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2), (g x) ^ 2)
      = ∫ x in Set.Ioo 0 (Real.pi / 2), (f x) ^ 2 := hIf1.trans hIf2
  simpa only [← hIg, ← hIf] using hmain

end Work.EllipticEst.Core.i0Aux.EndpointValues

import Mathlib
import Submission.Work.EKLComp.Hcond

namespace Work.EKLComp

open MeasureTheory

-- namespace Work.EKLComp; imports Mathlib, Submission.Work.EKLComp.Hcond; open MeasureTheory
-- Needed at `X : Type*` (the existing `Work.EKLComp.condExp_indicator_zero_inter_null` in
-- Submission/Work/EKLComp/Hcond_joinPart.lean is stated at `X : Type`).
theorem condExp_indicator_zero_inter_null_poly {X : Type*} {m : MeasurableSpace X} [mX : MeasurableSpace X]
    {ι : Type*} [Fintype ι] (A : ι → Set X) (hA : Work.EKLComp.Core.IsMPart A) (hm : m ≤ mX)
    (μ : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ] (i : ι) :
    μ ({x | MeasureTheory.condExp m μ ((A i).indicator (fun _ => (1:ℝ))) x = 0} ∩ A i) = 0 := by
  set Z : Set X := {x | condExp m μ ((A i).indicator (fun _ => (1:ℝ))) x = 0} with hZdef
  have hp_meas : Measurable[m] (fun x => condExp m μ ((A i).indicator (fun _ => (1:ℝ))) x) :=
    stronglyMeasurable_condExp.measurable
  have hZmeas : MeasurableSet[m] Z := hp_meas (measurableSet_singleton 0)
  have hZamb : MeasurableSet Z := hm Z hZmeas
  have hint : Integrable ((A i).indicator (fun _ => (1:ℝ))) μ :=
    (integrable_const (1:ℝ)).indicator (hA.measurable i)
  have h1 : ∫ x in Z, condExp m μ ((A i).indicator (fun _ => (1:ℝ))) x ∂μ
      = ∫ x in Z, ((A i).indicator (fun _ => (1:ℝ))) x ∂μ :=
    setIntegral_condExp (m := m) (m₀ := mX) hm hint hZmeas
  have h2 : ∫ x in Z, condExp m μ ((A i).indicator (fun _ => (1:ℝ))) x ∂μ = 0 := by
    rw [show (∫ x in Z, condExp m μ ((A i).indicator (fun _ => (1:ℝ))) x ∂μ)
        = ∫ x in Z, (0:ℝ) ∂μ from ?_]
    · simp
    · refine setIntegral_congr_fun hZamb (fun x hx => ?_)
      exact hx
  have h3 : ∫ x in Z, ((A i).indicator (fun _ => (1:ℝ))) x ∂μ = (μ (Z ∩ A i)).toReal := by
    rw [← integral_indicator hZamb]
    have hfun : Z.indicator (fun x => ((A i).indicator (fun _ => (1:ℝ))) x)
        = (Z ∩ A i).indicator (fun _ => (1:ℝ)) := by
      funext x
      by_cases hx : x ∈ Z <;> by_cases hy : x ∈ A i <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx, hy]
    rw [hfun]
    exact integral_indicator_one (hZamb.inter (hA.measurable i))
  have h4 : (μ (Z ∩ A i)).toReal = 0 := by rw [← h3, ← h1, h2]
  rcases (ENNReal.toReal_eq_zero_iff (μ (Z ∩ A i))).mp h4 with h | h
  · exact h
  · exact absurd h (measure_ne_top μ _)

end Work.EKLComp

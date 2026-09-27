import Mathlib
import Submission.Work.EKLContract.Defs
import Submission.Work.EKLComp.Core
import Submission.Work.EKLComp.LeafDefs

namespace Work.Misiurewicz

open MeasureTheory Filter Topology
open scoped ENNReal

theorem tendsto_Hfam_of_tendsto_of_null_frontier {ι : Type*} [Fintype ι]
    (μ : MeasureTheory.ProbabilityMeasure Work.EKLContract.X3)
    (μs : ℕ → MeasureTheory.ProbabilityMeasure Work.EKLContract.X3)
    (h : Filter.Tendsto μs Filter.atTop (nhds μ)) (Q : ι → Set Work.EKLContract.X3)
    (hQ : ∀ i, (μ : MeasureTheory.Measure Work.EKLContract.X3) (frontier (Q i)) = 0) :
    Filter.Tendsto (fun j => Work.EKLContract.Hfam ((μs j : MeasureTheory.ProbabilityMeasure Work.EKLContract.X3) : MeasureTheory.Measure Work.EKLContract.X3) Q) Filter.atTop
      (nhds (Work.EKLContract.Hfam (μ : MeasureTheory.Measure Work.EKLContract.X3) Q)) := by
  have key : ∀ i, Filter.Tendsto
      (fun j => Real.negMulLog (((μs j : MeasureTheory.ProbabilityMeasure Work.EKLContract.X3) : MeasureTheory.Measure Work.EKLContract.X3) (Q i)).toReal)
      Filter.atTop
      (nhds (Real.negMulLog (((μ : MeasureTheory.ProbabilityMeasure Work.EKLContract.X3) : MeasureTheory.Measure Work.EKLContract.X3) (Q i)).toReal)) := by
    intro i
    have hbdry : (μ : MeasureTheory.Measure Work.EKLContract.X3) (frontier (Q i)) = 0 := hQ i
    have hconv := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' h hbdry
    have hreal := (ENNReal.tendsto_toReal
      (measure_ne_top (μ : MeasureTheory.Measure Work.EKLContract.X3) (Q i))).comp hconv
    exact (Real.continuous_negMulLog.tendsto _).comp hreal
  simp only [Work.EKLContract.Hfam]
  exact tendsto_finsetSum Finset.univ (fun i _ => key i)

end Work.Misiurewicz

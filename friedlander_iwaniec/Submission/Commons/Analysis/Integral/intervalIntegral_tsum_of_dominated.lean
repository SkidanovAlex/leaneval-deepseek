import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace Commons.Analysis.Integral

open MeasureTheory
open scoped Interval

theorem intervalIntegral_tsum_of_dominated {ι : Type*} [Countable ι]
    {a b : ℝ} (hab : a ≤ b) (f : ι → ℝ → ℂ) (g : ι → ℝ)
    (hf : ∀ n, Continuous (f n)) (hg : Summable g)
    (hbd : ∀ n y, y ∈ Set.Icc a b → ‖f n y‖ ≤ g n) :
    ∫ y in a..b, (∑' n, f n y) = ∑' n, ∫ y in a..b, f n y := by
  have hS : HasSum (fun n => ∫ y in a..b, f n y) (∫ y in a..b, ∑' n, f n y) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (μ := volume) (F := f) (f := fun y => ∑' n, f n y) (bound := fun n _ => g n) ?_ ?_ ?_ ?_ ?_
    · intro n
      exact (hf n).aestronglyMeasurable
    · intro n
      filter_upwards with t ht
      rw [Set.uIoc_of_le hab] at ht
      exact hbd n t (Set.Ioc_subset_Icc_self ht)
    · filter_upwards with t ht
      exact hg
    · simp
    · filter_upwards with t ht
      have htIcc : t ∈ Set.Icc a b := by
        rw [Set.uIoc_of_le hab] at ht
        exact Set.Ioc_subset_Icc_self ht
      exact (Summable.of_norm_bounded hg (fun n => hbd n t htIcc)).hasSum
  exact hS.tsum_eq.symm

end Commons.Analysis.Integral
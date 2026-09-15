import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open MeasureTheory

namespace Commons.Analysis.Calculus

theorem multilinear_intervalIntegral_apply {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {ι : Type*} [Fintype ι] {M : ι → Type*} [∀ i, NormedAddCommGroup (M i)] [∀ i, NormedSpace ℝ (M i)]
    {a b : ℝ} {T : ℝ → ContinuousMultilinearMap ℝ M G}
    (hT : IntervalIntegrable T volume a b) (m : ∀ i, M i) :
    (∫ s in a..b, T s) m = ∫ s in a..b, (T s) m := by
  rcases le_total a b with hab | hba
  · simp only [intervalIntegral.integral_of_le hab]
    exact ContinuousMultilinearMap.integral_apply (μ := volume.restrict (Set.Ioc a b)) hT.1 m
  · simp only [intervalIntegral.integral_of_ge hba]
    rw [neg_apply,
      ContinuousMultilinearMap.integral_apply (μ := volume.restrict (Set.Ioc b a)) hT.2 m]

end Commons.Analysis.Calculus
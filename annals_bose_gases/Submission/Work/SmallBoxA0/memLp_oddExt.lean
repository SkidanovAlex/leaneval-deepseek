import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.SmallBoxA0.SinParsevalDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxA0

open MeasureTheory

lemma memLp_oddExt {F : ℝ → ℝ} (hF : Continuous F) :
    MeasureTheory.MemLp (fun v : ℝ => ((Work.SmallBoxA0.oddExt F v : ℝ) : ℂ)) 2
      (MeasureTheory.volume.restrict (Set.Ioc (-1) 1)) := by
  -- `F` is continuous, hence bounded on the compact interval `[-1/2, 1/2]`.
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (f := F) hF.continuousOn (s := Set.Icc (-(1/2)) (1/2))
  -- `oddExt F` is measurable: it is a piecewise definition with measurable branches.
  have hmeas : Measurable (Work.SmallBoxA0.oddExt F) := by
    unfold Work.SmallBoxA0.oddExt
    refine Measurable.ite measurableSet_Iic ?_ ?_
    · exact (show Continuous (fun v : ℝ => -(F (-v - 1/2))) by fun_prop).measurable
    · exact (show Continuous (fun v : ℝ => F (v - 1/2)) by fun_prop).measurable
  -- The measure `volume.restrict (Ioc (-1) 1)` is finite, and the function is
  -- essentially bounded by `C`, so it lies in every `L^p`.
  refine MeasureTheory.MemLp.of_bound ?_ C ?_
  · exact (Complex.continuous_ofReal.measurable.comp hmeas).aestronglyMeasurable
  · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioc] with v hv
    rw [show ‖((Work.SmallBoxA0.oddExt F v : ℝ) : ℂ)‖ = |Work.SmallBoxA0.oddExt F v| from by simp]
    by_cases hv0 : v ≤ 0
    · rw [oddExt, if_pos hv0]
      simp only [abs_neg]
      -- `-v - 1/2 ∈ [-1/2, 1/2]` since `-1 < v ≤ 0`.
      exact hC _ (by constructor <;> linarith [hv.1, hv.2])
    · rw [oddExt, if_neg hv0]
      -- `v - 1/2 ∈ [-1/2, 1/2]` since `0 < v ≤ 1`.
      have hvpos : 0 < v := not_le.mp hv0
      exact hC _ (by constructor <;> linarith [hv.1, hv.2])

end Work.SmallBoxA0

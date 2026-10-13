import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS.PhiStar.Radial

theorem intervalIntegrable_of_Ioi_Ioo {f : ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hf : ContinuousOn f (Set.Ioi 0)) (h0 : MeasureTheory.IntegrableOn f (Set.Ioo 0 1)) :
    IntervalIntegrable f volume 0 z := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hz.le]
  rcases le_or_gt z 1 with hz1 | hz1
  · -- `z ≤ 1`: `Ioc 0 z ⊆ Ioo 0 1 ∪ {z}`, on which `f` is integrable.
    refine ((h0.union (MeasureTheory.IntegrableOn.of_measure_zero
      (MeasureTheory.measure_singleton z))).mono_set ?_)
    intro x hx
    rcases eq_or_lt_of_le hx.2 with h | h
    · exact Or.inr h
    · exact Or.inl ⟨hx.1, lt_of_lt_of_le h hz1⟩
  · -- `1 < z`: `Ioc 0 z = Ioo 0 1 ∪ Icc 1 z`; `f` is continuous on the compact `Icc 1 z`.
    have hB : MeasureTheory.IntegrableOn f (Set.Icc 1 z) volume :=
      (hf.mono (fun x hx => lt_of_lt_of_le zero_lt_one hx.1)).integrableOn_Icc
    have := h0.union hB
    rwa [Set.Ioo_union_Icc_eq_Ioc zero_lt_one hz1.le] at this

end Work.FTS.PhiStar.Radial

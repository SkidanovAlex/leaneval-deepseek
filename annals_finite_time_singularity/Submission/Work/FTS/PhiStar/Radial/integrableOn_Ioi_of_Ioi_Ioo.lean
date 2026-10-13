import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Radial

theorem integrableOn_Ioi_of_Ioi_Ioo {f : ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hf : ContinuousOn f (Set.Ioi 0)) (hinf : MeasureTheory.IntegrableOn f (Set.Ioi 1)) :
    MeasureTheory.IntegrableOn f (Set.Ioi z) := by
  rcases le_total 1 z with hz1 | hz1
  · exact hinf.mono_set (Set.Ioi_subset_Ioi hz1)
  · have hIoc : MeasureTheory.IntegrableOn f (Set.Ioc z 1) := by
      refine (hf.mono ?_).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
      intro x hx
      exact hz.trans_le hx.1
    have hsub : Set.Ioi z ⊆ Set.Ioc z 1 ∪ Set.Ioi 1 := by
      intro x hx
      rcases lt_trichotomy x 1 with h | h | h
      · exact Or.inl ⟨hx, le_of_lt h⟩
      · exact Or.inl ⟨hx, le_of_eq h⟩
      · exact Or.inr h
    exact (hIoc.union hinf).mono_set hsub

end Work.FTS.PhiStar.Radial

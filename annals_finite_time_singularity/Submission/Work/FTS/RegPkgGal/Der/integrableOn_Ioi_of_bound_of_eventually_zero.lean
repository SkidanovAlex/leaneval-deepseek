import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.RegPkgGal.Der.L12fBasic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.RegPkgGal.Der

theorem integrableOn_Ioi_of_bound_of_eventually_zero {f : ℝ → ℝ} {c L : ℝ}
    (hL : 0 < L)
    (hcont : ContinuousOn f (Set.Ioi 0))
    (hb : ∀ s : ℝ, 0 < s → |f s| ≤ c)
    (hz : ∀ s : ℝ, L ≤ s → f s = 0) :
    MeasureTheory.IntegrableOn f (Set.Ioi (0 : ℝ)) := by
  -- Split `Ioi 0` into the bounded piece `Ioo 0 L`, where `f` is continuous and
  -- bounded, and `Ici L`, where `f` vanishes.
  have hIoo : MeasureTheory.IntegrableOn f (Set.Ioo (0 : ℝ) L) := by
    refine MeasureTheory.IntegrableOn.of_bound ?_ ?_ c ?_
    · rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top
    · exact (hcont.mono Set.Ioo_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioo
    · rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
      filter_upwards with x hx
      rw [Real.norm_eq_abs]
      exact hb x hx.1
  have hIci : MeasureTheory.IntegrableOn f (Set.Ici L) := by
    refine (MeasureTheory.integrableOn_zero (s := Set.Ici L)).congr_fun ?_ measurableSet_Ici
    intro x hx
    exact (hz x hx).symm
  have hset : Set.Ioo (0 : ℝ) L ∪ Set.Ici L = Set.Ioi 0 := by
    ext x
    constructor
    · rintro (⟨h0, _⟩ | hLx)
      · exact h0
      · exact lt_of_lt_of_le hL hLx
    · intro hx
      rcases lt_or_ge x L with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr h
  rw [← hset]
  exact hIoo.union hIci

end Work.FTS.RegPkgGal.Der

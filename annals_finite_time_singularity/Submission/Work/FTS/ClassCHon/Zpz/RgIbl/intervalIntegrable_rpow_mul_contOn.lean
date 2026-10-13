import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassCHon.Zpz.RgIbl

theorem intervalIntegrable_rpow_mul_contOn {q : ℝ} {c : ℝ → ℝ}
    (hc : ContinuousOn c (Set.Ioi 0))
    (h0 : MeasureTheory.IntegrableOn
      (fun t : ℝ => c t * t ^ (q - 1)) (Set.Ioo 0 1))
    {z : ℝ} (hz : 0 < z) :
    IntervalIntegrable (fun t : ℝ => c t * t ^ (q - 1)) MeasureTheory.volume 0 z := by
  rw [intervalIntegrable_iff]
  have hcont : ContinuousOn (fun t : ℝ => c t * t ^ (q - 1)) (Set.Ioi 0) :=
    hc.mul fun t ht =>
      (Real.continuousAt_rpow_const t (q - 1) (Or.inl (ne_of_gt ht))).continuousWithinAt
  -- the whole interval of integration is contained in `Ioc 0 Z`, `Z := max z 1`
  set Z : ℝ := max z 1 with hZdef
  have hzZ : z ≤ Z := le_max_left _ _
  have hZ1 : 1 ≤ Z := le_max_right _ _
  -- on `[1,Z]` the function is continuous, hence integrable
  have hIcc : MeasureTheory.IntegrableOn (fun t : ℝ => c t * t ^ (q - 1))
      (Set.Icc 1 Z) MeasureTheory.volume :=
    (hcont.mono fun t ht => lt_of_lt_of_le zero_lt_one ht.1).integrableOn_compact isCompact_Icc
  have hIoc : MeasureTheory.IntegrableOn (fun t : ℝ => c t * t ^ (q - 1))
      (Set.Ioc 0 Z) MeasureTheory.volume := by
    have hset : Set.Ioc 0 Z = Set.Ioo 0 1 ∪ Set.Icc 1 Z := by
      ext t
      constructor
      · intro ht
        rcases lt_or_ge t 1 with h | h
        · exact Or.inl ⟨ht.1, h⟩
        · exact Or.inr ⟨h, ht.2⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact ⟨h1, le_trans h2.le hZ1⟩
        · exact ⟨lt_of_lt_of_le zero_lt_one h1, h2⟩
    rw [hset]
    exact h0.union hIcc
  exact hIoc.mono_set fun t ht => by
    rw [Set.uIoc_of_le hz.le] at ht
    exact ⟨ht.1, le_trans ht.2 hzZ⟩

end Work.FTS.ClassCHon.Zpz.RgIbl

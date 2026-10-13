import Mathlib
import Submission.Work.WilG4a.f1affine1_defs

namespace Work.WilG4a.CD

/-- The preimage under `ℝ → EReal` of an extended-real open interval `Ioo A B` with `A ≠ ⊥`
and `B ≠ ⊤` is an open interval of reals (possibly empty). -/
lemma exists_Ioo_preimage (A B : EReal) (hA : A ≠ ⊥) (hB : B ≠ ⊤) :
    ∃ a' b' : ℝ, Real.toEReal ⁻¹' Set.Ioo A B = Set.Ioo a' b' := by
  by_cases hAtop : A = ⊤
  · subst hAtop
    exact ⟨0, 0, by
      rw [Set.Ioo_eq_empty (not_top_lt : ¬ (⊤ : EReal) < B), Set.preimage_empty, Set.Ioo_self]⟩
  · by_cases hBbot : B = ⊥
    · subst hBbot
      exact ⟨0, 0, by
        rw [Set.Ioo_eq_empty (not_lt_bot : ¬ A < (⊥ : EReal)), Set.preimage_empty, Set.Ioo_self]⟩
    · refine ⟨A.toReal, B.toReal, ?_⟩
      rw [← EReal.coe_toReal hAtop hA, ← EReal.coe_toReal hB hBbot]
      exact EReal.preimage_coe_Ioo _ _

/-- Intersecting the preimage of an extended-real open interval with the unit interval `(0,1)`
yields an open interval of reals. -/
lemma preimage_Ioo_inter_unit (a b : EReal) :
    ∃ a' b' : ℝ, Real.toEReal ⁻¹' (Set.Ioo a b) ∩ Set.Ioo (0 : ℝ) 1 = Set.Ioo a' b' := by
  obtain ⟨a', b', hab⟩ := exists_Ioo_preimage (max a ((0 : ℝ) : EReal)) (min b ((1 : ℝ) : EReal))
    (ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (le_max_right a ((0 : ℝ) : EReal))))
    (ne_of_lt (lt_of_le_of_lt (min_le_right b ((1 : ℝ) : EReal)) (EReal.coe_lt_top (1 : ℝ))))
  refine ⟨a', b', ?_⟩
  rw [show Set.Ioo (0 : ℝ) 1 = Real.toEReal ⁻¹' Set.Ioo ((0 : ℝ) : EReal) ((1 : ℝ) : EReal)
        from (EReal.preimage_coe_Ioo 0 1).symm]
  rw [← Set.preimage_inter, Set.Ioo_inter_Ioo]
  exact hab

theorem fibre_inter_I {s : Set ℝ}
    (h : s.Subsingleton ∨ ∃ a b : EReal, s = {y : ℝ | a < (y : EReal) ∧ (y : EReal) < b}) :
    (s ∩ Work.WilG4a.I).Subsingleton ∨ ∃ a b : ℝ, s ∩ Work.WilG4a.I = Set.Ioo a b := by
  rcases h with hss | ⟨a, b, rfl⟩
  · exact Or.inl (hss.anti Set.inter_subset_left)
  · right
    obtain ⟨a', b', hab⟩ := preimage_Ioo_inter_unit a b
    exact ⟨a', b', hab⟩

end Work.WilG4a.CD

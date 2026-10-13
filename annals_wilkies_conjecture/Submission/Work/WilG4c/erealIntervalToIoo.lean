import Mathlib

namespace Work.WilG4c

theorem erealIntervalToIoo {a b : EReal} {lo hi : ℝ}
    (hne : ({y : ℝ | a < (y : EReal) ∧ (y : EReal) < b}).Nonempty)
    (hbdd : ∀ x : ℝ, a < (x : EReal) → (x : EReal) < b → lo ≤ x ∧ x ≤ hi) :
    a ≠ ⊥ ∧ b ≠ ⊤ ∧
      {y : ℝ | a < (y : EReal) ∧ (y : EReal) < b} = Set.Ioo a.toReal b.toReal := by
  obtain ⟨y0, hy0⟩ := hne
  obtain ⟨hy0a, hy0b⟩ := hy0
  obtain ⟨hlo, hhi⟩ := hbdd y0 hy0a hy0b
  -- `a ≠ ⊥`: if `a = ⊥` then `lo - 1` lies in the set, forcing `lo ≤ lo - 1`.
  have ha_ne_bot : a ≠ ⊥ := by
    intro h
    have h1 : a < ((lo - 1 : ℝ) : EReal) := by
      rw [h]; exact EReal.bot_lt_coe _
    have h2 : ((lo - 1 : ℝ) : EReal) < b :=
      (EReal.coe_lt_coe_iff.mpr (by linarith)).trans hy0b
    have h3 := (hbdd (lo - 1) h1 h2).1
    linarith
  -- `b ≠ ⊤`: if `b = ⊤` then `hi + 1` lies in the set, forcing `hi + 1 ≤ hi`.
  have hb_ne_top : b ≠ ⊤ := by
    intro h
    have h1 : a < ((hi + 1 : ℝ) : EReal) :=
      hy0a.trans (EReal.coe_lt_coe_iff.mpr (by linarith))
    have h2 : ((hi + 1 : ℝ) : EReal) < b := by
      rw [h]; exact EReal.coe_lt_top _
    have h3 := (hbdd (hi + 1) h1 h2).2
    linarith
  -- Nonemptiness rules out `a = ⊤` and `b = ⊥`.
  have ha_ne_top : a ≠ ⊤ := by
    intro h
    rw [h] at hy0a
    exact absurd (lt_of_lt_of_le hy0a le_top) (lt_irrefl (⊤ : EReal))
  have hb_ne_bot : b ≠ ⊥ := by
    intro h
    rw [h] at hy0b
    exact absurd (lt_of_lt_of_le hy0b bot_le) (lt_irrefl (y0 : EReal))
  have ha' : a = ((a.toReal : ℝ) : EReal) :=
    (EReal.coe_toReal ha_ne_top ha_ne_bot).symm
  have hb' : b = ((b.toReal : ℝ) : EReal) :=
    (EReal.coe_toReal hb_ne_top hb_ne_bot).symm
  refine ⟨ha_ne_bot, hb_ne_top, ?_⟩
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_Ioo]
  constructor
  · rintro ⟨h1, h2⟩
    rw [ha'] at h1
    rw [hb'] at h2
    exact ⟨EReal.coe_lt_coe_iff.mp h1, EReal.coe_lt_coe_iff.mp h2⟩
  · rintro ⟨h1, h2⟩
    rw [ha', hb']
    exact ⟨EReal.coe_lt_coe_iff.mpr h1, EReal.coe_lt_coe_iff.mpr h2⟩

end Work.WilG4c

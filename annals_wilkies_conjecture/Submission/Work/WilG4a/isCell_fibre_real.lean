import Mathlib
import Submission.Work.WilG4a.LipChartsDefs
import Submission.Work.WilG4a.isCell_fiber

namespace Work.WilG4a

/-- The fibre of a cell that is contained in the strip `{z | z(last) ∈ (0,1)}` is either a
subsingleton or an open interval with *real* endpoints.  `isCell_fiber` gives the dichotomy
with `EReal` endpoints; the strip hypothesis makes the endpoints finite (the fibre is bounded),
and finite `EReal`s are reals. -/
theorem isCell_fibre_real (p : ℕ) {C : Set (Fin (p + 1) → ℝ)}
    (hC : WilkiesDesign.IsCell (p + 1) C) (hstrip : C ⊆ Work.WilG4a.strip p) (l : Fin p → ℝ) :
    (Work.WilG4a.fibre C l).Subsingleton ∨ ∃ a b : ℝ, Work.WilG4a.fibre C l = Set.Ioo a b := by
  rcases isCell_fiber p hC l with ⟨x, hx⟩ | ⟨a, b, hab⟩
  · left
    have hx' : fibre C l = {x} := hx
    rw [hx']
    exact Set.subsingleton_singleton
  · by_cases hne : (fibre C l).Nonempty
    · right
      -- The `EReal`-interval `S` is contained in `(0,1)`, hence bounded.
      have hSsub : {y : ℝ | a < (y : EReal) ∧ (y : EReal) < b} ⊆ Set.Ioo (0 : ℝ) 1 := by
        intro y hy
        rw [← hab] at hy
        have hz : Fin.snoc l y ∈ C := hy
        have hstrip' := hstrip hz
        simpa [Work.WilG4a.strip, Work.WilG4a.I, Fin.snoc_last] using hstrip'
      obtain ⟨y₀, hy₀⟩ := hne
      have hy₀S : y₀ ∈ {y : ℝ | a < (y : EReal) ∧ (y : EReal) < b} := by
        rw [← hab]; exact hy₀
      have hy₀I := hSsub hy₀S
      obtain ⟨ha₀, hb₀⟩ := hy₀S
      -- All four endpoint infinities are excluded by non-emptiness + boundedness.
      have ha_ne_bot : a ≠ ⊥ := by
        intro hbot
        have hy : y₀ - 1 ∈ {y : ℝ | a < (y : EReal) ∧ (y : EReal) < b} := by
          refine ⟨?_, ?_⟩
          · rw [hbot]; exact EReal.bot_lt_coe _
          · calc ((y₀ - 1 : ℝ) : EReal) < (y₀ : EReal) :=
                EReal.coe_lt_coe_iff.2 (by linarith)
              _ < b := hb₀
        have := (hSsub hy).1
        linarith [hy₀I.2]
      have ha_ne_top : a ≠ ⊤ := by
        intro htop
        rw [htop] at ha₀
        exact absurd ha₀ (not_lt_of_ge le_top)
      have hb_ne_top : b ≠ ⊤ := by
        intro htop
        have hy : y₀ + 1 ∈ {y : ℝ | a < (y : EReal) ∧ (y : EReal) < b} := by
          refine ⟨?_, ?_⟩
          · calc a < (y₀ : EReal) := ha₀
              _ < ((y₀ + 1 : ℝ) : EReal) := EReal.coe_lt_coe_iff.2 (by linarith)
          · rw [htop]; exact EReal.coe_lt_top _
        have := (hSsub hy).2
        linarith [hy₀I.1]
      have hb_ne_bot : b ≠ ⊥ := by
        intro hbot
        rw [hbot] at hb₀
        exact absurd hb₀ (not_lt_of_ge bot_le)
      refine ⟨a.toReal, b.toReal, ?_⟩
      have hS_eq : {y : ℝ | a < (y : EReal) ∧ (y : EReal) < b} =
          Set.Ioo a.toReal b.toReal := by
        ext y
        simp only [Set.mem_ofPred_eq, Set.mem_Ioo]
        constructor
        · rintro ⟨h1, h2⟩
          refine ⟨?_, ?_⟩
          · rw [← EReal.coe_toReal ha_ne_top ha_ne_bot] at h1
            exact EReal.coe_lt_coe_iff.1 h1
          · rw [← EReal.coe_toReal hb_ne_top hb_ne_bot] at h2
            exact EReal.coe_lt_coe_iff.1 h2
        · rintro ⟨h1, h2⟩
          refine ⟨?_, ?_⟩
          · rw [← EReal.coe_toReal ha_ne_top ha_ne_bot, EReal.coe_lt_coe_iff]
            exact h1
          · rw [← EReal.coe_toReal hb_ne_top hb_ne_bot, EReal.coe_lt_coe_iff]
            exact h2
      have hfib : fibre C l = {y : ℝ | a < (y : EReal) ∧ (y : EReal) < b} := by
        rw [fibre, hab]
      rw [hfib, hS_eq]
    · left
      rw [Set.not_nonempty_iff_eq_empty] at hne
      rw [hne]
      exact Set.subsingleton_empty

end Work.WilG4a

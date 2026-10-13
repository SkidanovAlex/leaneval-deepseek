import Mathlib

namespace Work.WilC4

/-- Clark's real-induction principle, in the form used here.

If a predicate `P` holds at `x₁`, propagates to the right over a whole interval at every
point `x ∈ [x₁, x₂)`, and is closed under one-sided limits from the left on `(x₁, x₂]`,
then it holds at `x₂`. -/
theorem real_induction {P : ℝ → Prop} {x₁ x₂ : ℝ} (hx : x₁ ≤ x₂)
    (h1 : P x₁)
    (h2 : ∀ x, x₁ ≤ x → x < x₂ → (∀ y, x₁ ≤ y → y ≤ x → P y) →
            ∃ y, x < y ∧ y ≤ x₂ ∧ ∀ z, x₁ ≤ z → z ≤ y → P z)
    (h3 : ∀ x, x₁ < x → x ≤ x₂ → (∀ y, x₁ ≤ y → y < x → P y) → P x) :
    P x₂ := by
  set U : Set ℝ := {x | x₁ ≤ x ∧ x ≤ x₂ ∧ ∀ y, x₁ ≤ y → y ≤ x → P y}
  have hx1U : x₁ ∈ U :=
    ⟨le_rfl, hx, fun y hy1 hy2 => by
      have hy : y = x₁ := le_antisymm hy2 hy1
      rw [hy]
      exact h1⟩
  have hUne : U.Nonempty := ⟨x₁, hx1U⟩
  have hbdd : BddAbove U := ⟨x₂, fun x hx' => hx'.2.1⟩
  have hmem : sSup U ∈ U := by
    have hltc : ∀ y, x₁ ≤ y → y < sSup U → P y := by
      intro y hy1 hyc
      obtain ⟨x, hxU, hyx⟩ := (lt_csSup_iff hbdd hUne).mp hyc
      exact hxU.2.2 y hy1 (le_of_lt hyx)
    refine ⟨le_csSup hbdd hx1U, csSup_le hUne (fun x hx' => hx'.2.1), ?_⟩
    intro y hy1 hyc
    rcases lt_or_eq_of_le hyc with hlt | heq
    · exact hltc y hy1 hlt
    · subst heq
      rcases lt_or_eq_of_le (le_csSup hbdd hx1U : x₁ ≤ sSup U) with hlt2 | heq2
      · exact h3 (sSup U) hlt2 (csSup_le hUne (fun x hx' => hx'.2.1)) hltc
      · rw [← heq2]
        exact h1
  have hcx : sSup U = x₂ := by
    rcases lt_or_eq_of_le hmem.2.1 with hlt | heq
    · exfalso
      obtain ⟨y, hcy, hyx2, hPy⟩ := h2 (sSup U) hmem.1 hlt hmem.2.2
      have hyU : y ∈ U := ⟨le_of_lt (lt_of_le_of_lt hmem.1 hcy), hyx2, hPy⟩
      have hle := le_csSup hbdd hyU
      linarith
    · exact heq
  have hp : P (sSup U) := hmem.2.2 (sSup U) hmem.1 le_rfl
  rwa [hcx] at hp

theorem mono_of_germ {f : ℝ → ℝ} {a b : ℝ}
    (hL : ∀ x, a < x → x < b → ∃ ε, 0 < ε ∧ ∀ z, x - ε < z → z < x → f z < f x)
    (hR : ∀ x, a < x → x < b → ∃ ε, 0 < ε ∧ ∀ z, x < z → z < x + ε → f x < f z) :
    ∀ x₁ x₂, a < x₁ → x₁ < x₂ → x₂ < b → f x₁ ≤ f x₂ := by
  intro x₁ x₂ hx1 hx12 hx2
  refine real_induction (P := fun y => f x₁ ≤ f y) (le_of_lt hx12) le_rfl ?_ ?_
  · -- one step to the right
    intro x hx1' hxx2 hprev
    have hax : a < x := lt_of_lt_of_le hx1 hx1'
    have hxb : x < b := lt_trans hxx2 hx2
    obtain ⟨ε, hε, hε'⟩ := hR x hax hxb
    refine ⟨min (x + ε / 2) x₂, lt_min (by linarith) hxx2, min_le_right _ _, ?_⟩
    intro z hz1 hzy
    by_cases hzx : z ≤ x
    · exact hprev z hz1 hzx
    · have hzx' : x < z := by
        by_contra h
        push_neg at h
        exact hzx h
      have hzy' : z < x + ε := by
        have hle : z ≤ x + ε / 2 := le_trans hzy (min_le_left _ _)
        linarith
      exact le_of_lt (lt_of_le_of_lt (hprev x hx1' le_rfl) (hε' z hzx' hzy'))
  · -- closure under one-sided limits from the left
    intro x hx1x hxx2 hprev
    have hax : a < x := lt_trans hx1 hx1x
    have hxb : x < b := lt_of_le_of_lt hxx2 hx2
    obtain ⟨ε, hε, hε'⟩ := hL x hax hxb
    have hz2 : max x₁ (x - ε / 2) < x := max_lt hx1x (by linarith)
    have hz3 : x - ε < max x₁ (x - ε / 2) := lt_of_lt_of_le (by linarith) (le_max_right _ _)
    exact le_of_lt (lt_of_le_of_lt (hprev _ (le_max_left _ _) hz2) (hε' _ hz3 hz2))

end Work.WilC4

import Mathlib

namespace Work.WilC4

/-- If for every `x₁ < x₂ < x₃` the value `f x₂` lies (weakly) between `f x₁` and
`f x₃`, then `f` is monotone or antitone on `(a,b)`. -/
theorem cand_mono_of_between {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (h : ∀ x₁ x₂ x₃ : ℝ, x₁ ∈ Set.Ioo a b → x₂ ∈ Set.Ioo a b → x₃ ∈ Set.Ioo a b →
      x₁ < x₂ → x₂ < x₃ →
      (f x₁ ≤ f x₂ ∧ f x₂ ≤ f x₃) ∨ (f x₃ ≤ f x₂ ∧ f x₂ ≤ f x₁)) :
    MonotoneOn f (Set.Ioo a b) ∨ AntitoneOn f (Set.Ioo a b) := by
  -- reformulate the hypothesis as a "betweenness" statement
  have between : ∀ {r s t : ℝ}, r ∈ Set.Ioo a b → s ∈ Set.Ioo a b → t ∈ Set.Ioo a b →
      r < s → s < t → min (f r) (f t) ≤ f s ∧ f s ≤ max (f r) (f t) := by
    intro r s t hr hs ht hrs hst
    rcases h r s t hr hs ht hrs hst with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨le_trans (min_le_left _ _) h1, le_trans h2 (le_max_right _ _)⟩
    · exact ⟨le_trans (min_le_right _ _) h1, le_trans h2 (le_max_left _ _)⟩
  by_cases hd : ∃ p, p ∈ Set.Ioo a b ∧ ∃ q, q ∈ Set.Ioo a b ∧ p < q ∧ f p > f q
  · -- there is a strict descent, show `f` is antitone
    right
    intro x hx y hy hxy
    rcases lt_or_eq_of_le hxy with hlt | heq
    · by_contra hcon
      push_neg at hcon
      obtain ⟨p, hp, q, hq, hpq, hfpq⟩ := hd
      -- descent `p < q` with `f p > f q` forces: everything strictly to the right
      -- of `q` is `≤ f q`, everything strictly to the left of `p` is `≥ f p`.
      have keyB1 : ∀ w, w ∈ Set.Ioo a b → q < w → f w ≤ f q := by
        intro w hw hqw
        have hb := between hp hq hw hpq hqw
        by_contra hc
        push_neg at hc
        have hmin : f q < min (f p) (f w) := lt_min hfpq hc
        linarith [hb.1]
      have keyB2 : ∀ w, w ∈ Set.Ioo a b → w < p → f p ≤ f w := by
        intro w hw hwp
        have hb := between hw hp hq hwp hpq
        by_contra hc
        push_neg at hc
        have hmax : max (f w) (f q) < f p := max_lt hc hfpq
        linarith [hb.2]
      -- the assumed strict ascent `x < y` forces: everything strictly to the left of
      -- `x` is `≤ f x`, everything strictly to the right of `y` is `≥ f y`.
      have keyA1 : ∀ w, w ∈ Set.Ioo a b → w < x → f w ≤ f x := by
        intro w hw hwx
        have hb := between hw hx hy hwx hlt
        by_contra hc
        push_neg at hc
        have hmin : f x < min (f w) (f y) := lt_min hc hcon
        linarith [hb.1]
      have keyA2 : ∀ w, w ∈ Set.Ioo a b → y < w → f y ≤ f w := by
        intro w hw hyw
        have hb := between hx hy hw hlt hyw
        by_contra hc
        push_neg at hc
        have hmax : max (f x) (f w) < f y := max_lt hcon hc
        linarith [hb.2]
      by_cases hqx : q ≤ x
      · -- the ascent lies entirely to the right of the descent
        have hyq : f y ≤ f q := keyB1 y hy (lt_of_le_of_lt hqx hlt)
        have hqf : f q ≤ f x := by
          rcases lt_or_eq_of_le hqx with h' | h'
          · exact keyA1 q hq h'
          · subst h'; exact le_refl _
        linarith
      · push_neg at hqx
        by_cases hyp : y ≤ p
        · -- the ascent lies entirely to the left of the descent
          have hpfx : f p ≤ f x := keyB2 x hx (lt_of_lt_of_le hlt hyp)
          have hypf : f y ≤ f p := by
            rcases lt_or_eq_of_le hyp with h' | h'
            · exact keyA2 p hp h'
            · subst h'; exact le_refl _
          linarith
        · -- the two pairs interleave
          push_neg at hyp
          have hpfx : f p ≤ f x := by
            by_cases hpx : p ≤ x
            · rcases lt_or_eq_of_le hpx with h' | h'
              · exact keyA1 p hp h'
              · subst h'; exact le_refl _
            · push_neg at hpx
              exact keyB2 x hx hpx
          have hyq : f y ≤ f q := by
            by_cases hyq' : y ≤ q
            · rcases lt_or_eq_of_le hyq' with h' | h'
              · exact keyA2 q hq h'
              · subst h'; exact le_refl _
            · push_neg at hyq'
              exact keyB1 y hy hyq'
          linarith
    · subst heq; exact le_refl _
  · -- no strict descent exists, so `f` is monotone
    left
    intro x hx y hy hxy
    rcases lt_or_eq_of_le hxy with hlt | heq
    · by_contra hcon
      push_neg at hcon
      exact hd ⟨x, hx, y, hy, hlt, hcon⟩
    · subst heq; exact le_refl _

end Work.WilC4

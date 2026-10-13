import Mathlib

namespace Work.WilC4

open Set

/-- Betweenness is preserved under negation: if `f` sends middle points between
the outer values (with respect to an ordered triple), then so does `-f`. -/
private lemma betweenness_neg {f : ℝ → ℝ} {a b : ℝ}
    (h : ∀ x₁ x₂ x₃ : ℝ, x₁ ∈ Set.Ioo a b → x₂ ∈ Set.Ioo a b → x₃ ∈ Set.Ioo a b →
      x₁ < x₂ → x₂ < x₃ →
      (f x₁ ≤ f x₂ ∧ f x₂ ≤ f x₃) ∨ (f x₃ ≤ f x₂ ∧ f x₂ ≤ f x₁)) :
    ∀ x₁ x₂ x₃ : ℝ, x₁ ∈ Set.Ioo a b → x₂ ∈ Set.Ioo a b → x₃ ∈ Set.Ioo a b →
      x₁ < x₂ → x₂ < x₃ →
      (-f x₁ ≤ -f x₂ ∧ -f x₂ ≤ -f x₃) ∨ (-f x₃ ≤ -f x₂ ∧ -f x₂ ≤ -f x₁) := by
  intro x₁ x₂ x₃ h1 h2 h3 h12 h23
  rcases h x₁ x₂ x₃ h1 h2 h3 h12 h23 with ⟨a1, a2⟩ | ⟨a1, a2⟩
  · right
    exact ⟨by linarith, by linarith⟩
  · left
    exact ⟨by linarith, by linarith⟩

/-- **Key lemma.** If `f` preserves betweenness on `(a,b)` and there is an
ascending pair `x < y` in `(a,b)` with `f x < f y`, then `f` is monotone on
`(a,b)`. -/
private lemma up_imp_mono {f : ℝ → ℝ} {a b : ℝ}
    (h : ∀ x₁ x₂ x₃ : ℝ, x₁ ∈ Set.Ioo a b → x₂ ∈ Set.Ioo a b → x₃ ∈ Set.Ioo a b →
      x₁ < x₂ → x₂ < x₃ →
      (f x₁ ≤ f x₂ ∧ f x₂ ≤ f x₃) ∨ (f x₃ ≤ f x₂ ∧ f x₂ ≤ f x₁))
    {x y : ℝ} (hx : x ∈ Set.Ioo a b) (hy : y ∈ Set.Ioo a b)
    (hxy : x < y) (hfxy : f x < f y) :
    MonotoneOn f (Set.Ioo a b) := by
  -- (a) everything strictly left of `x` has value `≤ f x`
  have ha : ∀ t ∈ Set.Ioo a b, t < x → f t ≤ f x := by
    intro t ht htx
    rcases h t x y ht hx hy htx hxy with ⟨h1, _⟩ | ⟨h1, h2⟩
    · exact h1
    · linarith
  -- (c) everything strictly right of `y` has value `≥ f y`
  have hc : ∀ t ∈ Set.Ioo a b, y < t → f y ≤ f t := by
    intro t ht hyt
    rcases h x y t hx hy ht hxy hyt with ⟨_, h2⟩ | ⟨h1, _⟩
    · exact h2
    · linarith
  -- (d) everything weakly right of `x` has value `≥ f x`
  have hd : ∀ t ∈ Set.Ioo a b, x ≤ t → f x ≤ f t := by
    intro t ht hxt
    rcases lt_trichotomy t x with h' | h' | h'
    · exact absurd hxt (not_le.mpr h')
    · rw [h']
    · rcases lt_trichotomy t y with h'' | h'' | h''
      · rcases h x t y hx ht hy h' h'' with ⟨h1, _⟩ | ⟨h1, h2⟩
        · exact h1
        · linarith
      · rw [h'']; exact le_of_lt hfxy
      · exact le_trans (le_of_lt hfxy) (hc t ht h'')
  intro u hu v hv huv
  rcases lt_trichotomy u v with huv' | huv' | huv'
  · rcases lt_trichotomy v x with hvx | hvx | hvx
    · -- v < x, so u < v < x
      have hux : u < x := lt_trans huv' hvx
      rcases h u v x hu hv hx huv' hvx with ⟨h1, _⟩ | ⟨h1, h2⟩
      · exact h1
      · have hufx : f u ≤ f x := ha u hu hux
        linarith
    · -- v = x
      rw [hvx]
      exact ha u hu (hvx ▸ huv')
    · -- x < v
      rcases lt_trichotomy u x with hux | hux | hux
      · -- u < x < v
        have h1 : f u ≤ f x := ha u hu hux
        have h2 : f x ≤ f v := hd v hv (le_of_lt hvx)
        linarith
      · -- u = x
        rw [hux]
        exact hd v hv (le_of_lt hvx)
      · -- x < u < v
        rcases h x u v hx hu hv hux huv' with ⟨_, h2⟩ | ⟨h1, h2⟩
        · exact h2
        · have hax : f x ≤ f u := hd u hu (le_of_lt hux)
          have hbv : f x ≤ f v := hd v hv (le_of_lt hvx)
          linarith
  · -- u = v
    rw [huv']
  · -- v < u contradicts u ≤ v
    exact absurd huv (not_le.mpr huv')

theorem mono_of_three_point {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (h : ∀ x₁ x₂ x₃ : ℝ, x₁ ∈ Set.Ioo a b → x₂ ∈ Set.Ioo a b → x₃ ∈ Set.Ioo a b →
      x₁ < x₂ → x₂ < x₃ →
      (f x₁ ≤ f x₂ ∧ f x₂ ≤ f x₃) ∨ (f x₃ ≤ f x₂ ∧ f x₂ ≤ f x₁)) :
    MonotoneOn f (Set.Ioo a b) ∨ AntitoneOn f (Set.Ioo a b) := by
  by_cases hup : ∃ x : ℝ, x ∈ Set.Ioo a b ∧ ∃ y : ℝ, y ∈ Set.Ioo a b ∧ x < y ∧ f x < f y
  · obtain ⟨x, hx, y, hy, hxy, hfxy⟩ := hup
    exact Or.inl (up_imp_mono h hx hy hxy hfxy)
  · by_cases hdown : ∃ x : ℝ, x ∈ Set.Ioo a b ∧ ∃ y : ℝ, y ∈ Set.Ioo a b ∧ x < y ∧ f y < f x
    · obtain ⟨x, hx, y, hy, hxy, hfyx⟩ := hdown
      refine Or.inr ?_
      have hg : MonotoneOn (fun t => -f t) (Set.Ioo a b) :=
        up_imp_mono (f := fun t => -f t) (betweenness_neg h) hx hy hxy (by linarith)
      intro u hu v hv huv
      have := hg hu hv huv
      linarith
    · refine Or.inl ?_
      intro u hu v hv huv
      rcases lt_or_eq_of_le huv with huv' | huv'
      · exact not_lt.mp (fun hlt => hdown ⟨u, hu, v, hv, huv', hlt⟩)
      · rw [huv']

end Work.WilC4

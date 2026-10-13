import Mathlib
import Submission.Work.WilC4.monoDefs
import Submission.Work.WilC4.mono_of_germ
import Submission.Work.WilC4.antitone_of_germ

namespace Work.WilC4

/-- **Germ type determines monotonicity.**

If the partial function described by `Y` has, at every point `x ∈ (a, b)`, a left germ strictly
below the value at `x` (`MonoLm`) and a right germ strictly above it (`MonoHp`), then `Y` is
nondecreasing on `(a, b)`; dually `MonoHm` (left germ above) together with `MonoLp` (right germ
below) forces `Y` to be nonincreasing on `(a, b)`.

The proof materialises the partial function as a total function `F` on `(a, b)` (well defined by
`hfun`), observes that its one-sided germs satisfy the hypotheses of `mono_of_germ` /
`antitone_of_germ`, and reads the conclusion back off `Y` using uniqueness of the value. -/
theorem germ_mono_of_types {Y : Set (Fin 2 → ℝ)} {a b : ℝ}
    (hfun : ∀ x y y' : ℝ, ![x, y] ∈ Y → ![x, y'] ∈ Y → y = y') :
    ((Set.Ioo a b ⊆ MonoLm Y ∧ Set.Ioo a b ⊆ MonoHp Y) → MonoIncOn Y a b) ∧
      ((Set.Ioo a b ⊆ MonoHm Y ∧ Set.Ioo a b ⊆ MonoLp Y) → MonoDecOn Y a b) := by
  constructor
  · rintro ⟨hLm, hHp⟩
    have hval : ∀ x ∈ Set.Ioo a b, ∃ y, ![x, y] ∈ Y := fun x hx => by
      obtain ⟨ε, y, _, hy, _⟩ := hLm hx
      exact ⟨y, hy⟩
    let F : ℝ → ℝ := fun x => if hx : x ∈ Set.Ioo a b then Classical.choose (hval x hx) else 0
    have hFmem : ∀ x (hx : x ∈ Set.Ioo a b), ![x, F x] ∈ Y := by
      intro x hx
      have h1 : F x = Classical.choose (hval x hx) := dif_pos hx
      rw [h1]
      exact Classical.choose_spec (hval x hx)
    have hFgermL : ∀ x, a < x → x < b → ∃ ε, 0 < ε ∧ ∀ z, x - ε < z → z < x → F z < F x := by
      intro x hx1 hx2
      obtain ⟨ε₀, y, hε₀, hy, hgerm⟩ := hLm (show x ∈ Set.Ioo a b from ⟨hx1, hx2⟩)
      have hyF : y = F x := hfun x y (F x) hy (hFmem x ⟨hx1, hx2⟩)
      refine ⟨min ε₀ (x - a), lt_min hε₀ (by linarith), ?_⟩
      intro z hz1 hz2
      have hzI : z ∈ Set.Ioo a b := ⟨by have := min_le_right ε₀ (x - a); linarith, by linarith⟩
      obtain ⟨y', hy', hlt⟩ := hgerm z (by have := min_le_left ε₀ (x - a); linarith) hz2
      have hy'F : y' = F z := hfun z y' (F z) hy' (hFmem z hzI)
      rw [hy'F, hyF] at hlt
      exact hlt
    have hFgermR : ∀ x, a < x → x < b → ∃ ε, 0 < ε ∧ ∀ z, x < z → z < x + ε → F x < F z := by
      intro x hx1 hx2
      obtain ⟨ε₀, y, hε₀, hy, hgerm⟩ := hHp (show x ∈ Set.Ioo a b from ⟨hx1, hx2⟩)
      have hyF : y = F x := hfun x y (F x) hy (hFmem x ⟨hx1, hx2⟩)
      refine ⟨min ε₀ (b - x), lt_min hε₀ (by linarith), ?_⟩
      intro z hz1 hz2
      have hzI : z ∈ Set.Ioo a b := ⟨by linarith, by have := min_le_right ε₀ (b - x); linarith⟩
      obtain ⟨y', hy', hlt⟩ := hgerm z hz1 (by have := min_le_left ε₀ (b - x); linarith)
      have hy'F : y' = F z := hfun z y' (F z) hy' (hFmem z hzI)
      rw [hy'F, hyF] at hlt
      exact hlt
    have hmono := mono_of_germ hFgermL hFgermR
    intro x₁ x₂ y₁ y₂ ha h12 h2b hy1 hy2
    have hx1 : x₁ ∈ Set.Ioo a b := ⟨ha, by linarith⟩
    have hx2 : x₂ ∈ Set.Ioo a b := ⟨by linarith, h2b⟩
    have e1 : y₁ = F x₁ := hfun x₁ y₁ (F x₁) hy1 (hFmem x₁ hx1)
    have e2 : y₂ = F x₂ := hfun x₂ y₂ (F x₂) hy2 (hFmem x₂ hx2)
    have := hmono x₁ x₂ ha h12 h2b
    linarith
  · rintro ⟨hHm, hLp⟩
    have hval : ∀ x ∈ Set.Ioo a b, ∃ y, ![x, y] ∈ Y := fun x hx => by
      obtain ⟨ε, y, _, hy, _⟩ := hHm hx
      exact ⟨y, hy⟩
    let F : ℝ → ℝ := fun x => if hx : x ∈ Set.Ioo a b then Classical.choose (hval x hx) else 0
    have hFmem : ∀ x (hx : x ∈ Set.Ioo a b), ![x, F x] ∈ Y := by
      intro x hx
      have h1 : F x = Classical.choose (hval x hx) := dif_pos hx
      rw [h1]
      exact Classical.choose_spec (hval x hx)
    have hFgermL : ∀ x, a < x → x < b → ∃ ε, 0 < ε ∧ ∀ z, x - ε < z → z < x → F x < F z := by
      intro x hx1 hx2
      obtain ⟨ε₀, y, hε₀, hy, hgerm⟩ := hHm (show x ∈ Set.Ioo a b from ⟨hx1, hx2⟩)
      have hyF : y = F x := hfun x y (F x) hy (hFmem x ⟨hx1, hx2⟩)
      refine ⟨min ε₀ (x - a), lt_min hε₀ (by linarith), ?_⟩
      intro z hz1 hz2
      have hzI : z ∈ Set.Ioo a b := ⟨by have := min_le_right ε₀ (x - a); linarith, by linarith⟩
      obtain ⟨y', hy', hlt⟩ := hgerm z (by have := min_le_left ε₀ (x - a); linarith) hz2
      have hy'F : y' = F z := hfun z y' (F z) hy' (hFmem z hzI)
      rw [hy'F, hyF] at hlt
      exact hlt
    have hFgermR : ∀ x, a < x → x < b → ∃ ε, 0 < ε ∧ ∀ z, x < z → z < x + ε → F z < F x := by
      intro x hx1 hx2
      obtain ⟨ε₀, y, hε₀, hy, hgerm⟩ := hLp (show x ∈ Set.Ioo a b from ⟨hx1, hx2⟩)
      have hyF : y = F x := hfun x y (F x) hy (hFmem x ⟨hx1, hx2⟩)
      refine ⟨min ε₀ (b - x), lt_min hε₀ (by linarith), ?_⟩
      intro z hz1 hz2
      have hzI : z ∈ Set.Ioo a b := ⟨by linarith, by have := min_le_right ε₀ (b - x); linarith⟩
      obtain ⟨y', hy', hlt⟩ := hgerm z hz1 (by have := min_le_left ε₀ (b - x); linarith)
      have hy'F : y' = F z := hfun z y' (F z) hy' (hFmem z hzI)
      rw [hy'F, hyF] at hlt
      exact hlt
    have hmono := antitone_of_germ hFgermL hFgermR
    intro x₁ x₂ y₁ y₂ ha h12 h2b hy1 hy2
    have hx1 : x₁ ∈ Set.Ioo a b := ⟨ha, by linarith⟩
    have hx2 : x₂ ∈ Set.Ioo a b := ⟨by linarith, h2b⟩
    have e1 : y₁ = F x₁ := hfun x₁ y₁ (F x₁) hy1 (hFmem x₁ hx1)
    have e2 : y₂ = F x₂ := hfun x₂ y₂ (F x₂) hy2 (hFmem x₂ hx2)
    have := hmono x₁ x₂ ha h12 h2b
    linarith

end Work.WilC4

import Mathlib

set_option linter.unusedVariables false

namespace Work.Drive.Mono.intervalZeros

/-- Rolle, in the two-point form we need: if `g` is continuous on `[a,b]` and vanishes at
both endpoints then `deriv g` vanishes somewhere strictly inside.  Phrased here so that the
"continuity on a sub-interval" boilerplate is handled once. -/
theorem exists_deriv_eq_zero_of_cont
    {g : ℝ → ℝ} {a b c d : ℝ} (hgcont : ContinuousOn g (Set.Icc a b))
    (hac : a < c) (hdb : d < b) (hcd : c < d) (heq : g c = g d) :
    ∃ x ∈ Set.Ioo c d, deriv g x = 0 := by
  refine exists_deriv_eq_zero hcd (hgcont.mono ?_) heq
  intro x hx
  exact ⟨le_trans hac.le hx.1, le_trans hx.2 hdb.le⟩

theorem unique_zero_of_deriv_ne_zero
    {g : ℝ → ℝ} {a b ε : ℝ} (hab : a < b) (hε : 0 < ε)
    (hgcont : ContinuousOn g (Set.Icc a b))
    (hg' : ∀ x ∈ Set.Ioo a b, deriv g x ≠ 0)
    (hgε : ∀ x ∈ Set.Ioo a b, |g x| < ε) (hga : |g a| = ε) (hgb : |g b| = ε) :
    ∃! z : ℝ, z ∈ Set.Ioo a b ∧ g z = 0 := by
  -- The two endpoint values are distinct, otherwise Rolle yields an interior critical point.
  have hne : g a ≠ g b := by
    intro heq
    obtain ⟨c, hc, hc0⟩ := exists_deriv_eq_zero hab hgcont heq
    exact hg' c hc hc0
  -- Both endpoint values have absolute value `ε`, and they are distinct, so they have
  -- opposite signs.
  have hga' : g a = ε ∨ g a = -ε := (abs_eq (le_of_lt hε)).mp hga
  have hgb' : g b = ε ∨ g b = -ε := (abs_eq (le_of_lt hε)).mp hgb
  -- Existence: the intermediate value theorem on `[a,b]`.
  have hex : ∃ z ∈ Set.Ioo a b, g z = 0 := by
    rcases hga' with h1 | h1 <;> rcases hgb' with h2 | h2
    · exact absurd (h1.trans h2.symm) hne
    · have h0 : (0 : ℝ) ∈ Set.Ioo (g b) (g a) :=
        ⟨by rw [h2]; linarith, by rw [h1]; linarith⟩
      obtain ⟨z, hz, hz0⟩ := (intermediate_value_Ioo' (le_of_lt hab) hgcont) h0
      exact ⟨z, hz, hz0⟩
    · have h0 : (0 : ℝ) ∈ Set.Ioo (g a) (g b) :=
        ⟨by rw [h1]; linarith, by rw [h2]; linarith⟩
      obtain ⟨z, hz, hz0⟩ := (intermediate_value_Ioo (le_of_lt hab) hgcont) h0
      exact ⟨z, hz, hz0⟩
    · exact absurd (h1.trans h2.symm) hne
  obtain ⟨z0, hz0, hgz0⟩ := hex
  refine ⟨z0, ⟨hz0, hgz0⟩, ?_⟩
  intro y hy
  obtain ⟨hy_mem, hy_root⟩ := hy
  rcases lt_trichotomy y z0 with hlt | heq | hgt
  · exfalso
    obtain ⟨c, hc, hc0⟩ := exists_deriv_eq_zero_of_cont hgcont hy_mem.1 hz0.2 hlt
      (by rw [hy_root, hgz0])
    exact hg' c ⟨lt_trans hy_mem.1 hc.1, lt_trans hc.2 hz0.2⟩ hc0
  · exact heq
  · exfalso
    obtain ⟨c, hc, hc0⟩ := exists_deriv_eq_zero_of_cont hgcont hz0.1 hy_mem.2 hgt
      (by rw [hgz0, hy_root])
    exact hg' c ⟨lt_trans hz0.1 hc.1, lt_trans hc.2 hy_mem.2⟩ hc0

end Work.Drive.Mono.intervalZeros

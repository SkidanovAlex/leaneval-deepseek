import Mathlib

namespace Work.WilVP

/-- On a nonincreasing piece (centre at the right endpoint), the iso-radius is bounded below by
`dist(x, endpoints)/(2L)`. -/
theorem piece_lower_anti {ρ : ℝ → ℝ} {p₁ p₂ L : ℝ} (hp : p₁ < p₂) (hL : 1 ≤ L)
    (hanti : AntitoneOn ρ (Set.Ioo p₁ p₂))
    (hwin : ∀ t : ℝ, 0 < t → t ≤ (p₂ - p₁) / 2 →
      ∃ t' : ℝ, t / L ≤ t' ∧ t' ≤ t ∧ t' / 2 ≤ ρ (p₂ - t')) :
    ∀ x ∈ Set.Ioo p₁ p₂, min (x - p₁) (p₂ - x) / (2 * L) ≤ ρ x := by
  intro x hx
  obtain ⟨hx1, hx2⟩ := hx
  have hxmem : x ∈ Set.Ioo p₁ p₂ := ⟨hx1, hx2⟩
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  set t := p₂ - x with ht
  have htpos : 0 < t := by rw [ht]; linarith
  set t₀ := min t ((p₂ - p₁) / 2) with ht₀
  have ht₀pos : 0 < t₀ := by
    rw [ht₀]; exact lt_min htpos (by linarith)
  have ht₀le : t₀ ≤ (p₂ - p₁) / 2 := by
    rw [ht₀]; exact min_le_right _ _
  obtain ⟨t', ht'₁, ht'₂, ht'₃⟩ := hwin t₀ ht₀pos ht₀le
  have ht'pos : 0 < t' := by
    have h : 0 < t₀ / L := div_pos ht₀pos hLpos
    linarith
  have ht'let : t' ≤ t := by
    rw [ht₀] at ht'₂
    exact le_trans ht'₂ (min_le_left _ _)
  have hmin : min (x - p₁) (p₂ - x) ≤ t₀ := by
    rw [ht₀]
    apply le_min
    · rw [ht]; exact min_le_right _ _
    · have h2 : 2 * min (x - p₁) (p₂ - x) ≤ p₂ - p₁ := by
        have a := min_le_left (x - p₁) (p₂ - x)
        have b := min_le_right (x - p₁) (p₂ - x)
        linarith
      linarith
  have hdiv1 : min (x - p₁) (p₂ - x) / (2 * L) ≤ t₀ / (2 * L) :=
    div_le_div_of_nonneg_right hmin (by positivity)
  have hstep : t₀ / (2 * L) ≤ t' / 2 := by
    have heq : t₀ / (2 * L) = (t₀ / L) / 2 := by rw [div_div, mul_comm]
    rw [heq]
    exact div_le_div_of_nonneg_right ht'₁ (by norm_num)
  have hle : x ≤ p₂ - t' := by
    have hh : t' ≤ p₂ - x := by rw [← ht]; exact ht'let
    linarith
  have hmem : p₂ - t' ∈ Set.Ioo p₁ p₂ := by
    refine ⟨by linarith, by linarith⟩
  calc min (x - p₁) (p₂ - x) / (2 * L) ≤ t₀ / (2 * L) := hdiv1
    _ ≤ t' / 2 := hstep
    _ ≤ ρ (p₂ - t') := ht'₃
    _ ≤ ρ x := hanti hxmem hmem hle

end Work.WilVP

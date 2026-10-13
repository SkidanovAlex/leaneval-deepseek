import Mathlib

namespace Work.WilVP

/-- On a nondecreasing piece, the iso-radius is bounded below by
`dist(x, endpoints)/(2L)`. -/
theorem piece_lower_mono {ρ : ℝ → ℝ} {p₁ p₂ L : ℝ} (hp : p₁ < p₂) (hL : 1 ≤ L)
    (hmono : MonotoneOn ρ (Set.Ioo p₁ p₂))
    (hwin : ∀ t : ℝ, 0 < t → t ≤ (p₂ - p₁) / 2 →
      ∃ t' : ℝ, t / L ≤ t' ∧ t' ≤ t ∧ t' / 2 ≤ ρ (p₁ + t')) :
    ∀ x ∈ Set.Ioo p₁ p₂, min (x - p₁) (p₂ - x) / (2 * L) ≤ ρ x := by
  have _hp : p₁ < p₂ := hp
  intro x hx
  obtain ⟨hx1, hx2⟩ := Set.mem_Ioo.mp hx
  -- Let `t` be the distance from `x` to the nearer endpoint.
  set t := min (x - p₁) (p₂ - x) with ht_def
  have ht_le_x : t ≤ x - p₁ := by rw [ht_def]; exact min_le_left _ _
  have ht_le_e : t ≤ p₂ - x := by rw [ht_def]; exact min_le_right _ _
  have ht_pos : 0 < t := by
    rw [ht_def]; exact lt_min (by linarith) (by linarith)
  have ht_le : t ≤ (p₂ - p₁) / 2 := by linarith
  -- The window hypothesis produces a point `p₁ + t'` with `t' ∈ [t/L, t]`
  -- whose `ρ`-value is at least `t' / 2 ≥ t / (2L)`.
  obtain ⟨t', ht'1, ht'2, ht'3⟩ := hwin t ht_pos ht_le
  have hLpos : 0 < L := by linarith
  have ht'_pos : 0 < t' := by
    have : 0 < t / L := div_pos ht_pos hLpos
    linarith
  -- `p₁ + t'` lies strictly inside the piece and to the left of `x`.
  have hmem : p₁ + t' ∈ Set.Ioo p₁ p₂ := by
    rw [Set.mem_Ioo]; constructor <;> linarith
  -- Monotonicity forces `ρ x ≥ ρ (p₁ + t')`.
  have hρ : ρ (p₁ + t') ≤ ρ x := hmono hmem hx (by linarith)
  have step1 : t / (2 * L) ≤ t' / 2 := by
    have : (t / L) / 2 ≤ t' / 2 := by linarith
    have heq : t / (2 * L) = (t / L) / 2 := by rw [div_div, mul_comm]
    rw [heq]; exact this
  calc min (x - p₁) (p₂ - x) / (2 * L) = t / (2 * L) := by rw [ht_def]
    _ ≤ t' / 2 := step1
    _ ≤ ρ (p₁ + t') := ht'3
    _ ≤ ρ x := hρ

end Work.WilVP

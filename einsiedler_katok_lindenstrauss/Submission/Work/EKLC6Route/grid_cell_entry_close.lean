import Mathlib
import Submission.Work.EKLC6Route.Defs

namespace Work.EKLC6Route

/-- Two reals with the same integer floor differ by strictly less than one. -/
private lemma abs_sub_lt_one_of_floor_eq {x y : ℝ} (h : ⌊x⌋ = ⌊y⌋) : |x - y| < 1 := by
  have h2 : (⌊x⌋ : ℝ) ≤ y := h ▸ Int.floor_le y
  have h1 : x < (⌊x⌋ : ℝ) + 1 := Int.lt_floor_add_one x
  have h3 : (⌊x⌋ : ℝ) ≤ x := Int.floor_le x
  have h4 : y < (⌊x⌋ : ℝ) + 1 := h.symm ▸ Int.lt_floor_add_one y
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

theorem grid_cell_entry_close {ρ : ℝ} (hρ : 0 < ρ) {ℓ : ℕ} {k k' : Work.EKLContract.SL3} (h : Work.EKLC6Route.gridIdx ρ ℓ k = Work.EKLC6Route.gridIdx ρ ℓ k') : ∀ i j, |(k' : Matrix (Fin 3) (Fin 3) ℝ) i j - (k : Matrix (Fin 3) (Fin 3) ℝ) i j| < ρ / 2 ^ ℓ := by
  intro i j
  rw [lt_div_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) ℓ), abs_sub_comm]
  -- Goal: `|k i j - k' i j| * 2 ^ ℓ < ρ`.
  -- Both `(k i j - 1 i j) * 2^ℓ / ρ` and `(k' i j - 1 i j) * 2^ℓ / ρ` have the same floor.
  have h1 : gridIdx ρ ℓ k i j = gridIdx ρ ℓ k' i j := by rw [h]
  simp only [gridIdx] at h1
  have habs : |((k : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j) * 2 ^ ℓ / ρ
      - ((k' : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j) * 2 ^ ℓ / ρ| < 1 :=
    abs_sub_lt_one_of_floor_eq h1
  have hs : ((k : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j) * 2 ^ ℓ / ρ
      - ((k' : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j) * 2 ^ ℓ / ρ
      = ((k : Matrix (Fin 3) (Fin 3) ℝ) i j - (k' : Matrix (Fin 3) (Fin 3) ℝ) i j) * (2 ^ ℓ / ρ) := by
    ring
  have habs2 : |(k : Matrix (Fin 3) (Fin 3) ℝ) i j - (k' : Matrix (Fin 3) (Fin 3) ℝ) i j| * (2 ^ ℓ / ρ) < 1 := by
    have hh := habs
    rw [hs] at hh
    rw [abs_mul, abs_of_pos (div_pos (pow_pos (by norm_num : (0 : ℝ) < 2) ℓ) hρ)] at hh
    exact hh
  have hmul := mul_lt_mul_of_pos_right habs2 hρ
  have key : |(k : Matrix (Fin 3) (Fin 3) ℝ) i j - (k' : Matrix (Fin 3) (Fin 3) ℝ) i j| * (2 ^ ℓ / ρ) * ρ
      = |(k : Matrix (Fin 3) (Fin 3) ℝ) i j - (k' : Matrix (Fin 3) (Fin 3) ℝ) i j| * 2 ^ ℓ := by
    field_simp
  rw [key] at hmul
  linarith

end Work.EKLC6Route

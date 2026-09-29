import Mathlib

namespace Work.Fx

/-- Basic facts about truncated division `Int.tdiv` by a positive integer `L ≥ 1`.

Writing `q = y.tdiv L` and `r = y.tmod L`, we have `y = q * L + r` with
`-L < r < L`.  Everything below is a consequence of that decomposition:
the error `q * L - y = -r` is bounded by `L` in absolute value, and for
nonnegative `y` the remainder is nonnegative, so `q` is the floor of `y / L`. -/
theorem ExpPosTdivKit (y L : ℤ) (hL : 1 ≤ L) :
    (|y.tdiv L * L - y| ≤ L) ∧
    (0 ≤ y → y.tdiv L * L ≤ y) ∧
    (0 ≤ y → ((y.tdiv L : ℤ) : ℝ) ≤ (y : ℝ) / (L : ℝ) ∧
              (y : ℝ) / (L : ℝ) - ((y.tdiv L : ℤ) : ℝ) ≤ 1) ∧
    (0 ≤ y → (1 ≤ y.tdiv L ↔ L ≤ y)) ∧
    (|((y.tdiv L : ℤ) : ℝ) - (y : ℝ) / (L : ℝ)| ≤ 1) := by
  have hLpos : (0 : ℤ) < L := lt_of_lt_of_le Int.zero_lt_one hL
  have hLposR : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hLpos
  have hdecomp : y.tdiv L * L + y.tmod L = y := Int.tdiv_mul_add_tmod y L
  have hlo : -L < y.tmod L := Int.lt_tmod_of_pos y hLpos
  have hhi : y.tmod L < L := Int.tmod_lt_of_pos y hLpos
  have h1 : |y.tdiv L * L - y| ≤ L := by
    rw [abs_le]
    constructor <;> omega
  have h2 : 0 ≤ y → y.tdiv L * L ≤ y := by
    intro hy
    have h := Int.tmod_nonneg L hy
    omega
  have h3 : 0 ≤ y → ((y.tdiv L : ℤ) : ℝ) ≤ (y : ℝ) / (L : ℝ) ∧
              (y : ℝ) / (L : ℝ) - ((y.tdiv L : ℤ) : ℝ) ≤ 1 := by
    intro hy
    have h2' := h2 hy
    constructor
    · have hc : ((y.tdiv L * L : ℤ) : ℝ) ≤ (y : ℝ) := by exact_mod_cast h2'
      push_cast at hc
      rw [le_div_iff₀ hLposR]
      linarith
    · have hz : (y - y.tdiv L * L : ℤ) ≤ L := by omega
      have hyl : (y : ℝ) - ((y.tdiv L : ℤ) : ℝ) * (L : ℝ) ≤ (L : ℝ) := by exact_mod_cast hz
      have heq : ((y : ℝ) - ((y.tdiv L : ℤ) : ℝ) * (L : ℝ)) / (L : ℝ)
          = (y : ℝ) / (L : ℝ) - ((y.tdiv L : ℤ) : ℝ) := by
        rw [sub_div, mul_div_cancel_right₀ _ (ne_of_gt hLposR)]
      rw [← heq, div_le_one hLposR]
      exact hyl
  have h4 : 0 ≤ y → (1 ≤ y.tdiv L ↔ L ≤ y) := by
    intro hy
    constructor
    · intro hq
      have h2' := h2 hy
      have hmul : L ≤ y.tdiv L * L := by
        calc L = 1 * L := by ring
          _ ≤ y.tdiv L * L := by
              exact Int.mul_le_mul_of_nonneg_right hq (le_of_lt hLpos)
      omega
    · intro hLy
      have hmodnn := Int.tmod_nonneg L hy
      have hqL : 0 < y.tdiv L * L := by omega
      have hqpos : 0 < y.tdiv L := by
        rcases Int.mul_pos_iff.mp hqL with h | h
        · exact h.1
        · exact absurd h.2 (not_lt.mpr (le_of_lt hLpos))
      omega
  have h5 : |((y.tdiv L : ℤ) : ℝ) - (y : ℝ) / (L : ℝ)| ≤ 1 := by
    have hcast : |((y.tdiv L : ℤ) : ℝ) * (L : ℝ) - (y : ℝ)| ≤ (L : ℝ) := by
      have hc : |((y.tdiv L * L - y : ℤ) : ℝ)| ≤ (L : ℝ) := by exact_mod_cast h1
      simpa only [Int.cast_sub, Int.cast_mul] using hc
    have hqd : ((y.tdiv L : ℤ) : ℝ) - (y : ℝ) / (L : ℝ)
        = (((y.tdiv L : ℤ) : ℝ) * (L : ℝ) - (y : ℝ)) / (L : ℝ) := by
      rw [sub_div, mul_div_cancel_right₀ _ (ne_of_gt hLposR)]
    rw [hqd, abs_div, abs_of_pos hLposR, div_le_one hLposR]
    exact hcast
  exact ⟨h1, h2, h3, h4, h5⟩

end Work.Fx

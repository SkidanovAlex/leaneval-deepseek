import Mathlib
import Submission.Work.ThomBordism.TwoSet.Cells

/-!
# The clamp of a nearby point lands in the minimal cell of that point

`clampCell_mem_cOf`: if every coordinate of `x : I^j` is within `1/(4N)` of the corresponding
coordinate interval of the grid cell `c`, then the coordinatewise clamp of `x` onto `c` lies in the
cell `cOf N x` spanned by the floors and ceilings of the numbers `N * xᵢ`.

The point is that the clamp never moves a coordinate past the nearest grid lines: the floor of
`N * xᵢ` is at most `hiᵢ` (because `N * xᵢ < hiᵢ + 1/4`), and the ceiling of `N * xᵢ` is at least
`loᵢ` (because `loᵢ - 1/4 < N * xᵢ`), while the clamped value is always one of `loᵢ/N`, `hiᵢ/N`
and `xᵢ`.
-/

open scoped Topology unitInterval

namespace Work.ThomBordism.TwoSet

theorem clampCell_mem_cOf {j N : ℕ} (hN : 1 ≤ N) (c : CellIdx j N) {x : IC j}
    (hx : ∀ i : Fin j, (c.lo i : ℝ) - 1/4 < (N:ℝ) * (x i : ℝ) ∧
        (N:ℝ) * (x i : ℝ) < (c.hi i : ℝ) + 1/4) :
    clampCell c hN x ∈ cellSet (cOf N x) := by
  intro i
  have hxlo := (hx i).1
  have hxhi := (hx i).2
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have hz : (0:ℝ) ≤ (N:ℝ) * (x i : ℝ) := mul_nonneg (le_of_lt hNpos) (x i).2.1
  have hle : (c.lo i : ℝ) ≤ (c.hi i : ℝ) := by exact_mod_cast c.hle i
  have hdiv : (c.lo i : ℝ)/N ≤ (c.hi i : ℝ)/N :=
    div_le_div_of_nonneg_right hle (le_of_lt hNpos)
  have hfloor_le : ((⌊(N:ℝ)*(x i : ℝ)⌋₊ : ℕ):ℝ) ≤ (N:ℝ) * (x i:ℝ) := Nat.floor_le hz
  rw [clampCell_val, cOf_lo, cOf_hi]
  constructor
  · rw [clampR]
    rcases le_or_gt ((x i : ℝ)) ((c.hi i : ℝ)/N) with h | h
    · rw [min_eq_right h]
      have h2 : (((⌊(N:ℝ)*(x i:ℝ)⌋₊ : ℕ) : ℝ))/N ≤ (x i:ℝ) := by
        rw [div_le_iff₀ hNpos]; linarith [hfloor_le]
      exact le_trans h2 (le_max_right _ _)
    · rw [min_eq_left (le_of_lt h), max_eq_right hdiv]
      have hfl : ⌊(N:ℝ)*(x i:ℝ)⌋₊ ≤ c.hi i := by
        have : ⌊(N:ℝ)*(x i:ℝ)⌋₊ < c.hi i + 1 := by
          rw [Nat.floor_lt hz]; push_cast; linarith [hxhi]
        omega
      exact div_le_div_of_nonneg_right (by exact_mod_cast hfl) (le_of_lt hNpos)
  · rw [clampR]
    rcases le_or_gt ((x i : ℝ)) ((c.hi i : ℝ)/N) with h | h
    · rw [min_eq_right h]
      apply max_le
      · have hceil : c.lo i ≤ ⌈(N:ℝ)*(x i:ℝ)⌉₊ := by
          rcases Nat.eq_zero_or_pos (c.lo i) with h0 | hpos
          · omega
          · have hc : c.lo i - 1 < ⌈(N:ℝ)*(x i:ℝ)⌉₊ := by
              rw [Nat.lt_ceil]
              have hcast : (((c.lo i - 1 : ℕ) : ℝ)) = (c.lo i : ℝ) - 1 := by
                rw [Nat.cast_sub (show 1 ≤ c.lo i by omega)]; norm_num
              rw [hcast]; linarith [hxlo]
            omega
        exact div_le_div_of_nonneg_right (by exact_mod_cast hceil) (le_of_lt hNpos)
      · rw [le_div_iff₀ hNpos]
        have := Nat.le_ceil ((N:ℝ)*(x i:ℝ))
        linarith
    · rw [min_eq_left (le_of_lt h), max_eq_right hdiv]
      have hceil : c.hi i ≤ ⌈(N:ℝ)*(x i:ℝ)⌉₊ := by
        have hlt : (c.hi i : ℝ) < (N:ℝ)*(x i:ℝ) := by
          have hh := (div_lt_iff₀ hNpos).mp h; linarith
        have h2 : (c.hi i : ℝ) < ((⌈(N:ℝ)*(x i:ℝ)⌉₊:ℕ):ℝ) :=
          lt_of_lt_of_le hlt (Nat.le_ceil _)
        have h3 : c.hi i < ⌈(N:ℝ)*(x i:ℝ)⌉₊ := by exact_mod_cast h2
        omega
      exact div_le_div_of_nonneg_right (by exact_mod_cast hceil) (le_of_lt hNpos)

end Work.ThomBordism.TwoSet

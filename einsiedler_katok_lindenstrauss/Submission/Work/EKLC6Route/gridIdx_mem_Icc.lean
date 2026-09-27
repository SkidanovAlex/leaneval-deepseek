import Mathlib
import Submission.Work.EKLC6Route.Defs

namespace Work.EKLC6Route

/-- **The grid index of an element of `V ρ` is bounded by `2 ^ L`.**

For `k ∈ V ρ` (i.e. `|k i j - 1 i j| < ρ` for all entries) the level-`L` grid index
`gridIdx ρ L k i j = ⌊(k i j - 1 i j) * 2 ^ L / ρ⌋` is the floor of a real number of absolute
value `< 2 ^ L`, hence lies in the integer interval `[-2 ^ L, 2 ^ L]`.

This is what makes the grid cells `gridCell ρ L d` cover `V ρ` by a *finite* set of indices. -/
theorem gridIdx_mem_Icc (ρ : ℝ) (hρ : 0 < ρ) (L : ℕ) {k : Work.EKLContract.SL3}
    (hk : k ∈ Work.EKLContract.V ρ) (i j : Fin 3) :
    Work.EKLC6Route.gridIdx ρ L k i j ∈ Finset.Icc (-(2 ^ L : ℤ)) (2 ^ L : ℤ) := by
  rw [Finset.mem_Icc]
  have hL : (0 : ℝ) < 2 ^ L := by positivity
  -- `k ∈ V ρ` says every entry of `k - 1` has absolute value `< ρ`.
  have hd : |(k : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < ρ :=
    hk i j
  -- hence the rescaled entry `(k - 1)_{ij} * 2 ^ L / ρ` has absolute value `< 2 ^ L`.
  have hxabs : |((k : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j)
      * 2 ^ L / ρ| < (2 : ℝ) ^ L := by
    rw [abs_div, abs_mul, abs_of_pos hL, abs_of_pos hρ]
    rw [div_lt_iff₀ hρ]
    nlinarith [hL]
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hxabs
  simp only [Work.EKLC6Route.gridIdx]
  constructor
  · -- lower bound: `-2 ^ L ≤ ⌊x⌋` because `-2 ^ L < x`
    rw [Int.le_floor]
    push_cast
    linarith
  · -- upper bound: `⌊x⌋ < 2 ^ L ≤ ...` because `x < 2 ^ L`
    refine le_of_lt ?_
    rw [Int.floor_lt]
    push_cast
    exact hhi

end Work.EKLC6Route

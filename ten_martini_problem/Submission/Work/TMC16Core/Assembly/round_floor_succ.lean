import Mathlib

namespace Work.TMC16Core.Assembly

/-- Integer arithmetic helper: an integer in the closed interval `[a, a+1]`
is either `a` or `a+1`. -/
private theorem int_eq_or_eq_add_one {a b : ℤ} (h1 : a ≤ b) (h2 : b ≤ a + 1) :
    b = a ∨ b = a + 1 := by
  omega

/-- `⌊x⌋ ≤ ⌈x⌉` for real `x`. -/
private theorem floor_le_ceil_real (x : ℝ) : ⌊x⌋ ≤ ⌈x⌉ :=
  Int.cast_le.mp (le_trans (Int.floor_le x) (Int.le_ceil x))

/-- `⌈x⌉ ≤ ⌊x⌋ + 1` for real `x`. -/
private theorem ceil_le_floor_add_one_real (x : ℝ) : ⌈x⌉ ≤ ⌊x⌋ + 1 := by
  rw [Int.ceil_le]
  push_cast
  linarith [Int.lt_floor_add_one x]

theorem round_floor_succ (x : ℝ) : round x = ⌊x⌋ ∨ round x = ⌊x⌋ + 1 := by
  rw [round]
  split_ifs with h
  · exact Or.inl rfl
  · exact int_eq_or_eq_add_one (floor_le_ceil_real x) (ceil_le_floor_add_one_real x)

end Work.TMC16Core.Assembly

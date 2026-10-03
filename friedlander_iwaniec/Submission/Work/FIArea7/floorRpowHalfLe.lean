import Mathlib

namespace Work.FIArea7

/-- For `M ≥ 1` and `η ≥ 0` the number `M ^ η` is at least `1`, and any real number
`x ≥ 1` satisfies `x / 2 ≤ ⌊x⌋₊` (when `x < 2` both sides are controlled by `1`,
and when `x ≥ 2` the floor is at least `x - 1 ≥ x / 2`). -/
theorem floorRpowHalfLe {M η : ℝ} (hM : 1 ≤ M) (hη : 0 ≤ η) :
    M ^ η / 2 ≤ ((⌊M ^ η⌋₊ : ℕ) : ℝ) := by
  have h1 : (1:ℝ) ≤ M ^ η := Real.one_le_rpow hM hη
  set x : ℝ := M ^ η with hx
  have hx1 : ((1:ℕ):ℝ) ≤ x := by exact_mod_cast h1
  have hn1 : 1 ≤ ⌊x⌋₊ := Nat.le_floor hx1
  have hlt : x < ((⌊x⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one x
  have hn1' : (1:ℝ) ≤ ((⌊x⌋₊ : ℕ) : ℝ) := by exact_mod_cast hn1
  have hxle : x ≤ 2 * ((⌊x⌋₊ : ℕ) : ℝ) := by linarith
  have hfin : x / 2 ≤ ((⌊x⌋₊ : ℕ) : ℝ) := by linarith
  simpa [hx] using hfin

end Work.FIArea7

import Mathlib
import Submission.Work.BMF.SD.sd3_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.SD

/--
Rounding to the nearest grid point: if `x` lies in the interval `[s, s + J*g]` with `g > 0`,
then some grid point `s + j*g` with `0 ≤ j ≤ J` is within `g/2` of `x`.
-/
theorem grid_near (x s g : ℝ) (J : ℕ) (hg : 0 < g)
    (h1 : s ≤ x) (h2 : x ≤ s + (J : ℝ) * g) :
    ∃ j : ℕ, j ≤ J ∧ |x - (s + (j : ℝ) * g)| ≤ g / 2 := by
  have hgne : g ≠ 0 := ne_of_gt hg
  -- Normalised position of `x` on the grid, measured in units of `g`.
  set z : ℝ := (x - s) / g with hz
  have hz0 : 0 ≤ z := by
    rw [hz]; exact div_nonneg (by linarith) (le_of_lt hg)
  have hzJ : z ≤ (J : ℝ) := by
    rw [hz, div_le_iff₀ hg]; nlinarith [h2]
  -- The nearest grid index to `z`, which lies in `[0, J]`.
  refine ⟨Nat.floor (z + 1 / 2), ?_, ?_⟩
  · -- The index is at most `J`.
    have h1' : ((Nat.floor (z + 1 / 2) : ℕ) : ℝ) ≤ z + 1 / 2 :=
      Nat.floor_le (by linarith)
    have : ((Nat.floor (z + 1 / 2) : ℕ) : ℝ) < (J : ℝ) + 1 := by linarith
    have hlt : Nat.floor (z + 1 / 2) < J + 1 := by exact_mod_cast this
    omega
  · -- The grid point is within `g/2` of `x`.
    have h1' : ((Nat.floor (z + 1 / 2) : ℕ) : ℝ) ≤ z + 1 / 2 :=
      Nat.floor_le (by linarith)
    have h2' : z + 1 / 2 < ((Nat.floor (z + 1 / 2) : ℕ) : ℝ) + 1 :=
      Nat.lt_floor_add_one (z + 1 / 2)
    have hzj : |z - ((Nat.floor (z + 1 / 2) : ℕ) : ℝ)| ≤ 1 / 2 := by
      rw [abs_le]; constructor <;> linarith
    have hxg : x - s = z * g := by
      rw [hz]; exact (div_mul_cancel₀ (x - s) hgne).symm
    have hmain : x - (s + ((Nat.floor (z + 1 / 2) : ℕ) : ℝ) * g)
        = g * (z - ((Nat.floor (z + 1 / 2) : ℕ) : ℝ)) := by
      rw [show x - (s + ((Nat.floor (z + 1 / 2) : ℕ) : ℝ) * g)
            = (x - s) - ((Nat.floor (z + 1 / 2) : ℕ) : ℝ) * g by ring, hxg]
      ring
    rw [hmain, abs_mul, abs_of_pos hg]
    nlinarith [hzj, hg]

end Work.BMF.SD

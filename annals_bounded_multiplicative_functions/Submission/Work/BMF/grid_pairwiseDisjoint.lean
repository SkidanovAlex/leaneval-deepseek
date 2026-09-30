import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-- The half-open intervals `[i h, (i+1) h)` for `i : Fin N` are pairwise disjoint,
since for `i < j` one has `(i+1) h ≤ j h` (as `i + 1 ≤ j` and `h > 0`). -/
theorem grid_pairwiseDisjoint (h : ℝ) (hh : 0 < h) (N : ℕ) : Pairwise (fun i j : Fin N => Disjoint (Set.Ico ((i : ℝ) * h) (((i : ℝ) + 1) * h)) (Set.Ico ((j : ℝ) * h) (((j : ℝ) + 1) * h))) := by
  intro i j hij
  rw [Set.disjoint_left]
  intro x hx hxt
  rw [Set.mem_Ico] at hx hxt
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hxt1, hxt2⟩ := hxt
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have hval : ((i : ℕ) + 1 : ℕ) ≤ (j : ℕ) := Nat.succ_le_of_lt (Fin.lt_def.mp hlt)
    have hv : ((i : ℝ) + 1) ≤ (j : ℝ) := by exact_mod_cast hval
    have := mul_le_mul_of_nonneg_right hv hh.le
    linarith
  · have hval : ((j : ℕ) + 1 : ℕ) ≤ (i : ℕ) := Nat.succ_le_of_lt (Fin.lt_def.mp hgt)
    have hv : ((j : ℝ) + 1) ≤ (i : ℝ) := by exact_mod_cast hval
    have := mul_le_mul_of_nonneg_right hv hh.le
    linarith

end Work.BMF

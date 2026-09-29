import Mathlib

open Set

namespace Work.TMPuig

/-- For an irrational real number `α`, the set `{l * α + j | l j : ℤ}` is dense in `ℝ`:
in particular every nonempty open interval contains such an integer combination. -/
theorem irrational_int_pair_dense {α : ℝ} (hα : Irrational α) {x y : ℝ} (hxy : x < y) :
    ∃ l j : ℤ, x < (l : ℝ) * α + (j : ℝ) ∧ (l : ℝ) * α + (j : ℝ) < y := by
  have hdense : Dense (AddSubgroup.closure ({α, 1} : Set ℝ) : Set ℝ) := by
    rw [dense_addSubgroupClosure_pair_iff]
    simpa using hα
  obtain ⟨z, hzmem, hzIoo⟩ := hdense.exists_mem_open isOpen_Ioo (nonempty_Ioo.2 hxy)
  rw [mem_Ioo] at hzIoo
  change z ∈ AddSubgroup.closure ({α, 1} : Set ℝ) at hzmem
  rw [AddSubgroup.mem_closure_pair] at hzmem
  obtain ⟨m, n, hmn⟩ := hzmem
  have hz' : z = (m : ℝ) * α + (n : ℝ) := by
    rw [← hmn, zsmul_eq_mul, zsmul_eq_mul, mul_one]
  exact ⟨m, n, by rw [← hz']; exact hzIoo.1, by rw [← hz']; exact hzIoo.2⟩

end Work.TMPuig

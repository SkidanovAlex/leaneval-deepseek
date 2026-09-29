import Mathlib

namespace Work.TMComp.Perfect

/-- The subgroup `ℤ α + ℤ` of `ℝ` is dense when `α` is irrational. -/
theorem dense_zsmul_add_one (α : ℝ) (hα : Irrational α) :
    Dense (AddSubgroup.closure ({α, (1 : ℝ)} : Set ℝ) : Set ℝ) :=
  dense_addSubgroupClosure_pair_iff.mpr (by simpa using hα)

/-- For an irrational `α`, the set `{m * α + k | m k : ℤ}` is `ε`-dense in `ℝ`. -/
theorem exists_int_approx (α : ℝ) (hα : Irrational α) (y : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ m k : ℤ, |(m : ℝ) * α + (k : ℝ) - y| < ε := by
  have hdense := dense_zsmul_add_one α hα
  have hy : y ∈ closure ((AddSubgroup.closure ({α, (1 : ℝ)} : Set ℝ) : Set ℝ)) := by
    rw [hdense.closure_eq]; exact Set.mem_univ y
  rw [Metric.mem_closure_iff] at hy
  obtain ⟨x, hx, hxy⟩ := hy ε hε
  obtain ⟨m, k, hmk⟩ :=
    AddSubgroup.mem_closure_pair.mp (show x ∈ AddSubgroup.closure ({α, (1 : ℝ)} : Set ℝ) from hx)
  refine ⟨m, k, ?_⟩
  have hx' : (m : ℝ) * α + (k : ℝ) = x := by
    rw [← hmk]; simp [zsmul_eq_mul]
  rw [← hx'] at hxy
  simpa [Real.dist_eq, abs_sub_comm] using hxy

end Work.TMComp.Perfect

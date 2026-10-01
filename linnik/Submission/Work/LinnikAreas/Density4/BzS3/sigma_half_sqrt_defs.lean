import Mathlib
import Submission.Work.Commons.Analysis.Series.sum_Icc_sqrt_div_self_le

namespace Work.LinnikAreas.Density4.BzS3

open Finset

/-- The `σ_{-1/2}`-weight `a r = r^{-1/2} · Σ_{d ∣ r} d^{-1/2}`. -/
noncomputable def aTerm (r : ℕ) : ℝ :=
  (1 / Real.sqrt (r : ℝ)) * ∑ d ∈ r.divisors, 1 / Real.sqrt (d : ℝ)

/-- Elementary square-root sum bound: `Σ_{m ≤ N} 1/√m ≤ 2√N`,
deduced from the telescoping estimate `Σ_{m ≤ N} √m/m ≤ 2√N`. -/
lemma sum_Icc_inv_sqrt_le (N : ℕ) :
    ∑ m ∈ Finset.Icc 1 N, (1 : ℝ) / Real.sqrt (m : ℝ) ≤ 2 * Real.sqrt (N : ℝ) := by
  have h := Work.Commons.Analysis.Series.sum_Icc_sqrt_div_self_le N
  refine le_trans (le_of_eq ?_) h
  apply Finset.sum_congr rfl
  intro m hm
  obtain ⟨hm1, _⟩ := Finset.mem_Icc.mp hm
  have hmpos : (0:ℝ) < (m:ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hs : Real.sqrt (m:ℝ) * Real.sqrt (m:ℝ) = (m:ℝ) := by
    rw [← pow_two]; exact Real.sq_sqrt hmpos.le
  rw [div_eq_div_iff (Real.sqrt_pos_of_pos hmpos).ne' hmpos.ne', one_mul, hs]

end Work.LinnikAreas.Density4.BzS3

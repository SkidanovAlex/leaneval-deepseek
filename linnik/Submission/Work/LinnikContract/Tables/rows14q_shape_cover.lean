import Mathlib
import Submission.Work.LinnikContract.Pre

namespace Work.LinnikContract.Tables

/-- Shape and coverage of the §14 rows: every row is a genuine interval inside `[0, 0.348]` with a
strictly positive `min(λ₀,λ₂)` bound, and the rows cover the whole range `(0, 0.348]` of `λ₁`.
(`rows14q = [(3/10,348/1000,127/100), (25/100,3/10,141/100), (2/10,25/100,158/100), (0,2/10,18/10)]`,
so the last row starts at `0`.)

Prover notes: first conjunct by
`simp only [rows14q, List.mem_cons, List.not_mem_nil] at hr; rcases hr with rfl | … | rfl <;> norm_num`;
coverage by a case split at `1/5, 1/4, 3/10`.  Do NOT use `native_decide` (it adds the axiom
`Lean.ofReduceBool`); plain `decide` does not reduce `Rat` literal comparisons. -/
theorem rows14q_shape_cover :
    (∀ r ∈ Work.LinnikContract.rows14q, r.1 < r.2.1 ∧ r.2.1 ≤ (348:ℚ)/1000 ∧ 0 < r.2.2) ∧
    (∀ x : ℚ, 0 < x → x ≤ (348:ℚ)/1000 →
      ∃ r ∈ Work.LinnikContract.rows14q, r.1 ≤ x ∧ x ≤ r.2.1) := by
  constructor
  · intro r hr
    simp only [Work.LinnikContract.rows14q, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> norm_num
  · intro x hxpos hxle
    rcases le_or_gt x (1/5) with h1 | h1
    · exact ⟨(0, 2/10, 18/10), by simp [Work.LinnikContract.rows14q], by linarith, by linarith⟩
    rcases le_or_gt x (1/4) with h2 | h2
    · exact ⟨(2/10, 25/100, 158/100), by simp [Work.LinnikContract.rows14q],
        by linarith, by linarith⟩
    rcases le_or_gt x (3/10) with h3 | h3
    · exact ⟨(25/100, 3/10, 141/100), by simp [Work.LinnikContract.rows14q],
        by linarith, by linarith⟩
    · exact ⟨(3/10, 348/1000, 127/100), by simp [Work.LinnikContract.rows14q],
        by linarith, hxle⟩

end Work.LinnikContract.Tables

import Mathlib
import Submission.Work.LinnikContract.Pre

namespace Work.LinnikContract.Tables

/-- Shape and coverage of the §15 rows: every row is a genuine interval `lo < hi` inside
`[0.348, 0.6]` with strictly positive `λ₀, λ₂, λ₃` bounds, and the rows cover the whole range
`[0.348, 0.6]` of `λ₁` (so the numerics of §4.1 have no gap).

Prover notes: the rows are consecutive closed intervals tiling `[0.348, 0.6]`, so the second
conjunct is a case split on `x` (`le_or_gt` against `36/100, 38/100, 4/10, …`, each case closed by
`exact ⟨…, by norm_num, by norm_num⟩` and `norm_num`); the first conjunct is
`simp only [rows15q, List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | … | rfl <;> norm_num`.
Do NOT use `native_decide` (it adds the axiom `Lean.ofReduceBool`); plain `decide` does not reduce
`Rat` literal comparisons. -/
theorem rows15q_shape_cover :
    (∀ r ∈ Work.LinnikContract.rows15q, r.1 < r.2.1 ∧ (348:ℚ)/1000 ≤ r.1 ∧ r.2.1 ≤ (6:ℚ)/10 ∧
        0 < r.2.2.1 ∧ 0 < r.2.2.2.1 ∧ 0 < r.2.2.2.2) ∧
    (∀ x : ℚ, (348:ℚ)/1000 ≤ x → x ≤ (6:ℚ)/10 →
      ∃ r ∈ Work.LinnikContract.rows15q, r.1 ≤ x ∧ x ≤ r.2.1) := by
  constructor
  · intro r hr
    simp only [Work.LinnikContract.rows15q, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num
  · intro x hlo hhi
    rcases le_or_gt x ((36:ℚ)/100) with h1 | h1
    · exact ⟨((348:ℚ)/1000, (36:ℚ)/100, (1308:ℚ)/1000, (902:ℚ)/1000, (1229:ℚ)/1000),
        by simp [Work.LinnikContract.rows15q], hlo, h1⟩
    · rcases le_or_gt x ((38:ℚ)/100) with h2 | h2
      · exact ⟨((36:ℚ)/100, (38:ℚ)/100, (1249:ℚ)/1000, (886:ℚ)/1000, (1180:ℚ)/1000),
          by simp [Work.LinnikContract.rows15q], le_of_lt h1, h2⟩
      · rcases le_or_gt x ((4:ℚ)/10) with h3 | h3
        · exact ⟨((38:ℚ)/100, (4:ℚ)/10, (1195:ℚ)/1000, (870:ℚ)/1000, (1134:ℚ)/1000),
            by simp [Work.LinnikContract.rows15q], le_of_lt h2, h3⟩
        · rcases le_or_gt x ((42:ℚ)/100) with h4 | h4
          · exact ⟨((4:ℚ)/10, (42:ℚ)/100, (1144:ℚ)/1000, (855:ℚ)/1000, (1093:ℚ)/1000),
              by simp [Work.LinnikContract.rows15q], le_of_lt h3, h4⟩
          · rcases le_or_gt x ((44:ℚ)/100) with h5 | h5
            · exact ⟨((42:ℚ)/100, (44:ℚ)/100, (1098:ℚ)/1000, (841:ℚ)/1000, (1054:ℚ)/1000),
                by simp [Work.LinnikContract.rows15q], le_of_lt h4, h5⟩
            · rcases le_or_gt x ((46:ℚ)/100) with h6 | h6
              · exact ⟨((44:ℚ)/100, (46:ℚ)/100, (1054:ℚ)/1000, (828:ℚ)/1000, (1017:ℚ)/1000),
                  by simp [Work.LinnikContract.rows15q], le_of_lt h5, h6⟩
              · rcases le_or_gt x ((48:ℚ)/100) with h7 | h7
                · exact ⟨((46:ℚ)/100, (48:ℚ)/100, (1014:ℚ)/1000, (815:ℚ)/1000, (983:ℚ)/1000),
                    by simp [Work.LinnikContract.rows15q], le_of_lt h6, h7⟩
                · rcases le_or_gt x ((5:ℚ)/10) with h8 | h8
                  · exact ⟨((48:ℚ)/100, (5:ℚ)/10, (976:ℚ)/1000, (802:ℚ)/1000, (951:ℚ)/1000),
                      by simp [Work.LinnikContract.rows15q], le_of_lt h7, h8⟩
                  · rcases le_or_gt x ((52:ℚ)/100) with h9 | h9
                    · exact ⟨((5:ℚ)/10, (52:ℚ)/100, (940:ℚ)/1000, (790:ℚ)/1000, (921:ℚ)/1000),
                        by simp [Work.LinnikContract.rows15q], le_of_lt h8, h9⟩
                    · rcases le_or_gt x ((54:ℚ)/100) with h10 | h10
                      · exact ⟨((52:ℚ)/100, (54:ℚ)/100, (906:ℚ)/1000, (779:ℚ)/1000, (892:ℚ)/1000),
                          by simp [Work.LinnikContract.rows15q], le_of_lt h9, h10⟩
                      · rcases le_or_gt x ((56:ℚ)/100) with h11 | h11
                        · exact ⟨((54:ℚ)/100, (56:ℚ)/100, (874:ℚ)/1000, (768:ℚ)/1000, (865:ℚ)/1000),
                            by simp [Work.LinnikContract.rows15q], le_of_lt h10, h11⟩
                        · rcases le_or_gt x ((58:ℚ)/100) with h12 | h12
                          · exact ⟨((56:ℚ)/100, (58:ℚ)/100, (844:ℚ)/1000, (758:ℚ)/1000, (856:ℚ)/1000),
                              by simp [Work.LinnikContract.rows15q], le_of_lt h11, h12⟩
                          · exact ⟨((58:ℚ)/100, (6:ℚ)/10, (815:ℚ)/1000, (748:ℚ)/1000, (856:ℚ)/1000),
                              by simp [Work.LinnikContract.rows15q], le_of_lt h12, hhi⟩

end Work.LinnikContract.Tables

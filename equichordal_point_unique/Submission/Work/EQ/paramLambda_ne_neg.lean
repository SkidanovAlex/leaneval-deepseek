import Mathlib
import Submission.Work.EQ.bp_aux

namespace Work.EQ

/-- The two backward-branch points `paramΛ a Q λ` and `paramΛ a Q (-λ)` differ whenever `λ ≠ 0`
and `Q ≠ O₁`.  Indeed
`paramΛ a Q λ - paramΛ a Q (-λ) = (2/λ) • (Q - O₁)`,
so the difference vanishes exactly when `Q = O₁` (here `λ ≠ 0`). -/
theorem paramLambda_ne_neg {a : ℝ} {Q : ℂ × ℂ} {lam : ℂ} (hlam : lam ≠ 0)
    (hQ : Q ≠ Work.EQ.O1 a) :
    Work.EQ.paramΛ a Q lam ≠ Work.EQ.paramΛ a Q (-lam) := by
  intro h
  have hfst := congrArg Prod.fst h
  have hsnd := congrArg Prod.snd h
  have hdiff1 : (paramΛ a Q lam).1 - (paramΛ a Q (-lam)).1
      = 2 * (Q.1 + ((a / 2 : ℝ) : ℂ)) / lam := by
    simp only [paramΛ]; field_simp; ring
  have hdiff2 : (paramΛ a Q lam).2 - (paramΛ a Q (-lam)).2 = 2 * Q.2 / lam := by
    simp only [paramΛ]; field_simp; ring
  have hQ1 : Q.1 + ((a / 2 : ℝ) : ℂ) = 0 := by
    have hz : 2 * (Q.1 + ((a / 2 : ℝ) : ℂ)) / lam = 0 := by
      rw [← hdiff1, hfst, sub_self]
    field_simp at hz
    simp only [mul_zero] at hz
    exact (mul_eq_zero.mp hz).resolve_left two_ne_zero
  have hQ2 : Q.2 = 0 := by
    have hz : 2 * Q.2 / lam = 0 := by rw [← hdiff2, hsnd, sub_self]
    field_simp at hz
    simp only [mul_zero] at hz
    exact (mul_eq_zero.mp hz).resolve_left two_ne_zero
  refine hQ ?_
  ext
  · show Q.1 = (O1 a).1
    rw [O1]
    exact eq_neg_of_add_eq_zero_left hQ1
  · show Q.2 = (O1 a).2
    rw [O1]
    exact hQ2

end Work.EQ

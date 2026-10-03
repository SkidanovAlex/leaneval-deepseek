import Mathlib
import Submission.Work.A3.Weil.Defs

/-!
# Dirichlet's approximation theorem, normalised form (Area A3, `Weil`)

For every real `Λ` and every `Q ≥ 1` there are `a : ℤ`, `q : ℕ` with `1 ≤ q ≤ Q`, `a` coprime to
`q`, and

`|Λ - a/q| ≤ 1 / (q · Q)`.

This is Dirichlet's approximation theorem.  Mathlib's `Real.exists_rat_abs_sub_le_and_den_le`
(Dirichlet with the sharp denominator `n + 1` in the numerator) applied with `n = Q` produces a
rational `r` with `r.den ≤ Q` and `|Λ - r| ≤ 1/((Q+1) · r.den)`.  Since `Q ≥ 1` the factor
`Q + 1` can be relaxed to `Q`, and `r.num`/`r.den` are coprime by construction.
-/

set_option autoImplicit false

namespace Work.A3.Weil

theorem dirichletApprox (Λ : ℝ) (Q : ℕ) (hQ : 1 ≤ Q) :
    ∃ (a : ℤ) (q : ℕ), 1 ≤ q ∧ q ≤ Q ∧ IsCoprime a q ∧
      |Λ - (a : ℝ) / (q : ℝ)| ≤ 1 / ((q : ℝ) * (Q : ℝ)) := by
  obtain ⟨r, happrox, hden⟩ := Real.exists_rat_abs_sub_le_and_den_le Λ (by omega : 0 < Q)
  refine ⟨r.num, r.den, r.pos, hden, ?_, ?_⟩
  · rw [Int.isCoprime_iff_nat_coprime]
    simpa using r.reduced
  · have h1 : |Λ - (r.num : ℝ) / (r.den : ℝ)| ≤ 1 / (((Q : ℝ) + 1) * (r.den : ℝ)) := by
      simpa [Rat.cast_def] using happrox
    have h2 : 1 / (((Q : ℝ) + 1) * (r.den : ℝ)) ≤ 1 / ((r.den : ℝ) * (Q : ℝ)) := by
      have hd : (0 : ℝ) < (r.den : ℝ) := by exact_mod_cast r.pos
      have hQ' : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
      apply one_div_le_one_div_of_le
      · positivity
      · nlinarith
    exact h1.trans h2

end Work.A3.Weil

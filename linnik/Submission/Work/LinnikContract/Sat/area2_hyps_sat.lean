import Mathlib
import Submission.Work.LinnikContract.Pre

namespace Work.LinnikContract.Sat

/-- Non-degeneracy of the hypothesis list of AREA 2 (`Reduction`): the threshold `(3/10)^2 - ε` is
strictly positive (so the hypothesis `Σ < (3/10)^2 - ε` is a genuine constraint and not satisfied
by every sum), and the box `InBox q R ρ` is inhabited at a non-degenerate point (`ρ = 1`) while it
genuinely excludes other points (`ρ = -1`, where `λ = 2 log 2 > R = 1`), so the box is neither
empty nor all of `ℂ`.

Prover notes: witnesses `ε = 1/100`, `R = 1`, `q₀ = 0`, `q = 2`, `a = 1`.
`¬ InBox 2 1 (-1)` needs `1 < 2 * Real.log 2`, i.e. `Real.log_two_gt_d9`.  No `native_decide`. -/
theorem area2_hyps_sat :
    ∃ (ε R : ℝ) (q₀ q a : ℕ), 0 < ε ∧ 0 < (3/10:ℝ)^2 - ε ∧ 0 < R ∧ q₀ ≤ q ∧ 2 ≤ q ∧
      a.Coprime q ∧ a < q ∧ Work.LinnikContract.InBox q R (1 : ℂ) ∧
      ¬ Work.LinnikContract.InBox q R (-1 : ℂ) := by
  refine ⟨1/100, 1, 0, 2, 1, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by decide, by norm_num, ?_, ?_⟩
  · simp [Work.LinnikContract.InBox, Work.LinnikContract.lamOf]
  · intro h
    have h1 := h.1
    simp [Work.LinnikContract.lamOf, Complex.neg_re] at h1
    linarith [Real.log_two_gt_d9]

end Work.LinnikContract.Sat

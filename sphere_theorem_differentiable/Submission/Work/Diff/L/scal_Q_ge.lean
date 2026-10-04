import Mathlib
import Submission.Work.Diff.Alg.Pinch.scalAlg_Q

namespace Work.Diff.L

open Finset

/-- **The scalar curvature of Hamilton's reaction term dominates the Riccati growth.**
`(2/n) * (scalAlg R)^2 ≤ scalAlg (Q R)` for an algebraic curvature tensor `R` on `ℝⁿ`.

Route.  `Work.Diff.Alg.Pinch.scalAlg_Q` (in `Diff/Alg/Pinch/scalAlg_Q`, import it; do **not**
import `Diff/Alg/Pinch/linv_Q_ell` or `Diff/Alg/Pinch/BW_identity`, which duplicate declarations)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
gives `scalAlg (Q R) = 2 * ∑ i j, ric R i j * ric R i j` with `ric R i j = ∑ k, R k i k j`.
Also `scalAlg R = ∑ i, ric R i i` (`scalAlg` and `ric` are reducible: `simp only [scalAlg, ric]`
and `Finset.sum_comm`).  Cauchy-Schwarz on the diagonal (`sq_sum_le_card_mul_sum_sq` /
`Finset.sq_sum_le_card_mul_sum_sq`) gives `(scalAlg R)^2 ≤ n * ∑ i, (ric R i i)^2 ≤ n * ∑ i ∑ j,
(ric R i j)^2`, i.e. `(scalAlg R)^2 ≤ n * scalAlg (Q R) / 2`.  Multiplying by `2/n` finishes
(for `n = 0` both sides are `0`; for `n > 0` use `div_le_iff` or `le_div_iff`). -/
theorem scal_Q_ge {n : ℕ} {R : Submission.Diff.Alg.Curv4 n}
    (hR : Submission.Diff.Alg.IsAlgCurv R) :
    (2 / (n : ℝ)) * Submission.Diff.Alg.scalAlg R ^ 2
      ≤ Submission.Diff.Alg.scalAlg (Submission.Diff.Alg.Q R) := by
  have hQS := Work.Diff.Alg.Pinch.scalAlg_Q n hR
  -- The scalar curvature is the trace of the Ricci tensor.
  have hscal : Submission.Diff.Alg.scalAlg R = ∑ i, Work.Diff.Alg.Pinch.ric R i i := by
    simp only [Submission.Diff.Alg.scalAlg, Work.Diff.Alg.Pinch.ric]
    rw [Finset.sum_comm]
  -- Cauchy–Schwarz on the diagonal.
  have hcs : (∑ i, Work.Diff.Alg.Pinch.ric R i i) ^ 2
      ≤ (n : ℝ) * ∑ i, Work.Diff.Alg.Pinch.ric R i i * Work.Diff.Alg.Pinch.ric R i i := by
    have := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
      (f := fun i => Work.Diff.Alg.Pinch.ric R i i)
    simpa [pow_two] using this
  -- The diagonal sum is at most the full sum of squares.
  have hdiag : ∑ i, Work.Diff.Alg.Pinch.ric R i i * Work.Diff.Alg.Pinch.ric R i i
      ≤ ∑ i, ∑ j, Work.Diff.Alg.Pinch.ric R i j * Work.Diff.Alg.Pinch.ric R i j := by
    apply Finset.sum_le_sum; intro i _
    have h := Finset.single_le_sum
      (f := fun j => Work.Diff.Alg.Pinch.ric R i j * Work.Diff.Alg.Pinch.ric R i j)
      (fun j _ => mul_self_nonneg _) (Finset.mem_univ i)
    simpa using h
  have hmul : (∑ i, Work.Diff.Alg.Pinch.ric R i i) ^ 2
      ≤ (n : ℝ) * (∑ i, ∑ j, Work.Diff.Alg.Pinch.ric R i j * Work.Diff.Alg.Pinch.ric R i j) :=
    le_trans hcs (mul_le_mul_of_nonneg_left hdiag (Nat.cast_nonneg n))
  rw [hscal, hQS]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp
  · have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    rw [div_mul_eq_mul_div, div_le_iff₀ hnR]
    nlinarith [hmul]

end Work.Diff.L

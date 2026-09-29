import Mathlib
import Submission.Work.RedProj.Defs
import Submission.Work.RedProj.monomial_eval
import Submission.Work.RedProj.monomial_norm_le

/-!
# The monomial formal multilinear series on `ℂ × ℂ`

Given an arbitrary coefficient family `c : ℕ → ℕ → ℂ`, we build a formal
multilinear series `P` on `ℂ × ℂ` whose `n`-th term is the homogeneous
polynomial

`P n (fun _ => (u, v)) = ∑_{m = 0}^{n} c m (n - m) u^m v^{n-m}`,

together with the operator-norm bound `‖P n‖ ≤ ∑ m ‖c m (n-m)‖` (each monomial
multilinear map has norm at most `1`).
-/

namespace Work.RedProj

noncomputable section

/-- Given `c : ℕ → ℕ → ℂ` there is a formal multilinear series `P` on `ℂ × ℂ`
whose `n`-th term evaluates on the constant tuple `(u,v)` to the homogeneous
polynomial `∑_{m ≤ n} c m (n-m) u^m v^{n-m}`, and whose norm is bounded by the
sum of the absolute values of the coefficients. -/
theorem monomial_formalSeries (c : ℕ → ℕ → ℂ) :
    ∃ P : FormalMultilinearSeries ℂ (ℂ × ℂ) ℂ,
      (∀ n u v, P n (fun _ => (u, v)) = ∑ m ∈ Finset.range (n + 1), c m (n - m) * u ^ m * v ^ (n - m)) ∧
      (∀ n, ‖P n‖ ≤ ∑ m ∈ Finset.range (n + 1), ‖c m (n - m)‖) := by
  classical
  refine ⟨fun n => ∑ m ∈ Finset.range (n + 1), (c m (n - m)) • monomial n m, ?_, ?_⟩
  · -- evaluation on constant tuples
    intro n u v
    show (∑ m ∈ Finset.range (n + 1), (c m (n - m)) • monomial n m) (fun _ => (u, v))
        = ∑ m ∈ Finset.range (n + 1), c m (n - m) * u ^ m * v ^ (n - m)
    rw [sum_apply]
    refine Finset.sum_congr rfl (fun m hm => ?_)
    rw [smul_apply, smul_eq_mul,
      monomial_eval n m (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)) u v]
    ring
  · -- operator-norm bound
    intro n
    refine le_trans (norm_sum_le (Finset.range (n + 1)) _) ?_
    refine Finset.sum_le_sum (fun m hm => ?_)
    rw [norm_smul]
    calc ‖c m (n - m)‖ * ‖monomial n m‖ ≤ ‖c m (n - m)‖ * 1 :=
          mul_le_mul_of_nonneg_left (monomial_norm_le n m) (norm_nonneg _)
      _ = ‖c m (n - m)‖ := mul_one _

end

end Work.RedProj

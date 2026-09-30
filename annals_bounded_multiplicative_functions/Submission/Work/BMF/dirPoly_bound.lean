import Mathlib
import Submission.Work.BMF.parseval_kernels

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-- The Dirichlet polynomial `dirPoly a X t = ∑_{n ∈ [X,4X]} a n · n^{-(1+it)}` is continuous
in `t`, and when `‖a n‖ ≤ 1` it is bounded uniformly in `t` by `∑_{n ∈ [X,4X]} 1/n`. -/
theorem dirPoly_bound (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) (X : ℝ) :
    Continuous (fun t : ℝ => Work.BMF.dirPoly a X t) ∧
      ∀ t : ℝ, ‖Work.BMF.dirPoly a X t‖
        ≤ ∑ n ∈ Work.BMF.natIcc X (4 * X), (1 : ℝ) / (n : ℝ) := by
  have hcont : Continuous
      (fun t : ℝ => ∑ n ∈ natIcc X (4 * X),
        a n * (n : ℂ) ^ (-(1 + Complex.I * (t : ℂ)))) := by
    apply continuous_finsetSum
    intro n _
    have hf : Continuous (fun t : ℝ => -(1 + Complex.I * (t : ℂ))) := by fun_prop
    exact continuous_const.mul (hf.const_cpow (Or.inr (fun t => by
      intro h; have := congrArg Complex.re h; simp at this)))
  have hbd : ∀ t : ℝ,
      ‖∑ n ∈ natIcc X (4 * X), a n * (n : ℂ) ^ (-(1 + Complex.I * (t : ℂ)))‖
        ≤ ∑ n ∈ natIcc X (4 * X), (1 : ℝ) / (n : ℝ) := by
    intro t
    calc ‖∑ n ∈ natIcc X (4 * X), a n * (n : ℂ) ^ (-(1 + Complex.I * (t : ℂ)))‖
        ≤ ∑ n ∈ natIcc X (4 * X),
            ‖a n * (n : ℂ) ^ (-(1 + Complex.I * (t : ℂ)))‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ natIcc X (4 * X), (1 : ℝ) / (n : ℝ) := by
          apply Finset.sum_le_sum
          intro n _
          rw [norm_mul]
          have hnorm : ‖(n : ℂ) ^ (-(1 + Complex.I * (t : ℂ)))‖ = (n : ℝ)⁻¹ := by
            rw [Complex.norm_natCast_cpow_of_re_ne_zero n (by simp)]
            have : (-(1 + Complex.I * (t : ℂ))).re = -1 := by simp
            rw [this, Real.rpow_neg_one]
          calc ‖a n‖ * ‖(n : ℂ) ^ (-(1 + Complex.I * (t : ℂ)))‖
              ≤ 1 * (n : ℝ)⁻¹ :=
                mul_le_mul (ha n) (le_of_eq hnorm) (norm_nonneg _) (by norm_num)
            _ = (1 : ℝ) / (n : ℝ) := by rw [one_mul, one_div]
  exact ⟨by simpa only [dirPoly] using hcont,
    fun t => by simpa only [dirPoly] using hbd t⟩

end Work.BMF

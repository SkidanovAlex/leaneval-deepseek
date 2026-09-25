import Mathlib

namespace Work.NN.Final.ChartComp

/-- The `(n+1)`-st iterated derivative of `Real.log` at `r` is
`(-1)^n * n! * r^(-(n+1))`. -/
private lemma iteratedDeriv_succ_log (n : ℕ) (r : ℝ) :
    iteratedDeriv (n + 1) Real.log r = (-1) ^ n * (n.factorial : ℝ) * r ^ (-(n : ℤ) - 1) := by
  rw [iteratedDeriv_succ', Real.deriv_log', iteratedDeriv_eq_iterate, iter_deriv_inv]
  congr 1
  ring_nf

theorem exists_bound_iteratedFDeriv_log :
    ∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧ ∀ (m : ℕ), 1 ≤ m → ∀ (r : ℝ),
      0 < r → ‖iteratedFDeriv ℝ m Real.log r‖ ≤ C m * (1 / r) ^ m := by
  refine ⟨fun m => ((m - 1).factorial : ℝ), ?_, ?_⟩
  · intro m
    show (0 : ℝ) < ((m - 1).factorial : ℝ)
    exact_mod_cast Nat.factorial_pos _
  · intro m _hm r hr
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
    simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs, iteratedDeriv_succ_log]
    have hexp : r ^ (-(n : ℤ) - 1) = (1 / r) ^ (n + 1) := by
      have h1 : (-(n : ℤ) - 1) = -(((n + 1 : ℕ)) : ℤ) := by push_cast; ring
      rw [h1, zpow_neg, zpow_natCast, ← inv_pow, one_div]
    rw [hexp]
    have hz : 0 < (1 / r) ^ (n + 1) := by positivity
    have hc : (0 : ℝ) ≤ (n.factorial : ℝ) := by positivity
    rw [abs_mul, abs_mul, abs_of_nonneg hc, abs_of_pos hz]
    have habs : |(-1 : ℝ) ^ n| = 1 := by simp
    rw [habs, one_mul]

end Work.NN.Final.ChartComp

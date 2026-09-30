import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.liouville

open Finset

/-- Termwise norm bound for the prime-power expansion of `ψ · Λ / id`: for a prime `p` and any `k`,
the `k`-th term `ψ (p^k) * log p / p^k` has norm at most `log p / p^k`, using `‖ψ a‖ ≤ 1`. -/
lemma norm_term_prime_pow_le (d : ℕ) [NeZero d] (ψ : DirichletCharacter ℂ d) (p k : ℕ)
    (hp : p.Prime) :
    ‖ψ (p ^ k) * (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ k)‖ ≤ Real.log (p : ℝ) / (p : ℝ) ^ k := by
  have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp.one_le)
  rw [norm_div, norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hlog, mul_div_assoc]
  exact mul_le_of_le_one_left (by positivity) (DirichletCharacter.norm_le_one ψ _)

/-- The geometric bound `∑_{k=2}^{K} p^{-k} ≤ 1/(p(p-1))` for an integer `p ≥ 2`. -/
lemma geom_sum_Icc_inv_pow_le (p K : ℕ) (hp : 2 ≤ p) :
    ∑ k ∈ Finset.Icc 2 K, ((1 : ℝ) / (p : ℝ)) ^ k ≤ 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
  have hp2 : (1 : ℝ) < p := by exact_mod_cast (by omega : 1 < p)
  have hx0 : 0 ≤ (1 : ℝ) / (p : ℝ) := by positivity
  have hx1 : (1 : ℝ) / (p : ℝ) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have h := geom_sum_Ico_le_of_lt_one (x := (1 : ℝ) / (p : ℝ)) hx0 hx1 (m := 2) (n := K + 1)
  rw [show Finset.Ico 2 (K + 1) = Finset.Icc 2 K from by
        ext k; simp [Finset.mem_Ico, Finset.mem_Icc]] at h
  have hval : ((1 : ℝ) / (p : ℝ)) ^ 2 / (1 - 1 / (p : ℝ)) = 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
    field_simp
  rwa [hval] at h

/-- Namespace `Work.BMF.liouville`. Import: `Mathlib`.

For a prime `p`, the `k ≥ 2` part of the prime-power expansion of `ψ · Λ / id` is bounded by
`log p / (p(p-1))`, using `‖ψ a‖ ≤ 1` (`DirichletCharacter.norm_le_one`) and the geometric bound
`∑_{k=2}^{K} p^{-k} ≤ 1/(p(p-1))`. -/
theorem norm_row_tail_prime_le (d : ℕ) [NeZero d] (ψ : DirichletCharacter ℂ d) (p K : ℕ)
    (hp : p.Prime) :
    ‖∑ k ∈ Finset.Icc 2 K, ψ (p ^ k) * (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ k)‖
      ≤ Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by
  have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp.one_le)
  calc ‖∑ k ∈ Finset.Icc 2 K, ψ (p ^ k) * (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ k)‖
      ≤ ∑ k ∈ Finset.Icc 2 K,
          ‖ψ (p ^ k) * (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ k)‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.Icc 2 K, Real.log (p : ℝ) / (p : ℝ) ^ k :=
        Finset.sum_le_sum fun k _ => norm_term_prime_pow_le d ψ p k hp
    _ = Real.log (p : ℝ) * ∑ k ∈ Finset.Icc 2 K, ((1 : ℝ) / (p : ℝ)) ^ k := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [one_div, inv_pow, div_eq_mul_inv]
    _ ≤ Real.log (p : ℝ) * (1 / ((p : ℝ) * ((p : ℝ) - 1))) :=
        mul_le_mul_of_nonneg_left (geom_sum_Icc_inv_pow_le p K hp.two_le) hlog
    _ = Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by rw [mul_one_div]

end Work.BMF.liouville

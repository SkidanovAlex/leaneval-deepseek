import Mathlib

namespace Work.Sieve

theorem summable_div_prime_pow (p : ℕ) (hp : p.Prime) :
    Summable (fun k : ℕ => ((k : ℝ) + 2) / (p : ℝ) ^ (k + 1)) := by
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  -- The ratio `1 / p` has norm `< 1`.
  have hr : ‖(1 : ℝ) / (p : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity), div_lt_one hp_pos]
    have : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
    linarith
  -- `∑ (k+2) r^k` is summable as `∑ k r^k` plus `2 ∑ r^k`.
  have hs : Summable (fun k : ℕ => ((k : ℝ) + 2) * ((1 : ℝ) / (p : ℝ)) ^ k) := by
    have h1 : Summable (fun k : ℕ => ((k : ℝ)) * ((1 : ℝ) / (p : ℝ)) ^ k) := by
      simpa using summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hr
    have h2 : Summable (fun k : ℕ => (2 : ℝ) * ((1 : ℝ) / (p : ℝ)) ^ k) :=
      (summable_geometric_of_norm_lt_one hr).mul_left 2
    have h3 := h1.add h2
    refine h3.congr (fun k => ?_)
    ring
  -- Multiply by the ratio once more and rewrite `(1/p)^k * (1/p) = 1/p^(k+1)`.
  refine (hs.mul_left ((1 : ℝ) / (p : ℝ))).congr (fun k => ?_)
  simp only [one_mul, div_eq_mul_inv, pow_succ]
  ring

end Work.Sieve

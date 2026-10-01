import Mathlib
import Submission.Work.LinnikAreas.Density4.theta_lower_bound
import Submission.Work.LinnikAreas.Density4.primes_log_sq_lower

namespace Work.LinnikAreas.Density4

/-- Lower bound for the second moment of `log p` over the primes `p ≤ N`.

`theta_lower_bound` gives `θ(N) ≥ N − K N / log N`, and `primes_log_sq_lower`
turns any lower bound for `θ` into one for `∑_{p ≤ N} (log p)²`; multiplying the
first by `log N > 0` and combining the two yields the claim with `C = K + C'`. -/
theorem primes_sq_sum_lower : ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N →
    (N : ℝ) * Real.log (N : ℝ) - C * (N : ℝ)
      ≤ ∑ p ∈ Nat.primesLE N, (Real.log (p : ℝ)) ^ 2 := by
  obtain ⟨K, hKpos, hK⟩ := theta_lower_bound
  obtain ⟨D, hDpos, hD⟩ := primes_log_sq_lower
  refine ⟨K + D, by linarith, ?_⟩
  intro N hN
  have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 1 < N)
  have hlogn : 0 < Real.log (N : ℝ) := Real.log_pos hN1
  have hlognne : Real.log (N : ℝ) ≠ 0 := ne_of_gt hlogn
  -- multiplying the lower bound for `θ` by `log N > 0`
  have hmul := mul_le_mul_of_nonneg_left (hK N hN) (le_of_lt hlogn)
  have hid : Real.log (N : ℝ) * ((N : ℝ) - K * (N : ℝ) / Real.log (N : ℝ))
      = (N : ℝ) * Real.log (N : ℝ) - K * (N : ℝ) := by
    field_simp
  have h1 : (N : ℝ) * Real.log (N : ℝ) - K * (N : ℝ)
      ≤ Real.log (N : ℝ) * Chebyshev.theta (N : ℝ) := by
    rw [← hid]; exact hmul
  have h2 := hD N hN
  linarith

end Work.LinnikAreas.Density4

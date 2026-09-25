import Mathlib
import Submission.Commons.NumberTheory.Chebyshev.sum_prime_inv_sq_abel
import Submission.Commons.NumberTheory.Chebyshev.prime_sq_sum_error_bound
import Submission.Commons.Analysis.Real.integral_inv_sq_log_lower
import Submission.Commons.Analysis.Real.main_term_abel_identity

open MeasureTheory
open scoped Interval

namespace Commons.NumberTheory.Chebyshev

/-- The Abel-summation integrand `(2 log t + 1)/(t^3 (log t)^2)` is continuous on `[n,m]`
for `2 ≤ n ≤ m`. -/
private lemma continuousOn_fint {n m : ℝ} (hn : 2 ≤ n) (hnm : n ≤ m) :
    ContinuousOn (fun t : ℝ => (2*Real.log t + 1)/(t^3 * (Real.log t)^2)) (Set.uIcc n m) := by
  rw [Set.uIcc_of_le hnm]
  have hlog : ContinuousOn Real.log (Set.Icc n m) :=
    Real.continuousOn_log.mono (fun t ht => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      have h1 : (1:ℝ) < t := lt_of_lt_of_le (by linarith) ht.1
      linarith)
  have hid : ContinuousOn (fun t : ℝ => t) (Set.Icc n m) := continuousOn_id
  have hnum : ContinuousOn (fun t : ℝ => 2*Real.log t + 1) (Set.Icc n m) :=
    ((continuous_const : Continuous (fun _ : ℝ => (2:ℝ))).continuousOn.mul hlog).add continuousOn_const
  have hden : ContinuousOn (fun t : ℝ => t^3 * (Real.log t)^2) (Set.Icc n m) :=
    ((hid.pow 3).mul (hlog.pow 2))
  have hne : ∀ t ∈ Set.Icc n m, t^3 * (Real.log t)^2 ≠ 0 := by
    intro t ht
    have h1 : (1:ℝ) < t := lt_of_lt_of_le (by linarith) ht.1
    have ht0 : t ≠ 0 := by linarith
    have hl : Real.log t ≠ 0 := ne_of_gt (Real.log_pos h1)
    exact mul_ne_zero (pow_ne_zero 3 ht0) (pow_ne_zero 2 hl)
  exact hnum.div hden hne

/-- Splitting `θ t = t + (θ t - t)` inside the Abel-summation integral. -/
private lemma integral_fint_mul_theta_eq {n m : ℝ} (hn : 2 ≤ n) (hnm : n ≤ m) :
    (∫ t in n..m, (2*Real.log t + 1)/(t^3 * (Real.log t)^2) * Chebyshev.theta t)
      = (∫ t in n..m, (2*Real.log t + 1)/(t^3 * (Real.log t)^2) * t)
        + (∫ t in n..m, (2*Real.log t + 1)/(t^3 * (Real.log t)^2) * (Chebyshev.theta t - t)) := by
  have hcont := continuousOn_fint hn hnm
  have hθ : IntervalIntegrable Chebyshev.theta volume n m := Chebyshev.theta_mono.intervalIntegrable
  have hid : IntervalIntegrable (fun t : ℝ => t) volume n m := continuousOn_id.intervalIntegrable
  have h2 : IntervalIntegrable
      (fun t : ℝ => (2*Real.log t + 1)/(t^3 * (Real.log t)^2) * t) volume n m :=
    hid.continuousOn_mul hcont
  have h3 : IntervalIntegrable
      (fun t : ℝ => (2*Real.log t + 1)/(t^3 * (Real.log t)^2) * (Chebyshev.theta t - t)) volume n m :=
    (hθ.sub hid).continuousOn_mul hcont
  rw [← intervalIntegral.integral_add h2 h3]
  apply intervalIntegral.integral_congr
  intro x hx
  ring

/--

Lower bound for the tail of `∑ 1/p^2` over primes in `(n, m]`, assuming the Chebyshev
error bound `|θ t - t| ≤ C √t (log t)^{10}` on `[n,m]`.

-/
theorem sum_prime_inv_sq_lower_bound {n m : ℕ} {C : ℝ} (hn : 2 ≤ n) (hnm : n ≤ m) (hC : 0 ≤ C)
    (hθ : ∀ t ∈ Set.Icc (n:ℝ) (m:ℝ), |Chebyshev.theta t - t| ≤ C * Real.sqrt t * (Real.log t)^10) :
    (∑ p ∈ Finset.Ioc n m, if p.Prime then (1:ℝ)/((p:ℝ)^2) else 0)
      ≥ (1/((n:ℝ) * Real.log (n:ℝ))) * (1 - (n:ℝ)/min (m:ℝ) ((n:ℝ)^2) - 1/(Real.log (n:ℝ)))
        - 5*C*(Real.log (m:ℝ))^9 / ((n:ℝ)^(3/2 : ℝ)) := by
  have hn2 : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hn1 : (1:ℝ) < (n:ℝ) := by linarith
  have hnm' : (n:ℝ) ≤ (m:ℝ) := by exact_mod_cast hnm
  -- Abel summation: rewrite the sum as the boundary terms plus an integral.
  rw [sum_prime_inv_sq_abel hn hnm, ← intervalIntegral.integral_of_le hnm']
  -- Split `θ t = t + (θ t - t)` in the integral.
  rw [integral_fint_mul_theta_eq hn2 hnm']
  -- The "main term" is the integral `∫_n^m dt/(t^2 log t)`.
  have hmain := Commons.Analysis.Real.main_term_abel_identity hn1 hnm'
  rw [← intervalIntegral.integral_of_le hnm'] at hmain
  have hlow := Commons.Analysis.Real.integral_inv_sq_log_lower hn1 hnm'
  -- The error term is bounded by the Chebyshev-type hypothesis.
  have herr := prime_sq_sum_error_bound (n := (n:ℝ)) (m := (m:ℝ)) hn2 hnm' hC hθ
  rw [← intervalIntegral.integral_of_le hnm'] at herr
  have hE : (1/((m:ℝ)^2 * Real.log (m:ℝ))) * (Chebyshev.theta (m:ℝ) - (m:ℝ))
      - (1/((n:ℝ)^2 * Real.log (n:ℝ))) * (Chebyshev.theta (n:ℝ) - (n:ℝ))
      + ∫ t in (n:ℝ)..(m:ℝ), ((2*Real.log t + 1)/(t^3 * (Real.log t)^2)) * (Chebyshev.theta t - t)
      ≥ -(5*C*(Real.log (m:ℝ))^9 / ((n:ℝ)^(3/2 : ℝ))) := by
    have h := (abs_le.mp herr).1
    linarith
  have hmain' : (1/((m:ℝ)^2 * Real.log (m:ℝ))) * (m:ℝ) - (1/((n:ℝ)^2 * Real.log (n:ℝ))) * (n:ℝ)
      + ∫ t in (n:ℝ)..(m:ℝ), ((2*Real.log t + 1)/(t^3 * (Real.log t)^2)) * t
      ≥ (1/((n:ℝ) * Real.log (n:ℝ))) * (1 - (n:ℝ)/min (m:ℝ) ((n:ℝ)^2) - 1/(Real.log (n:ℝ))) := by
    rw [hmain]; exact hlow
  have hEq : (1/((m:ℝ)^2 * Real.log (m:ℝ))) * Chebyshev.theta (m:ℝ)
      - (1/((n:ℝ)^2 * Real.log (n:ℝ))) * Chebyshev.theta (n:ℝ)
      + ((∫ t in (n:ℝ)..(m:ℝ), (2*Real.log t + 1)/(t^3 * (Real.log t)^2) * t)
         + ∫ t in (n:ℝ)..(m:ℝ), (2*Real.log t + 1)/(t^3 * (Real.log t)^2) * (Chebyshev.theta t - t))
      = ((1/((m:ℝ)^2 * Real.log (m:ℝ))) * (m:ℝ) - (1/((n:ℝ)^2 * Real.log (n:ℝ))) * (n:ℝ)
          + ∫ t in (n:ℝ)..(m:ℝ), (2*Real.log t + 1)/(t^3 * (Real.log t)^2) * t)
        + ((1/((m:ℝ)^2 * Real.log (m:ℝ))) * (Chebyshev.theta (m:ℝ) - (m:ℝ))
          - (1/((n:ℝ)^2 * Real.log (n:ℝ))) * (Chebyshev.theta (n:ℝ) - (n:ℝ))
          + ∫ t in (n:ℝ)..(m:ℝ), (2*Real.log t + 1)/(t^3 * (Real.log t)^2) * (Chebyshev.theta t - t)) := by
    ring
  rw [hEq]
  linarith [hmain', hE]

end Commons.NumberTheory.Chebyshev

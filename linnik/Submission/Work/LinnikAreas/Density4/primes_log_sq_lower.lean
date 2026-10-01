import Mathlib
import Submission.Work.LinnikAreas.Density4.prime_log_sum_repr
import Submission.Work.LinnikAreas.Density4.interval_integrable_theta_div

namespace Work.LinnikAreas.Density4

open MeasureTheory intervalIntegral Finset

/-- `Nat.primesLE z` written as the `Icc 1 z`-filtered set matching the Abel-sum identity. -/
private lemma primesLE_eq_filter_Icc (z : ℕ) :
    (Finset.Icc 1 z).filter (fun p => Nat.Prime p ∧ (1 : ℝ) < (p : ℝ)) = Nat.primesLE z := by
  rw [Nat.primesLE_eq_filter_Icc_one]
  apply Finset.filter_congr
  intro p _
  constructor
  · rintro ⟨hp, _⟩; exact hp
  · intro hp; exact ⟨hp, by exact_mod_cast hp.one_lt⟩

/-- `log z · θ(z) − Σ_{p ≤ z} (log p)²` is the integral `∫_1^z θ(t)/t dt`.

This is `prime_log_sum_repr` at `y = 1`, `x = z`, with the sum rewritten over `Nat.primesLE z`. -/
private lemma log_theta_sub_sum_eq_integral (z : ℕ) (hz : 1 ≤ z) :
    Real.log (z : ℝ) * Chebyshev.theta (z : ℝ)
        - ∑ p ∈ Nat.primesLE z, (Real.log (p : ℝ)) ^ 2
      = ∫ t in (1 : ℝ)..(z : ℝ), Chebyshev.theta t / t := by
  have hz1 : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  have h := prime_log_sum_repr (y := (1 : ℝ)) (x := (z : ℝ)) (le_refl 1) hz1
  rw [Nat.floor_natCast] at h
  rw [primesLE_eq_filter_Icc z] at h
  simp only [div_one] at h
  have hsum : (∑ p ∈ Nat.primesLE z, (Real.log (p : ℝ)) ^ 2)
      = ∑ p ∈ Nat.primesLE z, Real.log (p : ℝ) * Real.log (p : ℝ) := by
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [sq]
  rw [hsum, h]
  ring

/-- Chebyshev's elementary upper bound `θ(t) ≤ log 4 · t` gives `∫_1^z θ(t)/t dt ≤ log 4 · z`. -/
private lemma integral_theta_div_le (z : ℕ) (hz : 1 ≤ z) :
    ∫ t in (1 : ℝ)..(z : ℝ), Chebyshev.theta t / t ≤ Real.log 4 * (z : ℝ) := by
  have hz1 : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  have hz1' : (0 : ℝ) ≤ (z : ℝ) - 1 := by linarith
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (1 : ℝ)) (b := (z : ℝ)) (C := Real.log 4)
    (f := fun t : ℝ => Chebyshev.theta t / t) (fun t _ => norm_theta_div_le t)
  rw [Real.norm_eq_abs, abs_of_nonneg hz1'] at h
  have hlog4nn : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  calc ∫ t in (1 : ℝ)..(z : ℝ), Chebyshev.theta t / t
      ≤ |∫ t in (1 : ℝ)..(z : ℝ), Chebyshev.theta t / t| := le_abs_self _
    _ ≤ Real.log 4 * ((z : ℝ) - 1) := h
    _ ≤ Real.log 4 * (z : ℝ) := by nlinarith [hlog4nn]

theorem primes_log_sq_lower :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℕ, 2 ≤ z →
      Real.log (z : ℝ) * Chebyshev.theta (z : ℝ) - C * (z : ℝ)
        ≤ ∑ p ∈ Nat.primesLE z, (Real.log (p : ℝ)) ^ 2 := by
  refine ⟨Real.log 4, Real.log_pos (by norm_num), ?_⟩
  intro z hz
  have hz1 : 1 ≤ z := by omega
  have heq := log_theta_sub_sum_eq_integral z hz1
  have hbound := integral_theta_div_le z hz1
  -- `heq : log z * θ z − Σ = ∫` and `hbound : ∫ ≤ log 4 * z`
  linarith [heq, hbound]

end Work.LinnikAreas.Density4

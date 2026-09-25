import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.NumberTheory.Chebyshev

open Finset MeasureTheory
open scoped BigOperators

namespace Commons.NumberTheory.Chebyshev

/-- `θ x` is the sum of `log p` over primes `p ≤ x`, expressed as an indicator sum. -/
lemma theta_eq_sum_c (x : ℝ) :
    (∑ k ∈ Finset.Icc 0 ⌊x⌋₊, (if k.Prime then Real.log (k:ℝ) else 0))
      = Chebyshev.theta x := by
  rw [Chebyshev.theta_eq_sum_Icc, Finset.sum_filter]

/-- Version of `theta_eq_sum_c` at a natural number. -/
lemma theta_eq_sum_c_nat (N : ℕ) :
    (∑ k ∈ Finset.Icc 0 N, (if k.Prime then Real.log (k:ℝ) else 0))
      = Chebyshev.theta (N:ℝ) := by
  simpa [Nat.floor_natCast] using theta_eq_sum_c (N:ℝ)

/-- Derivative of `t ↦ 1/(t^2 log t)`. -/
private lemma hasDerivAt_abel_f (t : ℝ) (ht : 2 ≤ t) :
    HasDerivAt (fun s : ℝ => 1/(s^2 * Real.log s))
      (-((2*Real.log t + 1)/(t^3 * (Real.log t)^2))) t := by
  have ht0 : t ≠ 0 := by linarith
  have hlog : Real.log t ≠ 0 := ne_of_gt (Real.log_pos (by linarith))
  have ht2 : t^2 * Real.log t ≠ 0 := mul_ne_zero (by positivity) hlog
  have h1 : HasDerivAt (fun s : ℝ => s^2 * Real.log s)
      (2*t * Real.log t + t^2 * t⁻¹) t := by
    have h0 := (hasDerivAt_pow 2 t).mul (Real.hasDerivAt_log ht0)
    refine h0.congr_deriv ?_
    simp only [Nat.reduceSub, pow_one]
    ring
  have hdiv := (hasDerivAt_const t (1:ℝ)).div h1 ht2
  refine hdiv.congr_deriv ?_
  field_simp
  ring

private lemma deriv_abel_f (t : ℝ) (ht : 2 ≤ t) :
    deriv (fun s : ℝ => 1/(s^2 * Real.log s)) t
      = -((2*Real.log t + 1)/(t^3 * (Real.log t)^2)) :=
  (hasDerivAt_abel_f t ht).deriv

/-- The integrand of the Abel-summation remainder is continuous. -/
private lemma continuousOn_H :
    ContinuousOn (fun t : ℝ => (2*Real.log t + 1)/(t^3 * (Real.log t)^2))
      (Set.Ici (2:ℝ)) := by
  have hlogc : ContinuousOn Real.log (Set.Ici (2:ℝ)) :=
    Real.continuousOn_log.mono (by
      intro t ht
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      have ht' : (2:ℝ) ≤ t := ht
      exact ne_of_gt (by linarith))
  have hnum : ContinuousOn (fun t : ℝ => 2*Real.log t + 1) (Set.Ici (2:ℝ)) :=
    ((continuous_const : Continuous (fun _ : ℝ => (2:ℝ))).continuousOn.mul hlogc).add
      (continuous_const.continuousOn)
  have hden : ContinuousOn (fun t : ℝ => t^3 * (Real.log t)^2) (Set.Ici (2:ℝ)) :=
    ((continuous_id.continuousOn.pow 3).mul (hlogc.pow 2))
  have hne : ∀ t ∈ Set.Ici (2:ℝ), t^3 * (Real.log t)^2 ≠ 0 := by
    intro t ht
    have ht' : (2:ℝ) ≤ t := ht
    have ht0 : t ≠ 0 := by linarith
    have hl : Real.log t ≠ 0 := ne_of_gt (Real.log_pos (by linarith))
    exact mul_ne_zero (pow_ne_zero 3 ht0) (pow_ne_zero 2 hl)
  exact hnum.div hden hne

/-- `deriv (fun t => 1/(t^2 log t))` is integrable on `Icc n m` for `2 ≤ n`. -/
private lemma integrableOn_derivF (n m : ℕ) (hn : 2 ≤ n) :
    IntegrableOn (deriv (fun s : ℝ => 1/(s^2 * Real.log s))) (Set.Icc (n:ℝ) m) := by
  have hsub : Set.Icc (n:ℝ) m ⊆ Set.Ici (2:ℝ) := by
    intro t ht
    simp only [Set.mem_Icc] at ht
    simp only [Set.mem_Ici]
    have hn' : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    linarith [ht.1]
  have hc : ContinuousOn (fun t : ℝ => -((2*Real.log t + 1)/(t^3 * (Real.log t)^2)))
      (Set.Icc (n:ℝ) m) := continuousOn_H.neg.mono hsub
  have hint : IntegrableOn (fun t : ℝ => -((2*Real.log t + 1)/(t^3 * (Real.log t)^2)))
      (Set.Icc (n:ℝ) m) := hc.integrableOn_Icc
  refine hint.congr_fun_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact (deriv_abel_f t (hsub ht)).symm

theorem sum_prime_inv_sq_abel {n m : ℕ} (hn : 2 ≤ n) (hnm : n ≤ m) :
    (∑ p ∈ Finset.Ioc n m, if p.Prime then (1:ℝ)/((p:ℝ)^2) else 0)
      = (1/((m:ℝ)^2 * Real.log (m:ℝ))) * Chebyshev.theta (m:ℝ)
        - (1/((n:ℝ)^2 * Real.log (n:ℝ))) * Chebyshev.theta (n:ℝ)
        + ∫ t in Set.Ioc (n:ℝ) (m:ℝ),
            ((2*Real.log t + 1)/(t^3 * (Real.log t)^2)) * Chebyshev.theta t := by
  let c : ℕ → ℝ := fun k => if k.Prime then Real.log (k:ℝ) else 0
  let f : ℝ → ℝ := fun t => 1/(t^2 * Real.log t)
  have hsub : ∀ t ∈ Set.Icc (n:ℝ) (m:ℝ), 2 ≤ t := by
    intro t ht
    simp only [Set.mem_Icc] at ht
    have hn' : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    linarith [ht.1]
  have hdiff : ∀ t ∈ Set.Icc (n:ℝ) (m:ℝ), DifferentiableAt ℝ f t := fun t ht =>
    (hasDerivAt_abel_f t (hsub t ht)).differentiableAt
  have hint : IntegrableOn (deriv f) (Set.Icc (n:ℝ) (m:ℝ)) := integrableOn_derivF n m hn
  have habel := sum_mul_eq_sub_sub_integral_mul' c hnm hdiff hint
  have hsm : (∑ k ∈ Finset.Icc 0 m, c k) = Chebyshev.theta (m:ℝ) := by
    show (∑ k ∈ Finset.Icc 0 m, (if k.Prime then Real.log (k:ℝ) else 0))
      = Chebyshev.theta (m:ℝ)
    exact theta_eq_sum_c_nat m
  have hsn : (∑ k ∈ Finset.Icc 0 n, c k) = Chebyshev.theta (n:ℝ) := by
    show (∑ k ∈ Finset.Icc 0 n, (if k.Prime then Real.log (k:ℝ) else 0))
      = Chebyshev.theta (n:ℝ)
    exact theta_eq_sum_c_nat n
  have hsum : (∑ p ∈ Finset.Ioc n m, (if p.Prime then (1:ℝ)/((p:ℝ)^2) else 0))
      = ∑ k ∈ Finset.Ioc n m, f k * c k := by
    apply Finset.sum_congr rfl
    intro k hk
    show (if k.Prime then (1:ℝ)/((k:ℝ)^2) else 0)
      = 1/((k:ℝ)^2 * Real.log (k:ℝ)) * (if k.Prime then Real.log (k:ℝ) else 0)
    by_cases hp : k.Prime
    · rw [if_pos hp, if_pos hp]
      have hlog : Real.log (k:ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast hp.one_lt))
      field_simp
    · rw [if_neg hp, if_neg hp, mul_zero]
  have hintg : (∫ t in Set.Ioc (n:ℝ) (m:ℝ), deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k)
      = - ∫ t in Set.Ioc (n:ℝ) (m:ℝ),
          ((2*Real.log t + 1)/(t^3 * (Real.log t)^2)) * Chebyshev.theta t := by
    rw [← integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    change deriv f t * (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k)
      = -(((2*Real.log t + 1)/(t^3 * (Real.log t)^2)) * Chebyshev.theta t)
    have ht2 : 2 ≤ t := hsub t (Set.Ioc_subset_Icc_self ht)
    have hd : deriv f t = -((2*Real.log t + 1)/(t^3 * (Real.log t)^2)) := deriv_abel_f t ht2
    have hs : (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) = Chebyshev.theta t := by
      show (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, (if k.Prime then Real.log (k:ℝ) else 0))
        = Chebyshev.theta t
      exact theta_eq_sum_c t
    rw [hd, hs, neg_mul]
  rw [hsum, habel, hsm, hsn, hintg]
  simp only [f]
  ring

end Commons.NumberTheory.Chebyshev
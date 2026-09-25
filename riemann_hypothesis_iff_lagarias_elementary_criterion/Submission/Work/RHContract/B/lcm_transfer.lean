import Mathlib
import Submission.Work.RHContract.Corpus
import Submission.Work.RHContract.Identity.logRatioSum_eq_psiTail
import Submission.Work.RHContract.Identity.primeTail_nonneg
import Submission.Work.RHContract.B.lcm_transfer_defs
import Submission.Commons.NumberTheory.Robin.sigma_ratio_prime_power_prod
import Submission.Work.RHContract.B.lcmCorr_le

/-!
# `Work.RHContract.B.lcm_transfer` — Lemma T (ROUTE_LEAD §3.1)

For `x ≥ 100`, with `N = lcm(1..⌊x⌋₊)`,

    γ + log log log N − J(x) − 5/√x ≤ log (σ(N)/N) ,

where `J = psiTail`.

## Proof (following ROUTE_LEAD §3.1)

1. `log N = ψ x` (`Chebyshev.psi_eq_log_lcmUpto`, `Chebyshev.psi_eq_psi_coe_floor`).
2. `Robin.sigma_ratio_prime_power_prod` writes `σ(N)/N` as the product over the primes
   `p ≤ ⌊x⌋₊` of `(1 − p^{−(e_p+1)})/(1 − 1/p)`, `e_p = Nat.log p ⌊x⌋₊`; taking logarithms,
   `log (σ(N)/N) = logRatioSum x − lcmCorr x`.
3. Mertens' identity (Lemma I, `Identity.logRatioSum_eq_psiTail`) gives
   `logRatioSum x = γ + loglog x + (ψ x − x)/(x log x) − J(x) + primeTail x`.
4. `log log ψ x ≤ log log x + (ψ x − x)/(x log x)`, by `log(1+y) ≤ y` and `log u ≤ u − 1`
   — the one-sided step that removes the boundary term.
5. `lcmCorr x ≤ 5/√x` (`B.lcmCorr_le`) and `primeTail x ≥ 0`.

Adding up, the right-hand side dominates `γ + log log log N − J(x) − 5/√x`.
-/

namespace Work.RHContract.B

open scoped ArithmeticFunction.sigma
open Finset

/-! ## Elementary log-log comparison -/

/-- `log log a ≤ log log b + (a − b)/(b log b)` for `a, b > 1`: write
`log log a = log log b + log (1 + log(a/b)/log b)` and apply `log(1+y) ≤ y` and
`log u ≤ u − 1`.  No size hypothesis on `a − b` is needed. -/
lemma log_log_le_log_log_add (a b : ℝ) (hb : 1 < b) (ha : 1 < a) :
    Real.log (Real.log a) ≤ Real.log (Real.log b) + (a - b) / (b * Real.log b) := by
  have hbpos : 0 < b := by linarith
  have hlb : 0 < Real.log b := Real.log_pos hb
  have hla : 0 < Real.log a := Real.log_pos ha
  have hratio : 0 < a / b := div_pos (by linarith) hbpos
  have hargs : Real.log a = Real.log b + Real.log (a / b) := by
    rw [Real.log_div (by linarith) (by linarith)]; ring
  have hz : 0 < 1 + Real.log (a / b) / Real.log b := by
    have : (1 + Real.log (a / b) / Real.log b) = Real.log a / Real.log b := by
      field_simp; linarith
    rw [this]
    exact div_pos hla hlb
  have step1 : Real.log (Real.log a) =
      Real.log (Real.log b) + Real.log (1 + Real.log (a / b) / Real.log b) := by
    rw [hargs]
    have : Real.log b + Real.log (a / b) = Real.log b * (1 + Real.log (a / b) / Real.log b) := by
      field_simp
    rw [this, Real.log_mul (ne_of_gt hlb) (ne_of_gt hz)]
  have step2 : Real.log (1 + Real.log (a / b) / Real.log b) ≤ Real.log (a / b) / Real.log b := by
    have := Real.log_le_sub_one_of_pos hz
    linarith
  have step3 : Real.log (a / b) / Real.log b ≤ (a - b) / (b * Real.log b) := by
    have h1 : Real.log (a / b) ≤ a / b - 1 := Real.log_le_sub_one_of_pos hratio
    calc Real.log (a / b) / Real.log b ≤ (a / b - 1) / Real.log b :=
          div_le_div_of_nonneg_right h1 (le_of_lt hlb)
      _ = (a - b) / (b * Real.log b) := by field_simp
  linarith [step1, step2, step3]

/-- `ψ x > 1` for `x ≥ 100`: indeed `lcm(1..⌊x⌋₊) ≥ 64 = 2^6`, so
`ψ x = log (lcm(1..⌊x⌋₊)) ≥ 6 log 2 ≥ 3`. -/
lemma psi_gt_one (x : ℝ) (hx : 100 ≤ x) : 1 < Chebyshev.psi x := by
  have hn : 100 ≤ ⌊x⌋₊ := Nat.le_floor hx
  have hdvd : 64 ∣ Nat.lcmUpto ⌊x⌋₊ := by
    rw [Nat.lcmUpto]
    exact Finset.dvd_lcm (f := id) (by simp only [Finset.mem_Icc]; omega)
  have hle : 64 ≤ Nat.lcmUpto ⌊x⌋₊ := Nat.le_of_dvd (Nat.lcmUpto_pos _) hdvd
  have hpsi : Chebyshev.psi x = Real.log (Nat.lcmUpto ⌊x⌋₊ : ℝ) := by
    rw [Chebyshev.psi_eq_psi_coe_floor, Chebyshev.psi_eq_log_lcmUpto]
  have hlog : Real.log (64 : ℝ) ≤ Real.log (Nat.lcmUpto ⌊x⌋₊ : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hle)
  have h64 : Real.log (64 : ℝ) = 6 * Real.log 2 := by
    rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]; norm_num
  have h2 : (1 : ℝ) / 2 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  rw [hpsi]
  linarith

/-! ## The product formula for `σ(N)/N` -/

/-- `(p^{e+1} − 1)/(p^e (p − 1)) = (p/(p−1)) · (1 − p^{−(e+1)})` for a prime `p`. -/
lemma lcmFactor_eq (x : ℝ) (p : ℕ) (hp : p.Prime) :
    (((p : ℝ) ^ (Nat.log p ⌊x⌋₊ + 1) - 1) /
        ((p : ℝ) ^ (Nat.log p ⌊x⌋₊) * ((p : ℝ) - 1)))
      = ((p : ℝ) / ((p : ℝ) - 1)) * (1 - 1 / (p : ℝ) ^ (Nat.log p ⌊x⌋₊ + 1)) := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hpe : (0 : ℝ) < (p : ℝ) ^ (Nat.log p ⌊x⌋₊ + 1) := by positivity
  rw [pow_succ]
  field_simp

/-- Positivity of the factors of the product formula. -/
lemma lcmFactor_pos (x : ℝ) (p : ℕ) (hp : p.Prime) :
    (0 : ℝ) < (((p : ℝ) ^ (Nat.log p ⌊x⌋₊ + 1) - 1) /
        ((p : ℝ) ^ (Nat.log p ⌊x⌋₊) * ((p : ℝ) - 1))) := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hpe : (0 : ℝ) < (p : ℝ) ^ (Nat.log p ⌊x⌋₊ + 1) := by positivity
  have h2 : (0 : ℝ) < 1 - 1 / (p : ℝ) ^ (Nat.log p ⌊x⌋₊ + 1) := by
    rw [sub_pos, div_lt_one hpe]
    exact one_lt_pow₀ hp1 (by omega)
  rw [lcmFactor_eq x p hp]
  positivity

/-- Logarithm of a factor of the product formula. -/
lemma log_lcmFactor (x : ℝ) (p : ℕ) (hp : p.Prime) :
    Real.log ((((p : ℝ) ^ (Nat.log p ⌊x⌋₊ + 1) - 1) /
        ((p : ℝ) ^ (Nat.log p ⌊x⌋₊) * ((p : ℝ) - 1))))
      = Real.log ((p : ℝ) / ((p : ℝ) - 1))
        + Real.log (1 - 1 / (p : ℝ) ^ (Nat.log p ⌊x⌋₊ + 1)) := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hpe : (0 : ℝ) < (p : ℝ) ^ (Nat.log p ⌊x⌋₊ + 1) := by positivity
  have h2 : (0 : ℝ) < 1 - 1 / (p : ℝ) ^ (Nat.log p ⌊x⌋₊ + 1) := by
    rw [sub_pos, div_lt_one hpe]
    exact one_lt_pow₀ hp1 (by omega)
  rw [lcmFactor_eq x p hp, Real.log_mul (by positivity) (ne_of_gt h2)]

/-- **Step 2 of Lemma T.**  Euler's divisor-sum identity for `N = lcm(1..⌊x⌋₊)` in
logarithmic form: `log (σ(N)/N) = logRatioSum x − lcmCorr x`. -/
theorem log_sigma_ratio_eq (x : ℝ) :
    Real.log (((ArithmeticFunction.sigma 1 (Nat.lcmUpto ⌊x⌋₊) : ℕ) : ℝ) /
        (Nat.lcmUpto ⌊x⌋₊ : ℝ))
      = Commons.NumberTheory.Mertens.logRatioSum x - lcmCorr x := by
  have hprod := Commons.NumberTheory.Robin.sigma_ratio_prime_power_prod
      (n := Nat.lcmUpto ⌊x⌋₊) (Nat.lcmUpto_ne_zero ⌊x⌋₊)
  have hprod' : ((ArithmeticFunction.sigma 1 (Nat.lcmUpto ⌊x⌋₊) : ℕ) : ℝ) /
        (Nat.lcmUpto ⌊x⌋₊ : ℝ)
      = ∏ p ∈ Nat.primesLE ⌊x⌋₊, (((p : ℝ) ^ (Nat.log p ⌊x⌋₊ + 1) - 1) /
          ((p : ℝ) ^ (Nat.log p ⌊x⌋₊) * ((p : ℝ) - 1))) := by
    rw [hprod, Nat.primeFactors_lcmUpto]
    refine Finset.prod_congr rfl (fun p hp => ?_)
    rw [Nat.factorization_lcmUpto _ (Nat.prime_of_mem_primesLE hp)]
  have hne : ∀ p ∈ Nat.primesLE ⌊x⌋₊, (((p : ℝ) ^ (Nat.log p ⌊x⌋₊ + 1) - 1) /
          ((p : ℝ) ^ (Nat.log p ⌊x⌋₊) * ((p : ℝ) - 1))) ≠ 0 :=
    fun p hp => ne_of_gt (lcmFactor_pos x p (Nat.prime_of_mem_primesLE hp))
  have hneg : (∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log (1 - 1 / (p : ℝ) ^ (Nat.log p ⌊x⌋₊ + 1)))
      = - (∑ p ∈ Nat.primesLE ⌊x⌋₊,
            -Real.log (1 - 1 / (p : ℝ) ^ (Nat.log p ⌊x⌋₊ + 1))) := by
    rw [Finset.sum_neg_distrib]
    ring
  calc Real.log (((ArithmeticFunction.sigma 1 (Nat.lcmUpto ⌊x⌋₊) : ℕ) : ℝ) /
          (Nat.lcmUpto ⌊x⌋₊ : ℝ))
      = Real.log (∏ p ∈ Nat.primesLE ⌊x⌋₊, (((p : ℝ) ^ (Nat.log p ⌊x⌋₊ + 1) - 1) /
          ((p : ℝ) ^ (Nat.log p ⌊x⌋₊) * ((p : ℝ) - 1)))) := by rw [hprod']
    _ = ∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log ((((p : ℝ) ^ (Nat.log p ⌊x⌋₊ + 1) - 1) /
          ((p : ℝ) ^ (Nat.log p ⌊x⌋₊) * ((p : ℝ) - 1)))) := Real.log_prod hne
    _ = ∑ p ∈ Nat.primesLE ⌊x⌋₊, (Real.log ((p : ℝ) / ((p : ℝ) - 1))
          + Real.log (1 - 1 / (p : ℝ) ^ (Nat.log p ⌊x⌋₊ + 1))) :=
        Finset.sum_congr rfl (fun p hp => log_lcmFactor x p (Nat.prime_of_mem_primesLE hp))
    _ = (∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log ((p : ℝ) / ((p : ℝ) - 1)))
          + ∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log (1 - 1 / (p : ℝ) ^ (Nat.log p ⌊x⌋₊ + 1)) :=
        Finset.sum_add_distrib
    _ = Commons.NumberTheory.Mertens.logRatioSum x - lcmCorr x := by
        rw [Commons.NumberTheory.Mertens.logRatioSum, lcmCorr, hneg]
        ring

/-! ## Lemma T -/

theorem lcm_transfer (x : ℝ) (hx : 100 ≤ x) :
    Real.eulerMascheroniConstant + Real.log (Real.log (Real.log (Nat.lcmUpto ⌊x⌋₊)))
        - Work.RHContract.psiTail x - 5 / Real.sqrt x
      ≤ Real.log (((ArithmeticFunction.sigma 1 (Nat.lcmUpto ⌊x⌋₊) : ℕ) : ℝ) /
          (Nat.lcmUpto ⌊x⌋₊ : ℝ)) := by
  have hx2 : (2 : ℝ) ≤ x := by linarith
  have hlogN : Real.log (Nat.lcmUpto ⌊x⌋₊ : ℝ) = Chebyshev.psi x := by
    rw [Chebyshev.psi_eq_psi_coe_floor, Chebyshev.psi_eq_log_lcmUpto]
  have hC : Real.log (Real.log (Real.log (Nat.lcmUpto ⌊x⌋₊)))
      ≤ Real.log (Real.log x) + (Chebyshev.psi x - x) / (x * Real.log x) := by
    rw [hlogN]
    exact log_log_le_log_log_add (Chebyshev.psi x) x (by linarith) (psi_gt_one x hx)
  have hB : Real.log (((ArithmeticFunction.sigma 1 (Nat.lcmUpto ⌊x⌋₊) : ℕ) : ℝ) /
        (Nat.lcmUpto ⌊x⌋₊ : ℝ))
      = Commons.NumberTheory.Mertens.logRatioSum x - lcmCorr x := log_sigma_ratio_eq x
  have hI := Work.RHContract.Identity.logRatioSum_eq_psiTail x hx2
  have hD : lcmCorr x ≤ 5 / Real.sqrt x := lcmCorr_le x hx
  have hE : 0 ≤ Work.RHContract.primeTail x := Work.RHContract.Identity.primeTail_nonneg x hx2
  rw [hB, hI]
  linarith

end Work.RHContract.B

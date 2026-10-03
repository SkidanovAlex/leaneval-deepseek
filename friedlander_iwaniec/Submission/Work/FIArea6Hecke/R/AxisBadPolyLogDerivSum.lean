/-
# `Submission.Work.FIArea6Hecke.R.AxisBadPolyLogDerivSum`

The logarithmic derivative of the bad-prime correction
`axisBadPoly d s = ∏_{p ∣ 4d}(1-p^{-s})(1-χ₄(p)p^{-s})` (from `R/AxisLogDefs.lean`) splits as the
sum over the primes `p ∣ 4d` of the logarithmic derivatives of its two elementary factors:

  `G_d'/G_d (s) = Σ_{p ∣ 4d} ( logDeriv (1-p^{-·}) s + logDeriv (1-χ₄(p)p^{-·}) s )`

for `re s > 1`.  This is the elementary `Submission.Port.logDeriv_prod_fun` / `Submission.Port.logDeriv_mul_fun` identity together with the
non-vanishing of each factor on the half-plane `re s > 1` (there `‖χ₄(p)p^{-s}‖ < 1`, so neither
`1 - p^{-s}` nor `1 - χ₄(p)p^{-s}` can vanish).
-/
import Mathlib
import Submission.Work.FIArea6Hecke.R.AxisLogDefs
import Submission.Port.LogDerivCompat

set_option autoImplicit false

namespace Work.FIArea6Hecke.R

open scoped BigOperators

noncomputable section

/-! ## Non-vanishing of the two elementary factors on `re s > 1` -/

/-- `1 - p^{-s} ≠ 0` for a prime `p` and `re s > 1`. -/
lemma axisBadPoly_one_sub_cpow_neg_ne_zero {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 1 < s.re) :
    (1 : ℂ) - (p : ℂ) ^ (-s) ≠ 0 := by
  rw [sub_ne_zero]
  exact (natCast_cpow_neg_ne_one hp.one_lt hs).symm

/-- `1 - χ₄(p)p^{-s} ≠ 0` for a prime `p` and `re s > 1`; indeed `‖χ₄(p)p^{-s}‖ ≤ p^{-re s} < 1`. -/
lemma axisBadPoly_one_sub_chi4_cpow_neg_ne_zero {p : ℕ} (hp : p.Prime) {s : ℂ}
    (hs : 1 < s.re) : (1 : ℂ) - axisChi4 p * (p : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have h1 : axisChi4 p * (p : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp h).symm
  have hnorm : ‖axisChi4 p * (p : ℂ) ^ (-s)‖ = 1 := by rw [h1]; simp
  have hp1 : 1 < p := hp.one_lt
  have hle : ‖axisChi4 p * (p : ℂ) ^ (-s)‖ ≤ (p : ℝ) ^ (-s.re) := by
    rw [norm_mul]
    calc ‖axisChi4 p‖ * ‖(p : ℂ) ^ (-s)‖ ≤ 1 * ‖(p : ℂ) ^ (-s)‖ :=
          mul_le_mul_of_nonneg_right (axisChi4_norm_le_one p) (norm_nonneg _)
      _ = ‖(p : ℂ) ^ (-s)‖ := one_mul _
      _ = (p : ℝ) ^ (-s.re) := by
          rw [Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]
  have hlt : (p : ℝ) ^ (-s.re) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp1) (by linarith)
  linarith

/-! ## Differentiability of the two elementary factors -/

lemma axisBadPoly_diff_one_sub_cpow_neg (p : ℕ) (hp : p ≠ 0) (s : ℂ) :
    DifferentiableAt ℂ (fun u : ℂ => (1 : ℂ) - (p : ℂ) ^ (-u)) s :=
  (differentiableAt_const (1 : ℂ)).sub
    (differentiableAt_cpow_neg_of_ne_zero (p : ℂ) (Nat.cast_ne_zero.mpr hp) s)

lemma axisBadPoly_diff_one_sub_chi4_cpow_neg (p : ℕ) (hp : p ≠ 0) (s : ℂ) :
    DifferentiableAt ℂ (fun u : ℂ => (1 : ℂ) - axisChi4 p * (p : ℂ) ^ (-u)) s :=
  (differentiableAt_const (1 : ℂ)).sub
    ((differentiableAt_const (axisChi4 p)).mul
      (differentiableAt_cpow_neg_of_ne_zero (p : ℂ) (Nat.cast_ne_zero.mpr hp) s))

/-- The logarithmic derivative of the bad-prime correction is the sum of the logarithmic
derivatives of its two elementary factors, over the primes dividing `4d`. -/
theorem AxisBadPolyLogDerivSum (d : ℕ) {s : ℂ} (hs : 1 < s.re) :
    logDeriv (Work.FIArea6Hecke.R.axisBadPoly d) s
      = ∑ p ∈ (4 * d).primeFactors,
          (logDeriv (fun u : ℂ => (1 : ℂ) - (p : ℂ) ^ (-u)) s
            + logDeriv (fun u : ℂ => (1 : ℂ) - Work.FIArea6Hecke.R.axisChi4 p * (p : ℂ) ^ (-u)) s) := by
  have hfun : axisBadPoly d
      = fun z : ℂ => ∏ p ∈ (4 * d).primeFactors,
          (1 - (p : ℂ) ^ (-z)) * (1 - axisChi4 p * (p : ℂ) ^ (-z)) := by
    funext z; rfl
  rw [hfun, Submission.Port.logDeriv_prod_fun]
  · refine Finset.sum_congr rfl fun p hp => ?_
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    rw [Submission.Port.logDeriv_mul_fun s (axisBadPoly_one_sub_cpow_neg_ne_zero hpp hs)
      (axisBadPoly_one_sub_chi4_cpow_neg_ne_zero hpp hs)
      (axisBadPoly_diff_one_sub_cpow_neg p hpp.ne_zero s)
      (axisBadPoly_diff_one_sub_chi4_cpow_neg p hpp.ne_zero s)]
  · intro p hp
    exact mul_ne_zero (axisBadPoly_one_sub_cpow_neg_ne_zero
        (Nat.prime_of_mem_primeFactors hp) hs)
      (axisBadPoly_one_sub_chi4_cpow_neg_ne_zero (Nat.prime_of_mem_primeFactors hp) hs)
  · intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    exact (axisBadPoly_diff_one_sub_cpow_neg p hpp.ne_zero s).mul
      (axisBadPoly_diff_one_sub_chi4_cpow_neg p hpp.ne_zero s)

end

end Work.FIArea6Hecke.R

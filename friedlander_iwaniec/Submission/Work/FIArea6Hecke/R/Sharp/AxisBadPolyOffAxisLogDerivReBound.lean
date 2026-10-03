import Mathlib
import Submission.Work.FIArea6Hecke.R.AxisLogDefs
import Submission.Work.FIArea6Hecke.R.norm_logDeriv_one_sub_mul_cpow_le
import Submission.Work.FIArea6Hecke.R.sum_log_primes_le
import Submission.Port.LogDerivCompat

/-!
# Off-axis real-part bound for the logarithmic derivative of `axisBadPoly`

`axisBadPoly d s = ∏_{p ∣ 4d} (1 - p^{-s})(1 - χ₄(p)p^{-s})` is the finite bad-prime
correction in the factorisation `L(s,1) = ζ(s)·L(s,χ₄)·G_d(s)` of the principal Hecke
`L`-function of `ℚ(i)`.  Here we prove that for `1 < σ ≤ 2`, `d ≥ 1` and any `τ ∈ ℝ`

`-Re (G_d'/G_d)(σ + iτ) ≤ C · log(4d)`

with an absolute constant `C = 3`.  The logarithmic derivative of the product is the sum of
the logarithmic derivatives of the local factors `1 - c·p^{-s}`; for `re s > 1` and `‖c‖ ≤ 1`
one has `‖c·p^{-s}‖ ≤ 1/2`, so that `‖(c p^{-s})/(1 - c p^{-s})‖ ≤ 4/3` and each local term is
at most `(4/3)·log p` in modulus.  Summing over the (at most two) local factors of each of the
distinct primes dividing `4d` and using that the product of those primes divides `4d` (so that
`∑ log p ≤ log(4d)`) gives the bound `8/3 · log(4d) ≤ 3 · log(4d)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.FIArea6Hecke.R.Sharp

open Work.FIArea6Hecke.R
open scoped BigOperators

noncomputable section

/-- `‖c * p^{-s}‖ ≤ 1/2` for `p ≥ 2`, `1 < re s` and `‖c‖ ≤ 1`. -/
private lemma norm_mul_cpow_neg_le_half {c : ℂ} {p : ℕ} {s : ℂ} (hp : 2 ≤ p)
    (hs : 1 < s.re) (hc : ‖c‖ ≤ 1) : ‖c * (p : ℂ) ^ (-s)‖ ≤ 1 / 2 := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos (n := p) (by omega) (-s), Complex.neg_re]
  have h1 : ‖c‖ * (p : ℝ) ^ (-s.re) ≤ 1 * (p : ℝ) ^ (-s.re) :=
    mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hp0.le _)
  rw [one_mul] at h1
  refine le_trans h1 ?_
  have hle : (p : ℝ) ^ (-s.re) ≤ (p : ℝ) ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  refine le_trans hle ?_
  rw [Real.rpow_neg_one, inv_eq_one_div]
  exact one_div_le_one_div_of_le (by norm_num) hp2

/-- The local factor `1 - c·p^{-s}` does not vanish when `‖c·p^{-s}‖ ≤ 1/2`. -/
private lemma one_sub_ne_zero_of_norm_le_half {c : ℂ} {p : ℕ} {s : ℂ}
    (h : ‖c * (p : ℂ) ^ (-s)‖ ≤ 1 / 2) : (1 : ℂ) - c * (p : ℂ) ^ (-s) ≠ 0 := by
  intro h0
  have h1 : c * (p : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp h0).symm
  have hnorm : ‖c * (p : ℂ) ^ (-s)‖ = 1 := by rw [h1]; simp
  linarith [h, hnorm]

/-- The logarithmic derivative of `axisBadPoly d` is the sum of the logarithmic derivatives of
its local factors. -/
private lemma logDeriv_axisBadPoly_eq_sum (d : ℕ) {s : ℂ} (hs : 1 < s.re) :
    logDeriv (axisBadPoly d) s
      = ∑ p ∈ (4 * d).primeFactors,
          (logDeriv (fun u : ℂ => (1 : ℂ) - (p : ℂ) ^ (-u)) s
            + logDeriv (fun u : ℂ => (1 : ℂ) - axisChi4 p * (p : ℂ) ^ (-u)) s) := by
  have hone : ∀ p ∈ (4 * d).primeFactors, (fun u : ℂ => (1 : ℂ) - (p : ℂ) ^ (-u)) s ≠ 0 := by
    intro p hp
    obtain ⟨hpp, -, -⟩ := Nat.mem_primeFactors.mp hp
    simpa only [one_mul] using one_sub_ne_zero_of_norm_le_half
      (norm_mul_cpow_neg_le_half (c := (1 : ℂ)) hpp.two_le hs (by simp))
  have hchi : ∀ p ∈ (4 * d).primeFactors,
      (fun u : ℂ => (1 : ℂ) - axisChi4 p * (p : ℂ) ^ (-u)) s ≠ 0 := by
    intro p hp
    obtain ⟨hpp, -, -⟩ := Nat.mem_primeFactors.mp hp
    exact one_sub_ne_zero_of_norm_le_half
      (norm_mul_cpow_neg_le_half (c := axisChi4 p) hpp.two_le hs (axisChi4_norm_le_one p))
  have hd1 : ∀ p ∈ (4 * d).primeFactors,
      DifferentiableAt ℂ (fun u : ℂ => (1 : ℂ) - (p : ℂ) ^ (-u)) s := by
    intro p hp
    obtain ⟨hpp, -, -⟩ := Nat.mem_primeFactors.mp hp
    exact (differentiableAt_const (1 : ℂ)).sub
      (differentiableAt_cpow_neg_of_ne_zero (p : ℂ) (by exact_mod_cast hpp.ne_zero) s)
  have hd2 : ∀ p ∈ (4 * d).primeFactors, DifferentiableAt ℂ
      (fun u : ℂ => (1 : ℂ) - axisChi4 p * (p : ℂ) ^ (-u)) s := by
    intro p hp
    obtain ⟨hpp, -, -⟩ := Nat.mem_primeFactors.mp hp
    exact (differentiableAt_const (1 : ℂ)).sub ((differentiableAt_const (axisChi4 p)).mul
      (differentiableAt_cpow_neg_of_ne_zero (p : ℂ) (by exact_mod_cast hpp.ne_zero) s))
  have hne : ∀ p ∈ (4 * d).primeFactors,
      (fun u : ℂ => ((1 : ℂ) - (p : ℂ) ^ (-u))
        * ((1 : ℂ) - axisChi4 p * (p : ℂ) ^ (-u))) s ≠ 0 :=
    fun p hp => mul_ne_zero (hone p hp) (hchi p hp)
  have hdiff : ∀ p ∈ (4 * d).primeFactors,
      DifferentiableAt ℂ (fun u : ℂ => ((1 : ℂ) - (p : ℂ) ^ (-u))
        * ((1 : ℂ) - axisChi4 p * (p : ℂ) ^ (-u))) s :=
    fun p hp => (hd1 p hp).mul (hd2 p hp)
  have hprod := Submission.Port.logDeriv_prod_fun (s := (4 * d).primeFactors)
    (f := fun p u => ((1 : ℂ) - (p : ℂ) ^ (-u))
      * ((1 : ℂ) - axisChi4 p * (p : ℂ) ^ (-u))) (x := s) hne hdiff
  have hfun : axisBadPoly d = (fun u : ℂ => ∏ p ∈ (4 * d).primeFactors,
      (((1 : ℂ) - (p : ℂ) ^ (-u)) * ((1 : ℂ) - axisChi4 p * (p : ℂ) ^ (-u)))) := by
    funext u
    simp only [axisBadPoly]
  rw [hfun, hprod]
  refine Finset.sum_congr rfl fun p hp => ?_
  exact Submission.Port.logDeriv_mul_fun (f := fun u : ℂ => (1 : ℂ) - (p : ℂ) ^ (-u))
    (g := fun u : ℂ => (1 : ℂ) - axisChi4 p * (p : ℂ) ^ (-u)) s
      (hone p hp) (hchi p hp) (hd1 p hp) (hd2 p hp)

/-- Modulus bound for the logarithmic derivative of `axisBadPoly d` in the strip `1 < re s`. -/
private lemma logDeriv_axisBadPoly_re_le (d : ℕ) (hd : 1 ≤ d) {s : ℂ} (hs : 1 < s.re) :
    |(logDeriv (axisBadPoly d) s).re| ≤ (8 / 3) * Real.log (4 * (d : ℝ)) := by
  have hsum : ∑ p ∈ (4 * d).primeFactors, Real.log p ≤ Real.log (4 * (d : ℝ)) := by
    apply sum_log_primes_le d ((4 * d).primeFactors) hd
    intro p hp
    obtain ⟨hpp, hdvd, -⟩ := Nat.mem_primeFactors.mp hp
    exact ⟨hpp, hdvd⟩
  rw [logDeriv_axisBadPoly_eq_sum d hs]
  have hterm : ∀ p ∈ (4 * d).primeFactors,
      ‖logDeriv (fun u : ℂ => (1 : ℂ) - (p : ℂ) ^ (-u)) s
        + logDeriv (fun u : ℂ => (1 : ℂ) - axisChi4 p * (p : ℂ) ^ (-u)) s‖
      ≤ (8 / 3) * Real.log p := by
    intro p hp
    obtain ⟨hpp, -, -⟩ := Nat.mem_primeFactors.mp hp
    have h1 : ‖logDeriv (fun u : ℂ => (1 : ℂ) - (p : ℂ) ^ (-u)) s‖
        ≤ (4 / 3) * Real.log p := by
      simpa only [one_mul] using norm_logDeriv_one_sub_mul_cpow_le (c := (1 : ℂ)) hpp.two_le
        (Or.inl (norm_mul_cpow_neg_le_half (c := (1 : ℂ)) hpp.two_le hs (by simp)))
    have h2 : ‖logDeriv (fun u : ℂ => (1 : ℂ) - axisChi4 p * (p : ℂ) ^ (-u)) s‖
        ≤ (4 / 3) * Real.log p :=
      norm_logDeriv_one_sub_mul_cpow_le (c := axisChi4 p) hpp.two_le
        (Or.inl (norm_mul_cpow_neg_le_half hpp.two_le hs (axisChi4_norm_le_one p)))
    calc ‖logDeriv (fun u : ℂ => (1 : ℂ) - (p : ℂ) ^ (-u)) s
          + logDeriv (fun u : ℂ => (1 : ℂ) - axisChi4 p * (p : ℂ) ^ (-u)) s‖
        ≤ ‖logDeriv (fun u : ℂ => (1 : ℂ) - (p : ℂ) ^ (-u)) s‖
          + ‖logDeriv (fun u : ℂ => (1 : ℂ) - axisChi4 p * (p : ℂ) ^ (-u)) s‖ :=
          norm_add_le _ _
      _ ≤ (8 / 3) * Real.log p := by linarith
  calc |(∑ p ∈ (4 * d).primeFactors,
          (logDeriv (fun u : ℂ => (1 : ℂ) - (p : ℂ) ^ (-u)) s
            + logDeriv (fun u : ℂ => (1 : ℂ) - axisChi4 p * (p : ℂ) ^ (-u)) s)).re|
      ≤ ‖∑ p ∈ (4 * d).primeFactors,
          (logDeriv (fun u : ℂ => (1 : ℂ) - (p : ℂ) ^ (-u)) s
            + logDeriv (fun u : ℂ => (1 : ℂ) - axisChi4 p * (p : ℂ) ^ (-u)) s)‖ :=
        Complex.abs_re_le_norm _
    _ ≤ ∑ p ∈ (4 * d).primeFactors,
          ‖logDeriv (fun u : ℂ => (1 : ℂ) - (p : ℂ) ^ (-u)) s
            + logDeriv (fun u : ℂ => (1 : ℂ) - axisChi4 p * (p : ℂ) ^ (-u)) s‖ :=
        norm_sum_le _ _
    _ ≤ ∑ p ∈ (4 * d).primeFactors, (8 / 3) * Real.log p := Finset.sum_le_sum hterm
    _ = (8 / 3) * ∑ p ∈ (4 * d).primeFactors, Real.log p := by rw [Finset.mul_sum]
    _ ≤ (8 / 3) * Real.log (4 * (d : ℝ)) := mul_le_mul_of_nonneg_left hsum (by norm_num)

theorem AxisBadPolyOffAxisLogDerivReBound :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ), 1 ≤ d → ∀ σ τ : ℝ, 1 < σ → σ ≤ 2 →
      (-deriv (Work.FIArea6Hecke.R.axisBadPoly d) ((σ : ℂ) + (τ : ℂ) * Complex.I)
        / Work.FIArea6Hecke.R.axisBadPoly d ((σ : ℂ) + (τ : ℂ) * Complex.I)).re
        ≤ C * Real.log (4 * (d : ℝ)) := by
  refine ⟨3, by norm_num, ?_⟩
  intro d hd σ τ hσ1 hσ2
  set s : ℂ := (σ : ℂ) + (τ : ℂ) * Complex.I with hsdef
  have hsre : 1 < s.re := by
    have hsr : s.re = σ := by rw [hsdef]; simp
    rw [hsr]; exact hσ1
  have hlog4d : 0 ≤ Real.log (4 * (d : ℝ)) := by
    apply Real.log_nonneg
    have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hmain := logDeriv_axisBadPoly_re_le d hd hsre
  have h1 : (-deriv (axisBadPoly d) s / axisBadPoly d s).re
      = -(logDeriv (axisBadPoly d) s).re := by
    rw [logDeriv_apply, neg_div, Complex.neg_re]
  rw [h1]
  exact le_trans (le_trans (neg_le_abs _) hmain) (by linarith only [hlog4d])

end

end Work.FIArea6Hecke.R.Sharp

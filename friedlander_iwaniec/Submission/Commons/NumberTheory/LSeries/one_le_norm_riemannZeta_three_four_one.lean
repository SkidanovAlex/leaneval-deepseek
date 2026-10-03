import Mathlib

noncomputable section

open Complex Filter
open scoped BigOperators Topology

namespace Commons.NumberTheory.LSeries

/-!
# The `(3,4,1)` inequality for the Riemann zeta function

For `σ > 1` and every real `t`,

    |ζ(σ)|³ · |ζ(σ + i t)|⁴ · |ζ(σ + 2 i t)| ≥ 1.

This is the classical "3-4-1" inequality, which follows from the Euler product
together with the elementary trigonometric identity
`3 + 4 cos θ + cos 2θ = 2 (1 + cos θ)² ≥ 0`.
-/

/-! ## A per-prime Euler-factor inequality -/

/-- For `‖w‖ < 1`, the real parts of the Taylor series of `-log (1 - w)` sum
to `-log ‖1 - w‖`. -/
private lemma hasSum_re_negLog (w : ℂ) (hw : ‖w‖ < 1) :
    HasSum (fun n : ℕ => (w ^ (n + 1) / ((n : ℂ) + 1)).re) (-Real.log ‖1 - w‖) := by
  have h := Complex.hasSum_re (Complex.hasSum_taylorSeries_neg_log' (z := w) hw)
  rwa [show (-Complex.log (1 - w)).re = -Real.log ‖1 - w‖ by
    rw [Complex.neg_re, Complex.log_re]] at h

/-- Real part of the `K`-th term of the Taylor series of `-log (1 - x)` at a real
`x ≥ 0`. -/
private lemma re_pow_div_real (x : ℝ) (K : ℕ) :
    (((x : ℂ) ^ K / ((K : ℕ) : ℂ))).re = x ^ K * ((K : ℝ))⁻¹ := by
  have h : ((x : ℂ) ^ K / ((K : ℕ) : ℂ)).re = x ^ K / (K : ℝ) := by
    rw [show ((K : ℕ) : ℂ) = ((K : ℝ) : ℂ) by norm_num]
    rw [← Complex.ofReal_pow, ← Complex.ofReal_div, Complex.ofReal_re]
  rw [h, div_eq_mul_inv]

/-- Real part of the `K`-th term of the Taylor series of `-log (1 - x z)`. -/
private lemma re_mul_pow_div (x : ℝ) (z : ℂ) (K : ℕ) :
    ((((x : ℂ) * z) ^ K / ((K : ℕ) : ℂ))).re = x ^ K * ((K : ℝ))⁻¹ * (z ^ K).re := by
  have h : ((x : ℂ) * z) ^ K / ((K : ℕ) : ℂ)
      = (((x ^ K * ((K : ℝ))⁻¹ : ℝ)) : ℂ) * z ^ K := by
    have hcast : ((K : ℕ) : ℂ) = (((K : ℝ)) : ℂ) := by norm_num
    rw [hcast, div_eq_mul_inv, mul_pow]
    rw [show ((x : ℂ) ^ K * z ^ K) * ((((K : ℝ)) : ℂ))⁻¹
        = ((x : ℂ) ^ K * ((((K : ℝ)) : ℂ))⁻¹) * z ^ K by ring]
    rw [← Complex.ofReal_pow, ← Complex.ofReal_inv, ← Complex.ofReal_mul]
  rw [h, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- Real part of the `K`-th term of the Taylor series of `-log (1 - x z²)`. -/
private lemma re_mul_sq_pow_div (x : ℝ) (z : ℂ) (K : ℕ) :
    ((((x : ℂ) * z ^ 2) ^ K / ((K : ℕ) : ℂ))).re = x ^ K * ((K : ℝ))⁻¹ * ((z ^ K) ^ 2).re := by
  have hz2 : ((x : ℂ) * z ^ 2) ^ K = (x : ℂ) ^ K * (z ^ K) ^ 2 := by
    rw [mul_pow]
    congr 1
    rw [← pow_mul z 2 K, ← pow_mul z K 2, Nat.mul_comm]
  have h : ((x : ℂ) * z ^ 2) ^ K / ((K : ℕ) : ℂ)
      = (((x ^ K * ((K : ℝ))⁻¹ : ℝ)) : ℂ) * (z ^ K) ^ 2 := by
    have hcast : ((K : ℕ) : ℂ) = (((K : ℝ)) : ℂ) := by norm_num
    rw [hz2, hcast, div_eq_mul_inv, mul_assoc]
    rw [show (x : ℂ) ^ K * ((z ^ K) ^ 2 * ((((K : ℝ)) : ℂ))⁻¹)
        = ((x : ℂ) ^ K * ((((K : ℝ)) : ℂ))⁻¹) * (z ^ K) ^ 2 by ring]
    rw [← Complex.ofReal_pow, ← Complex.ofReal_inv, ← Complex.ofReal_mul]
  rw [h, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- `exp (-log a) = a⁻¹` for `a > 0`. -/
private lemma exp_neg_log {a : ℝ} (ha : 0 < a) : Real.exp (-Real.log a) = a⁻¹ := by
  rw [Real.exp_neg, Real.exp_log ha]

/-- **Per-prime `(3,4,1)` Euler factor bound.**
For `0 ≤ x < 1` and `‖z‖ = 1`,

    |1 - x|⁻³ · |1 - x z|⁻⁴ · |1 - x z²|⁻¹ ≥ 1.

It is the statement `3(-log|1-x|) + 4(-log|1-xz|) + (-log|1-xz²|) ≥ 0`, obtained
by summing the nonnegative Taylor terms
`(x^n/n) · (3 + 4 Re z^n + Re z^{2n}) = 2 (x^n/n) (1 + Re z^n)²`. -/
private lemma euler_factor_bound {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) {z : ℂ} (hz : ‖z‖ = 1) :
    1 ≤ ‖(1 - (x : ℂ))⁻¹‖ ^ 3 * ‖(1 - (x : ℂ) * z)⁻¹‖ ^ 4
          * ‖(1 - (x : ℂ) * z ^ 2)⁻¹‖ := by
  have hxnorm : ‖(x : ℂ)‖ = x := by
    have := RCLike.norm_ofReal (K := ℂ) x
    rwa [abs_of_nonneg hx0] at this
  have hw1 : ‖(x : ℂ)‖ < 1 := by rw [hxnorm]; exact hx1
  have hw2 : ‖(x : ℂ) * z‖ < 1 := by rw [norm_mul, hxnorm, hz, mul_one]; exact hx1
  have hw3 : ‖(x : ℂ) * z ^ 2‖ < 1 := by
    rw [norm_mul, hxnorm, norm_pow, hz, one_pow, mul_one]; exact hx1
  have h1 := hasSum_re_negLog ((x : ℂ)) hw1
  have h2 := hasSum_re_negLog ((x : ℂ) * z) hw2
  have h3 := hasSum_re_negLog ((x : ℂ) * z ^ 2) hw3
  have hcomb := ((h1.mul_left 3).add (h2.mul_left 4)).add h3
  have hterm_nonneg : ∀ n : ℕ, 0 ≤ 3 * (((x : ℂ) ^ (n + 1) / ((n : ℂ) + 1)).re)
      + 4 * ((((x : ℂ) * z) ^ (n + 1) / ((n : ℂ) + 1)).re)
      + ((((x : ℂ) * z ^ 2) ^ (n + 1) / ((n : ℂ) + 1)).re) := by
    intro n
    have hden : ((n : ℂ) + 1) = (((n + 1 : ℕ)) : ℂ) := by push_cast; ring
    rw [hden, re_pow_div_real, re_mul_pow_div, re_mul_sq_pow_div]
    have hnorm : ‖z ^ (n + 1)‖ = 1 := by rw [norm_pow, hz, one_pow]
    have hsq : ((z ^ (n + 1)).re) ^ 2 + ((z ^ (n + 1)).im) ^ 2 = 1 := by
      have h1 : ‖z ^ (n + 1)‖ ^ 2 = 1 := by rw [hnorm]; norm_num
      rw [Complex.sq_norm, Complex.normSq_apply] at h1
      rw [← h1]; ring
    have hre2 : ((z ^ (n + 1)) ^ 2).re = 2 * ((z ^ (n + 1)).re) ^ 2 - 1 := by
      rw [pow_two, Complex.mul_re]; nlinarith [hsq]
    rw [hre2]
    have hX : 0 ≤ x ^ (n + 1) * (((n + 1 : ℕ)) : ℝ)⁻¹ :=
      mul_nonneg (pow_nonneg hx0 _) (inv_nonneg.mpr (by positivity))
    have heq : 3 * (x ^ (n + 1) * (((n + 1 : ℕ)) : ℝ)⁻¹)
        + 4 * (x ^ (n + 1) * (((n + 1 : ℕ)) : ℝ)⁻¹ * (z ^ (n + 1)).re)
        + (x ^ (n + 1) * (((n + 1 : ℕ)) : ℝ)⁻¹ * (2 * ((z ^ (n + 1)).re) ^ 2 - 1))
        = 2 * (x ^ (n + 1) * (((n + 1 : ℕ)) : ℝ)⁻¹) * ((z ^ (n + 1)).re + 1) ^ 2 := by ring
    rw [heq]
    exact mul_nonneg (mul_nonneg (by norm_num) hX) (sq_nonneg _)
  have hA : 0 ≤ 3 * (-Real.log ‖1 - (x : ℂ)‖) + 4 * (-Real.log ‖1 - (x : ℂ) * z‖)
      + (-Real.log ‖1 - (x : ℂ) * z ^ 2‖) := by
    rw [← hcomb.tsum_eq]
    exact tsum_nonneg hterm_nonneg
  have hpos1 : 0 < ‖1 - (x : ℂ)‖ := by
    rw [norm_pos_iff]
    intro hzero
    have h1 : (1 : ℝ) - x = 0 := by
      have := congrArg Complex.re hzero
      simpa using this
    linarith
  have hpos2 : 0 < ‖1 - (x : ℂ) * z‖ := by
    rw [norm_pos_iff]
    intro hzero
    have hz1 : ‖(x : ℂ) * z‖ = 1 := by
      rw [← sub_eq_zero.mp hzero]; simp
    rw [norm_mul, hxnorm, hz, mul_one] at hz1
    linarith
  have hpos3 : 0 < ‖1 - (x : ℂ) * z ^ 2‖ := by
    rw [norm_pos_iff]
    intro hzero
    have hz1 : ‖(x : ℂ) * z ^ 2‖ = 1 := by
      rw [← sub_eq_zero.mp hzero]; simp
    rw [norm_mul, hxnorm, norm_pow, hz, one_pow, mul_one] at hz1
    linarith
  have e1 : Real.exp (3 * (-Real.log ‖1 - (x : ℂ)‖)) = ‖(1 - (x : ℂ))⁻¹‖ ^ 3 := by
    rw [show (3 * (-Real.log ‖1 - (x : ℂ)‖)) = -(((3 : ℕ) : ℝ) * Real.log ‖1 - (x : ℂ)‖) by
      push_cast; ring]
    rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log hpos1, ← inv_pow, norm_inv]
  have e2 : Real.exp (4 * (-Real.log ‖1 - (x : ℂ) * z‖)) = ‖(1 - (x : ℂ) * z)⁻¹‖ ^ 4 := by
    rw [show (4 * (-Real.log ‖1 - (x : ℂ) * z‖)) = -(((4 : ℕ) : ℝ) * Real.log ‖1 - (x : ℂ) * z‖) by
      push_cast; ring]
    rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log hpos2, ← inv_pow, norm_inv]
  have e3 : Real.exp (-Real.log ‖1 - (x : ℂ) * z ^ 2‖) = ‖(1 - (x : ℂ) * z ^ 2)⁻¹‖ := by
    rw [exp_neg_log hpos3, norm_inv]
  have hexp : Real.exp (3 * (-Real.log ‖1 - (x : ℂ)‖) + 4 * (-Real.log ‖1 - (x : ℂ) * z‖)
      + (-Real.log ‖1 - (x : ℂ) * z ^ 2‖)) = ‖(1 - (x : ℂ))⁻¹‖ ^ 3 * ‖(1 - (x : ℂ) * z)⁻¹‖ ^ 4
          * ‖(1 - (x : ℂ) * z ^ 2)⁻¹‖ := by
    rw [Real.exp_add, Real.exp_add, e1, e2, e3]
  have hfinal : (1 : ℝ) ≤ Real.exp (3 * (-Real.log ‖1 - (x : ℂ)‖) + 4 * (-Real.log ‖1 - (x : ℂ) * z‖)
      + (-Real.log ‖1 - (x : ℂ) * z ^ 2‖)) := by
    rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr hA
  rwa [hexp] at hfinal

/-! ## Rewriting the complex powers of primes -/

private lemma cpow_neg_ofReal (p : ℕ) (σ : ℝ) :
    (p : ℂ) ^ (-(σ : ℂ)) = (((p : ℝ) ^ (-σ) : ℝ) : ℂ) := by
  have h : ((-σ : ℝ) : ℂ) = -(σ : ℂ) := by simp
  have h2 : (((p : ℝ) : ℂ)) = (p : ℂ) := by norm_num
  rw [← h, ← h2]
  exact (Complex.ofReal_cpow (Nat.cast_nonneg p) (-σ)).symm

private lemma cpow_neg_add_I (p : ℕ) (hp : 0 < p) (σ t : ℝ) :
    (p : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)) =
      (((p : ℝ) ^ (-σ) : ℝ) : ℂ) * (p : ℂ) ^ (-((t : ℂ) * Complex.I)) := by
  have hpne : (p : ℂ) ≠ 0 := by
    simp [Nat.cast_ne_zero.mpr (ne_of_gt hp)]
  have key := Complex.cpow_add (-(σ : ℂ)) (-((t : ℂ) * Complex.I)) hpne
  have he : -((σ : ℂ) + (t : ℂ) * Complex.I) = -(σ : ℂ) + (-((t : ℂ) * Complex.I)) := by ring
  rw [he, key]
  congr 1
  exact cpow_neg_ofReal p σ

private lemma cpow_neg_add_two_I (p : ℕ) (hp : 0 < p) (σ t : ℝ) :
    (p : ℂ) ^ (-((σ : ℂ) + 2 * (t : ℂ) * Complex.I)) =
      (((p : ℝ) ^ (-σ) : ℝ) : ℂ) * ((p : ℂ) ^ (-((t : ℂ) * Complex.I))) ^ 2 := by
  have hpne : (p : ℂ) ≠ 0 := by
    simp [Nat.cast_ne_zero.mpr (ne_of_gt hp)]
  have hnm := Complex.cpow_nat_mul (p : ℂ) 2 (-((t : ℂ) * Complex.I))
  have he2 : ((2 : ℕ) : ℂ) * (-((t : ℂ) * Complex.I)) = -(2 * ((t : ℂ) * Complex.I)) := by
    push_cast; ring
  rw [he2] at hnm
  have key := Complex.cpow_add (-(σ : ℂ)) (-(2 * ((t : ℂ) * Complex.I))) hpne
  have he : -((σ : ℂ) + 2 * (t : ℂ) * Complex.I) = -(σ : ℂ) + (-(2 * ((t : ℂ) * Complex.I))) := by
    ring
  rw [he, key, hnm]
  congr 1
  exact cpow_neg_ofReal p σ

/-! ## The main theorem -/

theorem one_le_norm_riemannZeta_three_four_one {σ t : ℝ} (hσ : 1 < σ) :
    1 ≤ ‖riemannZeta (σ : ℂ)‖ ^ 3 * ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 4
          * ‖riemannZeta ((σ : ℂ) + 2 * (t : ℂ) * Complex.I)‖ := by
  set s₁ : ℂ := (σ : ℂ) with hs₁
  set s₂ : ℂ := s₁ + (t : ℂ) * Complex.I with hs₂
  set s₃ : ℂ := s₁ + 2 * (t : ℂ) * Complex.I with hs₃
  have h1 : 1 < s₁.re := by rw [hs₁]; simpa using hσ
  have h2 : 1 < s₂.re := by rw [hs₂, hs₁]; simp; linarith
  have h3 : 1 < s₃.re := by rw [hs₃, hs₁]; simp; linarith
  let F1 : ℕ → ℂ := fun n => ∏ p ∈ Nat.primesBelow n, (1 - (p : ℂ) ^ (-s₁))⁻¹
  let F2 : ℕ → ℂ := fun n => ∏ p ∈ Nat.primesBelow n, (1 - (p : ℂ) ^ (-s₂))⁻¹
  let F3 : ℕ → ℂ := fun n => ∏ p ∈ Nat.primesBelow n, (1 - (p : ℂ) ^ (-s₃))⁻¹
  have t1 : Tendsto F1 atTop (𝓝 (riemannZeta s₁)) := by
    simpa [F1] using riemannZeta_eulerProduct (s := s₁) h1
  have t2 : Tendsto F2 atTop (𝓝 (riemannZeta s₂)) := by
    simpa [F2] using riemannZeta_eulerProduct (s := s₂) h2
  have t3 : Tendsto F3 atTop (𝓝 (riemannZeta s₃)) := by
    simpa [F3] using riemannZeta_eulerProduct (s := s₃) h3
  have hP : Tendsto (fun n => F1 n ^ 3 * F2 n ^ 4 * F3 n) atTop
      (𝓝 (riemannZeta s₁ ^ 3 * riemannZeta s₂ ^ 4 * riemannZeta s₃)) :=
    ((t1.pow 3).mul (t2.pow 4)).mul t3
  have hPn : ∀ n : ℕ, 1 ≤ ‖F1 n ^ 3 * F2 n ^ 4 * F3 n‖ := by
    intro n
    have hnorm : ‖F1 n ^ 3 * F2 n ^ 4 * F3 n‖
        = ∏ p ∈ Nat.primesBelow n,
            (‖(1 - (p : ℂ) ^ (-s₁))⁻¹‖ ^ 3 * ‖(1 - (p : ℂ) ^ (-s₂))⁻¹‖ ^ 4
              * ‖(1 - (p : ℂ) ^ (-s₃))⁻¹‖) := by
      simp only [F1, F2, F3, norm_mul, norm_pow, norm_prod]
      rw [← Finset.prod_pow, ← Finset.prod_pow]
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    rw [hnorm]
    refine Finset.one_le_prod₀ (fun p hp => ?_)
    have hpp : p.Prime := (Nat.mem_primesBelow.mp hp).2
    have hx0 : 0 ≤ (p : ℝ) ^ (-σ) := Real.rpow_nonneg (Nat.cast_nonneg p) _
    have hx1 : (p : ℝ) ^ (-σ) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hpp.one_lt) (by linarith)
    have hz : ‖(p : ℂ) ^ (-((t : ℂ) * Complex.I))‖ = 1 := by
      rw [Complex.norm_natCast_cpow_of_pos hpp.pos]
      simp
    have hb := euler_factor_bound hx0 hx1 hz
    have hc1 : (p : ℂ) ^ (-s₁) = (((p : ℝ) ^ (-σ) : ℝ) : ℂ) := by
      rw [hs₁]; exact cpow_neg_ofReal p σ
    have hc2 : (p : ℂ) ^ (-s₂) = (((p : ℝ) ^ (-σ) : ℝ) : ℂ)
        * (p : ℂ) ^ (-((t : ℂ) * Complex.I)) := by
      rw [hs₂, hs₁]; exact cpow_neg_add_I p hpp.pos σ t
    have hc3 : (p : ℂ) ^ (-s₃) = (((p : ℝ) ^ (-σ) : ℝ) : ℂ)
        * ((p : ℂ) ^ (-((t : ℂ) * Complex.I))) ^ 2 := by
      rw [hs₃, hs₁]; exact cpow_neg_add_two_I p hpp.pos σ t
    rw [hc1, hc2, hc3]
    exact hb
  have hlim := le_of_tendsto_of_tendsto' tendsto_const_nhds hP.norm hPn
  simpa only [norm_mul, norm_pow] using hlim

end Commons.NumberTheory.LSeries

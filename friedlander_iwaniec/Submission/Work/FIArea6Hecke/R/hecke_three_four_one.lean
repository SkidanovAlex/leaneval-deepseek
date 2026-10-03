/-
# `Work.FIArea6Hecke.R.hecke_three_four_one`

The classical `(3,4,1)` inequality for Hecke `L`-series of `ℚ(i)`:

  `1 ≤ |L(σ+it,ψ)|⁴ · |L(σ+2it,ψ²)| · |L(σ,1)|³`   for `σ > 1`,

where `ψ(z) = χ(z)(z/|z|)^m` is the Größencharacter attached to a character `χ` of
`(ℤ[i]/4dℤ[i])^*` extended by zero, and `L(·,1)` is the principal Hecke `L`-series
(`L(σ,1) = Σ_{n odd} r(n)n^{-σ}`, the odd part of `ζ_{ℚ(i)}`).

The proof is the standard one: the Euler products turn the product into a product over rational
primes of the local factors

  `|1-A T|^{-4}|1-A²T'|^{-1}(1-x)^{-3}`

(one factor for each Satake parameter `A` of `p`), and each such factor is `≥ 1` by the elementary
trigonometric inequality `3 + 4cos θ + cos 2θ = 2(1+cos θ)² ≥ 0` applied to the Taylor series of
`-log|1 - ·|`.  Taking finite Euler products and passing to the limit gives the result.
-/
import Mathlib
import Submission.Work.FIArea5.S16Hecke.Defs
import Submission.Work.FIArea5.S16Hecke.ThetaDefs
import Submission.Work.FIArea5.S16Hecke.heckeLam_localRec
import Submission.Work.FIArea5.S16Hecke.heckeLam_localInverse
import Submission.Work.FIArea5.S16Hecke.heckeLam_prime_eq_zero_of_ne_one_mod_four
import Submission.Work.FIArea5.S16Hecke.heckeLSeries_eulerProduct
import Submission.Work.FIArea5.S16Hecke.heckeLSeries_eulerProduct_hasProd

set_option maxHeartbeats 1000000

namespace Work.FIArea6Hecke.R

open Complex Filter
open scoped BigOperators Topology
open Work.FIArea5.S16Hecke
open Work.FIPlan

noncomputable section

/-! ## 1. The elementary per-prime analytic inequality

For `0 ≤ x < 1` and `‖z‖ ≤ 1` we have `1 ≤ (1-x)^{-3}|1-xz|^{-4}|1-xz²|^{-1}`.
This is the numerical content of `3 + 4 cos θ + cos 2θ ≥ 0`, read off the Taylor series of
`-log |1 - w| = Σ_n Re(w^n)/n`. -/

private lemma hasSum_re_negLog (w : ℂ) (hw : ‖w‖ < 1) :
    HasSum (fun n : ℕ => (w ^ (n + 1) / ((n : ℂ) + 1)).re) (-Real.log ‖1 - w‖) := by
  have h := Complex.hasSum_re (Complex.hasSum_taylorSeries_neg_log' (z := w) hw)
  rwa [show (-Complex.log (1 - w)).re = -Real.log ‖1 - w‖ by
    rw [Complex.neg_re, Complex.log_re]] at h

private lemma re_pow_div_real (x : ℝ) (K : ℕ) :
    (((x : ℂ) ^ K / ((K : ℕ) : ℂ))).re = x ^ K * ((K : ℝ))⁻¹ := by
  have h : ((x : ℂ) ^ K / ((K : ℕ) : ℂ)).re = x ^ K / (K : ℝ) := by
    rw [show ((K : ℕ) : ℂ) = ((K : ℝ) : ℂ) by norm_num]
    rw [← Complex.ofReal_pow, ← Complex.ofReal_div, Complex.ofReal_re]
  rw [h, div_eq_mul_inv]

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

private lemma exp_neg_log {a : ℝ} (ha : 0 < a) : Real.exp (-Real.log a) = a⁻¹ := by
  rw [Real.exp_neg, Real.exp_log ha]

/-- **The `(3,4,1)` local factor bound.**  For `0 ≤ x < 1` and `‖z‖ ≤ 1`,

  `1 ≤ (1-x)^{-3} · |1 - xz|^{-4} · |1 - xz²|^{-1}`.

It is the statement `3(-log|1-x|) + 4(-log|1-xz|) + (-log|1-xz²|) ≥ 0`, obtained by summing the
nonnegative Taylor terms `(x^n/n)·(3 + 4 Re(z^n) + Re(z^{2n}))`: writing `s = ‖z^n‖ ≤ 1` and
`a = Re(z^n)`, this term is `x^n/n·(3 + 4a + a² - b²) ≥ x^n/n·(2(a+1)²) ≥ 0`. -/
theorem local_three_four_one {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    1 ≤ ‖(1 - (x : ℂ))⁻¹‖ ^ 3 * ‖(1 - (x : ℂ) * z)⁻¹‖ ^ 4 * ‖(1 - (x : ℂ) * z ^ 2)⁻¹‖ := by
  have hxnorm : ‖(x : ℂ)‖ = x := by
    have := RCLike.norm_ofReal (K := ℂ) x
    rwa [abs_of_nonneg hx0] at this
  have hw1 : ‖(x : ℂ)‖ < 1 := by rw [hxnorm]; exact hx1
  have hw2 : ‖(x : ℂ) * z‖ < 1 := by
    rw [norm_mul, hxnorm]
    calc x * ‖z‖ ≤ x * 1 := mul_le_mul_of_nonneg_left hz hx0
      _ = x := mul_one x
      _ < 1 := hx1
  have hw3 : ‖(x : ℂ) * z ^ 2‖ < 1 := by
    rw [norm_mul, hxnorm, norm_pow]
    have hz2 : ‖z‖ ^ 2 ≤ 1 := by nlinarith [hz, norm_nonneg z]
    calc x * ‖z‖ ^ 2 ≤ x * 1 := mul_le_mul_of_nonneg_left hz2 hx0
      _ = x := by ring
      _ < 1 := hx1
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
    have hnorm : ‖z ^ (n + 1)‖ ≤ 1 := by
      rw [norm_pow]; exact pow_le_one₀ (norm_nonneg z) hz
    have hsq : ((z ^ (n + 1)).re) ^ 2 + ((z ^ (n + 1)).im) ^ 2 ≤ 1 := by
      have h1 : ‖z ^ (n + 1)‖ ^ 2 ≤ 1 := by nlinarith [hnorm, norm_nonneg (z ^ (n + 1))]
      rw [Complex.sq_norm, Complex.normSq_apply] at h1
      linarith [h1]
    have hre2 : ((z ^ (n + 1)) ^ 2).re = ((z ^ (n + 1)).re) ^ 2 - ((z ^ (n + 1)).im) ^ 2 := by
      rw [pow_two, Complex.mul_re]; ring
    rw [hre2]
    have hX : 0 ≤ x ^ (n + 1) * (((n + 1 : ℕ)) : ℝ)⁻¹ :=
      mul_nonneg (pow_nonneg hx0 _) (inv_nonneg.mpr (by positivity))
    have heq : 3 * (x ^ (n + 1) * (((n + 1 : ℕ)) : ℝ)⁻¹)
        + 4 * (x ^ (n + 1) * (((n + 1 : ℕ)) : ℝ)⁻¹ * (z ^ (n + 1)).re)
        + (x ^ (n + 1) * (((n + 1 : ℕ)) : ℝ)⁻¹ * (((z ^ (n + 1)).re) ^ 2 - ((z ^ (n + 1)).im) ^ 2))
        = (x ^ (n + 1) * (((n + 1 : ℕ)) : ℝ)⁻¹) *
          (2 * ((z ^ (n + 1)).re + 1) ^ 2 + (1 - ((z ^ (n + 1)).re) ^ 2 - ((z ^ (n + 1)).im) ^ 2)) := by
      ring
    rw [heq]
    refine mul_nonneg hX ?_
    nlinarith [sq_nonneg ((z ^ (n + 1)).re + 1), hsq]
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
    have hz1 : ‖(x : ℂ) * z‖ = 1 := by rw [← sub_eq_zero.mp hzero]; simp
    linarith [hw2]
  have hpos3 : 0 < ‖1 - (x : ℂ) * z ^ 2‖ := by
    rw [norm_pos_iff]
    intro hzero
    have hz1 : ‖(x : ℂ) * z ^ 2‖ = 1 := by rw [← sub_eq_zero.mp hzero]; simp
    linarith [hw3]
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
  have hfinal : (1 : ℝ) ≤ Real.exp (3 * (-Real.log ‖1 - (x : ℂ)‖)
      + 4 * (-Real.log ‖1 - (x : ℂ) * z‖) + (-Real.log ‖1 - (x : ℂ) * z ^ 2‖)) := by
    rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr hA
  rwa [hexp] at hfinal


/-! ## 2. The local Euler factors at a rational prime

For `p ≡ 1 (4)` the Satake parameters of `ψ = χ(·)(·/|·|)^k` are `ψ(π), ψ(π')` at the two primary
primes `π, π'` of norm `p`, and for `p ≡ 3 (4)` there is a single one, `ψ(-p)`, at the prime
`-p` of norm `p²`.  These are the closed forms of the Euler factor at `p`. -/

theorem heckeFp_split_eq (p : ℕ) (hp : p.Prime) (h4 : p % 4 = 1)
    (chi : GaussianInt → ℂ) (k : ℤ) (h1 : chi 1 = 1)
    (hmul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w)
    (hb : ∀ z : GaussianInt, ‖chi z‖ ≤ 1)
    (π π' : GaussianInt) (hπ : IsPrimary π) (hπ' : IsPrimary π')
    (hgπ : gnorm π = p) (hgπ' : gnorm π' = p)
    (hclass : ∀ ν z, IsPrimary z → gnorm z = p ^ ν →
      ∃! a, a ≤ ν ∧ z = π ^ a * π' ^ (ν - a))
    {s : ℂ} (hs : 1 < s.re) :
    (∑' e : ℕ, heckeLam chi k (p ^ e) / ((p : ℂ) ^ (e * s)))
      = (1 - psi chi k π * (p : ℂ) ^ (-s))⁻¹ *
        (1 - psi chi k π' * (p : ℂ) ^ (-s))⁻¹ := by
  set T : ℂ := (p : ℂ) ^ (-s) with hT
  have hTnorm : ‖T‖ < 1 := by
    rw [hT, Complex.norm_natCast_cpow_of_pos hp.pos, Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)
  have hterm : ∀ e : ℕ, heckeLam chi k (p ^ e) / ((p : ℂ) ^ (e * s))
      = heckeLam chi k (p ^ e) * T ^ e := by
    intro e
    rw [hT, Complex.cpow_nat_mul, div_eq_mul_inv, ← inv_pow, ← Complex.cpow_neg]
  have hloc := heckeLam_localInverse (chi := chi) (k := k) (p := p) hp hmul h1 hb
    (z := T) hTnorm
  have hgeo : ∀ ν : ℕ, heckeLam chi k (p ^ ν) = geo (psi chi k π) (psi chi k π') ν :=
    fun ν => heckeLam_splitSum chi k p hp.pos hmul h1 π π' hπ hπ' hgπ hgπ' hclass ν
  have hAB : heckeLam chi k p = psi chi k π + psi chi k π' := by
    have h := hgeo 1
    rw [pow_one, geo_one] at h
    exact h
  have hAB2 : heckeLam chi k (p ^ 2)
      = (psi chi k π) ^ 2 + psi chi k π * psi chi k π' + (psi chi k π') ^ 2 := by
    have h := hgeo 2
    rw [geo_two] at h
    exact h
  have hc : (heckeLam chi k p) ^ 2 - heckeLam chi k (p ^ 2) = psi chi k π * psi chi k π' := by
    rw [hAB, hAB2]; ring
  have hB : 1 - heckeLam chi k p * T + ((heckeLam chi k p) ^ 2 - heckeLam chi k (p ^ 2)) * T ^ 2
      = (1 - psi chi k π * T) * (1 - psi chi k π' * T) := by
    rw [hc, hAB]; ring
  have hinv : (∑' e : ℕ, heckeLam chi k (p ^ e) * T ^ e)
      = ((1 - psi chi k π * T) * (1 - psi chi k π' * T))⁻¹ := by
    have h' := hloc
    rw [hB] at h'
    exact eq_inv_of_mul_eq_one_left h'
  calc (∑' e : ℕ, heckeLam chi k (p ^ e) / ((p : ℂ) ^ (e * s)))
      = ∑' e : ℕ, heckeLam chi k (p ^ e) * T ^ e := tsum_congr hterm
    _ = ((1 - psi chi k π * T) * (1 - psi chi k π' * T))⁻¹ := hinv
    _ = (1 - psi chi k π * T)⁻¹ * (1 - psi chi k π' * T)⁻¹ := mul_inv _ _
    _ = (1 - psi chi k π * (p : ℂ) ^ (-s))⁻¹ *
          (1 - psi chi k π' * (p : ℂ) ^ (-s))⁻¹ := by rw [hT]

theorem heckeFp_inert_eq (p : ℕ) (hp : p.Prime) (h3 : p % 4 = 3)
    (chi : GaussianInt → ℂ) (k : ℤ) (h1 : chi 1 = 1)
    (hmul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w)
    (hb : ∀ z : GaussianInt, ‖chi z‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    (∑' e : ℕ, heckeLam chi k (p ^ e) / ((p : ℂ) ^ (e * s)))
      = (1 - psi chi k (-(p : GaussianInt)) * ((p : ℂ) ^ (-s)) ^ 2)⁻¹ := by
  obtain ⟨hq, -, hgq, hclass⟩ := inertPrimaryClass p hp h3
  set T : ℂ := (p : ℂ) ^ (-s) with hT
  have hTnorm : ‖T‖ < 1 := by
    rw [hT, Complex.norm_natCast_cpow_of_pos hp.pos, Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)
  have hterm : ∀ e : ℕ, heckeLam chi k (p ^ e) / ((p : ℂ) ^ (e * s))
      = heckeLam chi k (p ^ e) * T ^ e := by
    intro e
    rw [hT, Complex.cpow_nat_mul, div_eq_mul_inv, ← inv_pow, ← Complex.cpow_neg]
  have hloc := heckeLam_localInverse (chi := chi) (k := k) (p := p) hp hmul h1 hb
    (z := T) hTnorm
  have hg : ∀ ν : ℕ, heckeLam chi k (p ^ ν) = geoInert (psi chi k (-(p : GaussianInt))) ν :=
    fun ν => heckeLam_inertSum chi k p hp.pos hmul h1 (-(p : GaussianInt)) hq hgq hclass ν
  have hp1 : heckeLam chi k p = 0 := by
    have h := hg 1
    rw [pow_one] at h
    rw [h]
    simp [geoInert]
  have hp2 : heckeLam chi k (p ^ 2) = psi chi k (-(p : GaussianInt)) := by
    have h := hg 2
    rw [h]
    norm_num [geoInert]
  have hB : 1 - heckeLam chi k p * T + ((heckeLam chi k p) ^ 2 - heckeLam chi k (p ^ 2)) * T ^ 2
      = 1 - psi chi k (-(p : GaussianInt)) * T ^ 2 := by
    rw [hp1, hp2]; ring
  have hinv : (∑' e : ℕ, heckeLam chi k (p ^ e) * T ^ e)
      = (1 - psi chi k (-(p : GaussianInt)) * T ^ 2)⁻¹ := by
    have h' := hloc
    rw [hB] at h'
    exact eq_inv_of_mul_eq_one_left h'
  calc (∑' e : ℕ, heckeLam chi k (p ^ e) / ((p : ℂ) ^ (e * s)))
      = ∑' e : ℕ, heckeLam chi k (p ^ e) * T ^ e := tsum_congr hterm
    _ = (1 - psi chi k (-(p : GaussianInt)) * T ^ 2)⁻¹ := hinv
    _ = (1 - psi chi k (-(p : GaussianInt)) * ((p : ℂ) ^ (-s)) ^ 2)⁻¹ := by rw [hT]


/-! ## 3. Auxiliary facts about complex powers of natural numbers -/

private lemma natCast_cpow_neg_real (q : ℕ) (a : ℝ) :
    ((q : ℂ)) ^ (-(a : ℂ)) = ((((q : ℝ) ^ (-a)) : ℝ) : ℂ) := by
  have h := Complex.ofReal_cpow (Nat.cast_nonneg q) (-a)
  rw [show ((q : ℝ) : ℂ) = (q : ℂ) by simp, show ((-a : ℝ) : ℂ) = -(a : ℂ) by simp] at h
  exact h.symm

private lemma natCast_cpow_neg_add_real {q : ℕ} (hq : 0 < q) (a : ℝ) (w : ℂ) :
    ((q : ℂ)) ^ (-(a : ℂ) + w) = ((((q : ℝ) ^ (-a)) : ℝ) : ℂ) * ((q : ℂ)) ^ w := by
  rw [Complex.cpow_add _ _ (by simp [hq.ne']), natCast_cpow_neg_real]

private lemma norm_natCast_cpow_neg_mul_I {q : ℕ} (hq : 0 < q) (t : ℝ) :
    ‖((q : ℂ)) ^ (-((t : ℂ) * Complex.I))‖ = 1 := by
  rw [Complex.norm_natCast_cpow_of_pos hq]
  have h : (-((t : ℂ) * Complex.I)).re = 0 := by simp
  rw [h]; simp

/-- The `(3,4,1)` bound for one Satake parameter: if `‖A‖ ≤ 1`, `‖w‖ = 1` and `0 ≤ x < 1`, then
`1 ≤ (1-x)^{-3}|1 - A(xw)|^{-4}|1 - A²(xw²)|^{-1}`. -/
private lemma local_group {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) {A w : ℂ}
    (hA : ‖A‖ ≤ 1) (hw : ‖w‖ = 1) :
    1 ≤ ‖(1 - (x : ℂ))⁻¹‖ ^ 3 * ‖(1 - A * ((x : ℂ) * w))⁻¹‖ ^ 4
      * ‖(1 - A ^ 2 * ((x : ℂ) * w ^ 2))⁻¹‖ := by
  have hz : ‖A * w‖ ≤ 1 := by rw [norm_mul, hw, mul_one]; exact hA
  have h := local_three_four_one hx0 hx1 hz
  have e1 : (x : ℂ) * (A * w) = A * ((x : ℂ) * w) := by ring
  have e2 : (x : ℂ) * (A * w) ^ 2 = A ^ 2 * ((x : ℂ) * w ^ 2) := by ring
  rw [e1, e2] at h
  exact h

theorem hecke_three_four_one (d : ℕ) (hd : 1 ≤ d) (chi : GaussianInt → ℂ)
    (hchi : Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi) (m : ℤ) {σ t : ℝ} (hσ : 1 < σ) :
    1 ≤ ‖Work.FIArea5.S16Hecke.heckeLSeries chi m ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 4 *
        ‖Work.FIArea5.S16Hecke.heckeLSeries (fun z : GaussianInt => chi z * chi z) (2 * m)
          ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)‖ *
        ‖Work.FIArea5.S16Hecke.heckeLSeries (fun _ : GaussianInt => (1 : ℂ)) 0 (σ : ℂ)‖ ^ 3 := by
  obtain ⟨hchar, -⟩ := hchi
  obtain ⟨hchi1, hchimul, hchibd, -, -⟩ := hchar
  set chi2 : GaussianInt → ℂ := fun z => chi z * chi z with hchi2
  have hchi2_1 : chi2 1 = 1 := by rw [hchi2]; simp [hchi1]
  have hchi2_mul : ∀ z w : GaussianInt, chi2 (z * w) = chi2 z * chi2 w := by
    intro z w; rw [hchi2]; simp only [hchimul z w]; ring
  have hchi2_bd : ∀ z : GaussianInt, ‖chi2 z‖ ≤ 1 := by
    intro z; rw [hchi2, norm_mul]
    exact mul_le_one₀ (hchibd z) (norm_nonneg _) (hchibd z)
  have hpsi2 : ∀ z : GaussianInt, psi chi2 (2 * m) z = psi chi m z ^ 2 := by
    have key : ∀ (c W : ℂ) (j : ℤ), (c * W ^ j) ^ (2 : ℤ) = (c * c) * W ^ (j * 2) := by
      intro c W j
      rw [mul_zpow, ← zpow_mul]
      congr 1
      rw [show (2:ℤ) = ((2:ℕ):ℤ) by norm_num, zpow_natCast, pow_two]
    intro z
    simp only [psi, hchi2]
    rw [show (2 * m : ℤ) = m * 2 by ring, ← zpow_natCast (n := 2)]
    exact (key (chi z) _ m).symm
  set s1 : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hs1
  set s2 : ℂ := (σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I with hs2
  set s3 : ℂ := (σ : ℂ) with hs3
  have hs1re : 1 < s1.re := by
    have h : s1.re = σ := by simp [hs1, hs3]
    rw [h]; exact hσ
  have hs2re : 1 < s2.re := by
    have h : s2.re = σ := by simp [hs2, hs3]
    rw [h]; exact hσ
  have hs3re : 1 < s3.re := by
    have h : s3.re = σ := by simp [hs3]
    rw [h]; exact hσ
  let F1 : Nat.Primes → ℂ :=
    fun p => ∑' e : ℕ, heckeLam chi m ((p:ℕ)^e) / (((p:ℕ):ℂ)^(e*s1))
  let F2 : Nat.Primes → ℂ :=
    fun p => ∑' e : ℕ, heckeLam chi2 (2*m) ((p:ℕ)^e) / (((p:ℕ):ℂ)^(e*s2))
  let F3 : Nat.Primes → ℂ :=
    fun p => ∑' e : ℕ, heckeLam (fun _ : GaussianInt => (1:ℂ)) 0 ((p:ℕ)^e) /
      (((p:ℕ):ℂ)^(e*s3))
  have H1 : HasProd F1 (heckeLSeries chi m s1) :=
    heckeLSeries_eulerProduct_hasProd chi m hchi1 hchimul hchibd hs1re
  have H2 : HasProd F2 (heckeLSeries chi2 (2*m) s2) :=
    heckeLSeries_eulerProduct_hasProd chi2 (2*m) hchi2_1 hchi2_mul hchi2_bd hs2re
  have H3 : HasProd F3 (heckeLSeries (fun _ : GaussianInt => (1:ℂ)) 0 s3) :=
    heckeLSeries_eulerProduct_hasProd (fun _ : GaussianInt => (1:ℂ)) 0 rfl (by intro z w; ring)
      (by intro z; simp) hs3re
  have hpb : ∀ p : Nat.Primes, 1 ≤ ‖F1 p ^ 4 * F2 p * F3 p ^ 3‖ := by
    intro p
    have hp : (p:ℕ).Prime := p.prop
    rcases hp.eq_two_or_odd' with hp2 | hpodd
    · -- ## `p = 2`: all three local factors are `1`
      have hF1 : F1 p = 1 := by
        show (∑' e : ℕ, heckeLam chi m ((p:ℕ)^e) / (((p:ℕ):ℂ)^(e*s1))) = 1
        rw [tsum_eq_single 0]
        · simp [heckeLam_one, hchi1]
        · intro e he
          obtain ⟨e', rfl⟩ := Nat.exists_eq_succ_of_ne_zero he
          rw [hp2, pow_succ, heckeLam_even chi m ⟨2^e', by ring⟩, zero_div]
      have hF2 : F2 p = 1 := by
        show (∑' e : ℕ, heckeLam chi2 (2*m) ((p:ℕ)^e) / (((p:ℕ):ℂ)^(e*s2))) = 1
        rw [tsum_eq_single 0]
        · simp [heckeLam_one, hchi2_1]
        · intro e he
          obtain ⟨e', rfl⟩ := Nat.exists_eq_succ_of_ne_zero he
          rw [hp2, pow_succ, heckeLam_even chi2 (2*m) ⟨2^e', by ring⟩, zero_div]
      have hF3 : F3 p = 1 := by
        show (∑' e : ℕ, heckeLam (fun _ : GaussianInt => (1:ℂ)) 0 ((p:ℕ)^e) /
          (((p:ℕ):ℂ)^(e*s3))) = 1
        rw [tsum_eq_single 0]
        · simp [heckeLam_one]
        · intro e he
          obtain ⟨e', rfl⟩ := Nat.exists_eq_succ_of_ne_zero he
          rw [hp2, pow_succ, heckeLam_even (fun _ : GaussianInt => (1:ℂ)) 0 ⟨2^e', by ring⟩,
            zero_div]
      rw [hF1, hF2, hF3]
      simp
    · have hp41 : (p:ℕ) % 4 = 1 ∨ (p:ℕ) % 4 = 3 := by
        obtain ⟨k, hk⟩ := hpodd
        omega
      rcases hp41 with h4 | h3
      · -- ## split prime `p ≡ 1 (4)`
        obtain ⟨π, π', hπ, hπ', hgπ, hgπ', -, -, -, hclass⟩ := splitPrimaryClass (p:ℕ) hp h4
        set x : ℝ := (((p:ℕ):ℝ) ^ (-σ)) with hxdef
        set u : ℂ := (((p:ℕ):ℂ) ^ (-((t:ℂ) * Complex.I))) with hudef
        have hx0 : 0 ≤ x := by rw [hxdef]; positivity
        have hx1 : x < 1 := by
          rw [hxdef]
          exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)
        have hu1 : ‖u‖ = 1 := by rw [hudef]; exact norm_natCast_cpow_neg_mul_I hp.pos t
        have hT1 : ((p:ℕ):ℂ) ^ (-s1) = (x : ℂ) * u := by
          rw [show -s1 = (-(σ:ℂ)) + (-((t:ℂ) * Complex.I)) by rw [hs1]; ring,
            natCast_cpow_neg_add_real hp.pos σ (-((t:ℂ) * Complex.I)), ← hudef, ← hxdef]
        have hT2 : ((p:ℕ):ℂ) ^ (-s2) = (x : ℂ) * u ^ 2 := by
          rw [show -s2 = (-(σ:ℂ)) + (((2:ℕ):ℂ) * (-((t:ℂ) * Complex.I))) by
                rw [hs2]; push_cast; ring,
            natCast_cpow_neg_add_real hp.pos σ (((2:ℕ):ℂ) * (-((t:ℂ) * Complex.I))),
            Complex.cpow_nat_mul, ← hudef, ← hxdef]
        have hF1 : F1 p = (1 - psi chi m π * ((x:ℂ) * u))⁻¹ *
            (1 - psi chi m π' * ((x:ℂ) * u))⁻¹ := by
          show (∑' e : ℕ, heckeLam chi m ((p:ℕ)^e) / (((p:ℕ):ℂ)^(e*s1))) = _
          rw [heckeFp_split_eq (p := (p:ℕ)) hp h4 chi m hchi1 hchimul hchibd π π' hπ hπ'
            hgπ hgπ' hclass hs1re, hT1]
        have hF2 : F2 p = (1 - (psi chi m π)^2 * ((x:ℂ) * u^2))⁻¹ *
            (1 - (psi chi m π')^2 * ((x:ℂ) * u^2))⁻¹ := by
          show (∑' e : ℕ, heckeLam chi2 (2*m) ((p:ℕ)^e) / (((p:ℕ):ℂ)^(e*s2))) = _
          rw [heckeFp_split_eq (p := (p:ℕ)) hp h4 chi2 (2*m) hchi2_1 hchi2_mul hchi2_bd π π'
            hπ hπ' hgπ hgπ' hclass hs2re, hT2, hpsi2 π, hpsi2 π']
        have hF3 : F3 p = ((1 - (x:ℂ))⁻¹)^2 := by
          show (∑' e : ℕ, heckeLam (fun _ : GaussianInt => (1:ℂ)) 0 ((p:ℕ)^e) /
            (((p:ℕ):ℂ)^(e*s3))) = _
          rw [heckeFp_split_eq (p := (p:ℕ)) hp h4 (fun _ : GaussianInt => (1:ℂ)) 0 rfl
            (by intro z w; ring) (by intro z; simp) π π' hπ hπ' hgπ hgπ' hclass hs3re]
          have hps : ∀ z : GaussianInt, psi (fun _ : GaussianInt => (1:ℂ)) 0 z = 1 := by
            intro z; rw [psi, zpow_zero, mul_one]
          have h3 : ((p:ℕ):ℂ) ^ (-s3) = (x : ℂ) := by
            rw [hs3]
            simpa [hxdef] using natCast_cpow_neg_real (p:ℕ) σ
          rw [hps π, hps π', h3]
          simp only [one_mul, ← sq]
        rw [hF1, hF2, hF3]
        have hPA := local_group hx0 hx1 (A := psi chi m π) (w := u)
          (norm_psi_le_one chi m hchibd π) hu1
        have hPB := local_group hx0 hx1 (A := psi chi m π') (w := u)
          (norm_psi_le_one chi m hchibd π') hu1
        have hexp : ‖((1 - psi chi m π * ((x:ℂ) * u))⁻¹ *
              (1 - psi chi m π' * ((x:ℂ) * u))⁻¹) ^ 4 *
              ((1 - (psi chi m π)^2 * ((x:ℂ) * u^2))⁻¹ *
                (1 - (psi chi m π')^2 * ((x:ℂ) * u^2))⁻¹) *
              (((1 - (x:ℂ))⁻¹)^2)^3‖
            = (‖(1 - (x:ℂ))⁻¹‖ ^ 3 * ‖(1 - psi chi m π * ((x:ℂ) * u))⁻¹‖ ^ 4 *
                ‖(1 - (psi chi m π)^2 * ((x:ℂ) * u^2))⁻¹‖) *
              (‖(1 - (x:ℂ))⁻¹‖ ^ 3 * ‖(1 - psi chi m π' * ((x:ℂ) * u))⁻¹‖ ^ 4 *
                ‖(1 - (psi chi m π')^2 * ((x:ℂ) * u^2))⁻¹‖) := by
          simp only [norm_mul, norm_pow]
          ring
        rw [hexp]
        exact le_trans (by norm_num : (1:ℝ) ≤ 1 * 1)
          (mul_le_mul hPA hPB (by norm_num) (le_trans (by norm_num) hPA))
      · -- ## inert prime `p ≡ 3 (4)`
        obtain ⟨hq, -, hgq, hclass⟩ := inertPrimaryClass (p:ℕ) hp h3
        set x0 : ℝ := (((p:ℕ):ℝ) ^ (-σ)) with hx0def
        set u : ℂ := (((p:ℕ):ℂ) ^ (-((t:ℂ) * Complex.I))) with hudef
        have hu1 : ‖u‖ = 1 := by rw [hudef]; exact norm_natCast_cpow_neg_mul_I hp.pos t
        have hw1 : ‖u ^ 2‖ = 1 := by rw [norm_pow, hu1]; norm_num
        have hX0 : 0 ≤ x0 := by rw [hx0def]; positivity
        have hX01 : x0 < 1 := by
          rw [hx0def]
          exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)
        have hx2_0 : 0 ≤ x0 ^ 2 := sq_nonneg x0
        have hx2_1 : x0 ^ 2 < 1 := by nlinarith [hX0, hX01]
        have hT1 : ((p:ℕ):ℂ) ^ (-s1) = (x0 : ℂ) * u := by
          rw [show -s1 = (-(σ:ℂ)) + (-((t:ℂ) * Complex.I)) by rw [hs1]; ring,
            natCast_cpow_neg_add_real hp.pos σ (-((t:ℂ) * Complex.I)), ← hudef, ← hx0def]
        have hT2 : ((p:ℕ):ℂ) ^ (-s2) = (x0 : ℂ) * u ^ 2 := by
          rw [show -s2 = (-(σ:ℂ)) + (((2:ℕ):ℂ) * (-((t:ℂ) * Complex.I))) by
                rw [hs2]; push_cast; ring,
            natCast_cpow_neg_add_real hp.pos σ (((2:ℕ):ℂ) * (-((t:ℂ) * Complex.I))),
            Complex.cpow_nat_mul, ← hudef, ← hx0def]
        have hT1sq : (((p:ℕ):ℂ) ^ (-s1)) ^ 2 = (((x0 ^ 2 : ℝ)) : ℂ) * u ^ 2 := by
          rw [hT1, mul_pow, ← Complex.ofReal_pow]
        have hT2sq : (((p:ℕ):ℂ) ^ (-s2)) ^ 2 = (((x0 ^ 2 : ℝ)) : ℂ) * (u ^ 2) ^ 2 := by
          rw [hT2, mul_pow, ← Complex.ofReal_pow]
        have hT3sq : (((p:ℕ):ℂ) ^ (-s3)) ^ 2 = (((x0 ^ 2 : ℝ)) : ℂ) := by
          have h3 : ((p:ℕ):ℂ) ^ (-s3) = (x0 : ℂ) := by
            rw [hs3]
            simpa [hx0def] using natCast_cpow_neg_real (p:ℕ) σ
          rw [h3, ← Complex.ofReal_pow]
        have hA : ‖psi chi m (-(p:GaussianInt))‖ ≤ 1 := norm_psi_le_one chi m hchibd _
        have hps : ∀ z : GaussianInt, psi (fun _ : GaussianInt => (1:ℂ)) 0 z = 1 := by
          intro z; rw [psi, zpow_zero, mul_one]
        have hF1 : F1 p = (1 - psi chi m (-(p:GaussianInt)) *
            ((((x0 ^ 2 : ℝ)) : ℂ) * u ^ 2))⁻¹ := by
          show (∑' e : ℕ, heckeLam chi m ((p:ℕ)^e) / (((p:ℕ):ℂ)^(e*s1))) = _
          rw [heckeFp_inert_eq (p := (p:ℕ)) hp h3 chi m hchi1 hchimul hchibd hs1re, hT1sq]
        have hF2 : F2 p = (1 - (psi chi m (-(p:GaussianInt)))^2 *
            ((((x0 ^ 2 : ℝ)) : ℂ) * (u ^ 2) ^ 2))⁻¹ := by
          show (∑' e : ℕ, heckeLam chi2 (2*m) ((p:ℕ)^e) / (((p:ℕ):ℂ)^(e*s2))) = _
          rw [heckeFp_inert_eq (p := (p:ℕ)) hp h3 chi2 (2*m) hchi2_1 hchi2_mul hchi2_bd hs2re,
            hT2sq, hpsi2 (-(p:GaussianInt))]
        have hF3 : F3 p = (1 - (((x0 ^ 2 : ℝ)) : ℂ))⁻¹ := by
          show (∑' e : ℕ, heckeLam (fun _ : GaussianInt => (1:ℂ)) 0 ((p:ℕ)^e) /
            (((p:ℕ):ℂ)^(e*s3))) = _
          rw [heckeFp_inert_eq (p := (p:ℕ)) hp h3 (fun _ : GaussianInt => (1:ℂ)) 0 rfl
            (by intro z w; ring) (by intro z; simp) hs3re, hps (-(p:GaussianInt)), hT3sq]
          simp only [one_mul]
        rw [hF1, hF2, hF3]
        have hPA := local_group hx2_0 hx2_1 (A := psi chi m (-(p:GaussianInt))) (w := u ^ 2)
          hA hw1
        have hexp : ‖(1 - psi chi m (-(p:GaussianInt)) *
                ((((x0 ^ 2 : ℝ)) : ℂ) * u ^ 2))⁻¹ ^ 4 *
              (1 - (psi chi m (-(p:GaussianInt)))^2 *
                ((((x0 ^ 2 : ℝ)) : ℂ) * (u ^ 2) ^ 2))⁻¹ *
              ((1 - (((x0 ^ 2 : ℝ)) : ℂ))⁻¹)^3‖
            = (‖(1 - (((x0 ^ 2 : ℝ)) : ℂ))⁻¹‖ ^ 3 *
                ‖(1 - psi chi m (-(p:GaussianInt)) * ((((x0 ^ 2 : ℝ)) : ℂ) * u ^ 2))⁻¹‖ ^ 4 *
                ‖(1 - (psi chi m (-(p:GaussianInt)))^2 *
                  ((((x0 ^ 2 : ℝ)) : ℂ) * (u ^ 2) ^ 2))⁻¹‖) := by
          simp only [norm_mul, norm_pow]
          ring
        rw [hexp]
        exact hPA
  have hmain : 1 ≤ ‖heckeLSeries chi m s1‖ ^ 4 * ‖heckeLSeries chi2 (2*m) s2‖ *
      ‖heckeLSeries (fun _ : GaussianInt => (1:ℂ)) 0 s3‖ ^ 3 := by
    have htend : Tendsto (fun S : Finset Nat.Primes => ∏ p ∈ S, (F1 p ^ 4 * F2 p * F3 p ^ 3))
        atTop (𝓝 (heckeLSeries chi m s1 ^ 4 * heckeLSeries chi2 (2*m) s2 *
          heckeLSeries (fun _ : GaussianInt => (1:ℂ)) 0 s3 ^ 3)) :=
      ((H1.pow 4).mul H2).mul (H3.pow 3)
    have hge : 1 ≤ ‖heckeLSeries chi m s1 ^ 4 * heckeLSeries chi2 (2*m) s2 *
        (heckeLSeries (fun _ : GaussianInt => (1:ℂ)) 0 s3) ^ 3‖ := by
      refine ge_of_tendsto htend.norm (Filter.Eventually.of_forall (fun S => ?_))
      rw [Complex.norm_prod]
      exact Finset.one_le_prod₀ (fun q _ => hpb q)
    simpa only [norm_mul, norm_pow] using hge
  simpa only [hs1, hs2, hs3, hchi2] using hmain


end

end Work.FIArea6Hecke.R
import Mathlib
import Submission.Work.FIArea6Road.ZcontPQBound
import Submission.Work.FIArea5.S16Hecke.heckeLam_prime_norm_le_two
import Submission.Work.FIArea5.S16Hecke.heckeLam_prime_eq_zero_of_ne_one_mod_four
import Submission.Commons.NumberTheory.Chebyshev.sum_prime_inv_le_log_log_add
import Submission.Commons.NumberTheory.Chebyshev.sum_prime_log_div_le

set_option autoImplicit false

namespace Work.FIArea6Road.ZT

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-!
# `Submission.Work.FIArea6Road.PfacSharpZT` (a `ZcontPQBound`-world copy)

The §16 Euler product `P(s) = ∏_{p ≤ Pz} (1 - λ(p)p^{-s})^{-1}` of *FI* (16.33) is bounded by
`K·(log Pz + 2)³` on the region `re s ≥ 1 - 1/log Pz` (FI (16.32)) with `K` absolute.

The proof has two halves:

* every local factor is at most `(1 - 2p^{-re s})^{-1}` when `p ≡ 1 (mod 4)` (and is exactly `1`
  at the other primes, where `λ(p) = 0`), so `‖P(s)‖ ≤ ∏_{p ≡ 1(4), p ≤ Pz}(1 - 2p^{-re s})^{-1}`;
* on the region, `2p^{-σ} ≤ 2p^{-1}(1 + 2 log p/log Pz)`, so `Σ 2p^{-σ} ≲ 2 loglog Pz` and the
  product is `(log Pz)^{O(1)}`; the finitely many primes `p ≤ 13` are absorbed into the constant.
-/

/-! ## Elementary numerical and algebraic estimates -/

/-- `(1-u)⁻¹ ≤ 1 + u + 2u²` for `0 ≤ u ≤ 1/2`. -/
lemma inv_one_sub_le_add_sq {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2) :
    (1 - u)⁻¹ ≤ 1 + u + 2 * u ^ 2 := by
  have hpos : 0 < 1 - u := by linarith
  rw [inv_le_iff_one_le_mul₀ hpos]
  nlinarith [mul_nonneg (sq_nonneg u) (by linarith : (0 : ℝ) ≤ 1 - 2 * u), hu0]

/-- `Real.exp v ≤ 1 + 2v` for `0 ≤ v ≤ 1` (convexity of `exp` and `e < 3`). -/
lemma exp_le_one_add_two_mul {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    Real.exp v ≤ 1 + 2 * v := by
  have h := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ))
    (by linarith : (0 : ℝ) ≤ 1 - v) hv0 (by ring : (1 - v) + v = 1)
  simp only [smul_eq_mul, mul_zero, mul_one, Real.exp_zero] at h
  rw [zero_add] at h
  nlinarith [Real.exp_one_lt_three, hv0]

/-- `(1-u)⁻¹ ≤ exp (3u/2)` for `0 ≤ u ≤ 1/4`. -/
lemma inv_one_sub_le_exp {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 1 / 4) :
    (1 - u)⁻¹ ≤ Real.exp (3 / 2 * u) := by
  refine le_trans (inv_one_sub_le_add_sq hu0 (by linarith)) ?_
  have h2 : 1 + u + 2 * u ^ 2 ≤ Real.exp (u + 2 * u ^ 2) := by
    have := Real.add_one_le_exp (u + 2 * u ^ 2)
    linarith
  refine le_trans h2 (Real.exp_le_exp.mpr ?_)
  nlinarith

/-- `2·17^{-3/4} ≤ 1/4`, i.e. `8^4 ≤ 17^3`. -/
lemma two_mul_17_rpow_neg_le_quarter : 2 * (17 : ℝ) ^ (-(3 / 4 : ℝ)) ≤ 1 / 4 := by
  have h17 : (8 : ℝ) ≤ (17 : ℝ) ^ ((3 : ℝ) / 4) := by
    have h4 : (8 : ℝ) ^ 4 ≤ ((17 : ℝ) ^ ((3 : ℝ) / 4)) ^ 4 := by
      rw [show ((17 : ℝ) ^ ((3 : ℝ) / 4)) ^ 4 = (17 : ℝ) ^ 3 by
        rw [← Real.rpow_natCast ((17 : ℝ) ^ ((3 : ℝ) / 4)) 4,
          ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 17)]
        norm_num]
      norm_num
    exact (pow_le_pow_iff_left₀ (by norm_num) (by positivity) (by norm_num)).mp h4
  have hneg : (17 : ℝ) ^ (-(3 / 4 : ℝ)) = ((17 : ℝ) ^ ((3 : ℝ) / 4))⁻¹ := by
    rw [show (-(3 / 4 : ℝ)) = -((3 : ℝ) / 4) by norm_num,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 17)]
  rw [hneg]
  have h := (inv_le_inv₀ (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 17) ((3 : ℝ) / 4))
    (by norm_num : (0 : ℝ) < 8)).mpr h17
  norm_num at h ⊢
  linarith

/-- The uniform majorant `(1 - 2·5^{-3/4})⁻¹` of a single local factor at an odd prime. -/
def C5 : ℝ := (1 - 2 * (5 : ℝ) ^ (-(3 / 4 : ℝ)))⁻¹

lemma two_mul_five_rpow_neg_lt_one : 2 * (5 : ℝ) ^ (-(3 / 4 : ℝ)) < 1 :=
  two_mul_rpow_neg_lt_one (show 3 ≤ 5 by norm_num)

lemma C5_pos : 0 < C5 := by
  rw [C5]
  exact inv_pos.mpr (by linarith [two_mul_five_rpow_neg_lt_one])

lemma one_le_C5 : 1 ≤ C5 := by
  rw [C5, one_le_inv₀ (by linarith [two_mul_five_rpow_neg_lt_one])]
  linarith [two_mul_five_rpow_neg_lt_one,
    Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 5) (-(3 / 4 : ℝ))]

/-- For a prime `p ≥ 5` and `σ ≥ 3/4`, the local majorant `(1 - 2p^{-σ})⁻¹` is nonnegative. -/
lemma inv_two_rpow_nonneg {p : ℕ} {σ : ℝ} (hp5 : 5 ≤ p) (hσ : (3 / 4 : ℝ) ≤ σ) :
    0 ≤ (1 - 2 * (p : ℝ) ^ (-σ))⁻¹ := by
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (show 1 ≤ p by omega)
  have h5le : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp5
  have hle1 : (p : ℝ) ^ (-σ) ≤ (p : ℝ) ^ (-(3 / 4 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
  have hle2 : (p : ℝ) ^ (-(3 / 4 : ℝ)) ≤ (5 : ℝ) ^ (-(3 / 4 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) h5le (by norm_num)
  exact (inv_pos.mpr (by linarith [two_mul_five_rpow_neg_lt_one])).le

/-- For a prime `p ≥ 5` and `σ ≥ 3/4`, the local majorant is at most the constant `C5`. -/
lemma inv_two_rpow_le_C5 {p : ℕ} {σ : ℝ} (hp5 : 5 ≤ p) (hσ : (3 / 4 : ℝ) ≤ σ) :
    (1 - 2 * (p : ℝ) ^ (-σ))⁻¹ ≤ C5 := by
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (show 1 ≤ p by omega)
  have h5le : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp5
  have hle1 : (p : ℝ) ^ (-σ) ≤ (p : ℝ) ^ (-(3 / 4 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
  have hle2 : (p : ℝ) ^ (-(3 / 4 : ℝ)) ≤ (5 : ℝ) ^ (-(3 / 4 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) h5le (by norm_num)
  have hpos5 : 0 < 1 - 2 * (5 : ℝ) ^ (-(3 / 4 : ℝ)) := by
    linarith [two_mul_five_rpow_neg_lt_one]
  have hpos : 0 < 1 - 2 * (p : ℝ) ^ (-σ) := by linarith
  rw [C5]
  exact (inv_le_inv₀ hpos hpos5).mpr (by linarith)

/-- For `a ≥ 17` and `σ ≥ 3/4`, the local majorant is at most `exp (3a^{-σ})`. -/
lemma inv_two_rpow_le_exp {a : ℕ} {σ : ℝ} (ha17 : 17 ≤ a) (hσ : (3 / 4 : ℝ) ≤ σ) :
    (1 - 2 * (a : ℝ) ^ (-σ))⁻¹ ≤ Real.exp (3 * (a : ℝ) ^ (-σ)) := by
  have ha1 : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast (show 1 ≤ a by omega)
  have ha17' : (17 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha17
  have hu0 : 0 ≤ 2 * (a : ℝ) ^ (-σ) :=
    mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg a) _)
  have hu : 2 * (a : ℝ) ^ (-σ) ≤ 1 / 4 := by
    have hle1 : (a : ℝ) ^ (-σ) ≤ (a : ℝ) ^ (-(3 / 4 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le ha1 (by linarith)
    have hle2 : (a : ℝ) ^ (-(3 / 4 : ℝ)) ≤ (17 : ℝ) ^ (-(3 / 4 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) ha17' (by norm_num)
    linarith [two_mul_17_rpow_neg_le_quarter]
  have h := inv_one_sub_le_exp hu0 hu
  rwa [show 3 / 2 * (2 * (a : ℝ) ^ (-σ)) = 3 * (a : ℝ) ^ (-σ) by ring] at h

/-- Product form of `inv_two_rpow_le_exp`: for a finite set of naturals `a ≥ 17`,
`∏ (1 - 2a^{-σ})⁻¹ ≤ exp (3 Σ a^{-σ})`. -/
lemma prod_inv_two_rpow_le_exp (A : Finset ℕ) (σ : ℝ) (hA : ∀ a ∈ A, 17 ≤ a)
    (hσ : (3 / 4 : ℝ) ≤ σ) :
    (∏ a ∈ A, (1 - 2 * (a : ℝ) ^ (-σ))⁻¹) ≤ Real.exp (3 * ∑ a ∈ A, (a : ℝ) ^ (-σ)) := by
  calc (∏ a ∈ A, (1 - 2 * (a : ℝ) ^ (-σ))⁻¹)
      ≤ ∏ a ∈ A, Real.exp (3 * (a : ℝ) ^ (-σ)) :=
        Finset.prod_le_prod₀ (fun a ha => inv_two_rpow_nonneg (by have := hA a ha; omega) hσ)
          (fun a ha => inv_two_rpow_le_exp (hA a ha) hσ)
    _ = Real.exp (∑ a ∈ A, 3 * (a : ℝ) ^ (-σ)) := (Real.exp_sum A _).symm
    _ = Real.exp (3 * ∑ a ∈ A, (a : ℝ) ^ (-σ)) := by
        congr 1
        rw [Finset.mul_sum]

/-! ## The local factor bound -/

/-- For a rational prime `p ≡ 1 (mod 4)` and `re s ≥ 3/4`, the local inverse Euler factor
`(1 - λ(p)p^{-s})⁻¹` is bounded by `(1 - 2p^{-re s})⁻¹`. -/
lemma locF_inv_bound_sigma (chi : GaussianInt → ℂ) (m : ℤ)
    (hchi : ∀ z : GaussianInt, ‖chi z‖ ≤ 1)
    {p : ℕ} (hp : p.Prime) (h4 : p % 4 = 1) {s : ℂ} (hσ : (3 / 4 : ℝ) ≤ s.re) :
    ‖(1 - Work.FIArea5.S16Hecke.heckeLam chi m p * (p : ℂ) ^ (-s))⁻¹‖
      ≤ (1 - 2 * (p : ℝ) ^ (-s.re))⁻¹ := by
  have hp5 : 5 ≤ p := by have h2 := hp.two_le; omega
  have hlam : ‖Work.FIArea5.S16Hecke.heckeLam chi m p‖ ≤ 2 :=
    Work.FIArea5.S16Hecke.heckeLam_prime_norm_le_two hp h4 hchi
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_le
  have hwn : ‖Work.FIArea5.S16Hecke.heckeLam chi m p * (p : ℂ) ^ (-s)‖
      ≤ 2 * (p : ℝ) ^ (-s.re) := by
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos hp.pos, Complex.neg_re]
    exact mul_le_mul_of_nonneg_right hlam (Real.rpow_nonneg (Nat.cast_nonneg p) _)
  have hlt : 2 * (p : ℝ) ^ (-s.re) < 1 := by
    have h := two_mul_rpow_neg_lt_one (p := p) (by omega)
    have hle : (p : ℝ) ^ (-s.re) ≤ (p : ℝ) ^ (-(3 / 4 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
    linarith
  have htri : 1 - ‖Work.FIArea5.S16Hecke.heckeLam chi m p * (p : ℂ) ^ (-s)‖
      ≤ ‖1 - Work.FIArea5.S16Hecke.heckeLam chi m p * (p : ℂ) ^ (-s)‖ := by
    have h := norm_sub_norm_le (1 : ℂ)
      (Work.FIArea5.S16Hecke.heckeLam chi m p * (p : ℂ) ^ (-s))
    rwa [norm_one] at h
  have hge : 0 < 1 - ‖Work.FIArea5.S16Hecke.heckeLam chi m p * (p : ℂ) ^ (-s)‖ := by
    linarith
  have h2pos : 0 < 1 - 2 * (p : ℝ) ^ (-s.re) := by linarith
  rw [norm_inv]
  calc (‖1 - Work.FIArea5.S16Hecke.heckeLam chi m p * (p : ℂ) ^ (-s)‖)⁻¹
      = 1 / ‖1 - Work.FIArea5.S16Hecke.heckeLam chi m p * (p : ℂ) ^ (-s)‖ := by rw [one_div]
    _ ≤ 1 / (1 - ‖Work.FIArea5.S16Hecke.heckeLam chi m p * (p : ℂ) ^ (-s)‖) :=
        one_div_le_one_div_of_le hge htri
    _ ≤ 1 / (1 - 2 * (p : ℝ) ^ (-s.re)) := one_div_le_one_div_of_le h2pos (by linarith)
    _ = (1 - 2 * (p : ℝ) ^ (-s.re))⁻¹ := by rw [one_div]

/-! ## The majorant product -/

/-- The product of the local majorants over the primes `p ≡ 1 (mod 4)`, `p ≤ Pz`. -/
def Pmaj (Pz : ℕ) (σ : ℝ) : ℝ :=
  ∏ p ∈ (Nat.primesBelow (Pz + 1)).filter (fun p => p % 4 = 1), (1 - 2 * (p : ℝ) ^ (-σ))⁻¹

/-- `‖P(s)‖` is at most the majorant product `Pmaj`. -/
lemma norm_Pfac_le_Pmaj (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ)
    (hchi : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) {s : ℂ} (hσ : (3 / 4 : ℝ) ≤ s.re) :
    ‖Work.FIArea6.TauPieces.Pfac Pa chi m s‖ ≤ Pmaj Pa.Pz s.re := by
  rw [Pmaj, Work.FIArea6.TauPieces.Pfac, norm_prod]
  have hsplit := Finset.prod_filter_mul_prod_filter_not (Nat.primesBelow (Pa.Pz + 1))
    (fun p => p % 4 = 1)
    (fun p => ‖(1 - Work.FIArea5.S16Hecke.heckeLam chi m p * (p : ℂ) ^ (-s))⁻¹‖)
  rw [← hsplit]
  have hsecond : (∏ p ∈ (Nat.primesBelow (Pa.Pz + 1)).filter (fun p => ¬ p % 4 = 1),
      ‖(1 - Work.FIArea5.S16Hecke.heckeLam chi m p * (p : ℂ) ^ (-s))⁻¹‖) = 1 := by
    refine Finset.prod_eq_one fun p hp => ?_
    obtain ⟨hmem, hmod⟩ := Finset.mem_filter.mp hp
    rw [Work.FIArea5.S16Hecke.heckeLam_prime_eq_zero_of_ne_one_mod_four
      (Nat.prime_of_mem_primesBelow hmem) hmod, zero_mul, sub_zero, inv_one, norm_one]
  rw [hsecond, mul_one]
  refine Finset.prod_le_prod₀ (fun p _ => norm_nonneg _) fun p hp => ?_
  obtain ⟨hmem, hmod⟩ := Finset.mem_filter.mp hp
  exact locF_inv_bound_sigma chi m hchi (Nat.prime_of_mem_primesBelow hmem) hmod hσ

/-- The part of the majorant product over the primes `p < 17` is at most the constant `C5^17`. -/
lemma prod_small_le (Pz : ℕ) (σ : ℝ) (hσ : (3 / 4 : ℝ) ≤ σ) :
    (∏ p ∈ ((Nat.primesBelow (Pz + 1)).filter (fun p => p % 4 = 1)).filter
        (fun p => p < 17), (1 - 2 * (p : ℝ) ^ (-σ))⁻¹) ≤ C5 ^ 17 := by
  have hmem5 : ∀ p ∈ ((Nat.primesBelow (Pz + 1)).filter (fun p => p % 4 = 1)).filter
      (fun p => p < 17), 5 ≤ p := by
    intro p hp
    have hpA : p ∈ (Nat.primesBelow (Pz + 1)).filter (fun p => p % 4 = 1) :=
      (Finset.mem_filter.mp hp).1
    have hprime : p.Prime := Nat.prime_of_mem_primesBelow (Finset.mem_filter.mp hpA).1
    have hm : p % 4 = 1 := (Finset.mem_filter.mp hpA).2
    have h2 := hprime.two_le
    omega
  calc (∏ p ∈ ((Nat.primesBelow (Pz + 1)).filter (fun p => p % 4 = 1)).filter
          (fun p => p < 17), (1 - 2 * (p : ℝ) ^ (-σ))⁻¹)
      ≤ ∏ p ∈ ((Nat.primesBelow (Pz + 1)).filter (fun p => p % 4 = 1)).filter
          (fun p => p < 17), C5 :=
        Finset.prod_le_prod₀ (fun p hp => inv_two_rpow_nonneg (hmem5 p hp) hσ)
          (fun p hp => inv_two_rpow_le_C5 (hmem5 p hp) hσ)
    _ = C5 ^ (((Nat.primesBelow (Pz + 1)).filter (fun p => p % 4 = 1)).filter
          (fun p => p < 17)).card := Finset.prod_const C5
    _ ≤ C5 ^ 17 := by
        apply pow_le_pow_right₀ one_le_C5
        have := Finset.card_le_card (s := ((Nat.primesBelow (Pz + 1)).filter
            (fun p => p % 4 = 1)).filter (fun p => p < 17)) (t := Finset.range 17)
          (fun p hp => by rw [Finset.mem_range]; exact (Finset.mem_filter.mp hp).2)
        simpa using this

/-- The part of the majorant product over the primes `17 ≤ p` is at most
`exp (3 (log log Pz + C))`, given the Mertens-type input `C`. -/
lemma prod_big_le (Pz : ℕ) (σ : ℝ) (hT : 4 ≤ Real.log (Pz : ℝ))
    (hσ : 1 - 1 / Real.log (Pz : ℝ) ≤ σ) (C : ℝ)
    (hC : ∀ (N : ℕ) (τ : ℝ), 4 ≤ Real.log (N : ℝ) → 1 - 1 / Real.log (N : ℝ) ≤ τ →
      (∑ p ∈ Nat.primesBelow (N + 1), (p : ℝ) ^ (-τ)) ≤ Real.log (Real.log (N : ℝ)) + C) :
    (∏ p ∈ ((Nat.primesBelow (Pz + 1)).filter (fun p => p % 4 = 1)).filter
        (fun p => ¬ p < 17), (1 - 2 * (p : ℝ) ^ (-σ))⁻¹)
      ≤ Real.exp (3 * (Real.log (Real.log (Pz : ℝ)) + C)) := by
  have hσ34 : (3 / 4 : ℝ) ≤ σ := by
    have h1 : 1 / Real.log (Pz : ℝ) ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hT
    linarith
  have hbig := prod_inv_two_rpow_le_exp
    (((Nat.primesBelow (Pz + 1)).filter (fun p => p % 4 = 1)).filter (fun p => ¬ p < 17)) σ
    (fun a ha => by have := (Finset.mem_filter.mp ha).2; omega) hσ34
  refine le_trans hbig (Real.exp_le_exp.mpr ?_)
  have hsub : ((Nat.primesBelow (Pz + 1)).filter (fun p => p % 4 = 1)).filter
      (fun p => ¬ p < 17) ⊆ Nat.primesBelow (Pz + 1) :=
    fun x hx => (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1
  have hle : (∑ a ∈ ((Nat.primesBelow (Pz + 1)).filter (fun p => p % 4 = 1)).filter
        (fun p => ¬ p < 17), (a : ℝ) ^ (-σ))
      ≤ ∑ a ∈ Nat.primesBelow (Pz + 1), (a : ℝ) ^ (-σ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun x _ _ => Real.rpow_nonneg (Nat.cast_nonneg x) _)
  have h2 := hC Pz σ hT hσ
  linarith

/-! ## The Mertens-type sum bound -/

/-- On the region `σ ≥ 1 - 1/log N` (with `log N ≥ 4`), the sum `Σ_{p ≤ N} p^{-σ}` over primes is
at most `log log N + C` with an absolute constant `C`. -/
theorem exists_sum_prime_rpow_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (Pz : ℕ) (σ : ℝ), 4 ≤ Real.log (Pz : ℝ) →
      1 - 1 / Real.log (Pz : ℝ) ≤ σ →
      (∑ p ∈ Nat.primesBelow (Pz + 1), (p : ℝ) ^ (-σ))
        ≤ Real.log (Real.log (Pz : ℝ)) + C := by
  obtain ⟨C1, hC1pos, hC1⟩ := Commons.NumberTheory.Chebyshev.sum_prime_inv_le_log_log_add
  obtain ⟨C2, hC2pos, hC2⟩ := Commons.NumberTheory.Chebyshev.sum_prime_log_div_le
  refine ⟨C1 + 2 + C2 / 2, by linarith, ?_⟩
  intro Pz σ hT hσ
  have hTpos : 0 < Real.log (Pz : ℝ) := by linarith
  have hPz2 : 2 ≤ Pz := by
    have h1 : (1 : ℕ) < Pz := by
      have h1R : (1 : ℝ) < (Pz : ℝ) := by
        by_contra hle
        have hle' : (Pz : ℝ) ≤ 1 := le_of_not_gt hle
        have h := Real.log_nonpos (by positivity : (0 : ℝ) ≤ (Pz : ℝ)) hle'
        linarith
      exact_mod_cast h1R
    omega
  have hprimes : Nat.primesBelow (Pz + 1) = (Finset.Icc 1 Pz).filter Nat.Prime := by
    show Nat.primesLE Pz = (Finset.Icc 1 Pz).filter Nat.Prime
    rw [Commons.NumberTheory.Chebyshev.filter_Icc_one_prime_eq_primesLE Pz]
  have hterm : ∀ p ∈ Nat.primesBelow (Pz + 1),
      (p : ℝ) ^ (-σ) ≤ (p : ℝ)⁻¹ * (1 + 2 * (Real.log (p : ℝ) / Real.log (Pz : ℝ))) := by
    intro p hp
    have hprime : p.Prime := Nat.prime_of_mem_primesBelow hp
    have hple : p ≤ Pz := by have := (Nat.mem_primesBelow.mp hp).1; omega
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hprime.one_le
    have hppos : (0 : ℝ) < (p : ℝ) := by linarith
    have h1 : (p : ℝ) ^ (-σ) ≤ (p : ℝ) ^ (-(1 - 1 / Real.log (Pz : ℝ))) :=
      Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
    have h2 : (p : ℝ) ^ (-(1 - 1 / Real.log (Pz : ℝ)))
        = (p : ℝ)⁻¹ * (p : ℝ) ^ (1 / Real.log (Pz : ℝ)) := by
      rw [show -(1 - 1 / Real.log (Pz : ℝ)) = -1 + 1 / Real.log (Pz : ℝ) by ring,
        Real.rpow_add hppos, Real.rpow_neg_one]
    have h3 : (p : ℝ) ^ (1 / Real.log (Pz : ℝ))
        ≤ 1 + 2 * (Real.log (p : ℝ) / Real.log (Pz : ℝ)) := by
      rw [Real.rpow_def_of_pos hppos]
      have hv0 : 0 ≤ Real.log (p : ℝ) / Real.log (Pz : ℝ) :=
        div_nonneg (Real.log_nonneg hp1) hTpos.le
      have hv1 : Real.log (p : ℝ) / Real.log (Pz : ℝ) ≤ 1 := by
        rw [div_le_one hTpos]
        exact Real.log_le_log (by linarith) (by exact_mod_cast hple)
      rw [show Real.log (p : ℝ) * (1 / Real.log (Pz : ℝ))
            = Real.log (p : ℝ) / Real.log (Pz : ℝ) by ring]
      exact exp_le_one_add_two_mul hv0 hv1
    calc (p : ℝ) ^ (-σ) ≤ (p : ℝ) ^ (-(1 - 1 / Real.log (Pz : ℝ))) := h1
      _ = (p : ℝ)⁻¹ * (p : ℝ) ^ (1 / Real.log (Pz : ℝ)) := h2
      _ ≤ (p : ℝ)⁻¹ * (1 + 2 * (Real.log (p : ℝ) / Real.log (Pz : ℝ))) :=
          mul_le_mul_of_nonneg_left h3 (inv_nonneg.mpr (by positivity))
  have hsum1 : (∑ p ∈ Nat.primesBelow (Pz + 1), (p : ℝ) ^ (-σ))
      ≤ ∑ p ∈ Nat.primesBelow (Pz + 1),
          (p : ℝ)⁻¹ * (1 + 2 * (Real.log (p : ℝ) / Real.log (Pz : ℝ))) :=
    Finset.sum_le_sum hterm
  have hsum2 : (∑ p ∈ Nat.primesBelow (Pz + 1),
        (p : ℝ)⁻¹ * (1 + 2 * (Real.log (p : ℝ) / Real.log (Pz : ℝ))))
      = (∑ p ∈ Nat.primesBelow (Pz + 1), (p : ℝ)⁻¹)
        + (2 / Real.log (Pz : ℝ)) * ∑ p ∈ Nat.primesBelow (Pz + 1),
            Real.log (p : ℝ) / (p : ℝ) := by
    have hpt : ∀ p ∈ Nat.primesBelow (Pz + 1),
        (p : ℝ)⁻¹ * (1 + 2 * (Real.log (p : ℝ) / Real.log (Pz : ℝ)))
          = (p : ℝ)⁻¹ + (Real.log (p : ℝ) / (p : ℝ)) * (2 / Real.log (Pz : ℝ)) := by
      intro p _
      ring
    rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, ← Finset.sum_mul]
    ring
  have hA1 : (∑ p ∈ Nat.primesBelow (Pz + 1), (p : ℝ)⁻¹)
      ≤ Real.log (Real.log (Pz : ℝ)) + C1 := by
    rw [hprimes]
    have := hC1 Pz hPz2
    simpa [one_div] using this
  have hA2 : (∑ p ∈ Nat.primesBelow (Pz + 1), Real.log (p : ℝ) / (p : ℝ))
      ≤ Real.log (Pz : ℝ) + C2 := by
    rw [hprimes]
    exact hC2 Pz (by omega)
  calc (∑ p ∈ Nat.primesBelow (Pz + 1), (p : ℝ) ^ (-σ))
      ≤ ∑ p ∈ Nat.primesBelow (Pz + 1),
          (p : ℝ)⁻¹ * (1 + 2 * (Real.log (p : ℝ) / Real.log (Pz : ℝ))) := hsum1
    _ = (∑ p ∈ Nat.primesBelow (Pz + 1), (p : ℝ)⁻¹)
        + (2 / Real.log (Pz : ℝ)) * ∑ p ∈ Nat.primesBelow (Pz + 1),
            Real.log (p : ℝ) / (p : ℝ) := hsum2
    _ ≤ (Real.log (Real.log (Pz : ℝ)) + C1)
          + (2 / Real.log (Pz : ℝ)) * (Real.log (Pz : ℝ) + C2) := by
        refine add_le_add hA1 ?_
        exact mul_le_mul_of_nonneg_left hA2 (by positivity)
    _ = Real.log (Real.log (Pz : ℝ)) + (C1 + 2 + 2 * C2 / Real.log (Pz : ℝ)) := by
        field_simp
        ring
    _ ≤ Real.log (Real.log (Pz : ℝ)) + (C1 + 2 + C2 / 2) := by
        have h3 : 2 * C2 / Real.log (Pz : ℝ) ≤ C2 / 2 := by
          rw [div_le_iff₀ hTpos]
          nlinarith [hC2pos, hT]
        linarith

/-! ## The main theorem -/

/-- ***(FI)* (16.33) with an *absolute* constant.**  On the region `re s ≥ 1 - 1/log Pz`
(the paper's (16.32)) the §16 Euler product `P(s) = ∏_{p ≤ Pz} (1 - λ(p)p^{-s})^{-1}` is bounded
by `K·(log Pz + 2)^3` with `K` **independent** of `Pa`, `χ`, `m` and `s`.

(The proof on the shelf, `Work.FIArea6Road.Pfac_bound`, only gives the bound
`∏_{p ≤ Pz} locBnd p = ∏_{p ≤ Pz}(1 - 2p^{-3/4})^{-1}`, which grows like `exp(c·Pz^{1/4}/log Pz)`
and is *not* uniform in `Pa`.  The region hypothesis `re s ≥ 1 - 1/log Pz` is what upgrades it to a
power of `log Pz`: for `p ≤ Pz` one has `p^{-σ} ≤ p^{-1}·p^{1/log Pz} ≤ e·p^{-1}`, so
`Σ_{p ≤ Pz} 2p^{-σ} ≤ 2Σ_{p≤Pz}p^{-1} + 2Σ_{p≤Pz}(log p)/(p log Pz) ≤ C loglog Pz`, using
`Σ_{p ≤ y}1/p = loglog y + O(1)` and `Σ_{p≤y}(log p)/p = log y + O(1)`; the `p ≤ 7` factors are
handled by the crude `2p^{-3/4} < 1`.) -/
theorem PfacBoundSharpZT :
    ∃ K : ℝ, 0 < K ∧ ∀ (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ),
      chi 1 = 1 → (∀ z w : GaussianInt, chi (z * w) = chi z * chi w) →
      (∀ z : GaussianInt, ‖chi z‖ ≤ 1) → 4 ≤ Real.log (Pa.Pz : ℝ) →
      ∀ s : ℂ, 1 - 1 / Real.log (Pa.Pz : ℝ) ≤ s.re →
        ‖Work.FIArea6.TauPieces.Pfac Pa chi m s‖
          ≤ K * (Real.log (Pa.Pz : ℝ) + 2) ^ (3 : ℕ) := by
  obtain ⟨C, hCpos, hC⟩ := exists_sum_prime_rpow_le
  refine ⟨C5 ^ 17 * Real.exp (3 * C),
    mul_pos (pow_pos C5_pos 17) (Real.exp_pos _), ?_⟩
  intro Pa chi m _hone _hmul hchi hlogPz s hs
  have hT4 : (4 : ℝ) ≤ Real.log (Pa.Pz : ℝ) := hlogPz
  have hloglogpos : 0 < Real.log (Real.log (Pa.Pz : ℝ)) := by
    apply Real.log_pos
    linarith
  have hσ34 : (3 / 4 : ℝ) ≤ s.re := by
    have h1 : 1 / Real.log (Pa.Pz : ℝ) ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hT4
    linarith
  have h1 : ‖Work.FIArea6.TauPieces.Pfac Pa chi m s‖ ≤ Pmaj Pa.Pz s.re :=
    norm_Pfac_le_Pmaj Pa chi m hchi hσ34
  have h2 : Pmaj Pa.Pz s.re
      ≤ C5 ^ 17 * Real.exp (3 * (Real.log (Real.log (Pa.Pz : ℝ)) + C)) := by
    rw [Pmaj]
    have hsplit := Finset.prod_filter_mul_prod_filter_not
      ((Nat.primesBelow (Pa.Pz + 1)).filter (fun p => p % 4 = 1)) (fun p => p < 17)
      (fun p => (1 - 2 * (p : ℝ) ^ (-s.re))⁻¹)
    rw [← hsplit]
    have hbig_nonneg : 0 ≤ ∏ p ∈ ((Nat.primesBelow (Pa.Pz + 1)).filter
        (fun p => p % 4 = 1)).filter (fun p => ¬ p < 17), (1 - 2 * (p : ℝ) ^ (-s.re))⁻¹ :=
      Finset.prod_nonneg (fun p hp =>
        inv_two_rpow_nonneg (by have := (Finset.mem_filter.mp hp).2; omega) hσ34)
    calc (∏ p ∈ ((Nat.primesBelow (Pa.Pz + 1)).filter (fun p => p % 4 = 1)).filter
              (fun p => p < 17), (1 - 2 * (p : ℝ) ^ (-s.re))⁻¹)
            * (∏ p ∈ ((Nat.primesBelow (Pa.Pz + 1)).filter (fun p => p % 4 = 1)).filter
              (fun p => ¬ p < 17), (1 - 2 * (p : ℝ) ^ (-s.re))⁻¹)
          ≤ C5 ^ 17 * (∏ p ∈ ((Nat.primesBelow (Pa.Pz + 1)).filter (fun p => p % 4 = 1)).filter
              (fun p => ¬ p < 17), (1 - 2 * (p : ℝ) ^ (-s.re))⁻¹) :=
            mul_le_mul_of_nonneg_right (prod_small_le Pa.Pz s.re hσ34) hbig_nonneg
      _ ≤ C5 ^ 17 * Real.exp (3 * (Real.log (Real.log (Pa.Pz : ℝ)) + C)) :=
            mul_le_mul_of_nonneg_left (prod_big_le Pa.Pz s.re hT4 hs C hC)
              (le_of_lt (pow_pos C5_pos 17))
  have h3 : C5 ^ 17 * Real.exp (3 * (Real.log (Real.log (Pa.Pz : ℝ)) + C))
      = C5 ^ 17 * Real.exp (3 * C) * (Real.log (Pa.Pz : ℝ)) ^ 3 := by
    have hexpval : Real.exp (3 * (Real.log (Real.log (Pa.Pz : ℝ)) + C))
        = (Real.log (Pa.Pz : ℝ)) ^ 3 * Real.exp (3 * C) := by
      calc Real.exp (3 * (Real.log (Real.log (Pa.Pz : ℝ)) + C))
          = Real.exp (3 * Real.log (Real.log (Pa.Pz : ℝ)) + 3 * C) := by
            congr 1; ring
        _ = Real.exp (3 * Real.log (Real.log (Pa.Pz : ℝ))) * Real.exp (3 * C) :=
            Real.exp_add _ _
        _ = (Real.exp (Real.log (Real.log (Pa.Pz : ℝ)))) ^ 3 * Real.exp (3 * C) := by
            rw [show (3 : ℝ) * Real.log (Real.log (Pa.Pz : ℝ))
                = ((3 : ℕ) : ℝ) * Real.log (Real.log (Pa.Pz : ℝ)) by norm_num,
              Real.exp_nat_mul]
        _ = (Real.log (Pa.Pz : ℝ)) ^ 3 * Real.exp (3 * C) := by
            rw [Real.exp_log (by linarith : (0 : ℝ) < Real.log (Pa.Pz : ℝ))]
    rw [hexpval]
    ring
  have h4 : (Real.log (Pa.Pz : ℝ)) ^ 3 ≤ (Real.log (Pa.Pz : ℝ) + 2) ^ 3 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 3
  have h5 : C5 ^ 17 * Real.exp (3 * C) * (Real.log (Pa.Pz : ℝ)) ^ 3
      ≤ C5 ^ 17 * Real.exp (3 * C) * (Real.log (Pa.Pz : ℝ) + 2) ^ 3 :=
    mul_le_mul_of_nonneg_left h4
      (le_of_lt (mul_pos (pow_pos C5_pos 17) (Real.exp_pos _)))
  linarith [h1, h2, h3, h5]

end

end Work.FIArea6Road.ZT

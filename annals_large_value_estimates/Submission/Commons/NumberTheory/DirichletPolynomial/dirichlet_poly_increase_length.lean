import Mathlib.Data.Int.Star
import Submission.Commons.Analysis.Fourier.fejer_window_localization_majorant
import Submission.Commons.NumberTheory.ArithmeticFunction.card_divisors_le_rpow

open Finset
open scoped BigOperators ComplexConjugate

set_option autoImplicit false

namespace Commons.NumberTheory.DirichletPolynomial


lemma two_pi_I_ne_zero : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
  have h1 : (2 : ℂ) ≠ 0 := by norm_num
  have h2 : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  exact mul_ne_zero (mul_ne_zero h1 h2) Complex.I_ne_zero

lemma orthogonality (P : ℕ) (hP : P ≠ 0) (d : ℤ) :
    (∑ a ∈ Finset.range P, Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) * (d : ℂ) / (P : ℂ))))
      = if (P : ℤ) ∣ d then (P : ℂ) else 0 := by
  have hPc : (P : ℂ) ≠ 0 := by exact_mod_cast hP
  set ω : ℂ := Complex.exp (2 * Real.pi * Complex.I * (d : ℂ) / (P : ℂ)) with hω
  have hterm : ∀ a : ℕ,
      Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) * (d : ℂ) / (P : ℂ))) = ω ^ a := by
    intro a
    rw [hω, ← Complex.exp_nat_mul]
    congr 1
    ring
  rw [Finset.sum_congr rfl (fun a _ => hterm a)]
  have hpow : ω ^ P = 1 := by
    rw [hω, ← Complex.exp_nat_mul]
    have harg : (P : ℂ) * (2 * Real.pi * Complex.I * (d : ℂ) / (P : ℂ))
        = (d : ℂ) * (2 * Real.pi * Complex.I) := by field_simp
    rw [harg, Complex.exp_int_mul_two_pi_mul_I]
  have hω_one : ω = 1 ↔ (P : ℤ) ∣ d := by
    rw [hω, Complex.exp_eq_one_iff]
    constructor
    · rintro ⟨n, hn⟩
      have h4 : (d : ℂ) = (n : ℂ) * (P : ℂ) := by
        have h5 := congrArg (fun z => z * (P : ℂ)) hn
        rw [div_mul_cancel₀ _ hPc] at h5
        have h6 : (2 * (Real.pi : ℂ) * Complex.I) * (d : ℂ) =
            (2 * (Real.pi : ℂ) * Complex.I) * ((n : ℂ) * (P : ℂ)) := by
          rw [h5]; ring
        exact mul_left_cancel₀ two_pi_I_ne_zero h6
      refine ⟨n, ?_⟩
      have h7 : (d : ℂ) = ((P : ℤ) * n : ℤ) := by push_cast; rw [h4]; ring
      exact_mod_cast h7
    · rintro ⟨n, hn⟩
      refine ⟨n, ?_⟩
      rw [hn]
      push_cast
      rw [show 2 * (Real.pi : ℂ) * Complex.I * ((P : ℂ) * (n : ℂ)) / (P : ℂ)
            = (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by field_simp]
  by_cases hdvd : (P : ℤ) ∣ d
  · rw [if_pos hdvd]
    have : ω = 1 := hω_one.mpr hdvd
    rw [this]; simp
  · rw [if_neg hdvd]
    have h1 : ω ≠ 1 := fun h => hdvd (hω_one.mp h)
    rw [geom_sum_eq h1 P, hpow]
    simp

lemma hterm_lem (P0 u u' : ℕ) (hP0 : 0 < P0) (a : ℕ) :
    Complex.exp (2*Real.pi*Complex.I*((a:ℂ)*(u:ℂ)/(P0:ℂ)))
      * (starRingEnd ℂ) (Complex.exp (2*Real.pi*Complex.I*((a:ℂ)*(u':ℂ)/(P0:ℂ))))
    = Complex.exp (2*Real.pi*Complex.I*((a:ℂ)*((((u:ℤ)-(u':ℤ)):ℤ):ℂ)/(P0:ℂ))) := by
  have hPc : ((P0:ℕ):ℂ) ≠ 0 := by exact_mod_cast (by omega : P0 ≠ 0)
  have hconj : (starRingEnd ℂ) (Complex.exp (2*Real.pi*Complex.I*((a:ℂ)*(u':ℂ)/(P0:ℂ))))
      = Complex.exp (-(2*Real.pi*Complex.I*((a:ℂ)*(u':ℂ)/(P0:ℂ)))) := by
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, map_div₀, map_natCast, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [hconj, ← Complex.exp_add]
  congr 1
  push_cast
  field_simp
  ring

lemma charsum_identity_complex (P0 u1 u2 : ℕ) (hP0 : u2 - u1 < P0) (w : ℕ → ℂ) :
    (∑ a ∈ Finset.range P0, (∑ u ∈ Finset.Icc u1 u2,
        Complex.exp (2*Real.pi*Complex.I*((a:ℂ)*(u:ℂ)/(P0:ℂ))) * w u)
      * (starRingEnd ℂ) (∑ u ∈ Finset.Icc u1 u2,
        Complex.exp (2*Real.pi*Complex.I*((a:ℂ)*(u:ℂ)/(P0:ℂ))) * w u))
      = (P0 : ℂ) * ∑ u ∈ Finset.Icc u1 u2, w u * (starRingEnd ℂ) (w u) := by
  have hP0pos : 0 < P0 := by omega
  have horth : ∀ u ∈ Finset.Icc u1 u2, ∀ u' ∈ Finset.Icc u1 u2,
      (∑ a ∈ Finset.range P0, Complex.exp (2*Real.pi*Complex.I*((a:ℂ)*(u:ℂ)/(P0:ℂ)))
        * (starRingEnd ℂ) (Complex.exp (2*Real.pi*Complex.I*((a:ℂ)*(u':ℂ)/(P0:ℂ)))))
      = if u = u' then (P0 : ℂ) else 0 := by
    intro u hu u' hu'
    obtain ⟨hu1, hu2'⟩ := Finset.mem_Icc.mp hu
    obtain ⟨hu'1, hu'2⟩ := Finset.mem_Icc.mp hu'
    have habs : |(u:ℤ)-(u':ℤ)| < (P0:ℤ) := by
      have hle : |(u:ℤ)-(u':ℤ)| ≤ ((u2-u1:ℕ):ℤ) := by
        rw [abs_le]; constructor <;> (push_cast; omega)
      exact lt_of_le_of_lt hle (by exact_mod_cast hP0)
    have hdvd0 : ((P0:ℤ)) ∣ ((u:ℤ)-(u':ℤ)) ↔ u = u' := by
      constructor
      · intro hd
        have hd0 : ((u:ℤ)-(u':ℤ)) = 0 := by
          obtain ⟨k, hk⟩ := hd
          have hk0 : k = 0 := by
            have h1 : ((P0:ℤ)) * |k| < (P0:ℤ) := by
              have hb := habs; rw [hk, abs_mul] at hb; simpa using hb
            have h2 : |k| = 0 := by have := abs_nonneg (k:ℤ); nlinarith [h1, hP0pos]
            exact abs_eq_zero.mp h2
          rw [hk0, mul_zero] at hk; exact hk
        omega
      · intro h
        rw [show ((u:ℤ)-(u':ℤ)) = 0 by omega]; exact dvd_zero _
    rw [Finset.sum_congr rfl (fun a _ => hterm_lem P0 u u' hP0pos a),
        orthogonality P0 (by omega) ((u:ℤ)-(u':ℤ)), if_congr hdvd0 rfl rfl]
  calc (∑ a ∈ Finset.range P0, (∑ u ∈ Finset.Icc u1 u2,
        Complex.exp (2*Real.pi*Complex.I*((a:ℂ)*(u:ℂ)/(P0:ℂ))) * w u)
      * (starRingEnd ℂ) (∑ u ∈ Finset.Icc u1 u2,
        Complex.exp (2*Real.pi*Complex.I*((a:ℂ)*(u:ℂ)/(P0:ℂ))) * w u))
      = ∑ a ∈ Finset.range P0, ∑ u ∈ Finset.Icc u1 u2, ∑ u' ∈ Finset.Icc u1 u2,
          Complex.exp (2*Real.pi*Complex.I*((a:ℂ)*(u:ℂ)/(P0:ℂ)))
          * (starRingEnd ℂ) (Complex.exp (2*Real.pi*Complex.I*((a:ℂ)*(u':ℂ)/(P0:ℂ))))
          * (w u * (starRingEnd ℂ) (w u')) := by
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [map_sum]
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun u _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun u' _ => ?_)
        simp only [map_mul]
        ring
    _ = ∑ u ∈ Finset.Icc u1 u2, ∑ u' ∈ Finset.Icc u1 u2,
          (∑ a ∈ Finset.range P0, Complex.exp (2*Real.pi*Complex.I*((a:ℂ)*(u:ℂ)/(P0:ℂ)))
            * (starRingEnd ℂ) (Complex.exp (2*Real.pi*Complex.I*((a:ℂ)*(u':ℂ)/(P0:ℂ)))))
          * (w u * (starRingEnd ℂ) (w u')) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun u _ => ?_)
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun u' _ => ?_)
        rw [Finset.sum_mul]
    _ = ∑ u ∈ Finset.Icc u1 u2, ∑ u' ∈ Finset.Icc u1 u2,
          (if u = u' then (P0 : ℂ) else 0) * (w u * (starRingEnd ℂ) (w u')) := by
        refine Finset.sum_congr rfl (fun u hu => ?_)
        refine Finset.sum_congr rfl (fun u' hu' => ?_)
        rw [horth u hu u' hu']
    _ = (P0 : ℂ) * ∑ u ∈ Finset.Icc u1 u2, w u * (starRingEnd ℂ) (w u) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun u hu => ?_)
        have hsimp : ∀ u' ∈ Finset.Icc u1 u2,
            (if u = u' then (P0 : ℂ) else 0) * (w u * (starRingEnd ℂ) (w u'))
            = (if u = u' then (P0 : ℂ) * (w u * (starRingEnd ℂ) (w u')) else 0) := by
          intro u' _; by_cases h : u = u' <;> simp [h]
        rw [Finset.sum_congr rfl hsimp, Finset.sum_ite_eq, if_pos hu]

lemma charsum_identity (P0 u1 u2 : ℕ) (hP0 : u2 - u1 < P0) (w : ℕ → ℂ) :
    (∑ a ∈ Finset.range P0, Complex.normSq (∑ u ∈ Finset.Icc u1 u2,
        Complex.exp (2*Real.pi*Complex.I*((a:ℂ)*(u:ℂ)/(P0:ℂ))) * w u))
      = (P0 : ℝ) * ∑ u ∈ Finset.Icc u1 u2, Complex.normSq (w u) := by
  have hc := charsum_identity_complex P0 u1 u2 hP0 w
  have hL : ∀ a, Complex.normSq (∑ u ∈ Finset.Icc u1 u2,
        Complex.exp (2*Real.pi*Complex.I*((a:ℂ)*(u:ℂ)/(P0:ℂ))) * w u)
      = ((∑ u ∈ Finset.Icc u1 u2, Complex.exp (2*Real.pi*Complex.I*((a:ℂ)*(u:ℂ)/(P0:ℂ))) * w u)
        * (starRingEnd ℂ) (∑ u ∈ Finset.Icc u1 u2, Complex.exp (2*Real.pi*Complex.I*((a:ℂ)*(u:ℂ)/(P0:ℂ))) * w u)).re := by
    intro a
    have h2 : (Complex.normSq (∑ u ∈ Finset.Icc u1 u2,
          Complex.exp (2*Real.pi*Complex.I*((a:ℂ)*(u:ℂ)/(P0:ℂ))) * w u) : ℂ)
        = (∑ u ∈ Finset.Icc u1 u2, Complex.exp (2*Real.pi*Complex.I*((a:ℂ)*(u:ℂ)/(P0:ℂ))) * w u)
          * (starRingEnd ℂ) (∑ u ∈ Finset.Icc u1 u2, Complex.exp (2*Real.pi*Complex.I*((a:ℂ)*(u:ℂ)/(P0:ℂ))) * w u) := by
      rw [Complex.normSq_eq_conj_mul_self, mul_comm]
    rw [← h2, Complex.ofReal_re]
  have hR : ∀ u, Complex.normSq (w u) = (w u * (starRingEnd ℂ) (w u)).re := by
    intro u
    have h2 : (Complex.normSq (w u) : ℂ) = w u * (starRingEnd ℂ) (w u) := by
      rw [Complex.normSq_eq_conj_mul_self, mul_comm]
    rw [← h2, Complex.ofReal_re]
  trans ∑ a ∈ Finset.range P0, ((∑ u ∈ Finset.Icc u1 u2, Complex.exp (2*Real.pi*Complex.I*((a:ℂ)*(u:ℂ)/(P0:ℂ))) * w u)
        * (starRingEnd ℂ) (∑ u ∈ Finset.Icc u1 u2, Complex.exp (2*Real.pi*Complex.I*((a:ℂ)*(u:ℂ)/(P0:ℂ))) * w u)).re
  · exact Finset.sum_congr rfl (fun a _ => hL a)
  · rw [← Complex.re_sum, hc, Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul,
        sub_zero, Complex.re_sum]
    congr 1
    exact Finset.sum_congr rfl (fun u _ => (hR u).symm)

noncomputable def sqt (n : ℕ) : ℂ := ((Real.sqrt (n:ℝ) : ℝ) : ℂ)
noncomputable def dval (n : ℕ) (θ : ℝ) : ℂ := (n:ℂ)^(Complex.I*(θ:ℂ)) / sqt n

lemma cpow_I_eq_exp (n : ℕ) (hn : 1 ≤ n) (θ : ℝ) :
    (n:ℂ)^(Complex.I * (θ:ℂ)) = Complex.exp (((θ * Real.log n : ℝ)) * Complex.I) := by
  have hn0 : (n:ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  rw [Complex.cpow_def_of_ne_zero hn0]
  have hcast : ((n:ℕ):ℂ) = (((n:ℝ)):ℂ) := by simp
  rw [hcast, ← Complex.ofReal_log (by positivity : (0:ℝ) ≤ (n:ℝ))]
  congr 1
  push_cast
  ring
lemma sqrt_mul (n u : ℕ) : sqt (n*u) = sqt n * sqt u := by
  rw [sqt, sqt, sqt, Nat.cast_mul, ← Complex.ofReal_mul, Real.sqrt_mul (by positivity)]
lemma cpow_mul (n u : ℕ) (hn : 1 ≤ n) (hu : 1 ≤ u) (θ : ℝ) :
    (n:ℂ)^(Complex.I * (θ:ℂ)) * (u:ℂ)^(Complex.I * (θ:ℂ)) = ((n*u:ℕ):ℂ)^(Complex.I * (θ:ℂ)) := by
  have hnu : 1 ≤ n*u := by simpa using Nat.mul_le_mul hn hu
  rw [cpow_I_eq_exp n hn, cpow_I_eq_exp u hu, cpow_I_eq_exp (n*u) hnu]
  rw [← Complex.exp_add]
  congr 1
  rw [Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
  push_cast
  ring

lemma dval_mul (n u : ℕ) (hn : 1 ≤ n) (hu : 1 ≤ u) (θ : ℝ) :
    dval (n*u) θ = dval n θ * dval u θ := by
  have h1 : ((n:ℂ)^(Complex.I*(θ:ℂ)) / sqt n) * ((u:ℂ)^(Complex.I*(θ:ℂ)) / sqt u)
      = ((n:ℂ)^(Complex.I*(θ:ℂ)) * (u:ℂ)^(Complex.I*(θ:ℂ))) / (sqt n * sqt u) := by ring
  rw [dval, dval, dval, h1, cpow_mul n u hn hu θ, ← sqrt_mul n u]

noncomputable def bfun (A B u1 u2 : ℕ) (c ea : ℕ → ℂ) (m : ℕ) : ℂ :=
  ∑ p ∈ (Finset.Icc A B ×ˢ Finset.Icc u1 u2).filter (fun p => p.1 * p.2 = m),
    c p.1 * ea p.2

lemma product_reindex (A B u1 u2 Mm : ℕ) (hA : 1 ≤ A) (hu1 : 1 ≤ u1)
    (hM1 : Mm ≤ A*u1) (hM2 : B*u2 ≤ 2*Mm) (c ea : ℕ → ℂ) (θ : ℝ) :
    (∑ n ∈ Finset.Icc A B, c n * dval n θ) * (∑ u ∈ Finset.Icc u1 u2, ea u * dval u θ)
    = ∑ m ∈ (Finset.Icc Mm (2*Mm) : Finset ℕ), bfun A B u1 u2 c ea m * dval m θ := by
  have hprod : (∑ n ∈ Finset.Icc A B, c n * dval n θ) * (∑ u ∈ Finset.Icc u1 u2, ea u * dval u θ)
      = ∑ p ∈ Finset.Icc A B ×ˢ Finset.Icc u1 u2, c p.1 * ea p.2 * dval (p.1*p.2) θ := by
    rw [Finset.sum_mul]
    have h1 : ∀ n ∈ Finset.Icc A B, c n * dval n θ
        * (∑ u ∈ Finset.Icc u1 u2, ea u * dval u θ)
        = ∑ u ∈ Finset.Icc u1 u2, c n * ea u * dval (n*u) θ := by
      intro n hn
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun u hu => ?_)
      have hn1 : 1 ≤ n := le_trans hA (Finset.mem_Icc.mp hn).1
      have hu1' : 1 ≤ u := le_trans hu1 (Finset.mem_Icc.mp hu).1
      rw [dval_mul n u hn1 hu1' θ]; ring
    rw [Finset.sum_congr rfl h1,
        ← Finset.sum_product (Finset.Icc A B) (Finset.Icc u1 u2)
          (fun p => c p.1 * ea p.2 * dval (p.1*p.2) θ)]
  rw [hprod]
  have hmap : ∀ p ∈ Finset.Icc A B ×ˢ Finset.Icc u1 u2, p.1 * p.2 ∈ Finset.Icc Mm (2*Mm) := by
    intro p hp
    rw [Finset.mem_product] at hp
    obtain ⟨hn, hu⟩ := hp
    have hn1 : A ≤ p.1 := (Finset.mem_Icc.mp hn).1
    have hn2 : p.1 ≤ B := (Finset.mem_Icc.mp hn).2
    have hu1' : u1 ≤ p.2 := (Finset.mem_Icc.mp hu).1
    have hu2' : p.2 ≤ u2 := (Finset.mem_Icc.mp hu).2
    rw [Finset.mem_Icc]
    exact ⟨le_trans hM1 (Nat.mul_le_mul hn1 hu1'), le_trans (Nat.mul_le_mul hn2 hu2') hM2⟩
  symm
  calc ∑ m ∈ (Finset.Icc Mm (2*Mm) : Finset ℕ), bfun A B u1 u2 c ea m * dval m θ
      = ∑ m ∈ (Finset.Icc Mm (2*Mm) : Finset ℕ),
          (∑ p ∈ (Finset.Icc A B ×ˢ Finset.Icc u1 u2).filter (fun p => p.1 * p.2 = m),
            c p.1 * ea p.2) * dval m θ := by simp only [bfun]
    _ = ∑ m ∈ (Finset.Icc Mm (2*Mm) : Finset ℕ),
          ∑ p ∈ (Finset.Icc A B ×ˢ Finset.Icc u1 u2).filter (fun p => p.1 * p.2 = m),
            (c p.1 * ea p.2) * dval m θ := by
        refine Finset.sum_congr rfl (fun m _ => ?_)
        rw [Finset.sum_mul]
    _ = ∑ m ∈ (Finset.Icc Mm (2*Mm) : Finset ℕ),
          ∑ p ∈ Finset.Icc A B ×ˢ Finset.Icc u1 u2,
            (if p.1 * p.2 = m then (c p.1 * ea p.2) * dval m θ else 0) := by
        refine Finset.sum_congr rfl (fun m _ => ?_)
        rw [Finset.sum_filter]
    _ = ∑ p ∈ Finset.Icc A B ×ˢ Finset.Icc u1 u2,
          ∑ m ∈ (Finset.Icc Mm (2*Mm) : Finset ℕ),
            (if p.1 * p.2 = m then (c p.1 * ea p.2) * dval m θ else 0) :=
        Finset.sum_comm
    _ = ∑ p ∈ Finset.Icc A B ×ˢ Finset.Icc u1 u2, c p.1 * ea p.2 * dval (p.1*p.2) θ := by
        refine Finset.sum_congr rfl (fun p hp => ?_)
        rw [Finset.sum_ite_eq, if_pos (hmap p hp)]

lemma norm_cpow_I (n : ℕ) (hn : 1 ≤ n) (θ : ℝ) :
    ‖(n:ℂ)^(Complex.I*(θ:ℂ))‖ = 1 := by
  rw [cpow_I_eq_exp n hn θ]
  exact Complex.norm_exp_ofReal_mul_I _

lemma normSq_dval (u : ℕ) (hu : 1 ≤ u) (θ : ℝ) : Complex.normSq (dval u θ) = 1/u := by
  have h1 : Complex.normSq ((u:ℂ)^(Complex.I*(θ:ℂ))) = 1 := by
    rw [Complex.normSq_eq_norm_sq, norm_cpow_I u hu θ]; norm_num
  have h2 : Complex.normSq (sqt u) = (u:ℝ) := by
    rw [sqt, Complex.normSq_ofReal, ← sq]; exact Real.sq_sqrt (by positivity : (0:ℝ) ≤ (u:ℝ))
  rw [dval, Complex.normSq_div, h1, h2, one_div]

noncomputable def eaf (P0 : ℕ) (a u : ℕ) : ℂ :=
  Complex.exp (2*Real.pi*Complex.I*((a:ℂ)*(u:ℂ)/(P0:ℂ)))
noncomputable def Ppoly (A B : ℕ) (c : ℕ→ℂ) (θ : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc A B, c n * dval n θ
noncomputable def Qpoly (L : ℕ) (θ : ℝ) : ℂ :=
  ∑ m ∈ Finset.Icc L (2*L), dval m θ
noncomputable def Cpoly (P0 u1 u2 : ℕ) (a : ℕ) (θ : ℝ) : ℂ :=
  ∑ u ∈ Finset.Icc u1 u2, eaf P0 a u * dval u θ



theorem piece_increase
    (A B u1 u2 P0 Mm : ℕ) (hA : 1 ≤ A) (hu1 : 1 ≤ u1) (h12 : u1 ≤ u2) (hP0 : u2 - u1 < P0)
    (hMm : 1 ≤ Mm) (hM1 : Mm ≤ A*u1) (hM2 : B*u2 ≤ 2*Mm)
    (c : ℕ → ℂ) (Bc D Cmaj : ℝ) (hBc : 0 ≤ Bc) (hD0 : 0 ≤ D) (hCmaj : 0 ≤ Cmaj)
    (hD : ∀ a m, ‖bfun A B u1 u2 c (fun u => eaf P0 a u) m‖ ≤ Bc * D)
    (hMAJ : ∀ (N : ℕ) (a : ℕ → ℂ) (cc : ℕ → ℝ), 1 ≤ N → (∀ n, ‖a n‖ ≤ cc n) →
        ∀ (R : ℕ) (t : Fin R → ℝ), (∀ i j, i ≠ j → 1 ≤ |t i - t j|) → ∀ Δ : ℝ, 0 < Δ →
        (∑ i, ∑ j, (if |t i - t j| ≤ Δ then ‖∑ n ∈ Finset.Icc N (2*N), a n * dval n (t i - t j)‖^2 else 0))
        ≤ Cmaj * (∑ i, ∑ j, (if |t i - t j| ≤ Δ then
            ‖∑ n ∈ Finset.Icc N (2*N), ((cc n:ℝ):ℂ) * dval n (t i - t j)‖^2 else 0)))
    (Δ : ℝ) (hΔ : 0 < Δ) (R : ℕ) (t : Fin R → ℝ) (ht : ∀ i j, i ≠ j → 1 ≤ |t i - t j|) :
    (∑ i, ∑ j, (if |t i - t j| ≤ Δ then ‖Ppoly A B c (t i - t j)‖^2 else 0))
    ≤ Cmaj * (Bc*D)^2 / (∑ u ∈ Finset.Icc u1 u2, (1:ℝ)/u)
        * (∑ i, ∑ j, (if |t i - t j| ≤ Δ then ‖Qpoly Mm (t i - t j)‖^2 else 0)) := by
  set G : ℝ := ∑ u ∈ Finset.Icc u1 u2, (1:ℝ)/u with hG
  set LHS : ℝ := ∑ i, ∑ j, (if |t i - t j| ≤ Δ then ‖Ppoly A B c (t i - t j)‖^2 else 0) with hLHS
  set RHSm : ℝ := ∑ i, ∑ j, (if |t i - t j| ≤ Δ then ‖Qpoly Mm (t i - t j)‖^2 else 0) with hRHS
  have hGnn : 0 < G := by
    rw [hG]
    refine Finset.sum_pos (fun u hu => ?_) ⟨u1, Finset.mem_Icc.mpr ⟨le_rfl, h12⟩⟩
    have : 0 < u := lt_of_lt_of_le (by norm_num) (le_trans hu1 (Finset.mem_Icc.mp hu).1)
    positivity
  have hP0pos : 0 < P0 := by omega
  have hchar : ∀ θ : ℝ, (∑ a ∈ Finset.range P0, Complex.normSq (Cpoly P0 u1 u2 a θ))
      = (P0 : ℝ) * G := by
    intro θ
    have h1 : (∑ a ∈ Finset.range P0, Complex.normSq (∑ u ∈ Finset.Icc u1 u2, eaf P0 a u * dval u θ))
        = (P0 : ℝ) * (∑ u ∈ Finset.Icc u1 u2, Complex.normSq (dval u θ)) :=
      charsum_identity P0 u1 u2 hP0 (fun u => dval u θ)
    have h2 : (∑ u ∈ Finset.Icc u1 u2, Complex.normSq (dval u θ)) = G := by
      rw [hG]
      exact Finset.sum_congr rfl (fun u hu => normSq_dval u (le_trans hu1 (Finset.mem_Icc.mp hu).1) θ)
    have hCp : (∑ a ∈ Finset.range P0, Complex.normSq (Cpoly P0 u1 u2 a θ))
        = ∑ a ∈ Finset.range P0, Complex.normSq (∑ u ∈ Finset.Icc u1 u2, eaf P0 a u * dval u θ) := by
      exact Finset.sum_congr rfl (fun a _ => by rw [Cpoly])
    rw [hCp, h1, h2]
  have hkey : ∀ a : ℕ, ∀ θ : ℝ, (Ppoly A B c θ) * (Cpoly P0 u1 u2 a θ)
      = ∑ m ∈ Finset.Icc Mm (2*Mm), bfun A B u1 u2 c (fun u => eaf P0 a u) m * dval m θ := fun a θ =>
    product_reindex A B u1 u2 Mm hA hu1 hM1 hM2 c (fun u => eaf P0 a u) θ
  have hnormmul : ∀ θ : ℝ, (P0:ℝ)*G*‖Ppoly A B c θ‖^2
      = ∑ a ∈ Finset.range P0, ‖Ppoly A B c θ * Cpoly P0 u1 u2 a θ‖^2 := by
    intro θ
    rw [← Complex.normSq_eq_norm_sq, ← hchar θ, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun a _ => by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_mul]; ring)
  have hstep2a : (P0:ℝ)*G*LHS = ∑ i, ∑ j, (if |t i - t j| ≤ Δ then ∑ a ∈ Finset.range P0,
      ‖Ppoly A B c (t i - t j) * Cpoly P0 u1 u2 a (t i - t j)‖^2 else 0) := by
    rw [hLHS, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    by_cases h : |t i - t j| ≤ Δ
    · rw [if_pos h, if_pos h]; exact hnormmul _
    · rw [if_neg h, if_neg h, mul_zero]
  have he1 : ∀ i j, (if |t i - t j| ≤ Δ then ∑ a ∈ Finset.range P0,
        ‖Ppoly A B c (t i - t j) * Cpoly P0 u1 u2 a (t i - t j)‖^2 else 0)
      = ∑ a ∈ Finset.range P0, (if |t i - t j| ≤ Δ then
        ‖Ppoly A B c (t i - t j) * Cpoly P0 u1 u2 a (t i - t j)‖^2 else 0) := by
    intro i j
    by_cases h : |t i - t j| ≤ Δ
    · rw [if_pos h]
      exact Finset.sum_congr rfl (fun a _ => (if_pos h).symm)
    · rw [if_neg h]
      exact (Finset.sum_eq_zero (fun a _ => by rw [if_neg h])).symm
  let Ff : ℕ → Fin R → Fin R → ℝ := fun a i j =>
    if |t i - t j| ≤ Δ then ‖Ppoly A B c (t i - t j) * Cpoly P0 u1 u2 a (t i - t j)‖^2 else 0
  have hswap : (∑ i : Fin R, ∑ j : Fin R, ∑ a ∈ Finset.range P0, Ff a i j)
      = ∑ a ∈ Finset.range P0, ∑ i : Fin R, ∑ j : Fin R, Ff a i j := by
    rw [show (∑ i : Fin R, ∑ j : Fin R, ∑ a ∈ Finset.range P0, Ff a i j)
        = ∑ i : Fin R, ∑ a ∈ Finset.range P0, ∑ j : Fin R, Ff a i j from
      Finset.sum_congr rfl (fun i _ => by rw [Finset.sum_comm])]
    rw [Finset.sum_comm]
  have hstep2c : (∑ a ∈ Finset.range P0, ∑ i, ∑ j, (if |t i - t j| ≤ Δ then
        ‖Ppoly A B c (t i - t j) * Cpoly P0 u1 u2 a (t i - t j)‖^2 else 0))
      = ∑ a ∈ Finset.range P0, ∑ i, ∑ j, (if |t i - t j| ≤ Δ then
        ‖∑ m ∈ Finset.Icc Mm (2*Mm), bfun A B u1 u2 c (fun u => eaf P0 a u) m * dval m (t i - t j)‖^2 else 0) := by
    refine Finset.sum_congr rfl (fun a _ => ?_)
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by
      by_cases h : |t i - t j| ≤ Δ
      · rw [if_pos h, if_pos h, hkey a (t i - t j)]
      · rw [if_neg h, if_neg h]))
  have hstep2 : (P0:ℝ)*G*LHS = ∑ a ∈ Finset.range P0, ∑ i, ∑ j, (if |t i - t j| ≤ Δ then
        ‖∑ m ∈ Finset.Icc Mm (2*Mm), bfun A B u1 u2 c (fun u => eaf P0 a u) m * dval m (t i - t j)‖^2 else 0) := by
    rw [hstep2a]
    rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => he1 i j))]
    rw [show (∑ i : Fin R, ∑ j : Fin R, ∑ a ∈ Finset.range P0,
        (if |t i - t j| ≤ Δ then ‖Ppoly A B c (t i - t j) * Cpoly P0 u1 u2 a (t i - t j)‖^2 else 0))
        = ∑ a ∈ Finset.range P0, ∑ i : Fin R, ∑ j : Fin R,
        (if |t i - t j| ≤ Δ then ‖Ppoly A B c (t i - t j) * Cpoly P0 u1 u2 a (t i - t j)‖^2 else 0) from hswap]
    rw [hstep2c]
  have hbound : ∀ a ∈ Finset.range P0,
      (∑ i, ∑ j, (if |t i - t j| ≤ Δ then
        ‖∑ m ∈ Finset.Icc Mm (2*Mm), bfun A B u1 u2 c (fun u => eaf P0 a u) m * dval m (t i - t j)‖^2 else 0))
      ≤ Cmaj * (Bc*D)^2 * RHSm := by
    intro a _
    have hQ : (∑ i, ∑ j, (if |t i - t j| ≤ Δ then
          ‖∑ n ∈ Finset.Icc Mm (2*Mm), (((fun _ => Bc*D) n : ℝ):ℂ) * dval n (t i - t j)‖^2 else 0))
        = (Bc*D)^2 * RHSm := by
      rw [hRHS, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      by_cases h : |t i - t j| ≤ Δ
      · rw [if_pos h, if_pos h]
        have hfac : (∑ n ∈ Finset.Icc Mm (2*Mm), (((fun _ => Bc*D) n : ℝ):ℂ) * dval n (t i - t j))
            = ((Bc*D:ℝ):ℂ) * Qpoly Mm (t i - t j) := by
          rw [Qpoly, Finset.mul_sum]
        rw [hfac, norm_mul, mul_pow, ← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
        ring
      · rw [if_neg h, if_neg h, mul_zero]
    have hmaj := hMAJ Mm (fun m => bfun A B u1 u2 c (fun u => eaf P0 a u) m)
        (fun _ => Bc*D) hMm (fun n => hD a n) R t ht Δ hΔ
    refine le_trans hmaj ?_
    rw [hQ, ← mul_assoc]
  have hstep3 : (∑ a ∈ Finset.range P0, ∑ i, ∑ j, (if |t i - t j| ≤ Δ then
        ‖∑ m ∈ Finset.Icc Mm (2*Mm), bfun A B u1 u2 c (fun u => eaf P0 a u) m * dval m (t i - t j)‖^2 else 0))
      ≤ ∑ _a ∈ Finset.range P0, Cmaj * (Bc*D)^2 * RHSm :=
    Finset.sum_le_sum hbound
  have hstep4 : (∑ _a ∈ Finset.range P0, Cmaj * (Bc*D)^2 * RHSm)
      = (P0:ℝ) * (Cmaj * (Bc*D)^2 * RHSm) := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hfinal : (P0:ℝ) * G * LHS ≤ (P0:ℝ) * (Cmaj * (Bc*D)^2 * RHSm) := by
    rw [hstep2, ← hstep4]; exact hstep3
  have hP0R : (0:ℝ) < (P0:ℝ) := by exact_mod_cast hP0pos
  have hGR : 0 < G := hGnn
  rw [div_mul_eq_mul_div, le_div_iff₀ hGnn]
  nlinarith [hfinal, hP0R, hGR]


theorem gain_bound_interval (A Bb M : ℕ) (hA : 1 ≤ A) (hBb1 : 1 ≤ Bb) (hBb : Bb ≤ 4*A/3) (hBM : Bb ≤ M) (hM : 1 ≤ M)
    (hu : (M + A - 1)/A ≤ 2*M/Bb) :
    (1:ℝ)/10 ≤ ∑ u ∈ Finset.Icc ((M + A - 1)/A) (2*M/Bb), (1:ℝ)/u := by
  have hAposN : 0 < A := lt_of_lt_of_le Nat.zero_lt_one hA
  have hBposN : 0 < Bb := lt_of_lt_of_le Nat.zero_lt_one hBb1
  have hBbA : 3*Bb ≤ 4*A := by omega
  have hbmod : (2*M/Bb)*Bb + Bb ≥ 2*M + 1 := by
    have h1 := Nat.div_add_mod (2*M) Bb
    have h2 := Nat.mod_lt (2*M) hBposN
    rw [Nat.mul_comm Bb] at h1
    omega
  have h1a : (M+A-1)/A ≤ M/A + 1 := by
    calc (M+A-1)/A ≤ (M+A)/A := Nat.div_le_div_right (Nat.sub_le _ _)
      _ = M/A + 1 := Nat.add_div_right M hAposN
  have h2a : 10*(M/A) ≤ 10*M/A := by
    rw [Nat.le_div_iff_mul_le hAposN]
    calc 10*(M/A)*A = 10*((M/A)*A) := by ring
      _ ≤ 10*M := Nat.mul_le_mul_left 10 (Nat.div_mul_le_self M A)
  have h10 : 10*((M+A-1)/A) ≤ 9*(2*M/Bb) + 10 := by
    by_cases hcase : Bb ≤ M/2
    · have h2Bb : 2*Bb ≤ M := by omega
      have h3a : 10*M/A ≤ 9*(2*M/Bb) := by
        rw [Nat.div_le_iff_le_mul hAposN]
        have key : 4 * (10*M + 1) ≤ 4 * (9*(2*M/Bb)*A + A) := by
          have e1 : 4 * (9*(2*M/Bb)*A) ≥ 27 * ((2*M/Bb)*Bb) := by
            have h := Nat.mul_le_mul_left (9*(2*M/Bb)) hBbA
            nlinarith [h]
          have e2 : (2*M/Bb)*Bb ≥ 2*M + 1 - Bb := by omega
          have e4 : 27*Bb ≤ 14*M := by omega
          have e3 : 4*A ≥ 3*Bb := hBbA
          nlinarith [e1, e2, e3, e4]
        omega
      omega
    · push Not at hcase
      have hb3 : 2*M/Bb ≤ 3 := by
        rw [Nat.div_le_iff_le_mul_add_pred hBposN]
        omega
      have ha_le : (M+A-1)/A ≤ 2*M/Bb := hu
      omega
  have hab : (M + A - 1)/A ≤ 2*M/Bb := hu
  have hbnn : (0:ℝ) < (2*M/Bb : ℕ) := by
    have : 0 < 2*M/Bb := Nat.div_pos (by omega) hBposN
    exact_mod_cast this
  have hsum : ((Finset.Icc ((M+A-1)/A) (2*M/Bb)).card : ℝ) / (2*M/Bb : ℕ)
      ≤ ∑ u ∈ Finset.Icc ((M+A-1)/A) (2*M/Bb), (1:ℝ)/u := by
    have h1 : ∑ u ∈ Finset.Icc ((M+A-1)/A) (2*M/Bb), (1/(2*M/Bb : ℕ) : ℝ)
        ≤ ∑ u ∈ Finset.Icc ((M+A-1)/A) (2*M/Bb), (1:ℝ)/u := by
      refine Finset.sum_le_sum (fun u hu' => ?_)
      rw [Finset.mem_Icc] at hu'
      rw [show (1:ℝ)/(2*M/Bb : ℕ) = 1/(2*M/Bb : ℕ) by rfl, show (1:ℝ)/u = 1/u by rfl]
      have ha1 : 1 ≤ (M+A-1)/A := (Nat.one_le_div_iff hAposN).mpr (Nat.le_sub_one_of_lt (by rw [add_comm]; exact Nat.lt_add_of_pos_right (by omega : 0 < M)))
      have hu0 : 0 < u := lt_of_lt_of_le (lt_of_lt_of_le Nat.zero_lt_one ha1) hu'.1
      exact one_div_le_one_div_of_le (by exact_mod_cast hu0) (by exact_mod_cast hu'.2)
    have h2 : (∑ u ∈ Finset.Icc ((M+A-1)/A) (2*M/Bb), (1/(2*M/Bb : ℕ) : ℝ))
        = ((Finset.Icc ((M+A-1)/A) (2*M/Bb)).card : ℝ) / (2*M/Bb : ℕ) := by
      rw [Finset.sum_const, nsmul_eq_mul]; ring
    linarith [h1, h2]
  refine le_trans ?_ hsum
  rw [le_div_iff₀ hbnn]
  have hcard : ((Finset.Icc ((M+A-1)/A) (2*M/Bb)).card : ℝ)
      = ((2*M/Bb : ℕ):ℝ) + 1 - (((M+A-1)/A : ℕ):ℝ) := by
    rw [Nat.card_Icc, Nat.cast_sub (by omega : (M+A-1)/A ≤ 2*M/Bb + 1)]; push_cast; ring
  rw [hcard]
  have hnum : 10*(((M+A-1)/A : ℕ):ℝ) ≤ 9*((2*M/Bb : ℕ):ℝ) + 10 := by
    push_cast; exact_mod_cast h10
  nlinarith [hnum]


lemma norm_eaf (P0 a u : ℕ) : ‖eaf P0 a u‖ = 1 := by
  rw [eaf]
  have h : (2 * (Real.pi:ℂ) * Complex.I * ((a:ℂ)*(u:ℂ)/(P0:ℂ)))
      = ((2 * Real.pi * (a:ℝ) * (u:ℝ) / (P0:ℝ) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

lemma bfun_norm_le (A Bi u1 u2 P0 : ℕ) (c : ℕ → ℂ) (a : ℕ) (B : ℝ)
    (hc : ∀ n, ‖c n‖ ≤ B) (hA : 1 ≤ A) (hu1 : 1 ≤ u1) (m : ℕ) :
    ‖bfun A Bi u1 u2 c (fun u => eaf P0 a u) m‖ ≤ B * (m.divisors.card : ℝ) := by
  have hBnn : 0 ≤ B := le_trans (norm_nonneg (c 0)) (hc 0)
  set sF := (Finset.Icc A Bi ×ˢ Finset.Icc u1 u2).filter (fun p => p.1 * p.2 = m) with hsF
  have h1 : ‖bfun A Bi u1 u2 c (fun u => eaf P0 a u) m‖ ≤ ∑ p ∈ sF, ‖c p.1‖ := by
    rw [bfun, ← hsF]
    refine le_trans (norm_sum_le _ _) ?_
    refine Finset.sum_le_sum (fun p hp => ?_)
    rw [norm_mul, norm_eaf, mul_one]
  have h2 : ∑ p ∈ sF, ‖c p.1‖ ≤ B * (sF.card : ℝ) := by
    calc ∑ p ∈ sF, ‖c p.1‖ ≤ ∑ p ∈ sF, B := Finset.sum_le_sum (fun p hp => hc p.1)
      _ = B * (sF.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  have h3 : (sF.card : ℝ) ≤ (m.divisors.card : ℝ) := by
    have : sF.card ≤ m.divisors.card := by
      apply Finset.card_le_card_of_injOn (fun p : ℕ × ℕ => p.2)
      · intro p hp
        simp only [Finset.mem_coe, hsF, Finset.mem_filter, Finset.mem_product] at hp
        obtain ⟨⟨hp1, hp2⟩, hpm⟩ := hp
        have hp2n : 0 < p.2 := lt_of_lt_of_le (by omega) (le_trans hu1 (Finset.mem_Icc.mp hp2).1)
        rw [Finset.mem_coe, Nat.mem_divisors]
        have hp1n : 0 < p.1 := by have := (Finset.mem_Icc.mp hp1).1; omega
        exact ⟨⟨p.1, by rw [← hpm]; ring⟩, by rw [← hpm]; exact Nat.mul_ne_zero hp1n.ne' hp2n.ne'⟩
      · intro p hp q hq hpq
        simp only [Finset.mem_coe, hsF, Finset.mem_filter, Finset.mem_product] at hp hq
        obtain ⟨⟨hp1, hp2⟩, hpm⟩ := hp
        obtain ⟨⟨hq1, hq2⟩, hqm⟩ := hq
        have hp2n : 0 < p.2 := by have := (Finset.mem_Icc.mp hp2).1; omega
        have hpq' : p.2 = q.2 := hpq
        refine Prod.ext (Nat.mul_right_cancel hp2n ?_) hpq'
        rw [hpm, ← hqm, hpq']
    exact_mod_cast this
  calc ‖bfun A Bi u1 u2 c (fun u => eaf P0 a u) m‖ ≤ ∑ p ∈ sF, ‖c p.1‖ := h1
    _ ≤ B * (sF.card : ℝ) := h2
    _ ≤ B * (m.divisors.card : ℝ) := mul_le_mul_of_nonneg_left h3 hBnn


lemma Ppoly_partition (N : ℕ) (c : ℕ → ℂ) (θ : ℝ) :
    Ppoly N (2*N) c θ = Ppoly N ((4*N)/3) c θ + Ppoly ((4*N)/3+1) ((3*N)/2) c θ
      + Ppoly ((3*N)/2+1) (2*N) c θ := by
  rw [Ppoly, Ppoly, Ppoly, Ppoly]
  have hU : Finset.Icc N (2*N) = Finset.Icc N ((4*N)/3)
      ∪ (Finset.Icc ((4*N)/3+1) ((3*N)/2) ∪ Finset.Icc ((3*N)/2+1) (2*N)) := by
    ext n; simp only [Finset.mem_union, Finset.mem_Icc]; omega
  have hd1 : Disjoint (Finset.Icc ((4*N)/3+1) ((3*N)/2)) (Finset.Icc ((3*N)/2+1) (2*N)) := by
    rw [Finset.disjoint_left]; intro n hn1 hn2
    simp only [Finset.mem_Icc] at hn1 hn2; omega
  have hd2 : Disjoint (Finset.Icc N ((4*N)/3))
      (Finset.Icc ((4*N)/3+1) ((3*N)/2) ∪ Finset.Icc ((3*N)/2+1) (2*N)) := by
    rw [Finset.disjoint_left]; intro n hn1 hn2
    simp only [Finset.mem_union, Finset.mem_Icc] at hn1 hn2; omega
  rw [hU, Finset.sum_union hd2, Finset.sum_union hd1]
  ring

lemma Ppoly_cs (N : ℕ) (c : ℕ → ℂ) (θ : ℝ) :
    ‖Ppoly N (2*N) c θ‖^2 ≤ 3 * (‖Ppoly N ((4*N)/3) c θ‖^2
      + ‖Ppoly ((4*N)/3+1) ((3*N)/2) c θ‖^2 + ‖Ppoly ((3*N)/2+1) (2*N) c θ‖^2) := by
  rw [Ppoly_partition]
  set A1 := ‖Ppoly N ((4*N)/3) c θ‖
  set A2 := ‖Ppoly ((4*N)/3+1) ((3*N)/2) c θ‖
  set A3 := ‖Ppoly ((3*N)/2+1) (2*N) c θ‖
  have h1 : ‖Ppoly N ((4*N)/3) c θ + Ppoly ((4*N)/3+1) ((3*N)/2) c θ
      + Ppoly ((3*N)/2+1) (2*N) c θ‖ ≤ A1 + A2 + A3 :=
    le_trans (norm_add_le _ _) (add_le_add_left (norm_add_le _ _) _)
  have h2 : (A1 + A2 + A3)^2 ≤ 3 * (A1^2 + A2^2 + A3^2) := by
    nlinarith [sq_nonneg (A1 - A2), sq_nonneg (A2 - A3), sq_nonneg (A1 - A3)]
  have h3 : (0:ℝ) ≤ A1 + A2 + A3 := by positivity
  nlinarith [h1, h2, h3, norm_nonneg (Ppoly N ((4*N)/3) c θ + Ppoly ((4*N)/3+1) ((3*N)/2) c θ
      + Ppoly ((3*N)/2+1) (2*N) c θ)]


/-- Rewriting a single term of `dval` into its explicit form. -/
lemma dval_eq (n : ℕ) (θ : ℝ) :
    dval n θ = (n : ℂ) ^ (Complex.I * (θ : ℂ)) / (Real.sqrt (n : ℝ) : ℂ) := by
  simp only [dval, sqt]

lemma Ppoly_eq (A B : ℕ) (c : ℕ → ℂ) (θ : ℝ) :
    Ppoly A B c θ = ∑ n ∈ Finset.Icc A B,
      c n * (n : ℂ) ^ (Complex.I * (θ : ℂ)) / (Real.sqrt (n : ℝ) : ℂ) := by
  rw [Ppoly]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [dval_eq]; ring

lemma Qpoly_eq (L : ℕ) (θ : ℝ) :
    Qpoly L θ = ∑ n ∈ Finset.Icc L (2*L),
      (n : ℂ) ^ (Complex.I * (θ : ℂ)) / (Real.sqrt (n : ℝ) : ℂ) := by
  rw [Qpoly]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [dval_eq]

/-- `M ≤ A * ⌈M/A⌉`. -/
lemma le_mul_div_self (A M : ℕ) (hA : 1 ≤ A) : M ≤ A*((M+A-1)/A) := by
  have hmod := Nat.mod_lt (M+A-1) (by omega : 0 < A)
  have hdiv := Nat.div_add_mod (M+A-1) A
  omega

/-- `B * ⌊2M/B⌋ ≤ 2M`. -/
lemma mul_div_self_le (B M : ℕ) : B*(2*M/B) ≤ 2*M := Nat.mul_div_le (2*M) B

/-- The gain interval is nonempty: `⌈M/A⌉ ≤ ⌊2M/B⌋` when `3B ≤ 4A`. -/
lemma u_le_u (A Bb M : ℕ) (hA : 1 ≤ A) (hBb1 : 1 ≤ Bb) (hBb : 3*Bb ≤ 4*A) (hBM : Bb ≤ M) :
    (M + A - 1)/A ≤ 2*M/Bb := by
  have hApos : 0 < A := lt_of_lt_of_le Nat.zero_lt_one hA
  have hBpos : 0 < Bb := lt_of_lt_of_le Nat.zero_lt_one hBb1
  rw [Nat.le_div_iff_mul_le hBpos]
  by_cases hk : (M + A - 1)/A ≤ 2
  · calc (M + A - 1)/A * Bb ≤ 2 * Bb := Nat.mul_le_mul_right Bb hk
      _ ≤ 2 * M := Nat.mul_le_mul_left 2 hBM
  · push Not at hk
    have hkl : (M+A-1)/A * A ≤ M + A - 1 := Nat.div_mul_le_self _ _
    have h2A : 2*A ≤ M := by
      have h3 : 3*A ≤ (M+A-1)/A * A := by
        calc 3*A ≤ ((M+A-1)/A)*A := Nat.mul_le_mul_right A hk
          _ = (M+A-1)/A*A := by ring
      omega
    have h1 : (M+A-1)/A ≤ M/A + 1 := by
      calc (M+A-1)/A ≤ (M+A)/A := Nat.div_le_div_right (Nat.sub_le _ _)
        _ = M/A + 1 := Nat.add_div_right M hApos
    have hkey : 2*A*((M+A-1)/A) ≤ 3*M := by
      have h2 : 2*A*(M/A+1) ≤ 3*M := by
        have h3 : A*(M/A) ≤ M := Nat.mul_div_le M A
        nlinarith [h3, h2A]
      calc 2*A*((M+A-1)/A) ≤ 2*A*(M/A+1) := Nat.mul_le_mul_left _ h1
        _ ≤ 3*M := h2
    have hm : (2*A*((M+A-1)/A)) * (3*Bb) ≤ (3*M) * (4*A) := Nat.mul_le_mul hkey hBb
    have hm2 : 6*A*((M+A-1)/A * Bb) ≤ 6*A*(2*M) := by nlinarith [hm]
    exact Nat.le_of_mul_le_mul_left hm2 (by omega)

/-- Redistribution of a factor `3` over three double sums. -/
lemma three_fold_sum_swap (R : ℕ) (B C D : Fin R → Fin R → ℝ) :
    3 * ((∑ i, ∑ j, B i j) + (∑ i, ∑ j, C i j) + (∑ i, ∑ j, D i j))
      = ∑ i, ∑ j, 3 * (B i j + C i j + D i j) := by
  rw [mul_add, mul_add]
  simp only [Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

theorem dirichlet_poly_increase_length : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ (N M : ℕ), 1 ≤ N → 2 * N ≤ M → ∀ (Δ : ℝ), 1 ≤ Δ → ∀ (B : ℝ), 1 ≤ B →
    ∀ (c : ℕ → ℂ), (∀ n, ‖c n‖ ≤ B) → ∀ (R : ℕ) (t : Fin R → ℝ),
    (∀ i j, i ≠ j → 1 ≤ |t i - t j|) →
    (∑ i : Fin R, ∑ j : Fin R,
      (if |t i - t j| ≤ Δ then
        ‖∑ n ∈ Finset.Icc N (2 * N),
          c n * (n : ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ)) / (Real.sqrt (n : ℝ) : ℂ)‖ ^ 2
       else 0))
    ≤ C * B ^ 2 * (M : ℝ) ^ ε * (∑ i : Fin R, ∑ j : Fin R,
      (if |t i - t j| ≤ Δ then
        ‖∑ n ∈ Finset.Icc M (2 * M),
          (n : ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ)) / (Real.sqrt (n : ℝ) : ℂ)‖ ^ 2
       else 0)) := by
  intro ε hε
  obtain ⟨Cma, hCmapos, hMAJ0⟩ := Commons.Analysis.Fourier.fejer_window_localization_majorant
  obtain ⟨Cd, hCdpos, hCd⟩ :=
    Commons.NumberTheory.ArithmeticFunction.card_divisors_le_rpow (ε/2) (by positivity)
  refine ⟨360 * (4*Cma) * Cd^2 * 2^ε + 1, by positivity, ?_⟩
  intro N M hN h2N Δ hΔ B hB c hc R t ht
  -- ### arithmetic facts (ℕ) that are used below
  have hM1 : 1 ≤ M := by omega
  have hN3 : 1 ≤ (4*N)/3 := by omega
  have hN2 : 1 ≤ (3*N)/2 := by omega
  have hA2 : 1 ≤ (4*N)/3 + 1 := by omega
  have hA3 : 1 ≤ (3*N)/2 + 1 := by omega
  have hB3 : 1 ≤ 2*N := by omega
  have hle1 : (4*N)/3 ≤ M := by omega
  have hle2 : (3*N)/2 ≤ M := by omega
  have hr1 : 3*((4*N)/3) ≤ 4*N := Nat.mul_div_le (4*N) 3
  have hr2 : 3*((3*N)/2) ≤ 4*((4*N)/3+1) := by omega
  have hr3 : 3*(2*N) ≤ 4*((3*N)/2+1) := by omega
  have huA1 : (M + N - 1)/N ≤ 2*M/((4*N)/3) := u_le_u N ((4*N)/3) M hN hN3 hr1 hle1
  have huA2 : (M + ((4*N)/3+1) - 1)/((4*N)/3+1) ≤ 2*M/((3*N)/2) :=
    u_le_u ((4*N)/3+1) ((3*N)/2) M hA2 hN2 hr2 hle2
  have huA3 : (M + ((3*N)/2+1) - 1)/((3*N)/2+1) ≤ 2*M/(2*N) :=
    u_le_u ((3*N)/2+1) (2*N) M hA3 hB3 hr3 h2N
  have hΔ0 : (0:ℝ) < Δ := lt_of_lt_of_le zero_lt_one hΔ
  have hBnn : (0:ℝ) ≤ B := le_trans (norm_nonneg (c 0)) (hc 0)
  -- ### the divisor growth constant
  set D : ℝ := Cd * (2*(M:ℝ))^(ε/2) with hDdef
  have hDpos : 0 < D := by rw [hDdef]; positivity
  -- ### Fejér majorant, adapted to `dval`
  have hMAJ : ∀ (L : ℕ) (a : ℕ → ℂ) (cc : ℕ → ℝ), 1 ≤ L → (∀ n, ‖a n‖ ≤ cc n) →
      ∀ (R : ℕ) (t : Fin R → ℝ), (∀ i j, i ≠ j → 1 ≤ |t i - t j|) → ∀ Δ : ℝ, 0 < Δ →
      (∑ i, ∑ j, (if |t i - t j| ≤ Δ then
          ‖∑ n ∈ Finset.Icc L (2*L), a n * dval n (t i - t j)‖^2 else 0))
      ≤ (4*Cma) * (∑ i, ∑ j, (if |t i - t j| ≤ Δ then
          ‖∑ n ∈ Finset.Icc L (2*L), ((cc n:ℝ):ℂ) * dval n (t i - t j)‖^2 else 0)) := by
    intro L a cc hL ha R t ht Δ hΔ
    have h := hMAJ0 (1/4) (by norm_num) (by norm_num) Δ hΔ L hL cc a ha R t ht
    have hconv : ∀ i j : Fin R,
        (if |t i - t j| ≤ Δ then ‖∑ n ∈ Finset.Icc L (2*L),
            a n * (n:ℂ)^(Complex.I*((t i - t j:ℝ):ℂ))/(Real.sqrt (n:ℝ):ℂ)‖^2 else 0)
        = (if |t i - t j| ≤ Δ then ‖∑ n ∈ Finset.Icc L (2*L), a n * dval n (t i - t j)‖^2 else 0) := by
      intro i j
      by_cases hh : |t i - t j| ≤ Δ
      · rw [if_pos hh, if_pos hh]
        have hS : (∑ n ∈ Finset.Icc L (2*L),
              a n * (n:ℂ)^(Complex.I*((t i - t j:ℝ):ℂ))/(Real.sqrt (n:ℝ):ℂ))
            = ∑ n ∈ Finset.Icc L (2*L), a n * dval n (t i - t j) := by
          refine Finset.sum_congr rfl (fun n _ => ?_)
          rw [dval_eq]; ring
        rw [hS]
      · rw [if_neg hh, if_neg hh]
    have hconv2 : ∀ i j : Fin R,
        (if |t i - t j| ≤ 4*(1/4)*Δ then ‖∑ n ∈ Finset.Icc L (2*L),
            ((cc n:ℝ):ℂ) * (n:ℂ)^(Complex.I*((t i - t j:ℝ):ℂ))/(Real.sqrt (n:ℝ):ℂ)‖^2 else 0)
        = (if |t i - t j| ≤ Δ then ‖∑ n ∈ Finset.Icc L (2*L), ((cc n:ℝ):ℂ) * dval n (t i - t j)‖^2 else 0) := by
      intro i j
      rw [show (4*(1/4)*Δ : ℝ) = Δ by ring]
      by_cases hh : |t i - t j| ≤ Δ
      · rw [if_pos hh, if_pos hh]
        have hS : (∑ n ∈ Finset.Icc L (2*L),
              ((cc n:ℝ):ℂ) * (n:ℂ)^(Complex.I*((t i - t j:ℝ):ℂ))/(Real.sqrt (n:ℝ):ℂ))
            = ∑ n ∈ Finset.Icc L (2*L), ((cc n:ℝ):ℂ) * dval n (t i - t j) := by
          refine Finset.sum_congr rfl (fun n _ => ?_)
          rw [dval_eq]; ring
        rw [hS]
      · rw [if_neg hh, if_neg hh]
    have e1 : (∑ i, ∑ j, (if |t i - t j| ≤ Δ then ‖∑ n ∈ Finset.Icc L (2*L),
            a n * (n:ℂ)^(Complex.I*((t i - t j:ℝ):ℂ))/(Real.sqrt (n:ℝ):ℂ)‖^2 else 0))
        = (∑ i, ∑ j, (if |t i - t j| ≤ Δ then
            ‖∑ n ∈ Finset.Icc L (2*L), a n * dval n (t i - t j)‖^2 else 0)) :=
      Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hconv i j))
    have e2 : (∑ i, ∑ j, (if |t i - t j| ≤ 4*(1/4)*Δ then ‖∑ n ∈ Finset.Icc L (2*L),
            ((cc n:ℝ):ℂ) * (n:ℂ)^(Complex.I*((t i - t j:ℝ):ℂ))/(Real.sqrt (n:ℝ):ℂ)‖^2 else 0))
        = (∑ i, ∑ j, (if |t i - t j| ≤ Δ then
            ‖∑ n ∈ Finset.Icc L (2*L), ((cc n:ℝ):ℂ) * dval n (t i - t j)‖^2 else 0)) :=
      Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hconv2 i j))
    rw [e1, e2] at h
    rw [show Cma / (1/4) = 4*Cma by ring] at h
    exact h
  -- ### the per-piece bound
  have hpiece : ∀ (A Bi : ℕ), 1 ≤ A → 1 ≤ Bi → 3*Bi ≤ 4*A → Bi ≤ M →
      (M + A - 1)/A ≤ 2*M/Bi →
      (∑ i, ∑ j, (if |t i - t j| ≤ Δ then ‖Ppoly A Bi c (t i - t j)‖^2 else 0))
      ≤ (4*Cma) * (B*D)^2 * 10
        * (∑ i, ∑ j, (if |t i - t j| ≤ Δ then ‖Qpoly M (t i - t j)‖^2 else 0)) := by
    intro A Bi hA1 hBi1 hBiA hBiM hu
    have hBiA' : Bi ≤ 4*A/3 :=
      (Nat.le_div_iff_mul_le (by norm_num : (0:ℕ) < 3)).mpr (by omega)
    have hgain : (1:ℝ)/10 ≤ ∑ u ∈ Finset.Icc ((M+A-1)/A) (2*M/Bi), (1:ℝ)/u :=
      gain_bound_interval A Bi M hA1 hBi1 hBiA' hBiM hM1 hu
    have hApos : 0 < A := lt_of_lt_of_le Nat.zero_lt_one hA1
    have hu1pos : 1 ≤ (M+A-1)/A := by
      rw [Nat.one_le_div_iff hApos]; omega
    have hP0 : (2*M/Bi) - ((M+A-1)/A) < (2*M/Bi)+1 :=
      lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_succ_self _)
    have hDpi : ∀ a m, ‖bfun A Bi ((M+A-1)/A) (2*M/Bi) c
        (fun u => eaf ((2*M/Bi)+1) a u) m‖ ≤ B * D := by
      intro a m
      by_cases hm : m ∈ Finset.Icc M (2*M)
      · have hm1 : 1 ≤ m := le_trans hM1 (Finset.mem_Icc.mp hm).1
        refine le_trans (bfun_norm_le A Bi ((M+A-1)/A) (2*M/Bi) ((2*M/Bi)+1)
          c a B hc hA1 hu1pos m) ?_
        refine mul_le_mul_of_nonneg_left ?_ hBnn
        have hm2 : (m:ℝ) ≤ 2*(M:ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hm).2
        have hm0 : (0:ℝ) ≤ (m:ℝ) := by positivity
        calc (m.divisors.card : ℝ) ≤ Cd * (m:ℝ)^(ε/2) := hCd m hm1
          _ ≤ Cd * (2*(M:ℝ))^(ε/2) :=
              mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hm0 hm2 (by linarith)) hCdpos.le
          _ = D := by rw [hDdef]
      · have hz : bfun A Bi ((M+A-1)/A) (2*M/Bi) c
            (fun u => eaf ((2*M/Bi)+1) a u) m = 0 := by
          rw [bfun]
          refine Finset.sum_eq_zero (fun p hp => ?_)
          simp only [Finset.mem_filter, Finset.mem_product] at hp
          obtain ⟨⟨hp1,hp2⟩, hpm⟩ := hp
          exfalso; exact hm (by
            have e1 : A*((M+A-1)/A) ≤ p.1*p.2 :=
              Nat.mul_le_mul (Finset.mem_Icc.mp hp1).1 (Finset.mem_Icc.mp hp2).1
            have e2 : p.1*p.2 ≤ Bi*(2*M/Bi) :=
              Nat.mul_le_mul (Finset.mem_Icc.mp hp1).2 (Finset.mem_Icc.mp hp2).2
            rw [hpm] at e1 e2
            exact Finset.mem_Icc.mpr
              ⟨le_trans (le_mul_div_self A M hA1) e1, le_trans e2 (mul_div_self_le Bi M)⟩)
        rw [hz, norm_zero]
        exact mul_nonneg hBnn hDpos.le
    have hres := piece_increase A Bi ((M+A-1)/A) (2*M/Bi) ((2*M/Bi)+1) M
      hA1 hu1pos hu hP0 hM1 (le_mul_div_self A M hA1) (mul_div_self_le Bi M)
      c B D (4*Cma) hBnn hDpos.le (by positivity) hDpi hMAJ Δ hΔ0 R t ht
    have hGpos : 0 < ∑ u ∈ Finset.Icc ((M+A-1)/A) (2*M/Bi), (1:ℝ)/u :=
      lt_of_lt_of_le (by norm_num) hgain
    have hKnn : 0 ≤ (4*Cma) * (B*D)^2 := by positivity
    have hRMSnn : 0 ≤ (∑ i, ∑ j, (if |t i - t j| ≤ Δ then ‖Qpoly M (t i - t j)‖^2 else 0)) :=
      Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => by positivity))
    have hKRnn : 0 ≤ (4*Cma) * (B*D)^2
        * (∑ i, ∑ j, (if |t i - t j| ≤ Δ then ‖Qpoly M (t i - t j)‖^2 else 0)) :=
      mul_nonneg hKnn hRMSnn
    have h10G : (1:ℝ) ≤ 10 * (∑ u ∈ Finset.Icc ((M+A-1)/A) (2*M/Bi), (1:ℝ)/u) := by
      linarith [hgain]
    refine le_trans hres ?_
    rw [div_mul_eq_mul_div, div_le_iff₀ hGpos]
    nlinarith [h10G, hKRnn]
  -- ### pointwise Cauchy–Schwarz for the three pieces
  have hpt : ∀ i j : Fin R,
      (if |t i - t j| ≤ Δ then ‖Ppoly N (2*N) c (t i - t j)‖^2 else 0)
      ≤ 3 * ((if |t i - t j| ≤ Δ then ‖Ppoly N ((4*N)/3) c (t i - t j)‖^2 else 0)
        + (if |t i - t j| ≤ Δ then ‖Ppoly ((4*N)/3+1) ((3*N)/2) c (t i - t j)‖^2 else 0)
        + (if |t i - t j| ≤ Δ then ‖Ppoly ((3*N)/2+1) (2*N) c (t i - t j)‖^2 else 0)) := by
    intro i j
    by_cases hh : |t i - t j| ≤ Δ
    · simp only [if_pos hh]
      exact Ppoly_cs N c (t i - t j)
    · simp only [if_neg hh]; norm_num
  have hLHSb : (∑ i, ∑ j, (if |t i - t j| ≤ Δ then ‖Ppoly N (2*N) c (t i - t j)‖^2 else 0))
      ≤ 3 * ((∑ i, ∑ j, (if |t i - t j| ≤ Δ then ‖Ppoly N ((4*N)/3) c (t i - t j)‖^2 else 0))
        + (∑ i, ∑ j, (if |t i - t j| ≤ Δ then
            ‖Ppoly ((4*N)/3+1) ((3*N)/2) c (t i - t j)‖^2 else 0))
        + (∑ i, ∑ j, (if |t i - t j| ≤ Δ then
            ‖Ppoly ((3*N)/2+1) (2*N) c (t i - t j)‖^2 else 0))) := by
    have h1 : (∑ i, ∑ j, (if |t i - t j| ≤ Δ then ‖Ppoly N (2*N) c (t i - t j)‖^2 else 0))
        ≤ ∑ i, ∑ j, 3 * ((if |t i - t j| ≤ Δ then ‖Ppoly N ((4*N)/3) c (t i - t j)‖^2 else 0)
          + (if |t i - t j| ≤ Δ then ‖Ppoly ((4*N)/3+1) ((3*N)/2) c (t i - t j)‖^2 else 0)
          + (if |t i - t j| ≤ Δ then ‖Ppoly ((3*N)/2+1) (2*N) c (t i - t j)‖^2 else 0)) :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hpt i j))
    have h2 := three_fold_sum_swap R
      (fun i j => if |t i - t j| ≤ Δ then ‖Ppoly N ((4*N)/3) c (t i - t j)‖^2 else 0)
      (fun i j => if |t i - t j| ≤ Δ then ‖Ppoly ((4*N)/3+1) ((3*N)/2) c (t i - t j)‖^2 else 0)
      (fun i j => if |t i - t j| ≤ Δ then ‖Ppoly ((3*N)/2+1) (2*N) c (t i - t j)‖^2 else 0)
    exact h1.trans (le_of_eq h2.symm)
  -- ### the three pieces
  have h1 := hpiece N ((4*N)/3) hN hN3 hr1 hle1 huA1
  have h2 := hpiece ((4*N)/3+1) ((3*N)/2) hA2 hN2 hr2 hle2 huA2
  have h3 := hpiece ((3*N)/2+1) (2*N) hA3 hB3 hr3 h2N huA3
  have hcombined :
      (∑ i, ∑ j, (if |t i - t j| ≤ Δ then ‖Ppoly N ((4*N)/3) c (t i - t j)‖^2 else 0))
        + (∑ i, ∑ j, (if |t i - t j| ≤ Δ then
            ‖Ppoly ((4*N)/3+1) ((3*N)/2) c (t i - t j)‖^2 else 0))
        + (∑ i, ∑ j, (if |t i - t j| ≤ Δ then
            ‖Ppoly ((3*N)/2+1) (2*N) c (t i - t j)‖^2 else 0))
      ≤ 3 * ((4*Cma) * (B*D)^2 * 10
          * (∑ i, ∑ j, (if |t i - t j| ≤ Δ then ‖Qpoly M (t i - t j)‖^2 else 0))) := by
    linarith [h1, h2, h3]
  have hsum : (∑ i, ∑ j, (if |t i - t j| ≤ Δ then ‖Ppoly N (2*N) c (t i - t j)‖^2 else 0))
      ≤ 90 * (4*Cma) * (B*D)^2
        * (∑ i, ∑ j, (if |t i - t j| ≤ Δ then ‖Qpoly M (t i - t j)‖^2 else 0)) := by
    calc (∑ i, ∑ j, (if |t i - t j| ≤ Δ then ‖Ppoly N (2*N) c (t i - t j)‖^2 else 0))
        ≤ 3 * ((∑ i, ∑ j, (if |t i - t j| ≤ Δ then ‖Ppoly N ((4*N)/3) c (t i - t j)‖^2 else 0))
          + (∑ i, ∑ j, (if |t i - t j| ≤ Δ then
              ‖Ppoly ((4*N)/3+1) ((3*N)/2) c (t i - t j)‖^2 else 0))
          + (∑ i, ∑ j, (if |t i - t j| ≤ Δ then
              ‖Ppoly ((3*N)/2+1) (2*N) c (t i - t j)‖^2 else 0))) := hLHSb
      _ ≤ 3 * (3 * ((4*Cma) * (B*D)^2 * 10
            * (∑ i, ∑ j, (if |t i - t j| ≤ Δ then ‖Qpoly M (t i - t j)‖^2 else 0)))) :=
          mul_le_mul_of_nonneg_left hcombined (by norm_num)
      _ = 90 * (4*Cma) * (B*D)^2
            * (∑ i, ∑ j, (if |t i - t j| ≤ Δ then ‖Qpoly M (t i - t j)‖^2 else 0)) := by ring
  -- ### removing the divisor factor
  have hD2 : (B*D)^2 ≤ B^2 * (Cd^2 * 2^ε) * (M:ℝ)^ε := by
    have hDM : (2*(M:ℝ))^(ε/2) = (2:ℝ)^(ε/2) * (M:ℝ)^(ε/2) :=
      Real.mul_rpow (by norm_num) (by positivity)
    have h22 : ((2:ℝ)^(ε/2))^2 = (2:ℝ)^ε := by
      rw [← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2) (ε/2) 2]
      congr 1
      ring
    have hMM : ((M:ℝ)^(ε/2))^2 = (M:ℝ)^ε := by
      rw [← Real.rpow_mul_natCast (by positivity : (0:ℝ) ≤ (M:ℝ)) (ε/2) 2]
      congr 1
      ring
    rw [hDdef, mul_pow, mul_pow, hDM, mul_pow, h22, hMM]
    exact le_of_eq (by ring)
  have hfin : 90 * (4*Cma) * (B*D)^2
        * (∑ i, ∑ j, (if |t i - t j| ≤ Δ then ‖Qpoly M (t i - t j)‖^2 else 0))
      ≤ (360 * (4*Cma) * Cd^2 * 2^ε + 1) * B^2 * (M:ℝ)^ε
        * (∑ i, ∑ j, (if |t i - t j| ≤ Δ then ‖Qpoly M (t i - t j)‖^2 else 0)) := by
    have hRnn : 0 ≤ (∑ i, ∑ j, (if |t i - t j| ≤ Δ then ‖Qpoly M (t i - t j)‖^2 else 0)) :=
      Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => by positivity))
    have hbase : 90 * (4*Cma) * (Cd^2 * (2:ℝ)^ε) ≤ 360 * (4*Cma) * Cd^2 * 2^ε + 1 := by
      have h2e : 0 ≤ (2:ℝ)^ε := Real.rpow_nonneg (by norm_num) ε
      have hnn := mul_nonneg hCmapos.le (mul_nonneg (sq_nonneg Cd) h2e)
      nlinarith [hnn]
    have hkey : 90 * (4*Cma) * (B*D)^2
        ≤ (360 * (4*Cma) * Cd^2 * 2^ε + 1) * B^2 * (M:ℝ)^ε := by
      have h1 : 90 * (4*Cma) * (B*D)^2
          ≤ 90 * (4*Cma) * (B^2 * (Cd^2 * 2^ε) * (M:ℝ)^ε) :=
        mul_le_mul_of_nonneg_left hD2 (by positivity)
      have h2 : 90 * (4*Cma) * (B^2 * (Cd^2 * 2^ε) * (M:ℝ)^ε)
          = (90 * (4*Cma) * (Cd^2 * 2^ε)) * (B^2 * (M:ℝ)^ε) := by ring
      have h3 : (90 * (4*Cma) * (Cd^2 * 2^ε)) * (B^2 * (M:ℝ)^ε)
          ≤ (360 * (4*Cma) * Cd^2 * 2^ε + 1) * (B^2 * (M:ℝ)^ε) :=
        mul_le_mul_of_nonneg_right hbase (by positivity)
      have h4 : (360 * (4*Cma) * Cd^2 * 2^ε + 1) * (B^2 * (M:ℝ)^ε)
          = (360 * (4*Cma) * Cd^2 * 2^ε + 1) * B^2 * (M:ℝ)^ε := by ring
      linarith [h1, h2, h3, h4]
    calc 90 * (4*Cma) * (B*D)^2
            * (∑ i, ∑ j, (if |t i - t j| ≤ Δ then ‖Qpoly M (t i - t j)‖^2 else 0))
        ≤ ((360 * (4*Cma) * Cd^2 * 2^ε + 1) * B^2 * (M:ℝ)^ε)
            * (∑ i, ∑ j, (if |t i - t j| ≤ Δ then ‖Qpoly M (t i - t j)‖^2 else 0)) :=
          mul_le_mul_of_nonneg_right hkey hRnn
      _ = (360 * (4*Cma) * Cd^2 * 2^ε + 1) * B^2 * (M:ℝ)^ε
            * (∑ i, ∑ j, (if |t i - t j| ≤ Δ then ‖Qpoly M (t i - t j)‖^2 else 0)) := by ring
  have hconvL : (∑ i : Fin R, ∑ j : Fin R,
        (if |t i - t j| ≤ Δ then ‖∑ n ∈ Finset.Icc N (2 * N),
          c n * (n : ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ)) / (Real.sqrt (n : ℝ) : ℂ)‖ ^ 2
         else 0))
      = (∑ i, ∑ j, (if |t i - t j| ≤ Δ then ‖Ppoly N (2*N) c (t i - t j)‖^2 else 0)) := by
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    by_cases hh : |t i - t j| ≤ Δ
    · rw [if_pos hh, if_pos hh, Ppoly_eq]
    · rw [if_neg hh, if_neg hh]
  have hconvR : (∑ i, ∑ j, (if |t i - t j| ≤ Δ then ‖Qpoly M (t i - t j)‖^2 else 0))
      = (∑ i : Fin R, ∑ j : Fin R,
        (if |t i - t j| ≤ Δ then ‖∑ n ∈ Finset.Icc M (2 * M),
          (n : ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ)) / (Real.sqrt (n : ℝ) : ℂ)‖ ^ 2
         else 0)) := by
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    by_cases hh : |t i - t j| ≤ Δ
    · rw [if_pos hh, if_pos hh, Qpoly_eq]
    · rw [if_neg hh, if_neg hh]
  rw [hconvL]
  rw [← hconvR]
  exact le_trans hsum hfin

end Commons.NumberTheory.DirichletPolynomial
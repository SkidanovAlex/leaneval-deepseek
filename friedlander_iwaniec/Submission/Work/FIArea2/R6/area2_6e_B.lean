import Mathlib
import Submission.Work.FIArea2.R6.Inputs6
import Submission.Work.FIArea2.R6.Area6eBDefs
import Submission.Work.FIArea2.R6.BetaFacts6
import Submission.Work.FIArea2.R6.Pack6
import Submission.Work.FIArea2.R6.ExactMain
import Submission.Work.FIArea2.R6.Decomp6
import Submission.Work.FIArea2.R6.Fint_gen
import Submission.Work.FIArea2.R6.vol_regG_le
import Submission.Work.FIArea2.R6.one_sub_gamOf_sq_eq
import Submission.Work.FIArea2.gamOf_nonneg_of_polarBox
import Submission.Work.FIArea2.isCoprime_star_of_squarefree_odd_gnorm
import Submission.Work.FITop4.Red6.G0_eq_ratioSym_sum
import Submission.Work.FIArea3.Y

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `FIArea2/R6/area2_6e_B` — the (7.10)/(10.4) replacement error `‖D₀^exact − D₀‖`

This file proves the round-6 area-2 "B" statement: the difference between the *exact* main term
`D0ex` of (9.11)/(6.13) (built on the Fourier integral (6.11) with the interpolant
`majF Pa f hf` of the §7 majorant) and the *approximated* main term `Defs6.D0` (built on the
(7.10) main term `Fhat Pa f · logFac6`) is bounded by
`C₃(τ⁻¹+θ)θ⁴M^{1/2}N^{3/2}(log N)^{2^20}` — the replacement-error part of *FI* (10.4)/(10.10).

## Structure of the proof

1. **Pair-sum reduction** (`norm_D0ex_sub_D0_le`): `‖D₀^exact − D₀‖` is at most the
   `‖β_{z₁}‖‖β_{z₂}‖`-weighted sum of the per-pair errors of (7.10) (`Defs6.D0` is real).
2. **The per-pair difference** (`C0ex_sub_C0_eq`): on the support of a round-6 coefficient,
   `C₀^exact − C₀ = |z₁z₂|^{-1/4}·G₀·((Fint F γ 0 0).re − Fhat·logFac6)`, where the Poisson
   `h = 0` term is the (6.12) count kernel (`Gsum_zero_zero6`).
3. **The (7.10) bracket** (`bracket_le`): the input `FintProp` gives the (7.10) estimate for
   functions with `0 ≤ F`, while `majF` may dip by `O(M⁻¹)` between consecutive integers.  The
   nonnegative majorisation `majG u = √(majF u² + δ²) − δ` (`δ = M⁻¹`, `Area6eBDefs`) has the same
   trace properties (`majG` vanishes exactly where `f` does), the same support, the same derivative
   constant, is pointwise within `O(M⁻¹)` of `majF`, and is nonnegative; applying `FintProp` to it
   and controlling the two differences by the volume bound `vol_regG_le` gives the bracket bound.
4. **Assembly**: `|G₀| ≤ 2(1+τ(|Δ|)) ≤ 4τ₃(|Δ|)` on the pairs that occur, `|z₁z₂|^{-1/4} ≤ N^{-1/2}`
   on the polar box, and the (10.6)/(10.7) input `YProp` (`Y(β) ≤ Cθ⁴N²(log N)^{2^19}`) give the
   stated bound.
-/

namespace Work.FIArea2.R6

open Finset MeasureTheory
open scoped BigOperators Topology

attribute [local instance] Classical.propDecidable

noncomputable section

set_option maxHeartbeats 1000000


/-! ## 0. Elementary Gaussian-integer facts (re-proved here)

The version of these lemmas in `Submission/Work/FIArea2/area2_r3.lean` sits in a module that also
contains an (unrelated) open leaf, and its shim cannot be imported alongside `FITop3.Areas3`.  They
are short, so they are reproduced here with `R6`-local names. -/

theorem star_mul_eq_of_Delta_eq_zero {z1 z2 : GaussianInt}
    (h : Work.FIPlan.Delta z1 z2 = 0) : star z1 * z2 = z1 * star z2 := by
  have him : z1.re * z2.im + -(z1.im * z2.re) = 0 := by
    simpa [Work.FIPlan.Delta, Zsqrtd.star_mk] using h
  ext <;> simp <;> linarith

theorem dvd_star_of_Delta_eq_zero {z1 z2 : GaussianInt} (h : Work.FIPlan.Delta z1 z2 = 0)
    (h12 : IsCoprime z1 z2) : z1 ∣ star z1 ∧ z2 ∣ star z2 := by
  have h' := star_mul_eq_of_Delta_eq_zero h
  have h1 : z1 ∣ z2 * star z1 := ⟨star z2, by rw [mul_comm z2 (star z1), h']⟩
  have h2 : z2 ∣ z1 * star z2 := ⟨star z1, by rw [← h', mul_comm (star z1) z2]⟩
  exact ⟨h12.dvd_of_dvd_mul_left h1, h12.symm.dvd_of_dvd_mul_left h2⟩

theorem isUnit_of_Delta_eq_zero {z1 z2 : GaussianInt} (h : Work.FIPlan.Delta z1 z2 = 0)
    (h12 : IsCoprime z1 z2) (h1 : IsCoprime z1 (star z1)) (h2 : IsCoprime z2 (star z2)) :
    IsUnit z1 ∧ IsUnit z2 := by
  obtain ⟨hd1, hd2⟩ := dvd_star_of_Delta_eq_zero h h12
  exact ⟨h1.isUnit_of_dvd hd1, h2.isUnit_of_dvd hd2⟩

/-- On a coprime pair of primitive points of norm `≥ 2`, `Δ` does not vanish. -/
theorem delta_ne_zero_of_coprime {z1 z2 : GaussianInt} (h12 : IsCoprime z1 z2)
    (h1 : IsCoprime z1 (star z1)) (h2 : IsCoprime z2 (star z2))
    (hn1 : 2 ≤ Work.FIPlan.gnorm z1) : Work.FIPlan.Delta z1 z2 ≠ 0 := by
  intro hΔ
  obtain ⟨hu1, _⟩ := isUnit_of_Delta_eq_zero hΔ h12 h1 h2
  obtain ⟨u, hu⟩ := hu1
  have hgn : Work.FIPlan.gnorm z1 = 1 := by
    rw [← hu]
    exact Zsqrtd.norm_eq_one_iff.mpr u.isUnit
  omega

theorem IsPrimary.odd_gnorm {z : GaussianInt} (h : Work.FIPlan.IsPrimary z) :
    Odd (Work.FIPlan.gnorm z) := by
  obtain ⟨h1, h2, -⟩ := h
  have hgn : Work.FIPlan.gnorm z = (z.re ^ 2 + z.im ^ 2).natAbs := by
    simp [Work.FIPlan.gnorm, Zsqrtd.norm_def, sq]
  rw [hgn]
  have h2' : Even (z.im ^ 2) := by
    obtain ⟨r, hr⟩ := h2
    exact ⟨2 * r ^ 2, by rw [hr]; ring⟩
  exact (h1.pow.add_even h2').natAbs

theorem InPolarBox.isPrimary6 {Pa : Work.FITop.Params} {φ : ℝ} {z : GaussianInt}
    (h : Work.FITop3.InPolarBox Pa φ z) : Work.FIPlan.IsPrimary z := h.1

theorem InPolarBox.odd_gnorm6 {Pa : Work.FITop.Params} {φ : ℝ} {z : GaussianInt}
    (h : Work.FITop3.InPolarBox Pa φ z) : Odd (Work.FIPlan.gnorm z) :=
  IsPrimary.odd_gnorm (InPolarBox.isPrimary6 h)

theorem InPolarBox.norm_bounds6 {Pa : Work.FITop.Params} {φ : ℝ} {z : GaussianInt}
    (h : Work.FITop3.InPolarBox Pa φ z) :
    Pa.N < (Work.FIPlan.gnorm z : ℝ) ∧ (Work.FIPlan.gnorm z : ℝ) ≤ (1 + Pa.θ) * Pa.N :=
  ⟨h.2.1, h.2.2.1⟩

/-! ## 0b. Numeric facts -/

/-- `θ ≤ 1/16` for every `Params` (`θ = (log x)^{-A'}`, `A' ≥ 2^20`, `log x ≥ 1.098`). -/
theorem theta_le_inv_sixteen (Pa : Work.FITop.Params) : Pa.θ ≤ 1 / 16 := by
  have hlog3 : (1098 : ℝ) / 1000 ≤ Real.log 3 := by
    have h := Real.log_three_gt_d9
    rw [show (1.0986122885 : ℝ) = (10986122885 : ℝ) / 10000000000 by norm_num] at h
    linarith
  have hx3 : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
  have hlogbase : ((1098 : ℝ) / 1000) ≤ Real.log (Pa.x : ℝ) :=
    le_trans hlog3 (Real.log_le_log (by norm_num) hx3)
  have hlog1 : (1 : ℝ) ≤ Real.log (Pa.x : ℝ) := by
    have h : ((1098 : ℝ) / 1000) ≤ Real.log (Pa.x : ℝ) := hlogbase
    linarith
  have hlogpos : 0 < Real.log (Pa.x : ℝ) := lt_of_lt_of_le zero_lt_one hlog1
  have hA : (100 : ℝ) ≤ Pa.A' := by
    have h1 : (2 : ℝ) ^ (20 : ℕ) ≤ Pa.A' := by linarith [Pa.hA', Pa.hA]
    have h2 : (100 : ℝ) ≤ (2 : ℝ) ^ (20 : ℕ) := by norm_num
    linarith
  have h16 : (16 : ℝ) ≤ (Real.log (Pa.x : ℝ)) ^ (100 : ℕ) := by
    have h1098 : (16 : ℝ) ≤ ((1098 : ℝ) / 1000) ^ (100 : ℕ) := by norm_num
    exact le_trans h1098 (pow_le_pow_left₀ (by norm_num) hlogbase 100)
  have h16' : (16 : ℝ) ≤ (Real.log (Pa.x : ℝ)) ^ ((100 : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]; exact h16
  rw [Pa.hθ, Real.rpow_neg hlogpos.le, one_div]
  exact (inv_le_inv₀ (Real.rpow_pos_of_pos hlogpos _) (by norm_num)).mpr
    (le_trans h16' (Real.rpow_le_rpow_of_exponent_le hlog1 hA))

/-- `2πθ ≤ 1/2` (the angular width of the polar box (5.14) is at most a right angle). -/
theorem two_pi_theta_le_half (Pa : Work.FITop.Params) : 2 * Real.pi * Pa.θ ≤ 1 / 2 := by
  have h16 := theta_le_inv_sixteen Pa
  have hpi : Real.pi < 4 := Real.pi_lt_four
  nlinarith [h16, hpi, Pa.hθ0]

/-- `log N ≥ 1` for `x ≥ 10^4`: `N > x^{1/4+η} ≥ x^{1/4} > e`. -/
theorem one_le_log_N (Pa : Work.FITop.Params) (hx : 10000 ≤ (Pa.x : ℝ)) :
    1 ≤ Real.log Pa.N := by
  have hx3 : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
  have hexp4 : Real.exp 4 ≤ (Pa.x : ℝ) := by
    have h1 : Real.exp 4 = (Real.exp 1) ^ (4 : ℕ) := by
      rw [← Real.exp_nat_mul]; norm_num
    have h2 : Real.exp 1 < 3 := Real.exp_one_lt_three
    have h3 : Real.exp 4 < 81 := by
      rw [h1]
      have h5 : (Real.exp 1) ^ 2 < 9 := by nlinarith [h2, Real.exp_pos 1]
      have h6 : (Real.exp 1) ^ 4 = ((Real.exp 1) ^ 2) ^ 2 := by ring
      rw [h6]
      nlinarith [h5, sq_nonneg ((Real.exp 1) ^ 2)]
    linarith
  have hlog4 : (4 : ℝ) ≤ Real.log (Pa.x : ℝ) := by
    rw [Real.le_log_iff_exp_le (by linarith : (0 : ℝ) < (Pa.x : ℝ))]
    exact hexp4
  have hxpos : 0 < (Pa.x : ℝ) := by linarith
  have hlogN : ((1 : ℝ) / 4 + Pa.η) * Real.log (Pa.x : ℝ) ≤ Real.log Pa.N := by
    have h1 : ((Pa.x : ℝ)) ^ ((1 : ℝ) / 4 + Pa.η) < Pa.N := Pa.hNlo
    calc ((1 : ℝ) / 4 + Pa.η) * Real.log (Pa.x : ℝ)
        = Real.log (((Pa.x : ℝ)) ^ ((1 : ℝ) / 4 + Pa.η)) := by
          rw [Real.log_rpow hxpos]
      _ ≤ Real.log Pa.N := Real.log_le_log (Real.rpow_pos_of_pos hxpos _) h1.le
  have h2 : (1 : ℝ) ≤ (1 / 4) * Real.log (Pa.x : ℝ) := by linarith
  nlinarith [hlogN, Pa.hη]

/-- A geometric bound for the discrete sum in (7.7): `Σ_{u ∈ Icc L U} u^{-1/2} ≤ 15√M` when
`L ≥ M/8` and `U ≤ 5M`. -/
theorem sum_inv_sqrt_range (M : ℝ) (hM : 4 ≤ M) (L U : ℕ)
    (hL : (M / 8 : ℝ) ≤ (L : ℝ)) (hU : (U : ℝ) ≤ 5 * M) :
    (∑ u ∈ Finset.Icc L U, (1 : ℝ) / Real.sqrt u) ≤ 20 * Real.sqrt M := by
  have hMpos : 0 < M := by linarith
  have hsqrtM : 0 < Real.sqrt M := Real.sqrt_pos.mpr hMpos
  by_cases hLU : L ≤ U
  · have hcard : ((Finset.Icc L U).card : ℝ) ≤ 6 * M := by
      rw [Nat.card_Icc]
      have h1 : U - L + 1 ≤ U + 1 := by omega
      have h2 : ((U - L + 1 : ℕ) : ℝ) ≤ (U : ℝ) + 1 := by exact_mod_cast h1
      have h3 : ((U + 1 - L : ℕ) : ℝ) = ((U - L + 1 : ℕ) : ℝ) := by
        congr 1
        omega
      rw [h3]
      linarith
    have hterm : ∀ u ∈ Finset.Icc L U,
        (1 : ℝ) / Real.sqrt u ≤ Real.sqrt 8 / Real.sqrt M := by
      intro u hu
      have hu1 : L ≤ u := (Finset.mem_Icc.mp hu).1
      have hu2 : (L : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu1
      have hupos : 0 < (u : ℝ) := by linarith [hL, hu2, hM]
      have hMle : M ≤ 8 * (u : ℝ) := by linarith
      have hs : Real.sqrt M ≤ Real.sqrt 8 * Real.sqrt (u : ℝ) := by
        rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 8)]
        exact Real.sqrt_le_sqrt hMle
      have hsu : 0 < Real.sqrt (u : ℝ) := Real.sqrt_pos.mpr hupos
      rw [div_le_iff₀ hsu]
      rw [div_mul_eq_mul_div, le_div_iff₀ hsqrtM]
      simpa using hs
    calc (∑ u ∈ Finset.Icc L U, (1 : ℝ) / Real.sqrt u)
        ≤ ∑ _u ∈ Finset.Icc L U, Real.sqrt 8 / Real.sqrt M := Finset.sum_le_sum hterm
      _ = ((Finset.Icc L U).card : ℝ) * (Real.sqrt 8 / Real.sqrt M) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 6 * M * (Real.sqrt 8 / Real.sqrt M) := by
          have h : (0 : ℝ) ≤ Real.sqrt 8 / Real.sqrt M :=
            div_nonneg (Real.sqrt_nonneg 8) (Real.sqrt_nonneg M)
          exact mul_le_mul_of_nonneg_right hcard h
      _ = 6 * Real.sqrt 8 * Real.sqrt M := by
          have hsq : Real.sqrt M * Real.sqrt M = M := by
            rw [← sq]
            exact Real.sq_sqrt hMpos.le
          have h1 : M / Real.sqrt M = Real.sqrt M := by
            rw [div_eq_iff (ne_of_gt hsqrtM)]
            exact hsq.symm
          calc 6 * M * (Real.sqrt 8 / Real.sqrt M)
              = 6 * Real.sqrt 8 * (M / Real.sqrt M) := by ring
            _ = 6 * Real.sqrt 8 * Real.sqrt M := by rw [h1]
      _ ≤ 20 * Real.sqrt M := by
          have h2 : Real.sqrt 8 ≤ 3 := by
            rw [Real.sqrt_le_iff]
            norm_num
          nlinarith [h2, Real.sqrt_nonneg M]
  · rw [Finset.Icc_eq_empty (by omega)]
    simp

/-! ## 1. The pair-sum reduction `D₀^exact − D₀` -/

/-- `D0ex` in the real form used by the per-pair bounds. -/
theorem D0ex_re_eq (Pa : Work.FITop.Params) (F : ℝ → ℝ) (β : GaussianInt → ℂ) :
    D0ex (Work.FITop.radN Pa) F β
      = ∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
          if Work.FIPlan.GaussCoprime z1 z2 then
            (β z1 * star (β z2)).re * C0ex F z1 z2
          else 0 := by
  rw [D0ex_eq]

/-- **(5.26) vs (9.11)**: `D₀^exact − D₀` is the `(β_{z₁}β̄_{z₂}).re`-weighted sum of the per-pair
(7.10) replacement errors. -/
theorem D0ex_sub_D0_re_eq (Pa : Work.FITop.Params) (f : ℤ → ℝ)
    (hf : Work.FITop4.IsMajorant6 Pa f) (β : GaussianInt → ℂ) :
    D0ex (Work.FITop.radN Pa) (majF Pa f hf) β
        - (Work.FITop4.D0 (Work.FITop.radN Pa) (Work.FITop3.Fhat Pa f) β).re
      = ∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
          if Work.FIPlan.GaussCoprime z1 z2 then
            (β z1 * star (β z2)).re
              * (C0ex (majF Pa f hf) z1 z2 - Work.FITop4.C0 (Work.FITop3.Fhat Pa f) z1 z2)
          else 0 := by
  rw [D0ex_re_eq, D0_6_re_eq, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun z1 _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun z2 _ => ?_
  by_cases hc : Work.FIPlan.GaussCoprime z1 z2 <;> simp [hc, mul_sub]

/-- The norm bound: `‖D₀^exact − D₀‖` is dominated by the `‖β_{z₁}‖‖β_{z₂}‖`-weighted sum of the
per-pair (7.10) errors (using that `D₀` is real). -/
theorem norm_D0ex_sub_D0_le (Pa : Work.FITop.Params) (f : ℤ → ℝ)
    (hf : Work.FITop4.IsMajorant6 Pa f) (β : GaussianInt → ℂ) :
    ‖((D0ex (Work.FITop.radN Pa) (majF Pa f hf) β : ℝ) : ℂ)
        - Work.FITop4.D0 (Work.FITop.radN Pa) (Work.FITop3.Fhat Pa f) β‖
      ≤ ∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
          if Work.FIPlan.GaussCoprime z1 z2 then
            ‖β z1‖ * ‖β z2‖
              * |C0ex (majF Pa f hf) z1 z2 - Work.FITop4.C0 (Work.FITop3.Fhat Pa f) z1 z2|
          else 0 := by
  have him := D0_6_im_eq_zero (Work.FITop.radN Pa) (Work.FITop3.Fhat Pa f) β
  have hcz : ((D0ex (Work.FITop.radN Pa) (majF Pa f hf) β : ℝ) : ℂ)
      - Work.FITop4.D0 (Work.FITop.radN Pa) (Work.FITop3.Fhat Pa f) β
      = ((D0ex (Work.FITop.radN Pa) (majF Pa f hf) β
          - (Work.FITop4.D0 (Work.FITop.radN Pa) (Work.FITop3.Fhat Pa f) β).re : ℝ) : ℂ) := by
    refine Complex.ext ?_ ?_ <;>
      simp [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, him]
  rw [hcz, Complex.norm_real, Real.norm_eq_abs, D0ex_sub_D0_re_eq Pa f hf β]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine Finset.sum_le_sum fun z1 _ => ?_
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine Finset.sum_le_sum fun z2 _ => ?_
  by_cases hc : Work.FIPlan.GaussCoprime z1 z2
  · have h3 : |(β z1 * star (β z2)).re| ≤ ‖β z1‖ * ‖β z2‖ := by
      calc |(β z1 * star (β z2)).re| ≤ ‖β z1 * star (β z2)‖ :=
            Complex.abs_re_le_norm (β z1 * star (β z2))
        _ = ‖β z1‖ * ‖β z2‖ := by rw [norm_mul, norm_star]
    have h4 : |(β z1 * star (β z2)).re
            * (C0ex (majF Pa f hf) z1 z2 - Work.FITop4.C0 (Work.FITop3.Fhat Pa f) z1 z2)|
        ≤ ‖β z1‖ * ‖β z2‖
            * |C0ex (majF Pa f hf) z1 z2 - Work.FITop4.C0 (Work.FITop3.Fhat Pa f) z1 z2| := by
      calc |(β z1 * star (β z2)).re
              * (C0ex (majF Pa f hf) z1 z2 - Work.FITop4.C0 (Work.FITop3.Fhat Pa f) z1 z2)|
          = |(β z1 * star (β z2)).re|
              * |C0ex (majF Pa f hf) z1 z2 - Work.FITop4.C0 (Work.FITop3.Fhat Pa f) z1 z2| :=
            abs_mul _ _
        _ ≤ (‖β z1‖ * ‖β z2‖)
              * |C0ex (majF Pa f hf) z1 z2 - Work.FITop4.C0 (Work.FITop3.Fhat Pa f) z1 z2| :=
            mul_le_mul_of_nonneg_right h3 (abs_nonneg _)
        _ = _ := by ring
    simpa [hc] using h4
  · simp [hc]

/-! ## 2. The nonnegative majorisation `majG` of `majF` -/

theorem majF_abs_le (Pa : Work.FITop.Params) (f : ℤ → ℝ) (hf : Work.FITop4.IsMajorant6 Pa f)
    (u : ℝ) : |majF Pa f hf u| ≤ Cder6 := by
  have hder := (majF_spec Pa f hf).2.2.2.2 0 (by norm_num) u
  simp only [Nat.cast_zero, neg_zero, iteratedDeriv_zero, Real.rpow_zero, mul_one] at hder
  exact hder

theorem majF_trace (Pa : Work.FITop.Params) (f : ℤ → ℝ) (hf : Work.FITop4.IsMajorant6 Pa f)
    (n : ℤ) : majF Pa f hf (n : ℝ) = f n := (majF_spec Pa f hf).2.2.1 n

theorem majF_support_spec (Pa : Work.FITop.Params) (f : ℤ → ℝ)
    (hf : Work.FITop4.IsMajorant6 Pa f) :
    ∀ u : ℝ, majF Pa f hf u ≠ 0 → Pa.M / 64 ≤ u ∧ u ≤ 64 * Pa.M :=
  (majF_spec Pa f hf).2.2.2.1

theorem majF_deriv_le (Pa : Work.FITop.Params) (f : ℤ → ℝ) (hf : Work.FITop4.IsMajorant6 Pa f)
    (u : ℝ) : |deriv (majF Pa f hf) u| ≤ Cder6 * (Pa.M)⁻¹ := by
  have hder := (majF_spec Pa f hf).2.2.2.2 1 (by norm_num) u
  rw [iteratedDeriv_one] at hder
  simpa [Nat.cast_one, Real.rpow_neg_one] using hder

theorem majF_contDiff (Pa : Work.FITop.Params) (f : ℤ → ℝ) (hf : Work.FITop4.IsMajorant6 Pa f) :
    ContDiff ℝ 4 (majF Pa f hf) := (majF_spec Pa f hf).1

/-- The mean value bound for `majF`. -/
theorem majF_mvt (Pa : Work.FITop.Params) (f : ℤ → ℝ) (hf : Work.FITop4.IsMajorant6 Pa f)
    (u v : ℝ) : |majF Pa f hf u - majF Pa f hf v| ≤ Cder6 * (Pa.M)⁻¹ * |u - v| := by
  have hdiff : Differentiable ℝ (majF Pa f hf) :=
    (majF_contDiff Pa f hf).differentiable (by norm_num)
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (f := majF Pa f hf) (s := Set.Icc (min u v) (max u v)) (C := Cder6 * (Pa.M)⁻¹)
    (fun x _ => hdiff.differentiableAt)
    (fun x _ => by rw [Real.norm_eq_abs]; exact majF_deriv_le Pa f hf x)
    (convex_Icc _ _) (Set.mem_Icc.mpr ⟨min_le_left _ _, le_max_left _ _⟩)
    (Set.mem_Icc.mpr ⟨min_le_right _ _, le_max_right _ _⟩)
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
  simpa [abs_sub_comm] using h

/-- `majF ≥ −Cder6/(2M)`: its trace is nonnegative and every point is within `1/2` of an integer. -/
theorem majF_lower (Pa : Work.FITop.Params) (f : ℤ → ℝ) (hf : Work.FITop4.IsMajorant6 Pa f)
    (u : ℝ) : -(Cder6 * (Pa.M)⁻¹ / 2) ≤ majF Pa f hf u := by
  obtain ⟨n, hn⟩ : ∃ n : ℤ, |u - (n : ℝ)| ≤ 1 / 2 := by
    refine ⟨⌊u + 1 / 2⌋, ?_⟩
    have h1 : ((⌊u + 1 / 2⌋ : ℤ) : ℝ) ≤ u + 1 / 2 := Int.floor_le _
    have h2 : u + 1 / 2 < ((⌊u + 1 / 2⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
    rw [abs_le]
    constructor <;> linarith
  have hmvt := majF_mvt Pa f hf u (n : ℝ)
  rw [majF_trace Pa f hf n] at hmvt
  have hC : (0 : ℝ) ≤ Cder6 * (Pa.M)⁻¹ :=
    mul_nonneg (le_of_lt Cder6_pos) (le_of_lt (inv_pos.mpr (lt_of_lt_of_le zero_lt_one Pa.hM1)))
  have hstep : Cder6 * (Pa.M)⁻¹ * |u - (n : ℝ)| ≤ Cder6 * (Pa.M)⁻¹ * (1 / 2) :=
    mul_le_mul_of_nonneg_left hn hC
  have hfn : 0 ≤ f n := hf.2.1 n
  have h2 : -(Cder6 * (Pa.M)⁻¹ * |u - (n : ℝ)|) ≤ majF Pa f hf u - f n := by
    have := neg_le_of_abs_le hmvt
    linarith
  linarith [h2, hstep, hfn]

theorem majG_nonneg (Pa : Work.FITop.Params) (f : ℤ → ℝ) (hf : Work.FITop4.IsMajorant6 Pa f)
    (u : ℝ) : 0 ≤ majG Pa f hf u := by
  unfold majG
  have hδ : (0 : ℝ) ≤ (Pa.M)⁻¹ := le_of_lt (inv_pos.mpr (lt_of_lt_of_le zero_lt_one Pa.hM1))
  have h1 : ((Pa.M)⁻¹) ^ 2 ≤ (majF Pa f hf u) ^ 2 + (Pa.M)⁻¹ ^ 2 :=
    le_add_of_nonneg_left (sq_nonneg _)
  have h2 : (Pa.M)⁻¹ ≤ Real.sqrt ((majF Pa f hf u) ^ 2 + (Pa.M)⁻¹ ^ 2) :=
    (Real.le_sqrt hδ (by positivity)).mpr h1
  linarith

theorem majG_eq_zero_iff (Pa : Work.FITop.Params) (f : ℤ → ℝ) (hf : Work.FITop4.IsMajorant6 Pa f)
    (u : ℝ) : majG Pa f hf u = 0 ↔ majF Pa f hf u = 0 := by
  have hδpos : 0 < (Pa.M)⁻¹ := inv_pos.mpr (lt_of_lt_of_le zero_lt_one Pa.hM1)
  constructor
  · intro h
    unfold majG at h
    have h2 : Real.sqrt ((majF Pa f hf u) ^ 2 + (Pa.M)⁻¹ ^ 2) = (Pa.M)⁻¹ := by linarith
    have h3 : (majF Pa f hf u) ^ 2 + (Pa.M)⁻¹ ^ 2 = ((Pa.M)⁻¹) ^ 2 := by
      calc (majF Pa f hf u) ^ 2 + (Pa.M)⁻¹ ^ 2
          = (Real.sqrt ((majF Pa f hf u) ^ 2 + (Pa.M)⁻¹ ^ 2)) ^ 2 :=
            (Real.sq_sqrt (by positivity)).symm
        _ = ((Pa.M)⁻¹) ^ 2 := by rw [h2]
    have hzero : (majF Pa f hf u) ^ 2 = 0 := by linarith [sq_nonneg (majF Pa f hf u)]
    exact pow_eq_zero_iff (by norm_num : 2 ≠ 0) |>.mp hzero
  · intro h
    unfold majG
    rw [h]
    have h0 : (0 : ℝ) ^ 2 + (Pa.M)⁻¹ ^ 2 = ((Pa.M)⁻¹) ^ 2 := by ring
    rw [h0, Real.sqrt_sq_eq_abs, abs_of_pos hδpos]
    ring

theorem majG_abs_le (Pa : Work.FITop.Params) (f : ℤ → ℝ) (hf : Work.FITop4.IsMajorant6 Pa f)
    (u : ℝ) : |majG Pa f hf u| ≤ Cder6 := by
  rw [abs_of_nonneg (majG_nonneg Pa f hf u)]
  have hδ : (0 : ℝ) ≤ (Pa.M)⁻¹ := le_of_lt (inv_pos.mpr (lt_of_lt_of_le zero_lt_one Pa.hM1))
  have hsq : (majF Pa f hf u) ^ 2 + (Pa.M)⁻¹ ^ 2 ≤ (|majF Pa f hf u| + (Pa.M)⁻¹) ^ 2 := by
    rw [add_sq, sq_abs]
    nlinarith [mul_nonneg (abs_nonneg (majF Pa f hf u)) hδ]
  have h1 : Real.sqrt ((majF Pa f hf u) ^ 2 + (Pa.M)⁻¹ ^ 2) ≤ |majF Pa f hf u| + (Pa.M)⁻¹ := by
    calc Real.sqrt ((majF Pa f hf u) ^ 2 + (Pa.M)⁻¹ ^ 2)
        ≤ Real.sqrt ((|majF Pa f hf u| + (Pa.M)⁻¹) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = |majF Pa f hf u| + (Pa.M)⁻¹ := Real.sqrt_sq (by positivity)
  have h2 := majF_abs_le Pa f hf u
  unfold majG
  linarith

theorem majG_support_spec (Pa : Work.FITop.Params) (f : ℤ → ℝ)
    (hf : Work.FITop4.IsMajorant6 Pa f) :
    ∀ u : ℝ, majG Pa f hf u ≠ 0 → Pa.M / 64 ≤ u ∧ u ≤ 64 * Pa.M := by
  intro u hu
  refine majF_support_spec Pa f hf u ?_
  intro h0
  exact hu ((majG_eq_zero_iff Pa f hf u).mpr h0)

theorem majG_trace (Pa : Work.FITop.Params) (f : ℤ → ℝ) (hf : Work.FITop4.IsMajorant6 Pa f)
    (n : ℤ) :
    majG Pa f hf (n : ℝ) = Real.sqrt ((f n) ^ 2 + (Pa.M)⁻¹ ^ 2) - (Pa.M)⁻¹ := by
  unfold majG
  rw [majF_trace Pa f hf n]

theorem majG_hasCompactSupport (Pa : Work.FITop.Params) (f : ℤ → ℝ)
    (hf : Work.FITop4.IsMajorant6 Pa f) : HasCompactSupport (majG Pa f hf) := by
  refine HasCompactSupport.of_support_subset_isCompact
    (K := Set.Icc (Pa.M / 64) (64 * Pa.M)) isCompact_Icc ?_
  intro u hu
  exact ⟨(majG_support_spec Pa f hf u (Function.mem_support.mp hu)).1,
    (majG_support_spec Pa f hf u (Function.mem_support.mp hu)).2⟩

theorem majG_contDiff (Pa : Work.FITop.Params) (f : ℤ → ℝ) (hf : Work.FITop4.IsMajorant6 Pa f) :
    ContDiff ℝ 1 (majG Pa f hf) := by
  have hbase : ContDiff ℝ 1 (fun v : ℝ => (majF Pa f hf v) ^ 2 + (Pa.M)⁻¹ ^ 2) :=
    (((majF_contDiff Pa f hf).of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 4)).pow 2).add
      contDiff_const
  have hsqrt : ContDiff ℝ 1
      (fun v : ℝ => Real.sqrt ((majF Pa f hf v) ^ 2 + (Pa.M)⁻¹ ^ 2)) := by
    rw [contDiff_iff_contDiffAt]
    intro v
    have hpos : 0 < (majF Pa f hf v) ^ 2 + (Pa.M)⁻¹ ^ 2 := by
      have hδ : 0 < (Pa.M)⁻¹ := inv_pos.mpr (lt_of_lt_of_le zero_lt_one Pa.hM1)
      positivity
    exact (hbase.contDiffAt).sqrt (ne_of_gt hpos)
  exact hsqrt.sub contDiff_const

theorem majG_hasDerivAt (Pa : Work.FITop.Params) (f : ℤ → ℝ) (hf : Work.FITop4.IsMajorant6 Pa f)
    (u : ℝ) :
    HasDerivAt (majG Pa f hf)
      ((majF Pa f hf u * deriv (majF Pa f hf) u)
        / Real.sqrt ((majF Pa f hf u) ^ 2 + (Pa.M)⁻¹ ^ 2)) u := by
  have hδpos : 0 < (Pa.M)⁻¹ := inv_pos.mpr (lt_of_lt_of_le zero_lt_one Pa.hM1)
  have hpos : 0 < (majF Pa f hf u) ^ 2 + (Pa.M)⁻¹ ^ 2 := by positivity
  have hdiff : DifferentiableAt ℝ (majF Pa f hf) u :=
    ((majF_contDiff Pa f hf).differentiable (by norm_num)).differentiableAt
  have h1 : HasDerivAt (fun v : ℝ => (majF Pa f hf v) ^ 2 + (Pa.M)⁻¹ ^ 2)
      (2 * (majF Pa f hf u) ^ (2 - 1) * deriv (majF Pa f hf) u) u := by
    simpa using (hdiff.hasDerivAt.pow 2).add_const ((Pa.M)⁻¹ ^ 2)
  have h2 : HasDerivAt (fun v : ℝ => Real.sqrt ((majF Pa f hf v) ^ 2 + (Pa.M)⁻¹ ^ 2))
      ((2 * (majF Pa f hf u) ^ (2 - 1) * deriv (majF Pa f hf) u)
        / (2 * Real.sqrt ((majF Pa f hf u) ^ 2 + (Pa.M)⁻¹ ^ 2))) u :=
    h1.sqrt (ne_of_gt hpos)
  have h3 := h2.sub_const ((Pa.M)⁻¹)
  have h4 : (majG Pa f hf)
      = fun v : ℝ => Real.sqrt ((majF Pa f hf v) ^ 2 + (Pa.M)⁻¹ ^ 2) - (Pa.M)⁻¹ := rfl
  rw [h4]
  refine h3.congr_deriv ?_
  rw [show (2 - 1 : ℕ) = 1 by norm_num, pow_one]
  ring

theorem majG_deriv_le (Pa : Work.FITop.Params) (f : ℤ → ℝ) (hf : Work.FITop4.IsMajorant6 Pa f)
    (u : ℝ) : |deriv (majG Pa f hf) u| ≤ Cder6 * (Pa.M)⁻¹ := by
  rw [(majG_hasDerivAt Pa f hf u).deriv]
  have hδpos : 0 < (Pa.M)⁻¹ := inv_pos.mpr (lt_of_lt_of_le zero_lt_one Pa.hM1)
  have hden : 0 < Real.sqrt ((majF Pa f hf u) ^ 2 + (Pa.M)⁻¹ ^ 2) := by
    rw [Real.sqrt_pos]
    positivity
  have hge : |majF Pa f hf u| ≤ Real.sqrt ((majF Pa f hf u) ^ 2 + (Pa.M)⁻¹ ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (le_add_of_nonneg_right (by positivity))
  rw [abs_div, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [div_le_iff₀ hden]
  have hb := majF_deriv_le Pa f hf u
  calc |majF Pa f hf u| * |deriv (majF Pa f hf) u|
      ≤ Real.sqrt ((majF Pa f hf u) ^ 2 + (Pa.M)⁻¹ ^ 2) * (Cder6 * (Pa.M)⁻¹) :=
        mul_le_mul hge hb (abs_nonneg _) (Real.sqrt_nonneg _)
    _ = Cder6 * (Pa.M)⁻¹ * Real.sqrt ((majF Pa f hf u) ^ 2 + (Pa.M)⁻¹ ^ 2) := by ring

/-- `majG` is pointwise within `(Cder6+1)/M` of `majF`. -/
theorem majG_close (Pa : Work.FITop.Params) (f : ℤ → ℝ) (hf : Work.FITop4.IsMajorant6 Pa f)
    (u : ℝ) : |majG Pa f hf u - majF Pa f hf u| ≤ (Cder6 + 1) * (Pa.M)⁻¹ := by
  have hδpos : 0 < (Pa.M)⁻¹ := inv_pos.mpr (lt_of_lt_of_le zero_lt_one Pa.hM1)
  have hnn : 0 ≤ majG Pa f hf u := majG_nonneg Pa f hf u
  set a := majF Pa f hf u
  have hg : majG Pa f hf u = Real.sqrt (a ^ 2 + (Pa.M)⁻¹ ^ 2) - (Pa.M)⁻¹ := rfl
  have hsq : Real.sqrt (a ^ 2 + (Pa.M)⁻¹ ^ 2) ^ 2 = a ^ 2 + (Pa.M)⁻¹ ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hge : |a| ≤ Real.sqrt (a ^ 2 + (Pa.M)⁻¹ ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (le_add_of_nonneg_right (by positivity))
  have hle : Real.sqrt (a ^ 2 + (Pa.M)⁻¹ ^ 2) ≤ |a| + (Pa.M)⁻¹ := by
    have hs : a ^ 2 + (Pa.M)⁻¹ ^ 2 ≤ (|a| + (Pa.M)⁻¹) ^ 2 := by
      rw [add_sq, sq_abs]
      nlinarith [mul_nonneg (abs_nonneg a) (le_of_lt hδpos)]
    calc Real.sqrt (a ^ 2 + (Pa.M)⁻¹ ^ 2) ≤ Real.sqrt ((|a| + (Pa.M)⁻¹) ^ 2) :=
          Real.sqrt_le_sqrt hs
      _ = |a| + (Pa.M)⁻¹ := Real.sqrt_sq (by positivity)
  have halow : a ≥ -(Cder6 * (Pa.M)⁻¹ / 2) := majF_lower Pa f hf u
  rw [hg]
  rcases le_or_gt 0 a with ha0 | ha0
  · have h1 : a ≤ Real.sqrt (a ^ 2 + (Pa.M)⁻¹ ^ 2) := by
      simpa [abs_of_nonneg ha0] using hge
    have h2 : Real.sqrt (a ^ 2 + (Pa.M)⁻¹ ^ 2) ≤ a + (Pa.M)⁻¹ := by
      simpa [abs_of_nonneg ha0] using hle
    rw [abs_le]
    constructor
    · nlinarith [h1, hδpos, Cder6_pos]
    · nlinarith [h2, hδpos, Cder6_pos]
  · have h1 : -a ≤ Real.sqrt (a ^ 2 + (Pa.M)⁻¹ ^ 2) := by
      simpa [abs_of_neg ha0] using hge
    have h2 : Real.sqrt (a ^ 2 + (Pa.M)⁻¹ ^ 2) ≤ -a + (Pa.M)⁻¹ := by
      simpa [abs_of_neg ha0] using hle
    have h3 : -a ≤ Cder6 * (Pa.M)⁻¹ / 2 := by linarith [halow]
    rw [abs_le]
    constructor
    · nlinarith [h1, hδpos, Cder6_pos]
    · nlinarith [h2, h3, hδpos, Cder6_pos]

/-! ## 3. Two `Fint`/`Fhat` comparison lemmas -/

/-- At `(0,0)`, `Fint` is additive in the majorant: two continuous functions with the same support
window and pointwise distance `≤ c` have Fourier integrals within `c·vol(regG)`. -/
theorem Fint_sub_zero_zero_le (M γ A B c cF cG : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hA : 0 < A) (hAB : A ≤ B) (hB : B ≤ 64 * M) (hM : 1 ≤ M) (hc : 0 ≤ c)
    (F G : ℝ → ℝ) (hFc : Continuous F) (hGc : Continuous G)
    (hFs : ∀ u : ℝ, F u ≠ 0 → A ≤ u ∧ u ≤ B)
    (hGs : ∀ u : ℝ, G u ≠ 0 → A ≤ u ∧ u ≤ B)
    (hFb : ∀ u : ℝ, |F u| ≤ cF) (hGb : ∀ u : ℝ, |G u| ≤ cG)
    (hbd : ∀ u : ℝ, |F u - G u| ≤ c) :
    ‖Work.FIArea2.Fint F γ 0 0 - Work.FIArea2.Fint G γ 0 0‖
      ≤ c * (2000 * Real.sqrt M * Real.log (2 + 1 / (1 - γ ^ 2))) := by
  have hvol : volume (regG A B γ) < ⊤ :=
    lt_of_le_of_lt (vol_regG_le M γ A B hM hγ0 hγ1 hA hAB hB) ENNReal.ofReal_lt_top
  have hlog0 : (0 : ℝ) ≤ Real.log (2 + 1 / (1 - γ ^ 2)) := by
    refine Real.log_nonneg ?_
    have h1γ2 : 0 < 1 - γ ^ 2 := Work.FIArea2.one_sub_gamma_sq_pos γ hγ0 hγ1
    have h : 0 < 1 / (1 - γ ^ 2) := one_div_pos.mpr h1γ2
    linarith
  have hvolb : (volume (regG A B γ)).toReal
      ≤ 2000 * Real.sqrt M * Real.log (2 + 1 / (1 - γ ^ 2)) := by
    have h := vol_regG_le M γ A B hM hγ0 hγ1 hA hAB hB
    calc (volume (regG A B γ)).toReal
        ≤ (ENNReal.ofReal (2000 * Real.sqrt M * Real.log (2 + 1 / (1 - γ ^ 2)))).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_lt_top.ne h
      _ = 2000 * Real.sqrt M * Real.log (2 + 1 / (1 - γ ^ 2)) :=
          ENNReal.toReal_ofReal (by positivity)
  have hmem : ∀ t : ℝ × ℝ, t ∈ regG A B γ ↔
      A ≤ Work.FIArea2.gq γ t.1 t.2 ∧ Work.FIArea2.gq γ t.1 t.2 ≤ B := fun t => Iff.rfl
  have hIF : Integrable (fun t : ℝ × ℝ => ((F (Work.FIArea2.gQuartic γ t) : ℝ) : ℂ)) := by
    refine Integrable.mono' ((integrable_indicator_regG A B γ hvol).const_mul cF) ?_ ?_
    · exact (Complex.continuous_ofReal.comp
        (hFc.comp (by unfold Work.FIArea2.gQuartic; fun_prop))).aestronglyMeasurable
    · filter_upwards with t
      rw [Complex.norm_real, Real.norm_eq_abs]
      by_cases ht : A ≤ Work.FIArea2.gq γ t.1 t.2 ∧ Work.FIArea2.gq γ t.1 t.2 ≤ B
      · rw [Set.indicator_of_mem (hmem t |>.mpr ht), mul_one]
        exact hFb _
      · have hzero : F (Work.FIArea2.gQuartic γ t) = 0 := f_gq_eq_zero_gen A B γ F hFs ht
        rw [hzero, abs_zero,
          Set.indicator_of_notMem (fun hmem' => ht ((hmem t).mp hmem')), mul_zero]
  have hIG : Integrable (fun t : ℝ × ℝ => ((G (Work.FIArea2.gQuartic γ t) : ℝ) : ℂ)) := by
    refine Integrable.mono' ((integrable_indicator_regG A B γ hvol).const_mul cG) ?_ ?_
    · exact (Complex.continuous_ofReal.comp
        (hGc.comp (by unfold Work.FIArea2.gQuartic; fun_prop))).aestronglyMeasurable
    · filter_upwards with t
      rw [Complex.norm_real, Real.norm_eq_abs]
      by_cases ht : A ≤ Work.FIArea2.gq γ t.1 t.2 ∧ Work.FIArea2.gq γ t.1 t.2 ≤ B
      · rw [Set.indicator_of_mem (hmem t |>.mpr ht), mul_one]
        exact hGb _
      · have hzero : G (Work.FIArea2.gQuartic γ t) = 0 := f_gq_eq_zero_gen A B γ G hGs ht
        rw [hzero, abs_zero,
          Set.indicator_of_notMem (fun hmem' => ht ((hmem t).mp hmem')), mul_zero]
  rw [Work.FIArea2.Fint_zero_zero, Work.FIArea2.Fint_zero_zero, ← integral_sub hIF hIG]
  calc ‖∫ t : ℝ × ℝ, ((F (Work.FIArea2.gQuartic γ t) : ℝ) : ℂ)
        - ((G (Work.FIArea2.gQuartic γ t) : ℝ) : ℂ)‖
      ≤ ∫ t : ℝ × ℝ, ‖((F (Work.FIArea2.gQuartic γ t) : ℝ) : ℂ)
        - ((G (Work.FIArea2.gQuartic γ t) : ℝ) : ℂ)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ × ℝ, c * Set.indicator (regG A B γ) (fun _ => (1 : ℝ)) t := by
        refine integral_mono (hIF.sub hIG).norm
          ((integrable_indicator_regG A B γ hvol).const_mul c) (fun t => ?_)
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        by_cases ht : A ≤ Work.FIArea2.gq γ t.1 t.2 ∧ Work.FIArea2.gq γ t.1 t.2 ≤ B
        · rw [Set.indicator_of_mem (hmem t |>.mpr ht), mul_one]
          exact hbd _
        · have hzF : F (Work.FIArea2.gQuartic γ t) = 0 := f_gq_eq_zero_gen A B γ F hFs ht
          have hzG : G (Work.FIArea2.gQuartic γ t) = 0 := f_gq_eq_zero_gen A B γ G hGs ht
          rw [hzF, hzG, sub_zero, abs_zero,
            Set.indicator_of_notMem (fun hmem' => ht ((hmem t).mp hmem')), mul_zero]
    _ = c * (volume (regG A B γ)).toReal := by
        rw [MeasureTheory.integral_const_mul,
          MeasureTheory.integral_indicator_const (1 : ℝ) (measurableSet_regG A B γ), smul_eq_mul,
          mul_one, MeasureTheory.measureReal_def]
    _ ≤ c * (2000 * Real.sqrt M * Real.log (2 + 1 / (1 - γ ^ 2))) :=
        mul_le_mul_of_nonneg_left hvolb hc

/-- The geometric bound for a `ℤ`-indexed sum: `Σ_{u ∈ Icc L U} u^{-1/2} ≤ 20√M` when
`L ≥ M/8`, `U ≤ 5M`. -/
theorem sum_inv_sqrt_range_int (M : ℝ) (hM : 8 ≤ M) (L U : ℤ)
    (hL : (M / 8 : ℝ) ≤ (L : ℝ)) (hU : (U : ℝ) ≤ 5 * M) (hLU : L ≤ U) :
    (∑ u ∈ Finset.Icc L U, (1 : ℝ) / Real.sqrt (u : ℝ)) ≤ 20 * Real.sqrt M := by
  have hMpos : 0 < M := by linarith
  have hsqrtM : 0 < Real.sqrt M := Real.sqrt_pos.mpr hMpos
  have hL0 : (0 : ℤ) ≤ L := by
    have h : (0 : ℝ) ≤ (L : ℝ) := by linarith [hL, hM]
    exact_mod_cast h
  have hU0 : (0 : ℤ) ≤ U := le_trans hL0 hLU
  have hUt : ((U.toNat : ℕ) : ℤ) = U := Int.toNat_of_nonneg hU0
  have hcard : ((Finset.Icc L U).card : ℝ) ≤ 6 * M := by
    rw [Int.card_Icc]
    have hm : ((U + 1 - L).toNat : ℕ) ≤ U.toNat + 1 := by
      rw [Int.toNat_le]
      push_cast
      rw [hUt]
      omega
    have hUc : ((U.toNat : ℕ) : ℝ) = (U : ℝ) := by exact_mod_cast hUt
    have hbn : (((U.toNat + 1 : ℕ)) : ℝ) ≤ (U : ℝ) + 1 := by
      rw [Nat.cast_add, Nat.cast_one, hUc]
    have h1 : (((U + 1 - L).toNat : ℕ) : ℝ) ≤ (U : ℝ) + 1 :=
      le_trans (by exact_mod_cast hm) hbn
    linarith
  have hterm : ∀ u ∈ Finset.Icc L U,
      (1 : ℝ) / Real.sqrt (u : ℝ) ≤ Real.sqrt 8 / Real.sqrt M := by
    intro u hu
    have hu1 : L ≤ u := (Finset.mem_Icc.mp hu).1
    have hu2 : (L : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu1
    have hupos : 0 < (u : ℝ) := by linarith [hL, hu2, hM]
    have hMle : M ≤ 8 * (u : ℝ) := by linarith
    have hs : Real.sqrt M ≤ Real.sqrt 8 * Real.sqrt (u : ℝ) := by
      rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 8)]
      exact Real.sqrt_le_sqrt hMle
    have hsu : 0 < Real.sqrt (u : ℝ) := Real.sqrt_pos.mpr hupos
    rw [div_le_iff₀ hsu]
    rw [div_mul_eq_mul_div, le_div_iff₀ hsqrtM]
    simpa using hs
  calc (∑ u ∈ Finset.Icc L U, (1 : ℝ) / Real.sqrt (u : ℝ))
      ≤ ∑ _u ∈ Finset.Icc L U, Real.sqrt 8 / Real.sqrt M := Finset.sum_le_sum hterm
    _ = ((Finset.Icc L U).card : ℝ) * (Real.sqrt 8 / Real.sqrt M) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 6 * M * (Real.sqrt 8 / Real.sqrt M) := by
        have h : (0 : ℝ) ≤ Real.sqrt 8 / Real.sqrt M :=
          div_nonneg (Real.sqrt_nonneg 8) (Real.sqrt_nonneg M)
        exact mul_le_mul_of_nonneg_right hcard h
    _ = 6 * Real.sqrt 8 * Real.sqrt M := by
        have hsq : Real.sqrt M * Real.sqrt M = M := by
          rw [← sq]
          exact Real.sq_sqrt hMpos.le
        have h1 : M / Real.sqrt M = Real.sqrt M := by
          rw [div_eq_iff (ne_of_gt hsqrtM)]
          exact hsq.symm
        calc 6 * M * (Real.sqrt 8 / Real.sqrt M)
            = 6 * Real.sqrt 8 * (M / Real.sqrt M) := by ring
          _ = 6 * Real.sqrt 8 * Real.sqrt M := by rw [h1]
    _ ≤ 20 * Real.sqrt M := by
        have h2 : Real.sqrt 8 ≤ 3 := by
          rw [Real.sqrt_le_iff]
          norm_num
        nlinarith [h2, Real.sqrt_nonneg M]

/-- The discrete mean value (7.7): replacing `f` by the trace of `majG` changes `Fhat` by at most
`20/√M`. -/
theorem Fhat_trace_sub_le (Pa : Work.FITop.Params) (f : ℤ → ℝ)
    (hf : Work.FITop4.IsMajorant6 Pa f) (hM8 : 8 ≤ Pa.M) :
    |Work.FITop3.Fhat Pa (fun n : ℤ => majG Pa f hf (n : ℝ)) - Work.FITop3.Fhat Pa f|
      ≤ 20 / Real.sqrt Pa.M := by
  have hMpos : 0 < Pa.M := by linarith
  have hδpos : (0 : ℝ) < (Pa.M)⁻¹ := inv_pos.mpr hMpos
  have hsqpos : 0 < Real.sqrt Pa.M := Real.sqrt_pos.mpr hMpos
  have hL1 : (Pa.M / 8 : ℝ) ≤ (((⌊Pa.M / 4⌋₊ : ℕ)) : ℝ) := by
    have h := Nat.lt_floor_add_one (Pa.M / 4)
    linarith
  have hU1 : (((⌈4 * Pa.M⌉₊ : ℕ)) : ℝ) ≤ 5 * Pa.M := by
    have h := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ 4 * Pa.M)
    linarith
  have hLU : (⌊Pa.M / 4⌋₊ : ℤ) ≤ (⌈4 * Pa.M⌉₊ : ℤ) := by
    have h : (Pa.M / 4 : ℝ) ≤ (⌈4 * Pa.M⌉₊ : ℝ) := by
      have h1 := Nat.le_ceil (4 * Pa.M)
      linarith
    have h2 : (⌊Pa.M / 4⌋₊ : ℝ) ≤ Pa.M / 4 := Nat.floor_le (by linarith)
    have h3 : ((⌊Pa.M / 4⌋₊ : ℕ) : ℝ) ≤ ((⌈4 * Pa.M⌉₊ : ℕ) : ℝ) := le_trans h2 h
    exact_mod_cast h3
  have hsum := sum_inv_sqrt_range_int Pa.M hM8 (⌊Pa.M / 4⌋₊ : ℤ) (⌈4 * Pa.M⌉₊ : ℤ) hL1 hU1 hLU
  have hdiff : Work.FITop3.Fhat Pa (fun n : ℤ => majG Pa f hf (n : ℝ)) - Work.FITop3.Fhat Pa f
      = ∑ u ∈ Finset.Icc (⌊Pa.M / 4⌋₊ : ℤ) (⌈4 * Pa.M⌉₊ : ℤ),
          (Real.sqrt ((f u) ^ 2 + (Pa.M)⁻¹ ^ 2) - (Pa.M)⁻¹ - f u) / Real.sqrt (u : ℝ) := by
    unfold Work.FITop3.Fhat
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    simp only [majG_trace Pa f hf u]
    ring
  rw [hdiff]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ u ∈ Finset.Icc (⌊Pa.M / 4⌋₊ : ℤ) (⌈4 * Pa.M⌉₊ : ℤ),
      |(Real.sqrt ((f u) ^ 2 + (Pa.M)⁻¹ ^ 2) - (Pa.M)⁻¹ - f u) / Real.sqrt (u : ℝ)|
        ≤ (Pa.M)⁻¹ / Real.sqrt (u : ℝ) := by
    intro u _
    have hfu : 0 ≤ f u := hf.2.1 u
    have hge : f u ≤ Real.sqrt ((f u) ^ 2 + (Pa.M)⁻¹ ^ 2) :=
      (Real.le_sqrt hfu (by positivity)).mpr (le_add_of_nonneg_right (sq_nonneg (Pa.M)⁻¹))
    have hle : Real.sqrt ((f u) ^ 2 + (Pa.M)⁻¹ ^ 2) ≤ f u + (Pa.M)⁻¹ := by
      have hs : (f u) ^ 2 + (Pa.M)⁻¹ ^ 2 ≤ (f u + (Pa.M)⁻¹) ^ 2 := by
        nlinarith [hfu, hδpos.le]
      calc Real.sqrt ((f u) ^ 2 + (Pa.M)⁻¹ ^ 2) ≤ Real.sqrt ((f u + (Pa.M)⁻¹) ^ 2) :=
            Real.sqrt_le_sqrt hs
        _ = f u + (Pa.M)⁻¹ := Real.sqrt_sq (by linarith)
    have habs : |Real.sqrt ((f u) ^ 2 + (Pa.M)⁻¹ ^ 2) - (Pa.M)⁻¹ - f u| ≤ (Pa.M)⁻¹ := by
      rw [abs_le]
      exact ⟨by linarith, by linarith⟩
    rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg (u : ℝ))]
    exact div_le_div_of_nonneg_right habs (Real.sqrt_nonneg _)
  refine le_trans (Finset.sum_le_sum hterm) ?_
  calc (∑ u ∈ Finset.Icc (⌊Pa.M / 4⌋₊ : ℤ) (⌈4 * Pa.M⌉₊ : ℤ),
        (Pa.M)⁻¹ / Real.sqrt (u : ℝ))
      = (Pa.M)⁻¹ * ∑ u ∈ Finset.Icc (⌊Pa.M / 4⌋₊ : ℤ) (⌈4 * Pa.M⌉₊ : ℤ),
          (1 : ℝ) / Real.sqrt (u : ℝ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun u _ => ?_
        ring
    _ ≤ (Pa.M)⁻¹ * (20 * Real.sqrt Pa.M) := mul_le_mul_of_nonneg_left hsum hδpos.le
    _ = 20 / Real.sqrt Pa.M := by
        have hsq : Real.sqrt Pa.M * Real.sqrt Pa.M = Pa.M := by
          rw [← sq]
          exact Real.sq_sqrt hMpos.le
        have h1 : (Pa.M)⁻¹ = (Real.sqrt Pa.M)⁻¹ * (Real.sqrt Pa.M)⁻¹ := by
          rw [← mul_inv, hsq]
        calc Pa.M⁻¹ * (20 * Real.sqrt Pa.M)
            = 20 * ((Pa.M)⁻¹ * Real.sqrt Pa.M) := by ring
          _ = 20 * ((Real.sqrt Pa.M)⁻¹ * (Real.sqrt Pa.M)⁻¹ * Real.sqrt Pa.M) := by rw [h1]
          _ = 20 * (Real.sqrt Pa.M)⁻¹ := by
              rw [mul_assoc, inv_mul_cancel₀ (ne_of_gt hsqpos), mul_one]
          _ = 20 / Real.sqrt Pa.M := by rw [div_eq_mul_inv]

/-! ## 4. The kernel bound: the corrected (8.16) -/

/-- The Jacobi symbol of the residue (6.6) is `0` or `±1`. -/
theorem abs_ratioSym_le_one (z1 z2 : GaussianInt) (d : ℕ) :
    |(Work.FIArea7.ratioSym z1 z2 d : ℝ)| ≤ 1 := by
  rw [Work.FIArea7.ratioSym]
  rcases jacobiSym.trichotomy
    ((((star z1 * z2).re : ZMod d) * (((Work.FIPlan.gnorm z1 : ℕ) : ZMod d))⁻¹).val : ℤ) d
    with h | h | h <;> rw [h] <;> norm_num

/-- **The corrected (8.16) bound**: on the pairs that occur (coprime, both in the support of a
round-6 coefficient), `|G₀(z₁,z₂)| ≤ 2(1+τ(|Δ|))`. -/
theorem G0_abs_le6 {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt} {β : GaussianInt → ℂ}
    (hβ : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) {z1 z2 : GaussianInt}
    (h1 : β z1 ≠ 0) (h2 : β z2 ≠ 0) (hcop : Work.FIPlan.GaussCoprime z1 z2) :
    |Work.FITop4.G0 z1 z2| ≤ 2 * (1 + (((Work.FIPlan.absDelta z1 z2).divisors.card : ℕ) : ℝ)) := by
  have hbox1 := Work.FITop4.IsBetaCoeff6.support hβ h1
  have hbox2 := Work.FITop4.IsBetaCoeff6.support hβ h2
  have hodd1 := InPolarBox.odd_gnorm6 hbox1
  have hcl := Work.FITop4.IsBetaCoeff6.sameClass hβ h1 h2
  have hprim1 := Work.FIArea2.isCoprime_star_of_squarefree_odd_gnorm
    (Work.FITop4.IsBetaCoeff6.squarefree_gnorm hβ h1) hodd1
  have hprim2 := Work.FIArea2.isCoprime_star_of_squarefree_odd_gnorm
    (Work.FITop4.IsBetaCoeff6.squarefree_gnorm hβ h2) (InPolarBox.odd_gnorm6 hbox2)
  have hn1 : 2 ≤ Work.FIPlan.gnorm z1 := by
    have hgt : (1 : ℝ) < (Work.FIPlan.gnorm z1 : ℝ) :=
      lt_of_le_of_lt (by exact_mod_cast Pa.hN1) (InPolarBox.norm_bounds6 hbox1).1
    have hgt' : (1 : ℕ) < Work.FIPlan.gnorm z1 := by exact_mod_cast hgt
    omega
  have hDelta : Work.FIPlan.Delta z1 z2 ≠ 0 :=
    delta_ne_zero_of_coprime hcop hprim1 hprim2 hn1
  have hD : Work.FIPlan.absDelta z1 z2 ≠ 0 := by
    simpa [Work.FIPlan.absDelta] using Int.natAbs_ne_zero.mpr hDelta
  have hsum := Work.FITop4.Red6.G0_eq_ratioSym_sum hodd1 hcl hD hcop hprim1 hprim2
  have hcard : (Work.FITop4.Sset z1 z2).card ≤ (Work.FIPlan.absDelta z1 z2).divisors.card := by
    refine Finset.card_le_card fun d hd => ?_
    rw [Work.FITop4.Sset, Finset.mem_filter] at hd
    obtain ⟨hdIcc, hdvd⟩ := hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hdIcc).1
    exact Nat.mem_divisors.mpr ⟨dvd_trans (dvd_mul_left d 4) hdvd, hD⟩
  have hbound : |∑ d ∈ Work.FITop4.Sset z1 z2,
        ((Nat.totient d : ℝ) / (d : ℝ)) * (Work.FIArea7.ratioSym z1 z2 d : ℝ)|
      ≤ ((Work.FIPlan.absDelta z1 z2).divisors.card : ℝ) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ d ∈ Work.FITop4.Sset z1 z2,
        |((Nat.totient d : ℝ) / (d : ℝ)) * (Work.FIArea7.ratioSym z1 z2 d : ℝ)| ≤ 1 := by
      intro d hd
      rw [Work.FITop4.Sset, Finset.mem_filter] at hd
      have hd1 : (0 : ℝ) < (d : ℝ) := by
        have : 1 ≤ d := (Finset.mem_Icc.mp hd.1).1
        exact_mod_cast this
      have ht : |((Nat.totient d : ℝ) / (d : ℝ))| ≤ 1 := by
        rw [abs_of_nonneg (by positivity)]
        rw [div_le_one hd1]
        exact_mod_cast Nat.totient_le d
      calc |((Nat.totient d : ℝ) / (d : ℝ)) * (Work.FIArea7.ratioSym z1 z2 d : ℝ)|
          = |((Nat.totient d : ℝ) / (d : ℝ))| * |(Work.FIArea7.ratioSym z1 z2 d : ℝ)| :=
            abs_mul _ _
        _ ≤ 1 * 1 := mul_le_mul ht (abs_ratioSym_le_one z1 z2 d) (abs_nonneg _) (by norm_num)
        _ = 1 := by norm_num
    calc ∑ d ∈ Work.FITop4.Sset z1 z2,
          |((Nat.totient d : ℝ) / (d : ℝ)) * (Work.FIArea7.ratioSym z1 z2 d : ℝ)|
        ≤ ∑ _d ∈ Work.FITop4.Sset z1 z2, (1 : ℝ) := Finset.sum_le_sum hterm
      _ = ((Work.FITop4.Sset z1 z2).card : ℝ) := by simp
      _ ≤ ((Work.FIPlan.absDelta z1 z2).divisors.card : ℝ) := by exact_mod_cast hcard
  rw [hsum]
  have habs2 : |(2 : ℝ) * ∑ d ∈ Work.FITop4.Sset z1 z2,
        ((Nat.totient d : ℝ) / (d : ℝ)) * (Work.FIArea7.ratioSym z1 z2 d : ℝ)|
      = 2 * |∑ d ∈ Work.FITop4.Sset z1 z2,
        ((Nat.totient d : ℝ) / (d : ℝ)) * (Work.FIArea7.ratioSym z1 z2 d : ℝ)| := by
    rw [abs_mul]
    norm_num
  rw [habs2]
  have hdivnn : (0 : ℝ) ≤ (((Work.FIPlan.absDelta z1 z2).divisors.card : ℕ) : ℝ) := by positivity
  linarith

/-! ## 5. The per-pair algebra and the (7.10) bracket -/

/-- The conclusion shape of the (7.10) input `FintProp` at an explicit constant: this is
`FintProp` with its existential constant extracted. -/
def FintBound (Cf : ℝ) : Prop :=
  ∀ (Pa : Work.FITop.Params) (A B Cder : ℝ) (F : ℝ → ℝ) (f : ℤ → ℝ) (z1 z2 : GaussianInt),
    Pa.M / 64 ≤ A → B ≤ 64 * Pa.M → 1 ≤ Cder → 1 ≤ Pa.M →
    ContDiff ℝ 1 F → HasCompactSupport F → (∀ n : ℤ, F (n : ℝ) = f n) →
    (∀ u : ℤ, f u ≠ 0 → Pa.M / 4 ≤ (u : ℝ) ∧ (u : ℝ) ≤ 4 * Pa.M) →
    (∀ u : ℝ, 0 ≤ F u) → (∀ u : ℝ, |F u| ≤ Cder) →
    (∀ u : ℝ, F u ≠ 0 → A ≤ u ∧ u ≤ B) →
    (∀ u : ℝ, |deriv F u| ≤ Cder / Pa.M) →
    (1 / 2 : ℝ) ≤ Work.FIArea2.gamOf z1 z2 → Work.FIArea2.gamOf z1 z2 < 1 →
    Work.FIPlan.absDelta z1 z2 ≠ 0 →
    ‖Work.FIArea2.Fint F (Work.FIArea2.gamOf z1 z2) 0 0
        - ((Work.FITop3.Fhat Pa f : ℝ) : ℂ) * ((Work.FITop4.logFac6 z1 z2 : ℝ) : ℂ)‖
      ≤ Cf * Cder * (Real.sqrt Pa.M * (1 - Work.FIArea2.gamOf z1 z2 ^ 2)
            * Real.log (2 + 1 / (1 - Work.FIArea2.gamOf z1 z2 ^ 2))
          + (Real.sqrt Pa.M)⁻¹
            * Real.log (2 + 8 * Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ))))

/-- The per-pair difference of the two main-term kernels: `C₀^exact − C₀` is the (6.13) kernel
times the (7.10) bracket. -/
theorem C0ex_sub_C0_eq (Pa : Work.FITop.Params) (f : ℤ → ℝ)
    (hf : Work.FITop4.IsMajorant6 Pa f) (z1 z2 : GaussianInt) :
    C0ex (majF Pa f hf) z1 z2 - Work.FITop4.C0 (Work.FITop3.Fhat Pa f) z1 z2
      = (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ) ^ (-(1 : ℝ) / 4)) * (Work.FITop4.G0 z1 z2)
        * ((Work.FIArea2.Fint (majF Pa f hf) (Work.FIArea2.gamOf z1 z2) 0 0).re
            - (Work.FITop3.Fhat Pa f) * Work.FITop4.logFac6 z1 z2) := by
  unfold C0ex Work.FITop4.C0
  rw [Gsum_zero_zero6 z1 z2, Complex.mul_re, Complex.ofReal_im, Complex.ofReal_re]
  ring

/-- `γ ≥ 1/2` for two points of the polar box (their arguments differ by at most `2πθ ≤ 1/2`). -/
theorem gamOf_ge_half_of_polarBox6 (Pa : Work.FITop.Params) (φ : ℝ) (z1 z2 : GaussianInt)
    (h1 : Work.FITop3.InPolarBox Pa φ z1) (h2 : Work.FITop3.InPolarBox Pa φ z2) :
    1 / 2 ≤ Work.FIArea2.gamOf z1 z2 := by
  have hθ := two_pi_theta_le_half Pa
  have hd : |Complex.arg z2.toComplex - Complex.arg z1.toComplex| ≤ 2 * Real.pi * Pa.θ := by
    rw [abs_sub_le_iff]
    constructor <;> linarith [h1.2.2.2.1, h1.2.2.2.2, h2.2.2.2.1, h2.2.2.2.2]
  have hd1 : |Complex.arg z2.toComplex - Complex.arg z1.toComplex| ≤ 1 / 2 := le_trans hd hθ
  have hgn1 : (1 : ℝ) < (Work.FIPlan.gnorm z1 : ℝ) :=
    lt_of_le_of_lt (by exact_mod_cast Pa.hN1) h1.2.1
  have hgn2 : (1 : ℝ) < (Work.FIPlan.gnorm z2 : ℝ) :=
    lt_of_le_of_lt (by exact_mod_cast Pa.hN1) h2.2.1
  have hz1 : z1 ≠ 0 := by
    intro hz
    rw [hz] at hgn1
    simp [Work.FIPlan.gnorm] at hgn1
    linarith
  have hz2 : z2 ≠ 0 := by
    intro hz
    rw [hz] at hgn2
    simp [Work.FIPlan.gnorm] at hgn2
    linarith
  rw [Work.FIArea2.gamOf_eq_cos_arg z1 z2 hz1 hz2]
  set d := Complex.arg z2.toComplex - Complex.arg z1.toComplex with hddef
  have hcos0 : 0 ≤ Real.cos d := by
    refine Real.cos_nonneg_of_mem_Icc ⟨?_, ?_⟩
    · linarith [neg_abs_le d, Real.pi_gt_three]
    · linarith [le_abs_self d, Real.pi_gt_three]
  have hsin2 : (Real.sin d) ^ 2 ≤ 1 / 4 := by
    have ha : (Real.sin d) ^ 2 ≤ d ^ 2 := by
      have h := Real.abs_sin_le_abs (x := d)
      nlinarith [h, sq_abs (Real.sin d), sq_abs d, abs_nonneg (Real.sin d)]
    have hb : d ^ 2 ≤ 1 / 4 := by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, sq_le_sq]
      rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      exact hd1
    linarith
  have hcos2 : 1 / 4 ≤ (Real.cos d) ^ 2 := by
    have h := Real.sin_sq_add_cos_sq d
    linarith
  calc (1 / 2 : ℝ) = Real.sqrt (1 / 4) := by
        rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    _ ≤ Real.sqrt ((Real.cos d) ^ 2) := Real.sqrt_le_sqrt hcos2
    _ = Real.cos d := Real.sqrt_sq hcos0

/-- `γ < 1` when `Δ ≠ 0` (then `1 − γ² = |Δ|²/|z₁z₂|² > 0`). -/
theorem gamOf_lt_one_of_absDelta_ne {z1 z2 : GaussianInt}
    (hΔ : Work.FIPlan.absDelta z1 z2 ≠ 0) : Work.FIArea2.gamOf z1 z2 < 1 := by
  have h := Work.FIArea2.R6.one_sub_gamOf_sq_eq z1 z2 hΔ
  have h1 : (1 : ℝ) ≤ ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) :=
    by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hΔ
  have h2 : (0 : ℝ) < ((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ) := by
    rw [Work.FIArea4.gnorm_mul]
    push_cast
    refine mul_pos ?_ ?_
    · exact_mod_cast Nat.pos_of_ne_zero (fun h0 => by
        have : z1 = 0 := by
          simpa [Work.FIPlan.gnorm] using h0
        exact hΔ (by rw [this]; simp [Work.FIPlan.absDelta, Work.FIPlan.Delta]))
    · exact_mod_cast Nat.pos_of_ne_zero (fun h0 => by
        have : z2 = 0 := by
          simpa [Work.FIPlan.gnorm] using h0
        exact hΔ (by rw [this]; simp [Work.FIPlan.absDelta, Work.FIPlan.Delta]))
  have hpos : 0 < 1 - (Work.FIArea2.gamOf z1 z2) ^ 2 := by
    rw [h]
    exact div_pos (by positivity) h2
  have h3 : |Work.FIArea2.gamOf z1 z2| < 1 := by
    rw [← sq_lt_one_iff_abs_lt_one]
    linarith
  linarith [le_abs_self (Work.FIArea2.gamOf z1 z2), h3]

/-- The ingredient bounds for the bracket: `1-γ² ≤ 4π²θ²`, the two logarithmic factors are
`≤ 3log N` resp. `≤ 4log N`, and `|logFac6| ≤ 4log N`. -/
theorem logFac6_bounds {Pa : Work.FITop.Params} {φ : ℝ} {z1 z2 : GaussianInt}
    (h1 : Work.FITop3.InPolarBox Pa φ z1) (h2 : Work.FITop3.InPolarBox Pa φ z2)
    (hΔ : Work.FIPlan.absDelta z1 z2 ≠ 0) (hN10 : 10 ≤ Pa.N) (hθ1 : Pa.θ ≤ 1) :
    1 - (Work.FIArea2.gamOf z1 z2) ^ 2 ≤ 4 * Real.pi ^ 2 * Pa.θ ^ 2
    ∧ Real.log (2 + 1 / (1 - (Work.FIArea2.gamOf z1 z2) ^ 2)) ≤ 3 * Real.log Pa.N
    ∧ Real.log (2 + 8 * Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ))) ≤ 4 * Real.log Pa.N
    ∧ |Work.FITop4.logFac6 z1 z2| ≤ 4 * Real.log Pa.N := by
  have hlogN0 : 0 ≤ Real.log Pa.N := Real.log_nonneg (by linarith)
  have hN2 : (9 : ℝ) ≤ Pa.N ^ 2 := by nlinarith [hN10]
  have hN3 : (729 : ℝ) ≤ Pa.N ^ 3 := by nlinarith [hN10, hN2]
  have hgn1 : (1 : ℝ) < (Work.FIPlan.gnorm z1 : ℝ) :=
    lt_of_le_of_lt (by exact_mod_cast Pa.hN1) h1.2.1
  have hgn2 : (1 : ℝ) < (Work.FIPlan.gnorm z2 : ℝ) :=
    lt_of_le_of_lt (by exact_mod_cast Pa.hN1) h2.2.1
  have hz1 : z1 ≠ 0 := by
    intro hz
    rw [hz] at hgn1
    simp [Work.FIPlan.gnorm] at hgn1
    linarith
  have hz2 : z2 ≠ 0 := by
    intro hz
    rw [hz] at hgn2
    simp [Work.FIPlan.gnorm] at hgn2
    linarith
  -- (0) the norm of the product and the lower bound for `1-γ²`
  have hgnorm : ((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ) ≤ 4 * Pa.N ^ 2 := by
    rw [Work.FIArea4.gnorm_mul]
    push_cast
    have h3 := (InPolarBox.norm_bounds6 h1).2
    have h4 := (InPolarBox.norm_bounds6 h2).2
    have h4nn : (0 : ℝ) ≤ (1 + Pa.θ) * Pa.N := by nlinarith [Pa.hθ0, Pa.hN1]
    have hmul : ((Work.FIPlan.gnorm z1 : ℕ) : ℝ) * ((Work.FIPlan.gnorm z2 : ℕ) : ℝ)
        ≤ ((1 + Pa.θ) * Pa.N) * ((1 + Pa.θ) * Pa.N) :=
      mul_le_mul h3 h4 (by positivity) h4nn
    have h6 : (1 + Pa.θ) ≤ 2 := by linarith
    have h7 : (0 : ℝ) ≤ 1 + Pa.θ := by linarith [Pa.hθ0]
    have h8 : (1 + Pa.θ) * (1 + Pa.θ) ≤ 4 := by nlinarith [h6]
    have h5 : ((1 + Pa.θ) * Pa.N) * ((1 + Pa.θ) * Pa.N) ≤ 4 * Pa.N ^ 2 := by
      have h9 : ((1 + Pa.θ) * Pa.N) * ((1 + Pa.θ) * Pa.N)
          = ((1 + Pa.θ) * (1 + Pa.θ)) * (Pa.N * Pa.N) := by ring
      rw [h9]
      have h10 : (0 : ℝ) ≤ Pa.N * Pa.N := by positivity
      have h11 : ((1 + Pa.θ) * (1 + Pa.θ)) * (Pa.N * Pa.N) ≤ 4 * (Pa.N * Pa.N) :=
        mul_le_mul_of_nonneg_right h8 h10
      nlinarith [h11]
    exact le_trans hmul h5
  have hdelta1 : (1 : ℝ) ≤ ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) :=
    by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hΔ
  have hgn2pos : (0 : ℝ) < ((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ) := by
    rw [Work.FIArea4.gnorm_mul]
    push_cast
    exact mul_pos (by linarith [hgn1]) (by linarith [hgn2])
  have hgnmul1 : (1 : ℝ) ≤ ((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ) := by
    rw [Work.FIArea4.gnorm_mul]
    push_cast
    nlinarith [hgn1, hgn2]
  have hgam_eq := Work.FIArea2.R6.one_sub_gamOf_sq_eq z1 z2 hΔ
  have h1γ_pos : 0 < 1 - (Work.FIArea2.gamOf z1 z2) ^ 2 := by
    rw [hgam_eq]
    exact div_pos (by positivity) hgn2pos
  have hDle : ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) ^ 2
      ≤ ((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ) := by
    have h1 : 1 - (Work.FIArea2.gamOf z1 z2) ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg (Work.FIArea2.gamOf z1 z2)]
    rw [hgam_eq] at h1
    exact (div_le_one hgn2pos).mp h1
  have h1γ_low : 1 / (4 * Pa.N ^ 2) ≤ 1 - (Work.FIArea2.gamOf z1 z2) ^ 2 := by
    rw [hgam_eq]
    rw [div_le_div_iff₀ (show (0 : ℝ) < 4 * Pa.N ^ 2 by positivity) hgn2pos]
    have h6 : (1 : ℝ) ≤ ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) ^ 2 := by nlinarith [hdelta1]
    have h7 : (0 : ℝ) ≤ 4 * Pa.N ^ 2 := by positivity
    have h8 : 4 * Pa.N ^ 2 ≤ ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) ^ 2 * (4 * Pa.N ^ 2) := by
      simpa using mul_le_mul_of_nonneg_right h6 h7
    linarith [hgnorm, h8]
  -- (1) `1-γ² ≤ 4π²θ²`
  have harg : |Complex.arg z2.toComplex - Complex.arg z1.toComplex| ≤ 2 * Real.pi * Pa.θ := by
    rw [abs_sub_le_iff]
    constructor <;> linarith [h1.2.2.2.1, h1.2.2.2.2, h2.2.2.2.1, h2.2.2.2.2]
  have hγcos := Work.FIArea2.gamOf_eq_cos_arg z1 z2 hz1 hz2
  have hpart1 : 1 - (Work.FIArea2.gamOf z1 z2) ^ 2 ≤ 4 * Real.pi ^ 2 * Pa.θ ^ 2 := by
    have hsin : Real.sin (Complex.arg z2.toComplex - Complex.arg z1.toComplex) ^ 2
        ≤ (2 * Real.pi * Pa.θ) ^ 2 := by
      have hs := Real.abs_sin_le_abs (x := Complex.arg z2.toComplex - Complex.arg z1.toComplex)
      have h2' : |Real.sin (Complex.arg z2.toComplex - Complex.arg z1.toComplex)|
          ≤ 2 * Real.pi * Pa.θ := le_trans hs harg
      nlinarith [h2', sq_abs (Real.sin (Complex.arg z2.toComplex - Complex.arg z1.toComplex)),
        abs_nonneg (Real.sin (Complex.arg z2.toComplex - Complex.arg z1.toComplex)),
        Real.pi_pos, Pa.hθ0, harg]
    have hsq : 1 - (Work.FIArea2.gamOf z1 z2) ^ 2
        = Real.sin (Complex.arg z2.toComplex - Complex.arg z1.toComplex) ^ 2 := by
      rw [hγcos, Real.sin_sq]
    rw [hsq]
    nlinarith [hsin, Pa.hθ0, Real.pi_pos]
  -- (2) the two logs
  have hpart2 : Real.log (2 + 1 / (1 - (Work.FIArea2.gamOf z1 z2) ^ 2)) ≤ 3 * Real.log Pa.N := by
    have h4 : 1 / (1 - (Work.FIArea2.gamOf z1 z2) ^ 2) ≤ 4 * Pa.N ^ 2 := by
      have h6 : 1 ≤ (1 - (Work.FIArea2.gamOf z1 z2) ^ 2) * (4 * Pa.N ^ 2) :=
        (div_le_iff₀ (show (0 : ℝ) < 4 * Pa.N ^ 2 by positivity)).mp h1γ_low
      rw [div_le_iff₀ h1γ_pos]
      linarith [h6]
    have h3 : 2 + 1 / (1 - (Work.FIArea2.gamOf z1 z2) ^ 2) ≤ Pa.N ^ 3 := by
      have h5 : 4 * Pa.N ^ 2 + 2 ≤ Pa.N ^ 3 := by nlinarith [hN10, hN2, hN3]
      linarith [h4, h5]
    have hpos3 : (0 : ℝ) < 2 + 1 / (1 - (Work.FIArea2.gamOf z1 z2) ^ 2) := by
      have := one_div_pos.mpr h1γ_pos
      linarith
    calc Real.log (2 + 1 / (1 - (Work.FIArea2.gamOf z1 z2) ^ 2)) ≤ Real.log (Pa.N ^ 3) :=
          Real.log_le_log hpos3 h3
      _ = 3 * Real.log Pa.N := by rw [Real.log_pow]; push_cast; ring
  have hs_le : Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ)) ≤ 2 * Pa.N := by
    rw [Real.sqrt_le_iff]
    exact ⟨by positivity, by nlinarith [hgnorm]⟩
  have hpart3 : Real.log (2 + 8 * Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ)))
      ≤ 4 * Real.log Pa.N := by
    have h3 : 2 + 8 * Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ)) ≤ Pa.N ^ 4 := by
      have h5 : 16 * Pa.N + 2 ≤ Pa.N ^ 4 := by nlinarith [hN10, hN2, hN3, sq_nonneg Pa.N]
      linarith [hs_le, h5]
    calc Real.log (2 + 8 * Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ)))
        ≤ Real.log (Pa.N ^ 4) := Real.log_le_log (by positivity) h3
      _ = 4 * Real.log Pa.N := by rw [Real.log_pow]; push_cast; ring
  -- (3) `logFac6`
  have hpart4 : |Work.FITop4.logFac6 z1 z2| ≤ 4 * Real.log Pa.N := by
    rw [Work.FITop4.logFac6]
    have hDpos : 0 < ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) := by linarith
    have hge1 : 1 ≤ 8 * Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ))
        / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) := by
      rw [le_div_iff₀ hDpos]
      have hs : (1 : ℝ) ≤ Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ)) :=
        (Real.le_sqrt (by norm_num) (by positivity)).mpr (by nlinarith [hgnmul1])
      have hDl : ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
          ≤ Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ)) := by
        rw [Real.le_sqrt (by positivity) (by positivity)]
        exact hDle
      nlinarith [hs, hDl, Real.sqrt_nonneg (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ))]
    have hle2 : 8 * Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ))
        / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) ≤ Pa.N ^ 4 := by
      rw [div_le_iff₀ hDpos]
      have h16 : 8 * Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ)) ≤ 16 * Pa.N := by
        linarith
      have h5 : 16 * Pa.N + 2 ≤ Pa.N ^ 4 := by nlinarith [hN10, hN2, hN3, sq_nonneg Pa.N]
      nlinarith [h16, hdelta1, h5]
    rw [abs_le]
    constructor
    · have := Real.log_nonneg hge1
      linarith [this, hlogN0]
    · calc Real.log (8 * Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ))
            / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ))
          ≤ Real.log (Pa.N ^ 4) := Real.log_le_log (by positivity) hle2
        _ = 4 * Real.log Pa.N := by rw [Real.log_pow]; push_cast; ring
  exact ⟨hpart1, hpart2, hpart3, hpart4⟩

/-! ## 6. The (7.10) bracket for `majF` and the uniform per-pair bound -/

/-- The uniform per-pair bound for the (7.10) replacement error. -/
def Amax (Pa : Work.FITop.Params) (K1 K2 : ℝ) : ℝ :=
  K1 * Real.sqrt Pa.M * Pa.θ ^ 2 * Real.log Pa.N + K2 * Real.log Pa.N / Real.sqrt Pa.M

/-- The coefficient of `√M θ² log N` in `Amax` at the constant `Cf` of `FintProp`. -/
def Ka (Cf : ℝ) : ℝ := 12 * Real.pi ^ 2 * (Cf + 1) * (Cder6 + 1)

/-- The coefficient of `log N/√M` in `Amax` at the constant `Cf` of `FintProp`. -/
def Kb (Cf : ℝ) : ℝ := 4 * ((Cf + 1) * (Cder6 + 1)) + 6000 * (Cder6 + 1) + 288

theorem Ka_nonneg (Cf : ℝ) (hCf : 0 < Cf) : 0 ≤ Ka Cf := by
  rw [Ka]
  have h1 : (0 : ℝ) < Cder6 + 1 := by linarith [Cder6_pos]
  have h2 : (0 : ℝ) < Cf + 1 := by linarith
  have h3 : (0 : ℝ) < Real.pi ^ 2 := by positivity
  positivity

theorem Kb_nonneg (Cf : ℝ) (hCf : 0 < Cf) : 0 ≤ Kb Cf := by
  rw [Kb]
  have h1 : (0 : ℝ) < Cder6 + 1 := by linarith [Cder6_pos]
  have h2 : (0 : ℝ) < Cf + 1 := by linarith
  positivity

/-- `log N ≥ 10`'s proxy: `N ≥ 10` when `x ≥ 10^4`. -/
theorem ten_le_N (Pa : Work.FITop.Params) (hx : 10000 ≤ (Pa.x : ℝ)) : 10 ≤ Pa.N := by
  have hxpos : (0 : ℝ) < (Pa.x : ℝ) := by linarith
  have h1 : ((10000 : ℝ)) ^ ((1 : ℝ) / 4) ≤ (Pa.x : ℝ) ^ ((1 : ℝ) / 4) :=
    Real.rpow_le_rpow (by norm_num) hx (by norm_num)
  have h2 : ((10000 : ℝ)) ^ ((1 : ℝ) / 4) = 10 := by
    rw [show (10000 : ℝ) = (10 : ℝ) ^ 4 by norm_num, ← Real.rpow_natCast]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 10)]
    norm_num
  have h3 := Pa.hNlo
  have h4 : (Pa.x : ℝ) ^ ((1 : ℝ) / 4) ≤ (Pa.x : ℝ) ^ ((1 : ℝ) / 4 + Pa.η) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith [Pa.hη])
  have h5 : (10 : ℝ) ≤ Pa.N := by linarith [h1, h2, h3, h4]
  exact_mod_cast h5

/-- The main arithmetic: `Amax ≤ (2max)·(τ⁻¹+θ)·√M·(log N)^{2^19}`. -/
theorem Amax_le_target (Pa : Work.FITop.Params) {Cf : ℝ} (hCf : 0 < Cf)
    (hx : 10000 ≤ (Pa.x : ℝ)) :
    Amax Pa (Ka Cf) (Kb Cf)
      ≤ (2 * max (Ka Cf) (Kb Cf)) * (Pa.τ⁻¹ + Pa.θ) * Real.sqrt Pa.M
          * (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ)) := by
  have hN1 : (1 : ℝ) ≤ Pa.N := by exact_mod_cast Pa.hN1
  have hM1 : (1 : ℝ) ≤ Pa.M := Pa.hM1
  have hMpos : 0 < Pa.M := lt_of_lt_of_le zero_lt_one hM1
  have hlogN1 : 1 ≤ Real.log Pa.N := one_le_log_N Pa hx
  have hlN0 : 0 ≤ Real.log Pa.N := le_trans zero_le_one hlogN1
  have hsM : 0 < Real.sqrt Pa.M := Real.sqrt_pos.mpr hMpos
  have hsM0 : (0 : ℝ) ≤ Real.sqrt Pa.M := le_of_lt hsM
  have hsM2 : Real.sqrt Pa.M * Real.sqrt Pa.M = Pa.M := by
    rw [← sq]
    exact Real.sq_sqrt hMpos.le
  have hθ0 : 0 ≤ Pa.θ := le_of_lt Pa.hθ0
  have hθ1 : Pa.θ ≤ 1 := theta_le_one6 Pa
  have hK1 : 0 ≤ Ka Cf := Ka_nonneg Cf hCf
  have hK2 : 0 ≤ Kb Cf := Kb_nonneg Cf hCf
  have hKmax : 0 ≤ 2 * max (Ka Cf) (Kb Cf) := by
    have h := le_trans hK1 (le_max_left (Ka Cf) (Kb Cf))
    linarith
  have hKle1 : Ka Cf ≤ 2 * max (Ka Cf) (Kb Cf) := by
    have h := le_max_left (Ka Cf) (Kb Cf)
    linarith
  have hKle2 : Kb Cf ≤ 2 * max (Ka Cf) (Kb Cf) := by
    have h := le_max_right (Ka Cf) (Kb Cf)
    linarith
  have hP0 : 0 ≤ (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ)) := pow_nonneg hlN0 _
  have hlNleP : Real.log Pa.N ≤ (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ)) := by
    simpa using pow_le_pow_right₀ hlogN1 (by norm_num : 1 ≤ (2 : ℕ) ^ (19 : ℕ))
  have hterm1 : Ka Cf * Real.sqrt Pa.M * Pa.θ ^ 2 * Real.log Pa.N
      ≤ (2 * max (Ka Cf) (Kb Cf)) * Pa.θ * Real.sqrt Pa.M
          * (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ)) := by
    have hθ2 : Pa.θ ^ 2 ≤ Pa.θ := by nlinarith [hθ0, hθ1]
    have hmid : Ka Cf * (Pa.θ ^ 2 * Real.log Pa.N)
        ≤ (2 * max (Ka Cf) (Kb Cf)) * (Pa.θ * (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ))) := by
      have h5 : Pa.θ ^ 2 * Real.log Pa.N
          ≤ Pa.θ * (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ)) :=
        mul_le_mul hθ2 hlNleP hlN0 hθ0
      calc Ka Cf * (Pa.θ ^ 2 * Real.log Pa.N)
          ≤ Ka Cf * (Pa.θ * (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ))) :=
            mul_le_mul_of_nonneg_left h5 hK1
        _ ≤ (2 * max (Ka Cf) (Kb Cf)) * (Pa.θ * (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ))) :=
            mul_le_mul_of_nonneg_right hKle1 (mul_nonneg hθ0 hP0)
    calc Ka Cf * Real.sqrt Pa.M * Pa.θ ^ 2 * Real.log Pa.N
        = (Ka Cf * (Pa.θ ^ 2 * Real.log Pa.N)) * Real.sqrt Pa.M := by ring_nf
      _ ≤ ((2 * max (Ka Cf) (Kb Cf)) * (Pa.θ * (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ))))
            * Real.sqrt Pa.M := mul_le_mul_of_nonneg_right hmid hsM0
      _ = (2 * max (Ka Cf) (Kb Cf)) * Pa.θ * Real.sqrt Pa.M
            * (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ)) := by ring_nf
  have hterm2 : Kb Cf * Real.log Pa.N / Real.sqrt Pa.M
      ≤ (2 * max (Ka Cf) (Kb Cf)) * Pa.τ⁻¹ * Real.sqrt Pa.M
          * (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ)) := by
    have hxpos : (0 : ℝ) < (Pa.x : ℝ) := by linarith
    have hτle : Pa.τ ≤ (Pa.x : ℝ) ^ (Pa.η / 3) := Pa.hτ2
    have hlogxpos : 0 < Real.log (Pa.x : ℝ) := by
      have hx3 : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
      have h3 : (1.0986122885 : ℝ) < Real.log 3 := Real.log_three_gt_d9
      have h4 : Real.log 3 ≤ Real.log (Pa.x : ℝ) := Real.log_le_log (by norm_num) hx3
      linarith
    have hτpos : 0 < Pa.τ := lt_of_lt_of_le (Real.rpow_pos_of_pos hlogxpos _) Pa.hτ1
    have hτinv : ((Pa.x : ℝ)) ^ (-(Pa.η / 3)) ≤ Pa.τ⁻¹ := by
      have h := (inv_le_inv₀ (Real.rpow_pos_of_pos hxpos _) hτpos).mpr hτle
      simpa [← Real.rpow_neg hxpos.le] using h
    have hx14 : (1 : ℝ) ≤ ((Pa.x : ℝ)) ^ ((1 : ℝ) / 4) := by
      have h := Real.rpow_le_rpow (show (0 : ℝ) ≤ 1 by norm_num)
        (le_trans (by norm_num : (1:ℝ) ≤ 10000) hx) (show (0 : ℝ) ≤ (1 : ℝ) / 4 by norm_num)
      simpa using h
    have hsplit : ((Pa.x : ℝ)) ^ ((1 : ℝ) / 4)
        ≤ ((Pa.x : ℝ)) ^ (-(Pa.η / 3)) * ((Pa.x : ℝ)) ^ ((1 : ℝ) / 4 + Pa.η) := by
      rw [← Real.rpow_add hxpos]
      refine Real.rpow_le_rpow_of_exponent_le (by linarith) ?_
      linarith [Pa.hη]
    have hMlo : ((Pa.x : ℝ)) ^ ((1 : ℝ) / 4 + Pa.η) ≤ Pa.M := le_trans Pa.hNlo.le Pa.hMge
    have hτM : (1 : ℝ) ≤ Pa.τ⁻¹ * Pa.M := by
      have h3 : (0 : ℝ) ≤ ((Pa.x : ℝ)) ^ ((1 : ℝ) / 4 + Pa.η) :=
        Real.rpow_nonneg hxpos.le _
      have h4 : (0 : ℝ) ≤ Pa.τ⁻¹ := by positivity
      calc (1 : ℝ) ≤ ((Pa.x : ℝ)) ^ ((1 : ℝ) / 4) := hx14
        _ ≤ ((Pa.x : ℝ)) ^ (-(Pa.η / 3)) * ((Pa.x : ℝ)) ^ ((1 : ℝ) / 4 + Pa.η) := hsplit
        _ ≤ Pa.τ⁻¹ * Pa.M := mul_le_mul hτinv hMlo h3 h4
    have hKbP : Kb Cf * Real.log Pa.N
        ≤ (2 * max (Ka Cf) (Kb Cf)) * (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ)) := by
      calc Kb Cf * Real.log Pa.N ≤ Kb Cf * (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ)) :=
            mul_le_mul_of_nonneg_left hlNleP hK2
        _ ≤ (2 * max (Ka Cf) (Kb Cf)) * (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ)) :=
            mul_le_mul_of_nonneg_right hKle2 hP0
    have h1 : Kb Cf * Real.log Pa.N / Real.sqrt Pa.M
        ≤ (2 * max (Ka Cf) (Kb Cf)) * (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ)) / Real.sqrt Pa.M :=
      div_le_div_of_nonneg_right hKbP hsM0
    have h2 : (2 * max (Ka Cf) (Kb Cf)) * (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ)) / Real.sqrt Pa.M
        ≤ (2 * max (Ka Cf) (Kb Cf)) * Pa.τ⁻¹ * Real.sqrt Pa.M
            * (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ)) := by
      rw [div_le_iff₀ hsM]
      have h5 : (2 * max (Ka Cf) (Kb Cf)) ≤ (2 * max (Ka Cf) (Kb Cf)) * (Pa.τ⁻¹ * Pa.M) := by
        nlinarith [hτM, hKmax]
      have h3 : (2 * max (Ka Cf) (Kb Cf)) * (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ))
          ≤ (2 * max (Ka Cf) (Kb Cf)) * (Pa.τ⁻¹ * Pa.M) * (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ)) :=
        mul_le_mul_of_nonneg_right h5 hP0
      have h4 : (2 * max (Ka Cf) (Kb Cf)) * Pa.τ⁻¹ * Real.sqrt Pa.M
            * (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ)) * Real.sqrt Pa.M
          = (2 * max (Ka Cf) (Kb Cf)) * (Pa.τ⁻¹ * Pa.M) * (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ)) := by
        calc (2 * max (Ka Cf) (Kb Cf)) * Pa.τ⁻¹ * Real.sqrt Pa.M
              * (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ)) * Real.sqrt Pa.M
            = (2 * max (Ka Cf) (Kb Cf)) * Pa.τ⁻¹ * (Real.sqrt Pa.M * Real.sqrt Pa.M)
              * (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ)) := by ring
          _ = (2 * max (Ka Cf) (Kb Cf)) * Pa.τ⁻¹ * Pa.M
              * (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ)) := by rw [hsM2]
          _ = (2 * max (Ka Cf) (Kb Cf)) * (Pa.τ⁻¹ * Pa.M)
              * (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ)) := by ring
      linarith [h3, h4.le, h4.ge]
    linarith [h1, h2]
  rw [Amax]
  have hsum : Ka Cf * Real.sqrt Pa.M * Pa.θ ^ 2 * Real.log Pa.N + Kb Cf * Real.log Pa.N / Real.sqrt Pa.M
      ≤ (2 * max (Ka Cf) (Kb Cf)) * Pa.θ * Real.sqrt Pa.M * (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ))
        + (2 * max (Ka Cf) (Kb Cf)) * Pa.τ⁻¹ * Real.sqrt Pa.M
          * (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ)) := add_le_add hterm1 hterm2
  refine le_trans hsum ?_
  have h : (2 * max (Ka Cf) (Kb Cf)) * Pa.θ * Real.sqrt Pa.M * (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ))
      + (2 * max (Ka Cf) (Kb Cf)) * Pa.τ⁻¹ * Real.sqrt Pa.M
        * (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ))
      = (2 * max (Ka Cf) (Kb Cf)) * (Pa.τ⁻¹ + Pa.θ) * Real.sqrt Pa.M
        * (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ)) := by ring_nf
  rw [h]

/-- **The (7.10) bracket at a pair of the polar box.**  Applying the input `FintProp` to the
nonnegative majorisation `majG` (and controlling the two differences against `majF` by the volume
bound `vol_regG_le` and the discrete mean value `Fhat_trace_sub_le`) bounds the replacement error
of `C₀` by the uniform `Amax`. -/
theorem bracket_le (Cf : ℝ) (hCf : 0 < Cf) (hFP : FintBound Cf)
    (Pa : Work.FITop.Params) (f : ℤ → ℝ) (hf : Work.FITop4.IsMajorant6 Pa f)
    (hx : 10000 ≤ (Pa.x : ℝ)) {φ : ℝ} {z1 z2 : GaussianInt}
    (hbox1 : Work.FITop3.InPolarBox Pa φ z1) (hbox2 : Work.FITop3.InPolarBox Pa φ z2)
    (hΔ : Work.FIPlan.absDelta z1 z2 ≠ 0) :
    |(Work.FIArea2.Fint (majF Pa f hf) (Work.FIArea2.gamOf z1 z2) 0 0).re
        - (Work.FITop3.Fhat Pa f) * Work.FITop4.logFac6 z1 z2| ≤ Amax Pa (Ka Cf) (Kb Cf) := by
  set γ := Work.FIArea2.gamOf z1 z2 with hγdef
  set fG : ℤ → ℝ := fun n => majG Pa f hf (n : ℝ) with hfGdef
  have hN10 : 10 ≤ Pa.N := ten_le_N Pa hx
  have hM1 : 1 ≤ Pa.M := Pa.hM1
  have hMpos : 0 < Pa.M := lt_of_lt_of_le zero_lt_one hM1
  have hN10r : (10 : ℝ) ≤ Pa.N := by exact_mod_cast hN10
  have hM8 : 8 ≤ Pa.M := by
    have h1 : (8 : ℝ) ≤ Pa.M := by linarith [hN10r, Pa.hNlo, Pa.hMge]
    exact_mod_cast h1
  have hlogN1 : 1 ≤ Real.log Pa.N := one_le_log_N Pa hx
  have hlogN0 : 0 ≤ Real.log Pa.N := le_trans zero_le_one hlogN1
  have hθ0 : 0 ≤ Pa.θ := le_of_lt Pa.hθ0
  have hθ1 : Pa.θ ≤ 1 := theta_le_one6 Pa
  have hγ0 : 1 / 2 ≤ γ := hγdef ▸ gamOf_ge_half_of_polarBox6 Pa φ z1 z2 hbox1 hbox2
  have hγ1 : γ < 1 := hγdef ▸ gamOf_lt_one_of_absDelta_ne hΔ
  have hγnn : 0 ≤ γ := by linarith
  have h1γnn : 0 ≤ 1 - γ ^ 2 := by nlinarith [hγ1, hγnn]
  obtain ⟨hb1, hb2, hb3, hb4⟩ := logFac6_bounds hbox1 hbox2 hΔ hN10 hθ1
  -- the (7.10) input applied to `majG`
  have hFPb := hFP Pa (Pa.M / 64) (64 * Pa.M) (Cder6 + 1) (majG Pa f hf) fG z1 z2
    le_rfl le_rfl (by linarith [one_le_Cder6]) hM1
    (majG_contDiff Pa f hf) (majG_hasCompactSupport Pa f hf) (fun n => rfl)
    (fun u hu => by
      have h1 : f u ≠ 0 := by
        intro h0
        refine hu ?_
        show majG Pa f hf (u : ℝ) = 0
        rw [majG_trace Pa f hf u, h0]
        have hδ : 0 < (Pa.M)⁻¹ := inv_pos.mpr hMpos
        rw [zero_pow (by norm_num : 2 ≠ 0), zero_add, Real.sqrt_sq_eq_abs, abs_of_pos hδ,
          sub_self]
      exact hf.2.2.2.2 u h1)
    (fun u => majG_nonneg Pa f hf u)
    (fun u => by
      have h := majG_abs_le Pa f hf u
      linarith)
    (fun u => majG_support_spec Pa f hf u)
    (fun u => by
      have h := majG_deriv_le Pa f hf u
      rw [div_eq_mul_inv]
      have h2 : (0 : ℝ) ≤ (Pa.M)⁻¹ := by positivity
      calc |deriv (majG Pa f hf) u| ≤ Cder6 * (Pa.M)⁻¹ := h
        _ ≤ (Cder6 + 1) * (Pa.M)⁻¹ := by linarith)
    hγ0 hγ1 hΔ
  -- the decomposition of the bracket
  set A : ℝ := (Work.FIArea2.Fint (majF Pa f hf) γ 0 0).re with hAdef
  set A' : ℝ := (Work.FIArea2.Fint (majG Pa f hf) γ 0 0).re with hA'def
  set B : ℝ := (Work.FITop3.Fhat Pa f) * Work.FITop4.logFac6 z1 z2 with hBdef
  set B' : ℝ := (Work.FITop3.Fhat Pa fG) * Work.FITop4.logFac6 z1 z2 with hB'def
  have hmain : |A - B| ≤ |A - A'| + |A' - B'| + |B' - B| := by
    have he : A - B = (A - A') + (A' - B') + (B' - B) := by ring
    calc |A - B| = |(A - A') + (A' - B') + (B' - B)| := by rw [he]
      _ ≤ |(A - A') + (A' - B')| + |B' - B| := abs_add_le _ _
      _ ≤ (|A - A'| + |A' - B'|) + |B' - B| := by
          have h := abs_add_le (A - A') (A' - B')
          linarith
  have e1 : |A' - B'| ≤ Cf * (Cder6 + 1)
      * (Real.sqrt Pa.M * (1 - γ ^ 2) * Real.log (2 + 1 / (1 - γ ^ 2))
        + (Real.sqrt Pa.M)⁻¹
          * Real.log (2 + 8 * Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ)))) := by
    have hB'eq : B' = (((Work.FITop3.Fhat Pa fG : ℝ) : ℂ)
        * ((Work.FITop4.logFac6 z1 z2 : ℝ) : ℂ)).re := by
      rw [hB'def]
      simp
    rw [hA'def, hB'eq, ← Complex.sub_re]
    exact le_trans (Complex.abs_re_le_norm _) hFPb
  have e2 : |A - A'| ≤ (Cder6 + 1) * (Pa.M)⁻¹
      * (2000 * Real.sqrt Pa.M * Real.log (2 + 1 / (1 - γ ^ 2))) := by
    have hre : A - A' = (Work.FIArea2.Fint (majF Pa f hf) γ 0 0
        - Work.FIArea2.Fint (majG Pa f hf) γ 0 0).re := by
      rw [hAdef, hA'def, ← Complex.sub_re]
    rw [hre]
    refine le_trans (Complex.abs_re_le_norm _) ?_
    refine Fint_sub_zero_zero_le Pa.M γ (Pa.M / 64) (64 * Pa.M) ((Cder6 + 1) * (Pa.M)⁻¹)
      Cder6 Cder6 hγnn hγ1 (by positivity) (by linarith) le_rfl hM1 (by
        have h1 := Cder6_pos
        have h2 : (0:ℝ) < (Pa.M)⁻¹ := inv_pos.mpr hMpos
        positivity)
      (majF Pa f hf) (majG Pa f hf) ((majF_contDiff Pa f hf).continuous)
      ((majG_contDiff Pa f hf).continuous) (majF_support_spec Pa f hf)
      (majG_support_spec Pa f hf) (fun u => majF_abs_le Pa f hf u)
      (fun u => majG_abs_le Pa f hf u) (fun u => by
        rw [abs_sub_comm]
        exact majG_close Pa f hf u)
  have e3 : |B' - B| ≤ (20 / Real.sqrt Pa.M) * |Work.FITop4.logFac6 z1 z2| := by
    have he : B' - B = (Work.FITop3.Fhat Pa fG - Work.FITop3.Fhat Pa f)
        * Work.FITop4.logFac6 z1 z2 := by
      rw [hB'def, hBdef]
      ring
    rw [he, abs_mul]
    exact mul_le_mul_of_nonneg_right (Fhat_trace_sub_le Pa f hf hM8) (abs_nonneg _)
  refine le_trans hmain ?_
  have hmid : |A - A'| + |A' - B'| + |B' - B|
      ≤ Cf * (Cder6 + 1)
          * (Real.sqrt Pa.M * (1 - γ ^ 2) * Real.log (2 + 1 / (1 - γ ^ 2))
            + (Real.sqrt Pa.M)⁻¹
              * Real.log (2 + 8 * Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ))))
        + (Cder6 + 1) * (Pa.M)⁻¹ * (2000 * Real.sqrt Pa.M * Real.log (2 + 1 / (1 - γ ^ 2)))
        + (20 / Real.sqrt Pa.M) * |Work.FITop4.logFac6 z1 z2| := by
    linarith [e1, e2, e3]
  refine le_trans hmid ?_
  -- the final arithmetic
  rw [Amax, Ka, Kb]
  have hL2 : 0 ≤ Real.log (2 + 1 / (1 - γ ^ 2)) := by
    refine Real.log_nonneg ?_
    have h1γ : 0 < 1 - γ ^ 2 := by nlinarith [hγ1, hγnn]
    have h : 0 < 1 / (1 - γ ^ 2) := one_div_pos.mpr h1γ
    linarith
  have hL3 : 0 ≤ Real.log (2 + 8 * Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ))) := by
    refine Real.log_nonneg ?_
    have := Real.sqrt_nonneg (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ))
    linarith
  have hsM : 0 < Real.sqrt Pa.M := Real.sqrt_pos.mpr hMpos
  have hsM0 : 0 ≤ Real.sqrt Pa.M := le_of_lt hsM
  have hsMi : (Pa.M)⁻¹ * Real.sqrt Pa.M = (Real.sqrt Pa.M)⁻¹ := by
    have hsq : Real.sqrt Pa.M * Real.sqrt Pa.M = Pa.M := by
      rw [← sq]
      exact Real.sq_sqrt hMpos.le
    have h1 : (Pa.M)⁻¹ = (Real.sqrt Pa.M)⁻¹ * (Real.sqrt Pa.M)⁻¹ := by
      rw [← mul_inv, hsq]
    rw [h1, mul_assoc, inv_mul_cancel₀ (ne_of_gt hsM), mul_one]
  have hsMinv0 : 0 ≤ (Real.sqrt Pa.M)⁻¹ := by positivity
  have hKa : 12 * Real.pi ^ 2 * (Cf * (Cder6 + 1)) ≤ 12 * Real.pi ^ 2 * (Cf + 1) * (Cder6 + 1) := by
    nlinarith [hCf, Cder6_pos, Real.pi_pos, sq_nonneg Real.pi]
  have hKb : 4 * (Cf * (Cder6 + 1)) + 6000 * (Cder6 + 1) + 80
      ≤ 4 * ((Cf + 1) * (Cder6 + 1)) + 6000 * (Cder6 + 1) + 288 := by
    nlinarith [hCf, Cder6_pos]
  have hfour : 0 ≤ 4 * (Cder6 + 1) := by linarith [Cder6_pos]
  have hCfC : 0 ≤ Cf * (Cder6 + 1) := by
    have : 0 < Cder6 + 1 := by linarith [Cder6_pos]
    positivity
  have hθ2 : 0 ≤ Pa.θ ^ 2 := sq_nonneg Pa.θ
  have hprod : 0 ≤ (1 - γ ^ 2) * Real.log (2 + 1 / (1 - γ ^ 2)) := mul_nonneg h1γnn hL2
  have hkey : Cf * (Cder6 + 1) * (Real.sqrt Pa.M * (1 - γ ^ 2)
        * Real.log (2 + 1 / (1 - γ ^ 2))
      + (Real.sqrt Pa.M)⁻¹ * Real.log (2 + 8 * Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ))))
      + (Cder6 + 1) * (Pa.M)⁻¹ * (2000 * Real.sqrt Pa.M * Real.log (2 + 1 / (1 - γ ^ 2)))
      + (20 / Real.sqrt Pa.M) * |Work.FITop4.logFac6 z1 z2|
      ≤ 12 * Real.pi ^ 2 * (Cf + 1) * (Cder6 + 1) * Real.sqrt Pa.M * Pa.θ ^ 2 * Real.log Pa.N
        + (4 * ((Cf + 1) * (Cder6 + 1)) + 6000 * (Cder6 + 1) + 288) * Real.log Pa.N
          / Real.sqrt Pa.M := by
    have h1 : Real.sqrt Pa.M * (1 - γ ^ 2) * Real.log (2 + 1 / (1 - γ ^ 2))
        ≤ Real.sqrt Pa.M * (4 * Real.pi ^ 2 * Pa.θ ^ 2) * (3 * Real.log Pa.N) := by
      refine mul_le_mul (mul_le_mul_of_nonneg_left hb1 hsM0) hb2 hL2 ?_
      positivity
    have h2 : (Real.sqrt Pa.M)⁻¹ * Real.log (2 + 8 * Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ)))
        ≤ (Real.sqrt Pa.M)⁻¹ * (4 * Real.log Pa.N) :=
      mul_le_mul_of_nonneg_left hb3 hsMinv0
    have h3 : (Pa.M)⁻¹ * (2000 * Real.sqrt Pa.M * Real.log (2 + 1 / (1 - γ ^ 2)))
        = 2000 * ((Real.sqrt Pa.M)⁻¹ * Real.log (2 + 1 / (1 - γ ^ 2))) := by
      rw [← hsMi]
      ring
    have h4 : (20 / Real.sqrt Pa.M) * |Work.FITop4.logFac6 z1 z2|
        ≤ 20 * ((Real.sqrt Pa.M)⁻¹ * (4 * Real.log Pa.N)) := by
      have hdiv : 20 / Real.sqrt Pa.M = 20 * (Real.sqrt Pa.M)⁻¹ := by rw [div_eq_mul_inv]
      rw [hdiv]
      have h5 : |Work.FITop4.logFac6 z1 z2| ≤ 4 * Real.log Pa.N := hb4
      have h6 : (0:ℝ) ≤ (Real.sqrt Pa.M)⁻¹ := by positivity
      calc 20 * (Real.sqrt Pa.M)⁻¹ * |Work.FITop4.logFac6 z1 z2|
          ≤ 20 * (Real.sqrt Pa.M)⁻¹ * (4 * Real.log Pa.N) := by
            exact mul_le_mul_of_nonneg_left h5 (by positivity)
        _ = 20 * ((Real.sqrt Pa.M)⁻¹ * (4 * Real.log Pa.N)) := by ring
    have b1 : Cf * (Cder6 + 1) * (Real.sqrt Pa.M * (1 - γ ^ 2) * Real.log (2 + 1 / (1 - γ ^ 2))
          + (Real.sqrt Pa.M)⁻¹ * Real.log (2 + 8 * Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ))))
        ≤ Cf * (Cder6 + 1) * (Real.sqrt Pa.M * (4 * Real.pi ^ 2 * Pa.θ ^ 2) * (3 * Real.log Pa.N)
          + (Real.sqrt Pa.M)⁻¹ * (4 * Real.log Pa.N)) := by
      refine mul_le_mul_of_nonneg_left (add_le_add h1 h2) hCfC
    have b2 : (Cder6 + 1) * (Pa.M)⁻¹ * (2000 * Real.sqrt Pa.M * Real.log (2 + 1 / (1 - γ ^ 2)))
        ≤ (Cder6 + 1) * (2000 * ((Real.sqrt Pa.M)⁻¹ * (3 * Real.log Pa.N))) := by
      have hC : (0 : ℝ) ≤ Cder6 + 1 := by linarith [Cder6_pos]
      rw [mul_assoc (Cder6 + 1) (Pa.M)⁻¹, h3]
      refine mul_le_mul_of_nonneg_left ?_ hC
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb2 hsMinv0) (by norm_num)
    have b3 : (20 / Real.sqrt Pa.M) * |Work.FITop4.logFac6 z1 z2|
        ≤ 80 * ((Real.sqrt Pa.M)⁻¹ * Real.log Pa.N) := by
      have := h4
      calc (20 / Real.sqrt Pa.M) * |Work.FITop4.logFac6 z1 z2|
          ≤ 20 * ((Real.sqrt Pa.M)⁻¹ * (4 * Real.log Pa.N)) := this
        _ = 80 * ((Real.sqrt Pa.M)⁻¹ * Real.log Pa.N) := by ring
    have hsum := add_le_add (add_le_add b1 b2) b3
    refine le_trans hsum ?_
    have expand : Cf * (Cder6 + 1) * (Real.sqrt Pa.M * (4 * Real.pi ^ 2 * Pa.θ ^ 2) * (3 * Real.log Pa.N)
          + (Real.sqrt Pa.M)⁻¹ * (4 * Real.log Pa.N))
        + (Cder6 + 1) * (2000 * ((Real.sqrt Pa.M)⁻¹ * (3 * Real.log Pa.N)))
        + 80 * ((Real.sqrt Pa.M)⁻¹ * Real.log Pa.N)
        = (12 * Real.pi ^ 2 * (Cf * (Cder6 + 1))) * Real.sqrt Pa.M * Pa.θ ^ 2 * Real.log Pa.N
          + (4 * (Cf * (Cder6 + 1)) + 6000 * (Cder6 + 1) + 80)
            * ((Real.sqrt Pa.M)⁻¹ * Real.log Pa.N) := by
      ring
    rw [expand]
    rw [div_eq_mul_inv]
    have hA : (12 * Real.pi ^ 2 * (Cf * (Cder6 + 1))) * Real.sqrt Pa.M * Pa.θ ^ 2 * Real.log Pa.N
        ≤ 12 * Real.pi ^ 2 * (Cf + 1) * (Cder6 + 1) * Real.sqrt Pa.M * Pa.θ ^ 2 * Real.log Pa.N := by
      have h0 : (0:ℝ) ≤ Real.sqrt Pa.M * Pa.θ ^ 2 * Real.log Pa.N := by positivity
      nlinarith [hKa, h0, hsM0, hθ2, hlogN0]
    have hB : (4 * (Cf * (Cder6 + 1)) + 6000 * (Cder6 + 1) + 80)
          * ((Real.sqrt Pa.M)⁻¹ * Real.log Pa.N)
        ≤ (4 * ((Cf + 1) * (Cder6 + 1)) + 6000 * (Cder6 + 1) + 288)
          * ((Real.sqrt Pa.M)⁻¹ * Real.log Pa.N) := by
      have h0 : (0:ℝ) ≤ (Real.sqrt Pa.M)⁻¹ * Real.log Pa.N := mul_nonneg hsMinv0 hlogN0
      exact mul_le_mul_of_nonneg_right hKb h0
    linarith [hA, hB]
  exact hkey

/-! ## 7. The assembly -/

theorem area2_6e_B (hY : Work.FIArea2.R6.YProp) (hF : Work.FIArea2.R6.FintProp) :
    ∃ C3 x0 : ℝ, 0 < C3 ∧ 0 < x0 ∧
      ∀ (Pa : Work.FITop.Params), x0 ≤ (Pa.x : ℝ) →
      ∀ (f : ℤ → ℝ) (hf : Work.FITop4.IsMajorant6 Pa f) (φ : ℝ) (z0 : GaussianInt)
        (β : GaussianInt → ℂ),
        Work.FITop4.IsBetaCoeff6 Pa φ z0 β →
        ‖((Work.FIArea2.R6.D0ex (Work.FITop.radN Pa) (Work.FIArea2.R6.majF Pa f hf) β : ℝ) : ℂ)
            - Work.FITop4.D0 (Work.FITop.radN Pa) (Work.FITop3.Fhat Pa f) β‖
          ≤ C3 * (Pa.τ⁻¹ + Pa.θ) * Pa.θ ^ (4 : ℕ) * Pa.M ^ ((1 : ℝ) / 2)
              * Pa.N ^ ((3 : ℝ) / 2) * (Real.log Pa.N) ^ ((2 : ℕ) ^ (20 : ℕ)) := by
  obtain ⟨Cf, hCfpos, hFP⟩ := hF
  obtain ⟨Cy, hCypos, hYb⟩ := hY
  have hKa_pos : (0 : ℝ) < Ka Cf := by
    rw [Ka]
    have h1 := Cder6_pos
    have h2 := Real.pi_pos
    positivity
  have hKb_nn : (0 : ℝ) ≤ Kb Cf := Kb_nonneg Cf hCfpos
  refine ⟨4 * Cy * (2 * max (Ka Cf) (Kb Cf)), 10000, ?_, by norm_num, ?_⟩
  · have h2 : (0 : ℝ) < max (Ka Cf) (Kb Cf) := lt_of_lt_of_le hKa_pos (le_max_left _ _)
    positivity
  · intro Pa hx f hf φ z0 β hβ
    have hN1 : (1 : ℝ) ≤ Pa.N := by exact_mod_cast Pa.hN1
    have hMpos : (0 : ℝ) < Pa.M := lt_of_lt_of_le zero_lt_one Pa.hM1
    have hlogN0 : 0 ≤ Real.log Pa.N := le_trans zero_le_one (one_le_log_N Pa hx)
    have hθ0 : 0 ≤ Pa.θ := le_of_lt Pa.hθ0
    have hA0 : 0 ≤ Amax Pa (Ka Cf) (Kb Cf) := by
      rw [Amax]
      have h5 : (0 : ℝ) ≤ Real.log Pa.N / Real.sqrt Pa.M :=
        div_nonneg hlogN0 (Real.sqrt_nonneg _)
      have h6 : (0 : ℝ) ≤ Pa.θ ^ 2 := sq_nonneg _
      have h7 : (0 : ℝ) ≤ Real.sqrt Pa.M := Real.sqrt_nonneg _
      positivity
    have hpair : ∀ z1 z2 : GaussianInt,
        (if Work.FIPlan.GaussCoprime z1 z2 then
          ‖β z1‖ * ‖β z2‖
            * |C0ex (majF Pa f hf) z1 z2 - Work.FITop4.C0 (Work.FITop3.Fhat Pa f) z1 z2|
        else 0)
        ≤ (if Work.FIPlan.GaussCoprime z1 z2 then
            ‖β z1‖ * ‖β z2‖ * (4 * ((Work.FIArea2.R6.tau3 (Work.FIPlan.absDelta z1 z2) : ℕ) : ℝ)
              * Pa.N ^ (-(1 : ℝ) / 2) * Amax Pa (Ka Cf) (Kb Cf))
          else 0) := by
      intro z1 z2
      by_cases hcop : Work.FIPlan.GaussCoprime z1 z2
      · rw [if_pos hcop, if_pos hcop]
        by_cases h1 : β z1 = 0
        · rw [h1, norm_zero]
          simp
        by_cases h2 : β z2 = 0
        · rw [h2, norm_zero]
          simp
        have hbox1 := Work.FITop4.IsBetaCoeff6.support hβ h1
        have hbox2 := Work.FITop4.IsBetaCoeff6.support hβ h2
        have hodd1 := InPolarBox.odd_gnorm6 hbox1
        have hprim1 := Work.FIArea2.isCoprime_star_of_squarefree_odd_gnorm
          (Work.FITop4.IsBetaCoeff6.squarefree_gnorm hβ h1) hodd1
        have hprim2 := Work.FIArea2.isCoprime_star_of_squarefree_odd_gnorm
          (Work.FITop4.IsBetaCoeff6.squarefree_gnorm hβ h2) (InPolarBox.odd_gnorm6 hbox2)
        have hn1 : 2 ≤ Work.FIPlan.gnorm z1 := by
          have hgt : (1 : ℝ) < (Work.FIPlan.gnorm z1 : ℝ) :=
            lt_of_le_of_lt (by exact_mod_cast Pa.hN1) (InPolarBox.norm_bounds6 hbox1).1
          have hgt' : (1 : ℕ) < Work.FIPlan.gnorm z1 := by exact_mod_cast hgt
          omega
        have hDelta : Work.FIPlan.Delta z1 z2 ≠ 0 :=
          delta_ne_zero_of_coprime hcop hprim1 hprim2 hn1
        have hD : Work.FIPlan.absDelta z1 z2 ≠ 0 := by
          simpa [Work.FIPlan.absDelta] using Int.natAbs_ne_zero.mpr hDelta
        have hbr := bracket_le Cf hCfpos hFP Pa f hf hx hbox1 hbox2 hD
        have halg := C0ex_sub_C0_eq Pa f hf z1 z2
        have hN2gn : Pa.N ^ (2 : ℕ) ≤ ((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ) := by
          rw [Work.FIArea4.gnorm_mul]
          push_cast
          have h3 := (InPolarBox.norm_bounds6 hbox1).1
          have h4 := (InPolarBox.norm_bounds6 hbox2).1
          nlinarith [h3, h4, hN1]
        have hgn_ub : (((Work.FIPlan.gnorm (z1 * z2) : ℕ)) : ℝ) ^ (-(1 : ℝ) / 4)
            ≤ Pa.N ^ (-(1 : ℝ) / 2) := by
          have hposN : (0 : ℝ) < Pa.N := lt_of_lt_of_le zero_lt_one hN1
          have h1 : (((Work.FIPlan.gnorm (z1 * z2) : ℕ)) : ℝ) ^ (-(1 : ℝ) / 4)
              ≤ (Pa.N ^ (2 : ℕ)) ^ (-(1 : ℝ) / 4) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) hN2gn (by norm_num)
          have h2 : (Pa.N ^ (2 : ℕ)) ^ (-(1 : ℝ) / 4) = Pa.N ^ (-(1 : ℝ) / 2) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hposN)]
            norm_num
          rwa [h2] at h1
        have hG0 := G0_abs_le6 hβ h1 h2 hcop
        have htau : 2 * (1 + ((Work.FIPlan.absDelta z1 z2).divisors.card : ℝ))
            ≤ 4 * ((Work.FIArea2.R6.tau3 (Work.FIPlan.absDelta z1 z2) : ℕ) : ℝ) := by
          have h := Work.FIArea3.one_add_tau_le_two_tau3 (Work.FIPlan.absDelta z1 z2)
          have h' : (1 + (Work.FIPlan.absDelta z1 z2).divisors.card : ℕ)
              ≤ 2 * Work.FIArea2.R6.tau3 (Work.FIPlan.absDelta z1 z2) := h
          have h'' : ((1 + (Work.FIPlan.absDelta z1 z2).divisors.card : ℕ) : ℝ)
              ≤ ((2 * Work.FIArea2.R6.tau3 (Work.FIPlan.absDelta z1 z2) : ℕ) : ℝ) := by
            exact_mod_cast h'
          push_cast at h''
          linarith [h'']
        have hdiff : |C0ex (majF Pa f hf) z1 z2 - Work.FITop4.C0 (Work.FITop3.Fhat Pa f) z1 z2|
            ≤ 4 * ((Work.FIArea2.R6.tau3 (Work.FIPlan.absDelta z1 z2) : ℕ) : ℝ)
              * Pa.N ^ (-(1 : ℝ) / 2) * Amax Pa (Ka Cf) (Kb Cf) := by
          rw [halg, abs_mul, abs_mul]
          have h1' : |((((Work.FIPlan.gnorm (z1 * z2) : ℕ)) : ℝ) ^ (-(1 : ℝ) / 4))|
              ≤ Pa.N ^ (-(1 : ℝ) / 2) := by
            rw [abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
            exact hgn_ub
          have h2' : |Work.FITop4.G0 z1 z2|
              ≤ 4 * ((Work.FIArea2.R6.tau3 (Work.FIPlan.absDelta z1 z2) : ℕ) : ℝ) := by
            linarith [hG0, htau]
          have h4' : (0 : ℝ) ≤ Pa.N ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg (by linarith) _
          have h5' : (0 : ℝ) ≤ 4 * ((Work.FIArea2.R6.tau3 (Work.FIPlan.absDelta z1 z2) : ℕ) : ℝ) :=
            by positivity
          have h6' : (0 : ℝ) ≤ Amax Pa (Ka Cf) (Kb Cf) := hA0
          calc |((((Work.FIPlan.gnorm (z1 * z2) : ℕ)) : ℝ) ^ (-(1 : ℝ) / 4))|
                * |Work.FITop4.G0 z1 z2|
                * |(Work.FIArea2.Fint (majF Pa f hf) (Work.FIArea2.gamOf z1 z2) 0 0).re
                    - (Work.FITop3.Fhat Pa f) * Work.FITop4.logFac6 z1 z2|
              ≤ Pa.N ^ (-(1 : ℝ) / 2)
                * (4 * ((Work.FIArea2.R6.tau3 (Work.FIPlan.absDelta z1 z2) : ℕ) : ℝ))
                * Amax Pa (Ka Cf) (Kb Cf) := by
                refine mul_le_mul (mul_le_mul h1' h2' (abs_nonneg _) h4') hbr (abs_nonneg _) ?_
                positivity
            _ = 4 * ((Work.FIArea2.R6.tau3 (Work.FIPlan.absDelta z1 z2) : ℕ) : ℝ)
                * Pa.N ^ (-(1 : ℝ) / 2) * Amax Pa (Ka Cf) (Kb Cf) := by ring
        have hβnn : (0 : ℝ) ≤ ‖β z1‖ * ‖β z2‖ := by positivity
        calc ‖β z1‖ * ‖β z2‖
              * |C0ex (majF Pa f hf) z1 z2 - Work.FITop4.C0 (Work.FITop3.Fhat Pa f) z1 z2|
            ≤ ‖β z1‖ * ‖β z2‖ * (4 * ((Work.FIArea2.R6.tau3 (Work.FIPlan.absDelta z1 z2) : ℕ) : ℝ)
                * Pa.N ^ (-(1 : ℝ) / 2) * Amax Pa (Ka Cf) (Kb Cf)) :=
              mul_le_mul_of_nonneg_left hdiff hβnn
          _ = ‖β z1‖ * ‖β z2‖ * (4 * ((Work.FIArea2.R6.tau3 (Work.FIPlan.absDelta z1 z2) : ℕ) : ℝ)
                * Pa.N ^ (-(1 : ℝ) / 2) * Amax Pa (Ka Cf) (Kb Cf)) := by ring
      · rw [if_neg hcop, if_neg hcop]
    refine le_trans (norm_D0ex_sub_D0_le Pa f hf β) ?_
    refine le_trans (Finset.sum_le_sum fun z1 _ => Finset.sum_le_sum fun z2 _ => hpair z1 z2) ?_
    have hsum1 : (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
          (if Work.FIPlan.GaussCoprime z1 z2 then
            ‖β z1‖ * ‖β z2‖ * (4 * ((Work.FIArea2.R6.tau3 (Work.FIPlan.absDelta z1 z2) : ℕ) : ℝ)
              * Pa.N ^ (-(1 : ℝ) / 2) * Amax Pa (Ka Cf) (Kb Cf))
          else 0))
        = (∑ z1 ∈ Work.FITop.boxN Pa,
            (4 * Pa.N ^ (-(1 : ℝ) / 2) * Amax Pa (Ka Cf) (Kb Cf))
              * (∑ z2 ∈ Work.FITop.boxN Pa,
                  Work.FIArea2.R6.copInd z1 z2
                    * (‖β z1‖ * ‖β z2‖
                      * ((Work.FIArea2.R6.tau3 (Work.FIPlan.absDelta z1 z2) : ℕ) : ℝ)))) := by
      refine Finset.sum_congr rfl fun z1 _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun z2 _ => ?_
      rw [Work.FIArea2.R6.copInd]
      by_cases hc : Work.FIPlan.GaussCoprime z1 z2
      · rw [if_pos hc, if_pos hc]
        ring
      · rw [if_neg hc, if_neg hc]
        ring
    rw [hsum1, ← Finset.mul_sum]
    have hY' := hYb Pa φ z0 β hβ
    have hfac : (0 : ℝ) ≤ 4 * Pa.N ^ (-(1 : ℝ) / 2) * Amax Pa (Ka Cf) (Kb Cf) := by
      have h1 : (0 : ℝ) ≤ Pa.N ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg (by linarith) _
      positivity
    refine le_trans (mul_le_mul_of_nonneg_left hY' hfac) ?_
    have hAml := Amax_le_target Pa hCfpos hx
    calc 4 * Pa.N ^ (-(1 : ℝ) / 2) * Amax Pa (Ka Cf) (Kb Cf)
          * (Cy * Pa.θ ^ (4 : ℕ) * Pa.N ^ (2 : ℕ) * (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ)))
        ≤ 4 * Pa.N ^ (-(1 : ℝ) / 2)
          * ((2 * max (Ka Cf) (Kb Cf)) * (Pa.τ⁻¹ + Pa.θ) * Real.sqrt Pa.M
              * (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ)))
          * (Cy * Pa.θ ^ (4 : ℕ) * Pa.N ^ (2 : ℕ) * (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ))) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left hAml (by positivity)
      _ = (4 * Cy * (2 * max (Ka Cf) (Kb Cf))) * (Pa.τ⁻¹ + Pa.θ) * Pa.θ ^ (4 : ℕ)
            * Pa.M ^ ((1 : ℝ) / 2) * Pa.N ^ ((3 : ℝ) / 2)
            * (Real.log Pa.N) ^ ((2 : ℕ) ^ (20 : ℕ)) := by
          rw [Real.sqrt_eq_rpow]
          have hN : Pa.N ^ (-(1 : ℝ) / 2) * Pa.N ^ (2 : ℕ) = Pa.N ^ ((3 : ℝ) / 2) := by
            rw [← Real.rpow_natCast, ← Real.rpow_add (by linarith : (0 : ℝ) < Pa.N)]
            norm_num
          have hL : (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ))
              * (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ))
              = (Real.log Pa.N) ^ ((2 : ℕ) ^ (20 : ℕ)) := by
            rw [← pow_add]
            norm_num
          rw [show 4 * Pa.N ^ (-(1 : ℝ) / 2)
                * ((2 * max (Ka Cf) (Kb Cf)) * (Pa.τ⁻¹ + Pa.θ) * Pa.M ^ ((1 : ℝ) / 2)
                    * (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ)))
                * (Cy * Pa.θ ^ (4 : ℕ) * Pa.N ^ (2 : ℕ)
                    * (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ)))
              = 4 * Cy * (2 * max (Ka Cf) (Kb Cf)) * (Pa.τ⁻¹ + Pa.θ) * Pa.θ ^ (4 : ℕ)
                * Pa.M ^ ((1 : ℝ) / 2) * (Pa.N ^ (-(1 : ℝ) / 2) * Pa.N ^ (2 : ℕ))
                * ((Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ))
                    * (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ))) from by ring]
          rw [hN, hL]


end

end Work.FIArea2.R6

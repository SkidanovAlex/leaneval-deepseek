import Mathlib
import Submission.Work.FIArea7.quadruple_le
import Submission.Work.FITop4.Areas6
import Submission.Work.FIArea7.UniChain6
import Submission.Work.FIArea7.fibre_sum_regroup
import Submission.Work.FIArea7CF.card_gBox_absDelta_eq_le
import Submission.Work.FIArea7CF.card_gBox_filter_dvd_absDelta
import Submission.Work.FIArea7.isCoprime_coords_of_squarefree_gnorm
import Submission.Work.FIArea7.pairW_bilinear_le
import Submission.Work.FIArea7.sum_inv_sq_Icc_le_two
import Submission.Work.FIArea7.divisor_sum_Icc_le

namespace Work.FIArea7

open Finset
open scoped BigOperators

noncomputable section

private lemma radN_nonneg (Pa : Work.FITop.Params) : (0 : ℤ) ≤ Work.FITop.radN Pa := by
  rw [Work.FITop.radN]
  exact Int.natCast_nonneg _

private lemma absDelta_comm (z1 z2 : GaussianInt) :
    Work.FIPlan.absDelta z1 z2 = Work.FIPlan.absDelta z2 z1 := by
  rw [Work.FIPlan.absDelta, Work.FIPlan.absDelta, Work.FIPlan.Delta, Work.FIPlan.Delta,
    Zsqrtd.im_mul, Zsqrtd.im_mul, Zsqrtd.re_star, Zsqrtd.im_star, Zsqrtd.re_star,
    Zsqrtd.im_star]
  have h : z1.re * z2.im + -z1.im * z2.re = -(z2.re * z1.im + -z2.im * z1.re) := by ring
  rw [h, Int.natAbs_neg]

private lemma pairW_nonneg (B0 X d : ℕ) : 0 ≤ Work.FIArea7.pairW B0 X d := by
  unfold Work.FIArea7.pairW
  refine Finset.sum_nonneg fun b _ => Finset.sum_nonneg fun e _ => ?_
  by_cases h : 4 * b * e ∣ d
  · rw [if_pos h, mul_one]
    positivity
  · rw [if_neg h]
    positivity

/-- `|Δ(z₁,z₂)| ≤ 2R·max(|Re z₁|,|Im z₁|)` when `z₂` lies in the box `gBox R`. -/
private lemma absDelta_le_gRad_local {R : ℤ} (hR : 0 ≤ R) {z1 z2 : GaussianInt}
    (hz2 : z2 ∈ Work.FIPlan.gBox R) :
    (Work.FIPlan.absDelta z1 z2 : ℝ) ≤ 2 * (R : ℝ) * ((max z1.re.natAbs z1.im.natAbs : ℕ) : ℝ) := by
  have m2 := Work.FIArea7.cf_mem_gBox_iff.mp hz2
  have hR0 : (0 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  have e3 : |(z2.re : ℝ)| ≤ (R : ℝ) := by
    rw [abs_le]
    exact ⟨by exact_mod_cast m2.1, by exact_mod_cast m2.2.1⟩
  have e4 : |(z2.im : ℝ)| ≤ (R : ℝ) := by
    rw [abs_le]
    exact ⟨by exact_mod_cast m2.2.2.1, by exact_mod_cast m2.2.2.2⟩
  have e1 : |(z1.re : ℝ)| ≤ ((max z1.re.natAbs z1.im.natAbs : ℕ) : ℝ) := by
    rw [← Int.cast_abs, ← Nat.cast_natAbs (α := ℝ) z1.re]
    exact_mod_cast Nat.le_max_left _ _
  have e2 : |(z1.im : ℝ)| ≤ ((max z1.re.natAbs z1.im.natAbs : ℕ) : ℝ) := by
    rw [← Int.cast_abs, ← Nat.cast_natAbs (α := ℝ) z1.im]
    exact_mod_cast Nat.le_max_right _ _
  have hMnn : (0 : ℝ) ≤ ((max z1.re.natAbs z1.im.natAbs : ℕ) : ℝ) := by positivity
  have hreal : ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
      = |((Work.FIPlan.Delta z1 z2 : ℤ) : ℝ)| := by
    rw [Work.FIPlan.absDelta]
    rw [Nat.cast_natAbs (α := ℝ), Int.cast_abs]
  rw [hreal]
  have hcast : (((Work.FIPlan.Delta z1 z2 : ℤ)) : ℝ)
      = (z1.re : ℝ) * (z2.im : ℝ) - (z1.im : ℝ) * (z2.re : ℝ) := by
    rw [Work.FIArea7.Delta_eq]; push_cast; ring
  rw [hcast]
  calc |(z1.re : ℝ) * (z2.im : ℝ) - (z1.im : ℝ) * (z2.re : ℝ)|
      ≤ |(z1.re : ℝ) * (z2.im : ℝ)| + |(z1.im : ℝ) * (z2.re : ℝ)| := abs_sub _ _
    _ = |(z1.re : ℝ)| * |(z2.im : ℝ)| + |(z1.im : ℝ)| * |(z2.re : ℝ)| := by
        rw [abs_mul, abs_mul]
    _ ≤ ((max z1.re.natAbs z1.im.natAbs : ℕ) : ℝ) * (R : ℝ)
          + ((max z1.re.natAbs z1.im.natAbs : ℕ) : ℝ) * (R : ℝ) :=
        add_le_add (mul_le_mul e1 e4 (abs_nonneg _) hMnn)
          (mul_le_mul e2 e3 (abs_nonneg _) hMnn)
    _ = 2 * (R : ℝ) * ((max z1.re.natAbs z1.im.natAbs : ℕ) : ℝ) := by ring

/-- `θ = (log x)^{-A'} ≤ 1` for the round-6 smoothing parameter. -/
private lemma theta_le_one_local (Pa : Work.FITop.Params) : Pa.θ ≤ 1 := by
  have hx3 : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
  have hxpos : (0 : ℝ) < (Pa.x : ℝ) := by linarith
  have hlog1 : (1 : ℝ) ≤ Real.log (Pa.x : ℝ) :=
    le_of_lt ((Real.lt_log_iff_exp_lt hxpos).mpr (lt_of_lt_of_le Real.exp_one_lt_three hx3))
  have hA' : (0 : ℝ) ≤ Pa.A' := by linarith [Pa.hA, Pa.hA']
  rw [Pa.hθ]
  exact Real.rpow_le_one_of_one_le_of_nonpos hlog1 (by linarith)

/-- `gnorm z = |Re z|² + |Im z|²`. -/
private lemma gnorm_eq_natAbs_sq_add_local (z : GaussianInt) :
    Work.FIPlan.gnorm z = z.re.natAbs ^ 2 + z.im.natAbs ^ 2 := by
  unfold Work.FIPlan.gnorm
  rw [show z.norm = z.re ^ 2 + z.im ^ 2 by rw [Zsqrtd.norm_def]; ring,
    Int.natAbs_add_of_nonneg (by positivity) (by positivity),
    Int.natAbs_pow, Int.natAbs_pow]

/-- A support point of a round-6 coefficient has Chebyshev radius at most `radN Pa`. -/
private lemma gRadius_le_radN {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ} (hβ : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) {z : GaussianInt}
    (hz : β z ≠ 0) :
    ((max z.re.natAbs z.im.natAbs : ℕ) : ℝ) ≤ (Work.FITop.radN Pa : ℝ) := by
  have hsup := hβ.support hz
  have hgn : (Work.FIPlan.gnorm z : ℝ) ≤ (1 + Pa.θ) * Pa.N := hsup.2.2.1
  have hθ : Pa.θ ≤ 1 := theta_le_one_local Pa
  have hN1 : (1 : ℝ) ≤ Pa.N := Pa.hN1
  have hgn' : (Work.FIPlan.gnorm z : ℝ) ≤ 2 * Pa.N := by nlinarith [hgn, hθ, hN1]
  have hmax : ((max z.re.natAbs z.im.natAbs : ℕ) : ℝ) ^ 2 ≤ (Work.FIPlan.gnorm z : ℝ) := by
    have hgn2 : (Work.FIPlan.gnorm z : ℝ)
        = (z.re.natAbs : ℝ) ^ 2 + (z.im.natAbs : ℝ) ^ 2 := by
      rw [gnorm_eq_natAbs_sq_add_local]; push_cast; ring
    rw [hgn2]
    simp only [Nat.cast_max]
    rcases le_total (z.re.natAbs : ℝ) (z.im.natAbs : ℝ) with h | h
    · rw [max_eq_right h]
      nlinarith [sq_nonneg ((z.re.natAbs : ℝ))]
    · rw [max_eq_left h]
      nlinarith [sq_nonneg ((z.im.natAbs : ℝ))]
  have hmaxnn : (0 : ℝ) ≤ ((max z.re.natAbs z.im.natAbs : ℕ) : ℝ) := by positivity
  have hle : ((max z.re.natAbs z.im.natAbs : ℕ) : ℝ) ≤ Real.sqrt (2 * Pa.N) := by
    rw [← Real.sqrt_sq hmaxnn]
    exact Real.sqrt_le_sqrt (le_trans hmax hgn')
  have h4 : Real.sqrt (2 * Pa.N) ≤ (Work.FITop.radN Pa : ℝ) := by
    refine le_trans (Real.sqrt_le_sqrt (by linarith : 2 * Pa.N ≤ 4 * Pa.N)) ?_
    rw [Work.FITop.radN]
    push_cast
    exact Nat.le_ceil _
  linarith

/-- `|Δ(z₁,z₂)| ≤ K` for a support point `z₁` and a box point `z₂`, with `K ≥ 2·radN²`. -/
private lemma absDelta_le_K_of_beta {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ} (hβ : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) {K : ℕ}
    (hK : 2 * (Work.FITop.radN Pa : ℝ) ^ 2 ≤ (K : ℝ)) {z1 z2 : GaussianInt}
    (hz1 : β z1 ≠ 0) (hz2 : z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa)) :
    Work.FIPlan.absDelta z1 z2 ≤ K := by
  have hR := radN_nonneg Pa
  have hR0 : (0 : ℝ) ≤ (Work.FITop.radN Pa : ℝ) := by exact_mod_cast hR
  have hb := absDelta_le_gRad_local hR hz2 (z1 := z1)
  have hgr := gRadius_le_radN hβ hz1
  have hstep : 2 * (Work.FITop.radN Pa : ℝ) * ((max z1.re.natAbs z1.im.natAbs : ℕ) : ℝ)
      ≤ 2 * (Work.FITop.radN Pa : ℝ) ^ 2 := by
    nlinarith [hgr, hR0]
  exact_mod_cast (le_trans hb (le_trans hstep hK))

/-- **Level count.**  For a support point `z₁` of a round-6 coefficient and any `d`, the number
of `z₂` in the box `gBox (radN Pa)` with `|Δ(z₁,z₂)| = d` is at most `20`: the general bound
`2(2·radN/q + 1)` of `card_gBox_absDelta_eq_le` has `q ≥ √(N/2)` and `radN < 2√N+1`, which
gives `2(2·radN/q + 1) < 2(2·9/4 + 1) = 13`. -/
private lemma level_card_le {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ} (hβ : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) {z1 : GaussianInt}
    (hz1 : β z1 ≠ 0) (d : ℕ) :
    (((Work.FIPlan.gBox (Work.FITop.radN Pa)).filter
        (fun z2 => Work.FIPlan.absDelta z1 z2 = d)).card : ℝ) ≤ 20 := by
  have hsup := hβ.support hz1
  have hsq := hβ.squarefree_gnorm hz1
  have hcop := Work.FIArea7.isCoprime_coords_of_squarefree_gnorm hsq
  have hgn : Pa.N < (Work.FIPlan.gnorm z1 : ℝ) := hsup.2.1
  have hN1 : (1 : ℝ) ≤ Pa.N := Pa.hN1
  have hN0 : (0 : ℝ) ≤ Pa.N := by linarith
  have hz1ne : z1 ≠ 0 := by
    intro h0
    rw [h0] at hgn
    have h0' : Work.FIPlan.gnorm (0 : GaussianInt) = 0 :=
      Work.FIArea7.gnorm_eq_zero_iff.mpr rfl
    rw [h0'] at hgn
    exact absurd (hN1.trans (le_of_lt hgn)) (by norm_num)
  have hcard := Work.FIArea7.card_gBox_absDelta_eq_le (Work.FITop.radN Pa) (radN_nonneg Pa)
    z1 d hz1ne hcop
  set q : ℝ := max ((z1.re.natAbs : ℕ) : ℝ) ((z1.im.natAbs : ℕ) : ℝ) with hq
  set Rad : ℝ := (Work.FITop.radN Pa : ℝ) with hRad
  have hgn2 : (Work.FIPlan.gnorm z1 : ℝ)
      = (z1.re.natAbs : ℝ) ^ 2 + (z1.im.natAbs : ℝ) ^ 2 := by
    rw [gnorm_eq_natAbs_sq_add_local]; push_cast; ring
  have hq2 : (Work.FIPlan.gnorm z1 : ℝ) ≤ 2 * q ^ 2 := by
    rw [hgn2, hq]
    rcases le_total ((z1.re.natAbs : ℕ) : ℝ) ((z1.im.natAbs : ℕ) : ℝ) with h | h
    · rw [max_eq_right h]
      nlinarith [sq_nonneg ((z1.re.natAbs : ℝ))]
    · rw [max_eq_left h]
      nlinarith [sq_nonneg ((z1.im.natAbs : ℝ))]
  have hq_sq : Pa.N < 2 * q ^ 2 := by linarith [hq2, hgn]
  have hqnn : 0 ≤ q := by rw [hq]; positivity
  have hqpos : 0 < q := by nlinarith [hq_sq, hN1, hqnn]
  have hRadnn : 0 ≤ Rad := by rw [hRad]; exact_mod_cast radN_nonneg Pa
  have hsqrt4 : Real.sqrt (4 * Pa.N) = 2 * Real.sqrt Pa.N := by
    have h4 : Real.sqrt (4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4) Pa.N, h4]
  have hRad_lt : Rad < 2 * Real.sqrt Pa.N + 1 := by
    have hRad_eq : Rad = ((Nat.ceil (Real.sqrt (4 * Pa.N)) : ℕ) : ℝ) := by
      rw [hRad, Work.FITop.radN]
      push_cast
      rfl
    rw [hRad_eq]
    have h := Nat.ceil_lt_add_one (Real.sqrt_nonneg (4 * Pa.N))
    have h2 : Real.sqrt (4 * Pa.N) + 1 = 2 * Real.sqrt Pa.N + 1 := by rw [hsqrt4]
    linarith [h, h2]
  have h1 : Rad < 3 * Real.sqrt Pa.N := by
    nlinarith [hRad_lt, Real.sqrt_nonneg Pa.N, Real.sq_sqrt hN0, hN1]
  have h2 : 3 * Real.sqrt Pa.N ≤ 4.5 * q := by
    have h3 : Real.sqrt Pa.N ≤ 1.5 * q := by
      nlinarith [hq_sq, Real.sq_sqrt hN0, Real.sqrt_nonneg Pa.N, hqnn]
    linarith
  have hkey : 4 * Rad ≤ 18 * q := by linarith [h1, h2]
  have h20 : 2 * (2 * Rad / q + 1) ≤ 20 := by
    have h1' : 2 * Rad / q ≤ 9 := by
      rw [div_le_iff₀ hqpos]
      nlinarith [hkey]
    linarith
  refine le_trans hcard ?_
  exact h20

/-- `log(K+2) ≥ 0`. -/
private lemma log_K2_nonneg (K : ℕ) : (0 : ℝ) ≤ Real.log ((K : ℝ) + 2) := by
  refine Real.log_nonneg ?_
  have : (0 : ℝ) ≤ (K : ℝ) := by positivity
  linarith

/-- The multiples of `m` in `[1,K]`, written as `m·k` with `k ≤ K/m`. -/
private lemma dvd_filter_image {m K : ℕ} (hm : 1 ≤ m) :
    (Finset.Icc 1 K).filter (fun d => m ∣ d)
      = (Finset.Icc 1 (K / m)).image (fun k => m * k) := by
  have hm0 : 0 < m := hm
  ext d
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
  constructor
  · rintro ⟨⟨hd1, hdK⟩, hdvd⟩
    have hk_eq : m * (d / m) = d := Nat.mul_div_cancel' hdvd
    have hk1 : 1 ≤ d / m := by
      rcases Nat.eq_zero_or_pos (d / m) with h | h
      · rw [h, mul_zero] at hk_eq
        omega
      · exact h
    exact ⟨d / m, ⟨hk1, Nat.div_le_div_right hdK⟩, hk_eq⟩
  · rintro ⟨k, ⟨hk1, hkK⟩, rfl⟩
    refine ⟨⟨?_, ?_⟩, ⟨k, rfl⟩⟩
    · have : 1 * 1 ≤ m * k := Nat.mul_le_mul hm hk1
      simpa using this
    · exact le_trans (Nat.mul_le_mul_left m hkK) (Nat.mul_div_le K m)

/-- `∑_{d ≤ K, m ∣ d} 1/d ≤ (1 + log(K+2))/m`. -/
private lemma filter_dvd_sum_inv_le {m K : ℕ} (hm : 1 ≤ m) :
    (∑ d ∈ (Finset.Icc 1 K).filter (fun d => m ∣ d), ((d : ℝ))⁻¹)
      ≤ ((m : ℝ))⁻¹ * (1 + Real.log ((K : ℝ) + 2)) := by
  have hm0 : 0 < m := hm
  have hset := dvd_filter_image (m := m) (K := K) hm
  have hinj : Set.InjOn (fun k : ℕ => m * k) (↑(Finset.Icc 1 (K / m)) : Set ℕ) := by
    intro a _ b _ hab
    exact Nat.mul_left_cancel hm0 hab
  rw [hset, Finset.sum_image hinj]
  have hcongr : (∑ k ∈ Finset.Icc 1 (K / m), (((m * k : ℕ)) : ℝ)⁻¹)
      = ((m : ℝ))⁻¹ * ∑ k ∈ Finset.Icc 1 (K / m), ((k : ℝ))⁻¹ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Nat.cast_mul, mul_inv_rev]
    ring
  rw [hcongr]
  have h1 : (∑ k ∈ Finset.Icc 1 (K / m), (1 / (k : ℝ)))
      ≤ 1 + Real.log (((K / m : ℕ)) : ℝ) :=
    Work.FIArea7.divisorSum_sum_inv_Icc_le (K / m)
  have h2 : Real.log (((K / m : ℕ)) : ℝ) ≤ Real.log ((K : ℝ) + 2) := by
    rcases Nat.eq_zero_or_pos (K / m) with h0 | h0
    · rw [h0]
      push_cast
      rw [Real.log_zero]
      linarith [log_K2_nonneg K]
    · refine Real.log_le_log (by positivity) ?_
      have hle : (((K / m : ℕ)) : ℝ) ≤ (K : ℝ) := by
        exact_mod_cast Nat.div_le_self K m
      linarith
  have h1' : (∑ k ∈ Finset.Icc 1 (K / m), (((k : ℕ)) : ℝ)⁻¹)
      ≤ 1 + Real.log (((K / m : ℕ)) : ℝ) := by
    simpa [one_div] using h1
  exact mul_le_mul_of_nonneg_left (by linarith [h1', h2]) (by positivity)

/-- The `e`-sum of the weight, bounded by `(1/b)(4b)⁻¹ (1+log(K+2))²`. -/
private lemma sum_e_le {b K X : ℕ} (hb : 1 ≤ b) :
    (∑ e ∈ Finset.Icc 1 X, (1 / (b : ℝ)) *
        (if 4 * b * e ≤ K then ((4 * b * e : ℕ) : ℝ)⁻¹ * (1 + Real.log ((K : ℝ) + 2))
          else 0))
      ≤ (1 / (b : ℝ)) * (4 * (b : ℝ))⁻¹ * (1 + Real.log ((K : ℝ) + 2)) ^ 2 := by
  have hpt : ∀ e : ℕ,
      (1 / (b : ℝ)) * (if 4 * b * e ≤ K then
          ((4 * b * e : ℕ) : ℝ)⁻¹ * (1 + Real.log ((K : ℝ) + 2)) else 0)
        = (1 / (b : ℝ)) * (4 * (b : ℝ))⁻¹ * (1 + Real.log ((K : ℝ) + 2)) *
            (if e ≤ K / (4 * b) then (1 / (e : ℝ)) else 0) := by
    intro e
    have hb4 : 0 < 4 * b := by omega
    by_cases h : 4 * b * e ≤ K
    · have he : e ≤ K / (4 * b) :=
        (Nat.le_div_iff_mul_le hb4).mpr (by rw [mul_comm e (4 * b)]; exact h)
      rw [if_pos h, if_pos he]
      push_cast
      field_simp
    · have he : ¬ (e ≤ K / (4 * b)) := by
        intro he'
        have hle : e * (4 * b) ≤ K := (Nat.le_div_iff_mul_le hb4).mp he'
        rw [mul_comm e (4 * b)] at hle
        exact h hle
      simp [h, he]
  rw [Finset.sum_congr rfl fun e _ => hpt e]
  have hsub : (Finset.Icc 1 X).filter (fun e => e ≤ K / (4 * b))
      ⊆ Finset.Icc 1 (K / (4 * b)) := by
    intro e he
    rw [Finset.mem_filter, Finset.mem_Icc] at he
    exact Finset.mem_Icc.mpr ⟨he.1.1, he.2⟩
  have hsum : (∑ e ∈ Finset.Icc 1 X, (if e ≤ K / (4 * b) then (1 / (e : ℝ)) else 0))
      ≤ 1 + Real.log ((K : ℝ) + 2) := by
    rw [← Finset.sum_filter]
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun e _ _ => by positivity)) ?_
    have h1 : (∑ k ∈ Finset.Icc 1 (K / (4 * b)), (1 / (k : ℝ)))
        ≤ 1 + Real.log (((K / (4 * b) : ℕ)) : ℝ) :=
      Work.FIArea7.divisorSum_sum_inv_Icc_le (K / (4 * b))
    have h2 : Real.log (((K / (4 * b) : ℕ)) : ℝ) ≤ Real.log ((K : ℝ) + 2) := by
      rcases Nat.eq_zero_or_pos (K / (4 * b)) with h0 | h0
      · rw [h0]
        push_cast
        rw [Real.log_zero]
        linarith [log_K2_nonneg K]
      · refine Real.log_le_log (by positivity) ?_
        have hle : (((K / (4 * b) : ℕ)) : ℝ) ≤ (K : ℝ) := by
          exact_mod_cast Nat.div_le_self K (4 * b)
        linarith
    linarith [h1, h2]
  calc (∑ e ∈ Finset.Icc 1 X, (1 / (b : ℝ)) * (4 * (b : ℝ))⁻¹ *
        (1 + Real.log ((K : ℝ) + 2)) *
          (if e ≤ K / (4 * b) then (1 / (e : ℝ)) else 0))
      = (1 / (b : ℝ)) * (4 * (b : ℝ))⁻¹ * (1 + Real.log ((K : ℝ) + 2)) *
          ∑ e ∈ Finset.Icc 1 X, (if e ≤ K / (4 * b) then (1 / (e : ℝ)) else 0) := by
        rw [Finset.mul_sum]
    _ ≤ (1 / (b : ℝ)) * (4 * (b : ℝ))⁻¹ * (1 + Real.log ((K : ℝ) + 2)) *
          (1 + Real.log ((K : ℝ) + 2)) := by
        have hb1 : (0 : ℝ) ≤ 1 / (b : ℝ) := by positivity
        have hb2 : (0 : ℝ) ≤ (4 * (b : ℝ))⁻¹ := by positivity
        have hb3 : (0 : ℝ) ≤ 1 + Real.log ((K : ℝ) + 2) := by linarith [log_K2_nonneg K]
        exact mul_le_mul_of_nonneg_left hsum (mul_nonneg (mul_nonneg hb1 hb2) hb3)
    _ = (1 / (b : ℝ)) * (4 * (b : ℝ))⁻¹ * (1 + Real.log ((K : ℝ) + 2)) ^ 2 := by ring

/-- The arithmetic bound for the total `(b,e)`-weight: `∑_{d ≤ K} pairW B0 X d ≤ 2L²`. -/
private lemma sum_range_pairW_le (B0 X K : ℕ) :
    (∑ d ∈ Finset.range (K + 1), Work.FIArea7.pairW B0 X d)
      ≤ 2 * (1 + Real.log ((K : ℝ) + 2)) ^ 2 := by
  set L : ℝ := 1 + Real.log ((K : ℝ) + 2) with hL
  have hL1 : (1 : ℝ) ≤ L := by
    rw [hL]
    linarith [log_K2_nonneg K]
  have hzero : Work.FIArea7.pairW B0 X 0 = 0 := by
    simp [Work.FIArea7.pairW]
  have hsplit : (∑ d ∈ Finset.range (K + 1), Work.FIArea7.pairW B0 X d)
      = ∑ d ∈ Finset.Icc 1 K, Work.FIArea7.pairW B0 X d := by
    rcases Nat.eq_zero_or_pos K with hK | hK
    · subst hK
      simp [hzero]
    · have hset : Finset.range (K + 1) = insert 0 (Finset.Icc 1 K) := by
        ext d
        simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
        omega
      rw [hset, Finset.sum_insert (by simp), hzero, zero_add]
  rw [hsplit]
  have hopen : (∑ d ∈ Finset.Icc 1 K, Work.FIArea7.pairW B0 X d)
      = ∑ b ∈ Finset.Icc 1 B0, ∑ e ∈ Finset.Icc 1 X, (1 / (b : ℝ)) *
          (∑ d ∈ (Finset.Icc 1 K).filter (fun d => 4 * b * e ∣ d), ((d : ℝ))⁻¹) := by
    simp only [Work.FIArea7.pairW]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    by_cases h : 4 * b * e ∣ d <;> simp [h]
  rw [hopen]
  have hbe : ∀ b ∈ Finset.Icc 1 B0, ∀ e ∈ Finset.Icc 1 X,
      (∑ d ∈ (Finset.Icc 1 K).filter (fun d => 4 * b * e ∣ d), ((d : ℝ))⁻¹)
        ≤ (if 4 * b * e ≤ K then ((4 * b * e : ℕ) : ℝ)⁻¹ * L else 0) := by
    intro b hb e he
    have hb1 : 1 ≤ b := (Finset.mem_Icc.mp hb).1
    have he1 : 1 ≤ e := (Finset.mem_Icc.mp he).1
    have hm1 : 1 ≤ 4 * b * e := by
      have h1 : 1 ≤ 4 * b := by omega
      have := Nat.mul_le_mul h1 he1
      simpa using this
    have h := filter_dvd_sum_inv_le (m := 4 * b * e) (K := K) hm1
    rw [← hL] at h
    by_cases hc : 4 * b * e ≤ K
    · rw [if_pos hc]; exact h
    · rw [if_neg hc]
      have hno : ∀ d ∈ (Finset.Icc 1 K).filter (fun d => 4 * b * e ∣ d), False := by
        intro d hd
        rw [Finset.mem_filter, Finset.mem_Icc] at hd
        have := Nat.le_of_dvd (by omega) hd.2
        omega
      rw [Finset.sum_eq_zero (fun d hd => absurd hd (hno d))]
  calc (∑ b ∈ Finset.Icc 1 B0, ∑ e ∈ Finset.Icc 1 X, (1 / (b : ℝ)) *
        (∑ d ∈ (Finset.Icc 1 K).filter (fun d => 4 * b * e ∣ d), ((d : ℝ))⁻¹))
      ≤ ∑ b ∈ Finset.Icc 1 B0, ∑ e ∈ Finset.Icc 1 X, (1 / (b : ℝ)) *
          (if 4 * b * e ≤ K then ((4 * b * e : ℕ) : ℝ)⁻¹ * L else 0) := by
        refine Finset.sum_le_sum fun b hb => Finset.sum_le_sum fun e he => ?_
        exact mul_le_mul_of_nonneg_left (hbe b hb e he) (by positivity)
    _ ≤ ∑ b ∈ Finset.Icc 1 B0, (1 / (b : ℝ)) * (4 * (b : ℝ))⁻¹ * L ^ 2 := by
        refine Finset.sum_le_sum fun b hb => ?_
        have h := sum_e_le (b := b) (K := K) (X := X) (Finset.mem_Icc.mp hb).1
        rw [← hL] at h
        exact h
    _ = L ^ 2 / 4 * ∑ b ∈ Finset.Icc 1 B0, (1 / (b : ℝ)) ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        ring
    _ ≤ L ^ 2 / 4 * 2 := by
        have h := Work.FIArea7.sum_inv_sq_Icc_le_two B0
        have h2 : (∑ b ∈ Finset.Icc 1 B0, (1 / (b : ℝ)) ^ 2) ≤ 2 := by
          refine le_trans (le_of_eq ?_) h
          refine Finset.sum_congr rfl fun b _ => ?_
          ring
        exact mul_le_mul_of_nonneg_left h2 (by positivity)
    _ ≤ 2 * L ^ 2 := by nlinarith [hL1]

/-- The logarithm comparison finishing the assembly. -/
private lemma log_arith (Pa : Work.FITop.Params) (K : ℕ) (hK : (K : ℝ) ≤ 20 * Pa.N)
    (X : ℕ) (hX : 1 ≤ X) :
    40 * (1 + Real.log ((K : ℝ) + 2)) ^ 2
      ≤ 20000 * ((X : ℝ) + 1) * (Real.log (Pa.N + 2)) ^ 3 := by
  have hN1 : (1 : ℝ) ≤ Pa.N := Pa.hN1
  have hL1 : (1 : ℝ) ≤ Real.log (Pa.N + 2) := by
    have h3 : (3 : ℝ) ≤ Pa.N + 2 := by linarith
    have hlog3 : (1 : ℝ) ≤ Real.log 3 := by
      rw [show (1 : ℝ) = Real.log (Real.exp 1) from (Real.log_exp 1).symm]
      exact Real.log_le_log (Real.exp_pos 1) (le_of_lt Real.exp_one_lt_three)
    exact le_trans hlog3 (Real.log_le_log (by norm_num) h3)
  have hKlog : Real.log ((K : ℝ) + 2) ≤ 22 * Real.log (Pa.N + 2) := by
    have hle : (K : ℝ) + 2 ≤ 22 * (Pa.N + 2) := by linarith
    have hpos1 : (0 : ℝ) < (K : ℝ) + 2 := by positivity
    have hpos2 : (0 : ℝ) < Pa.N + 2 := by linarith
    have hlog22 : Real.log 22 ≤ 21 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 22)
      linarith
    calc Real.log ((K : ℝ) + 2) ≤ Real.log (22 * (Pa.N + 2)) := Real.log_le_log hpos1 hle
      _ = Real.log 22 + Real.log (Pa.N + 2) := Real.log_mul (by norm_num) (ne_of_gt hpos2)
      _ ≤ 21 + Real.log (Pa.N + 2) := by linarith
      _ ≤ 22 * Real.log (Pa.N + 2) := by linarith
  have hX2 : (2 : ℝ) ≤ (X : ℝ) + 1 := by
    have : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
    linarith
  have h2 : (0 : ℝ) ≤ 1 + Real.log ((K : ℝ) + 2) := by
    have hK0 : (0 : ℝ) ≤ (K : ℝ) := by positivity
    have hlog0 : (0 : ℝ) ≤ Real.log ((K : ℝ) + 2) :=
      Real.log_nonneg (by linarith)
    linarith
  have h1 : (1 : ℝ) + Real.log ((K : ℝ) + 2) ≤ 23 * Real.log (Pa.N + 2) := by linarith
  have key1 : (1 + Real.log ((K : ℝ) + 2)) ^ 2 ≤ 529 * (Real.log (Pa.N + 2)) ^ 2 := by
    have h := mul_self_le_mul_self h2 h1
    nlinarith [h]
  have key2 : 529 * (Real.log (Pa.N + 2)) ^ 2 ≤ 529 * (Real.log (Pa.N + 2)) ^ 3 := by
    have hL2 : (Real.log (Pa.N + 2)) ^ 2 ≤ (Real.log (Pa.N + 2)) ^ 3 := by nlinarith [hL1]
    exact mul_le_mul_of_nonneg_left hL2 (by norm_num)
  have key3 : 40 * 529 * (Real.log (Pa.N + 2)) ^ 3
      ≤ 20000 * ((X : ℝ) + 1) * (Real.log (Pa.N + 2)) ^ 3 := by
    have h23 : (40 : ℝ) * 529 ≤ 20000 * ((X : ℝ) + 1) := by linarith
    have hL3 : (0 : ℝ) ≤ (Real.log (Pa.N + 2)) ^ 3 := by positivity
    nlinarith [h23, hL3]
  linarith [key1, key2, key3]

theorem pairW_pair_sum_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt} {β : GaussianInt → ℂ} (X : ℕ),
        Work.FITop4.IsBetaCoeff6 Pa φ z0 β → 1 ≤ X →
        (∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
          ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
            Work.FIArea7.pairW (Work.FIArea7.uniB Pa) X (Work.FIPlan.absDelta z1 z2)
              * ‖β z1‖ * ‖β z2‖)
          ≤ C * ((X : ℝ) + 1) * (Real.log (Pa.N + 2)) ^ 3
              * (∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖β z‖ ^ 2) := by
  refine ⟨20000, by norm_num, ?_⟩
  intro Pa φ z0 β X hβ hX
  have hN0 : (0 : ℝ) ≤ Pa.N := by linarith [Pa.hN1]
  set k : ℕ := Nat.ceil (Real.sqrt (4 * Pa.N)) with hk
  set K : ℕ := 2 * k ^ 2 + 2 with hK
  have hrad_eq : (Work.FITop.radN Pa : ℝ) = (k : ℝ) := by
    rw [Work.FITop.radN, hk]; push_cast; ring
  have hceil : (k : ℝ) < Real.sqrt (4 * Pa.N) + 1 := by
    rw [hk]
    exact Nat.ceil_lt_add_one (Real.sqrt_nonneg _)
  have hsqrt4 : Real.sqrt (4 * Pa.N) = 2 * Real.sqrt Pa.N := by
    have h4 : Real.sqrt (4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4) Pa.N, h4]
  have hklt : (k : ℝ) < 2 * Real.sqrt Pa.N + 1 := by rw [hsqrt4] at hceil; linarith
  have hKval : (K : ℝ) = 2 * (k : ℝ) ^ 2 + 2 := by rw [hK]; push_cast; ring
  have hKbound : (K : ℝ) ≤ 20 * Pa.N := by
    have hsqrt_le : Real.sqrt Pa.N ≤ Pa.N := by
      nlinarith [Real.sq_sqrt hN0, Real.sqrt_nonneg Pa.N, Pa.hN1]
    have hkk : (k : ℝ) ^ 2 < (2 * Real.sqrt Pa.N + 1) ^ 2 := by
      nlinarith [hklt, show (0 : ℝ) ≤ (k : ℝ) by positivity]
    rw [hKval]
    nlinarith [hkk, hsqrt_le, Real.sq_sqrt hN0, Real.sqrt_nonneg Pa.N, Pa.hN1]
  have hKrad : 2 * (Work.FITop.radN Pa : ℝ) ^ 2 ≤ (K : ℝ) := by
    rw [hrad_eq, hKval]; linarith
  have hrow : ∀ z1 : GaussianInt, β z1 ≠ 0 →
      (∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
          Work.FIArea7.pairW (Work.FIArea7.uniB Pa) X (Work.FIPlan.absDelta z1 z2))
        ≤ 20 * ∑ d ∈ Finset.range (K + 1),
            Work.FIArea7.pairW (Work.FIArea7.uniB Pa) X d := by
    intro z1 hz1
    refine Work.FIArea7.fibre_sum_regroup (Work.FIPlan.gBox (Work.FITop.radN Pa))
      (fun z2 => Work.FIPlan.absDelta z1 z2) K 20
      (fun d => Work.FIArea7.pairW (Work.FIArea7.uniB Pa) X d)
      (fun d => pairW_nonneg _ _ _) ?_ ?_
    · intro z2 hz2
      exact absDelta_le_K_of_beta hβ hKrad hz1 hz2
    · intro d
      exact level_card_le hβ hz1 d
  have hWsum : (∑ d ∈ Finset.range (K + 1),
        Work.FIArea7.pairW (Work.FIArea7.uniB Pa) X d)
      ≤ 2 * (1 + Real.log ((K : ℝ) + 2)) ^ 2 :=
    sum_range_pairW_le (Work.FIArea7.uniB Pa) X K
  have hbil : (∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
        ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
          Work.FIArea7.pairW (Work.FIArea7.uniB Pa) X (Work.FIPlan.absDelta z1 z2)
            * ‖β z1‖ * ‖β z2‖)
      ≤ ∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
          ‖β z1‖ ^ 2 * (∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
            Work.FIArea7.pairW (Work.FIArea7.uniB Pa) X (Work.FIPlan.absDelta z1 z2)) :=
    Work.FIArea7.pairW_bilinear_le (Work.FIPlan.gBox (Work.FITop.radN Pa))
      (fun z1 z2 => Work.FIArea7.pairW (Work.FIArea7.uniB Pa) X (Work.FIPlan.absDelta z1 z2))
      (fun z => ‖β z‖) (fun a b => pairW_nonneg _ _ _) (fun a b => by rw [absDelta_comm a b])
  have hS2 : (0 : ℝ) ≤ ∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖β z‖ ^ 2 :=
    Finset.sum_nonneg fun z _ => sq_nonneg _
  have harith : 40 * (1 + Real.log ((K : ℝ) + 2)) ^ 2
      ≤ 20000 * ((X : ℝ) + 1) * (Real.log (Pa.N + 2)) ^ 3 := log_arith Pa K hKbound X hX
  calc (∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
          ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
            Work.FIArea7.pairW (Work.FIArea7.uniB Pa) X (Work.FIPlan.absDelta z1 z2)
              * ‖β z1‖ * ‖β z2‖)
      ≤ ∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
          ‖β z1‖ ^ 2 * (∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
            Work.FIArea7.pairW (Work.FIArea7.uniB Pa) X (Work.FIPlan.absDelta z1 z2)) := hbil
    _ ≤ ∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
          ‖β z1‖ ^ 2 * (20 * ∑ d ∈ Finset.range (K + 1),
            Work.FIArea7.pairW (Work.FIArea7.uniB Pa) X d) := by
        apply Finset.sum_le_sum
        intro z1 _
        by_cases hz : β z1 = 0
        · rw [hz, norm_zero]
          simp
        · exact mul_le_mul_of_nonneg_left (hrow z1 hz) (sq_nonneg _)
    _ = 20 * (∑ d ∈ Finset.range (K + 1),
            Work.FIArea7.pairW (Work.FIArea7.uniB Pa) X d)
          * (∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖β z1‖ ^ 2) := by
        rw [← Finset.sum_mul]; ring
    _ ≤ 20 * (2 * (1 + Real.log ((K : ℝ) + 2)) ^ 2)
          * (∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖β z1‖ ^ 2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hWsum (by norm_num)) hS2
    _ ≤ 20000 * ((X : ℝ) + 1) * (Real.log (Pa.N + 2)) ^ 3
          * (∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖β z‖ ^ 2) := by
        nlinarith [harith, hS2]

end

end Work.FIArea7

/-
# `OffAxis/HB10_3Engine` — HB (1992) §10 (10.1)–(10.6) for a general test function

The three-character engine of Heath-Brown's §10 (Lemma 10.1/10.2 endgame), run at rectangle
height `L`: from the pointwise positivity (10.1)–(10.3) (`Ksum_positivity_three`), the
parametric Lemma 5.2 bounds (`Ksum_le_self_of_L52_phi`, `Ksum_le_single_of_L52_phi`,
`KsumLeTwoOfL52`), the principal-character bounds (`Ksum_principal_le`,
`principalKsumWide`) and the test-function conditions (10.8) — here the two hypotheses on
`T.Fc` at `-a + i μ`, `0 ≤ a ≤ 6/7` — one deduces (10.6):

`F(-λ₁) - F(0) - F(λ₂-λ₁) - F(λ₃-λ₁) + f(0)(7/6 + 8ε') ≥ 0`.

The bookkeeping is exact: three leading terms at `f 0 (1/6+ε)L` each, six pairs and four triples
at the same rate with weights `1/2`, `1/4`, and the leading principal term at `f 0 ε L`, giving
`1/2 + 1/2 + 1/6 + ε = 7/6 + 8ε`; a principal triple's `F(-λ₁+iμ)` term is paid for by its
companion pair's `-2F(iμ)` (hypothesis (A) at `|μ| ≤ 4`) or by (B) at `|μ| ≥ 4`.
-/

import Mathlib
import Submission.Work.ZeroFreeTables.OffAxis.Defs
import Submission.Work.ZeroFreeTables.Engine
import Submission.Work.NumberTheory.Linnik.scratch_l62app_phi
import Submission.Work.ZeroFreeTables.Ksum_positivity_three
import Submission.Work.ZeroFreeTables.CertData
import Submission.Work.ZeroFreeTables.TestFn_F_eq_integral
import Submission.Work.ZeroFreeTables.TestFn_F_antitone
import Submission.Work.ZeroFreeTables.hbLemma6_2_engine_v2
import Submission.Work.ZeroFreeTables.OffAxis.HB10_3EngineHelpers
import Submission.Commons.NumberTheory.Linnik.Ksum_principal_le
import Submission.Work.A7.zeroMult_conj_inv
import Submission.Work.LinnikAreas.principalKsumWide
import Submission.Work.ZeroFreeTables.OffAxis.KsumLeTwoOfL52
import Submission.Work.LinnikContract.API.isZ_lambda_nonneg

set_option autoImplicit false
set_option maxHeartbeats 4000000

open Complex DirichletCharacter Metric BigOperators
open scoped BigOperators
open Work.LinnikContract
noncomputable section

namespace Work.ZeroFreeTables.OffAxis

/-! ## Elementary helpers -/

lemma mul_ofReal_re_add_im (z : ℂ) (L : ℝ) :
    z * (L : ℂ) = ((z.re * L : ℝ) : ℂ) + (((z.im * L : ℝ) : ℂ)) * Complex.I := by
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

lemma intervalIntegral_re {a b : ℝ} {g : ℝ → ℂ}
    (h : IntervalIntegrable g MeasureTheory.volume a b) :
    (∫ t in a..b, g t).re = ∫ t in a..b, (g t).re := by
  rw [← Complex.reCLM_apply, ← ContinuousLinearMap.intervalIntegral_comp_comm Complex.reCLM h]
  exact intervalIntegral.integral_congr (fun t _ => by rw [Complex.reCLM_apply])

lemma lamOf_eq (q : ℕ) (ρ : ℂ) (h : Real.log (q : ℝ) ≠ 0) :
    1 - ρ.re = lamOf q ρ / Real.log (q : ℝ) := by
  rw [lamOf]; field_simp

/-- The window argument `1 + τ i - u` in rectangular form. -/
lemma one_add_mul_I_sub (τ : ℝ) (u : ℂ) :
    (1:ℂ) + (τ : ℂ) * Complex.I - u
      = ((1 - u.re : ℝ) : ℂ) + ((τ - u.im : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext <;>
    simp [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.one_re, Complex.one_im] <;> ring

lemma norm_win {lam v Lq δ : ℝ} (hLq : 0 < Lq) (hδ : 0 < δ) (hlam : 0 ≤ lam)
    (hlam1 : lam ≤ 1) (hv : |v| ≤ 4) (hδLq : 5 ≤ δ * Lq) :
    ‖((lam / Lq : ℝ) : ℂ) + ((v / Lq : ℝ) : ℂ) * Complex.I‖ ≤ δ := by
  have hsq : ‖((lam / Lq : ℝ) : ℂ) + ((v / Lq : ℝ) : ℂ) * Complex.I‖ ^ 2
      = (lam / Lq) ^ 2 + (v / Lq) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_add_mul_I]
  have h1 : (lam / Lq) ^ 2 ≤ 1 / Lq ^ 2 := by
    rw [div_pow]
    exact div_le_div_of_nonneg_right (by nlinarith [hlam, hlam1]) (by positivity)
  have h2 : (v / Lq) ^ 2 ≤ 16 / Lq ^ 2 := by
    rw [div_pow]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    have := abs_le.mp hv
    nlinarith [this.1, this.2]
  have h3 : (1:ℝ) / Lq ^ 2 + 16 / Lq ^ 2 ≤ δ ^ 2 := by
    have h17 : (1:ℝ) / Lq ^ 2 + 16 / Lq ^ 2 = 17 / Lq ^ 2 := by ring
    rw [h17, div_le_iff₀ (by positivity)]
    nlinarith [hδLq, hLq, hδ]
  have hb : ‖((lam / Lq : ℝ) : ℂ) + ((v / Lq : ℝ) : ℂ) * Complex.I‖ ^ 2 ≤ δ ^ 2 := by
    rw [hsq]; linarith
  have h4 : |‖((lam / Lq : ℝ) : ℂ) + ((v / Lq : ℝ) : ℂ) * Complex.I‖| ≤ |δ| :=
    sq_le_sq.mp hb
  rwa [abs_of_nonneg (norm_nonneg _), abs_of_pos hδ] at h4

/-- Membership in the divisor ball `closedBall 0 (|z.im| + 2)` from the window condition
`‖1 + z.im·i - u‖ ≤ δ` and `|Re u| ≤ 1` (used with `z` the summation point and `u` the retained
zero of a Dirichlet `L`-function in the critical strip). -/
lemma mem_closedBall_of_window (z : ℂ) (δ : ℝ) {u : ℂ}
    (hwin : ‖(1:ℂ) + (z.im : ℂ) * Complex.I - u‖ ≤ δ) (hδ1 : δ < 1)
    (hu : |u.re| ≤ 1) :
    u ∈ Metric.closedBall (0:ℂ) (|z.im| + 2) := by
  rw [Metric.mem_closedBall, dist_zero_right]
  have h1 : |z.im - u.im| ≤ δ := by
    have h := Complex.abs_im_le_norm ((1:ℂ) + (z.im : ℂ) * Complex.I - u)
    have h' : (((1:ℂ) + (z.im : ℂ) * Complex.I - u).im) = z.im - u.im := by simp
    rw [h'] at h; exact le_trans h hwin
  have h2 : |u.im| ≤ |z.im| + δ := by
    calc |u.im| = |z.im - (z.im - u.im)| := by ring_nf
      _ ≤ |z.im| + |z.im - u.im| := abs_sub _ _
      _ ≤ |z.im| + δ := by linarith
  calc ‖u‖ ≤ |u.re| + |u.im| := Complex.norm_le_abs_re_add_abs_im u
    _ ≤ 1 + (|z.im| + δ) := by linarith
    _ ≤ |z.im| + 2 := by linarith

/-- The Laplace integral with an explicit exponential argument. -/
lemma Fc_of_exp_eq' (T : Work.ZeroFreeTables.TestFn) (z : ℂ) :
    (∫ t in (0:ℝ)..T.x₀, Complex.exp (-(z * (t : ℂ))) * ((T.f t : ℝ) : ℂ)).re
      = (T.Fc z).re := by
  rw [T.Fc_spec z]

lemma conj_mul_ofReal_re (w : ℂ) (x : ℝ) :
    ((starRingEnd ℂ) w * ((x : ℝ) : ℂ)).re = (w * ((x : ℝ) : ℂ)).re := by
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero, add_zero, mul_neg, neg_zero]

/-- The real part of the Laplace transform at `-i μ` and `i μ` agree. -/
lemma TestFn.Fc_neg_I_re (T : Work.ZeroFreeTables.TestFn) (mu : ℝ) :
    (T.Fc ((-(mu : ℂ)) * Complex.I)).re = (T.Fc ((mu : ℂ) * Complex.I)).re := by
  have hint : ∀ w : ℂ, IntervalIntegrable
      (fun t : ℝ => Complex.exp (-(w * (t : ℂ))) * ((T.f t : ℝ) : ℂ)) MeasureTheory.volume
      (0:ℝ) T.x₀ := by
    intro w
    refine ContinuousOn.intervalIntegrable_of_Icc (le_of_lt T.x₀_pos) ?_
    refine ContinuousOn.mul ?_ ?_
    · exact (by fun_prop : Continuous fun t : ℝ => Complex.exp (-(w * (t : ℂ)))).continuousOn
    · exact Complex.continuous_ofReal.comp_continuousOn
        (T.f_cont.mono (fun t (ht : t ∈ Set.Icc (0:ℝ) T.x₀) => ht.1))
  have hpt : ∀ t : ℝ, (Complex.exp (-(((-(mu : ℂ)) * Complex.I) * (t : ℂ)))
      * ((T.f t : ℝ) : ℂ)).re = (Complex.exp (-(((mu : ℂ) * Complex.I) * (t : ℂ)))
      * ((T.f t : ℝ) : ℂ)).re := by
    intro t
    have hc : Complex.exp (-(((-(mu : ℂ)) * Complex.I) * (t : ℂ)))
        = (starRingEnd ℂ) (Complex.exp (-(((mu : ℂ) * Complex.I) * (t : ℂ)))) := by
      rw [← Complex.exp_conj]
      congr 1
      rw [map_neg, map_mul, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.conj_ofReal]
      ring
    rw [hc, conj_mul_ofReal_re]
  rw [T.Fc_spec ((-(mu : ℂ)) * Complex.I), T.Fc_spec ((mu : ℂ) * Complex.I)]
  rw [intervalIntegral_re (hint _), intervalIntegral_re (hint _)]
  exact intervalIntegral.integral_congr (fun t _ => hpt t)

/-- The arithmetic kernel of HB (1992) §10: the `(10.6)` inequality follows from the four
"leading" bounds, the six pair bounds (aggregated) and the four triple bounds, with the
`(A)`-credits `crd j = L * Re F (i mu_j)` attached to the principal triples. -/
theorem hb103_kernel (T : Work.ZeroFreeTables.TestFn) (eps : ℝ) (heps : 0 < eps)
    {Lq lam1 lam2 lam3 : ℝ} (hLq : 0 < Lq) {crd0 crd1 crd2 crd3 : ℝ}
    {bt0 bt1 bt2 bt3 : ℝ} {bPsum K0 K1 K2 K3 : ℝ}
    (hbK0 : K0 ≤ Lq * T.F (-lam1) + T.f 0 * eps * Lq)
    (hbK1 : K1 ≤ -Lq * T.F 0 + T.f 0 * (1/6 + eps) * Lq)
    (hbK2 : K2 ≤ -Lq * T.F (lam2 - lam1) + T.f 0 * (1/6 + eps) * Lq)
    (hbK3 : K3 ≤ -Lq * T.F (lam3 - lam1) + T.f 0 * (1/6 + eps) * Lq)
    (hbt0 : bt0 ≤ T.f 0 * (1/6 + eps) * Lq + 2 * crd0)
    (hbt1 : bt1 ≤ T.f 0 * (1/6 + eps) * Lq + 2 * crd1)
    (hbt2 : bt2 ≤ T.f 0 * (1/6 + eps) * Lq + 2 * crd2)
    (hbt3 : bt3 ≤ T.f 0 * (1/6 + eps) * Lq + 2 * crd3)
    (hbP : bPsum ≤ 6 * (T.f 0 * (1/6 + eps) * Lq) - (crd0 + crd1 + crd2 + crd3))
    (hpos : 0 ≤ K0 + K1 + K2 + K3 + (1/2) * bPsum + (1/4) * (bt0 + bt1 + bt2 + bt3)) :
    0 ≤ T.F (-lam1) - T.F 0 - T.F (lam2 - lam1) - T.F (lam3 - lam1)
      + T.f 0 * (7/6 + 8 * eps) := by
  have key : 0 ≤ Lq * (T.F (-lam1) - T.F 0 - T.F (lam2 - lam1) - T.F (lam3 - lam1)
      + T.f 0 * (7/6 + 8 * eps)) := by
    linarith only [hpos, hbK0, hbK1, hbK2, hbK3, hbt0, hbt1, hbt2, hbt3, hbP]
  exact (mul_nonneg_iff_of_pos_left hLq).mp key

/-- **HB (1992) §10, (10.1)–(10.6), at rectangle height `L`.** -/
theorem HB10_3Engine (T : Work.ZeroFreeTables.TestFn) (ε' δ : ℝ) (hε' : 0 < ε') (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (L : ℝ)
      (χ₁ χ₂ χ₃ : DirichletCharacter ℂ q) (ρ₁ ρ₂ ρ₃ : ℂ),
      (∀ (χ : DirichletCharacter ℂ q) [NeZero χ.conductor], χ ≠ 1 →
        Commons.NumberTheory.Linnik.L52Hyp χ (1/6) ε' δ) →
      1 ≤ L → L ≤ Real.log (q : ℝ) →
      Work.ZeroFreeTables.IsRectMin L χ₁ ρ₁ →
      1 < |ρ₁.im| →
      Work.LinnikContract.IsZ χ₂ ρ₂ → Work.LinnikContract.IsZ χ₃ ρ₃ →
      χ₂ ≠ χ₁ → χ₂ ≠ χ₁⁻¹ → χ₃ ≠ χ₁ → χ₃ ≠ χ₁⁻¹ → χ₃ ≠ χ₂ → χ₃ ≠ χ₂⁻¹ →
      Work.LinnikContract.lamOf q ρ₂ ≤ Work.LinnikContract.lamOf q ρ₃ →
      Work.LinnikContract.lamOf q ρ₃ ≤ 6/7 →
      (∀ a μ : ℝ, 0 ≤ a → a ≤ 6/7 → |μ| ≤ 4 →
        (T.Fc (((-a : ℝ) : ℂ) + (μ : ℂ) * Complex.I)).re
          - 2 * (T.Fc ((μ : ℂ) * Complex.I)).re ≤ T.f 0 / 6) →
      (∀ a μ : ℝ, 0 ≤ a → a ≤ 6/7 → 4 ≤ |μ| →
        (T.Fc (((-a : ℝ) : ℂ) + (μ : ℂ) * Complex.I)).re ≤ T.f 0 / 6) →
      T.F (-(Work.LinnikContract.lamOf q ρ₁)) - T.F 0
        - T.F (Work.LinnikContract.lamOf q ρ₂ - Work.LinnikContract.lamOf q ρ₁)
        - T.F (Work.LinnikContract.lamOf q ρ₃ - Work.LinnikContract.lamOf q ρ₁)
        + T.f 0 * (7/6 + 8 * ε') ≥ 0 := by
  classical
  obtain ⟨B, hB0, hBnd⟩ := T.f_bound
  have hFnn : ∀ z : ℂ, 0 ≤ z.re →
      0 ≤ (∫ t in (0:ℝ)..T.x₀, Complex.exp (-(z * (t : ℂ))) * ((T.f t : ℝ) : ℂ)).re := by
    intro z hz; rw [← T.Fc_spec z]; exact T.Fc_re_nonneg z hz
  obtain ⟨q₀P, hq₀P⟩ := Work.LinnikAreas.principalKsumWide T.x₀ B T.x₀_pos hB0
    T.f_cont T.f_supp T.f_diff hBnd (by linarith : (0:ℝ) < ε'/4) T.f0_pos
  obtain ⟨q₀s, hq₀s⟩ := Commons.NumberTheory.Linnik.Ksum_le_self_of_L52_phi T.x₀ B (1/6)
    T.x₀_pos hB0 T.f_cont T.f_supp T.f_diff hBnd T.f0_pos hFnn hε' hδ0 hδ1
  obtain ⟨q₀o, hq₀o⟩ := Commons.NumberTheory.Linnik.Ksum_le_single_of_L52_phi T.x₀ B (1/6)
    T.x₀_pos hB0 T.f_cont T.f_supp T.f_diff hBnd T.f0_pos hFnn hε' hδ0 hδ1
  obtain ⟨q₀t, hq₀t⟩ := KsumLeTwoOfL52 T.x₀ B (1/6) T.x₀_pos hB0 T.f_cont T.f_supp T.f_diff
    hBnd T.f0_pos hFnn hε' hδ0 hδ1
  refine ⟨max (max (max (max q₀P q₀s) q₀o) q₀t)
    (Nat.ceil (Real.exp (max (Real.exp 2) (5/δ))) + 10), ?_⟩
  intro q hqq hqNe L χ₁ χ₂ χ₃ ρ₁ ρ₂ ρ₃ hL52 hL1 hLlog hR hoff hZ₂ hZ₃ h21 h21' h31 h31'
    h32 h32' hlam23 hlam3 hA hB
  have hM1 : max q₀P q₀s ≤ max (max q₀P q₀s) q₀o := le_max_left _ _
  have hM2 : max (max q₀P q₀s) q₀o ≤ max (max (max q₀P q₀s) q₀o) q₀t := le_max_left _ _
  have hM3 : max (max (max q₀P q₀s) q₀o) q₀t
      ≤ max (max (max (max q₀P q₀s) q₀o) q₀t)
        (Nat.ceil (Real.exp (max (Real.exp 2) (5/δ))) + 10) := le_max_left _ _
  have hM4 : Nat.ceil (Real.exp (max (Real.exp 2) (5/δ))) + 10
      ≤ max (max (max (max q₀P q₀s) q₀o) q₀t)
        (Nat.ceil (Real.exp (max (Real.exp 2) (5/δ))) + 10) := le_max_right _ _
  have hA1 : q₀P ≤ max q₀P q₀s := le_max_left _ _
  have hA2 : q₀s ≤ max q₀P q₀s := le_max_right _ _
  have hA3 : q₀o ≤ max (max q₀P q₀s) q₀o := le_max_right _ _
  have hA4 : q₀t ≤ max (max (max q₀P q₀s) q₀o) q₀t := le_max_right _ _
  have hq0P : q₀P ≤ q := ((hA1.trans hM1).trans hM2).trans (hM3.trans hqq)
  have hq0s : q₀s ≤ q := ((hA2.trans hM1).trans hM2).trans (hM3.trans hqq)
  have hq0o : q₀o ≤ q := (hA3.trans hM2).trans (hM3.trans hqq)
  have hq0t : q₀t ≤ q := (hA4.trans hM3).trans hqq
  have hqc : Nat.ceil (Real.exp (max (Real.exp 2) (5/δ))) + 10 ≤ q := hM4.trans hqq
  have hqpos : (0:ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hlogq_ge : max (Real.exp 2) (5/δ) ≤ Real.log (q : ℝ) := by
    have h1 : (Nat.ceil (Real.exp (max (Real.exp 2) (5/δ))) : ℝ) ≤ (q : ℝ) := by
      exact_mod_cast (le_trans (Nat.le_add_right _ 10) hqc)
    have h2 : Real.exp (max (Real.exp 2) (5/δ)) ≤ (q : ℝ) := le_trans (Nat.le_ceil _) h1
    have h3 := Real.log_le_log (Real.exp_pos _) h2
    rwa [Real.log_exp] at h3
  have hLqpos : 0 < Real.log (q : ℝ) :=
    lt_of_lt_of_le (Real.exp_pos 2) (le_trans (le_max_left _ _) hlogq_ge)
  have hLq1 : 1 ≤ Real.log (q : ℝ) := by
    have h : Real.exp 2 ≤ Real.log (q : ℝ) := le_trans (le_max_left _ _) hlogq_ge
    have h2 : (2:ℝ) < Real.exp 2 := by
      have h3 := Real.add_one_lt_exp (x := (2:ℝ)) (by norm_num)
      linarith
    linarith
  have hδLq5 : 5 ≤ δ * Real.log (q : ℝ) := by
    have h : 5/δ ≤ Real.log (q : ℝ) := le_trans (le_max_right _ _) hlogq_ge
    have h' := mul_le_mul_of_nonneg_left h hδ0.le
    have h5 : δ * (5/δ) = 5 := by field_simp
    linarith [h', h5]
  have hlogLq : 2 ≤ Real.log (Real.log (q : ℝ)) := by
    have h : Real.exp 2 ≤ Real.log (q : ℝ) := le_trans (le_max_left _ _) hlogq_ge
    have h2 := Real.log_le_log (Real.exp_pos 2) h
    rwa [Real.log_exp] at h2
  have hsqrt1 : 1 ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (le_trans (by norm_num) hlogLq)
  have hχ₁ : χ₁ ≠ 1 := hR.1.1
  have hzm₁ : zeroMult χ₁ ρ₁ ≠ 0 := hR.1.2.1
  have hbit₁ : |ρ₁.im| ≤ L := hR.1.2.2
  have hχ₂ : χ₂ ≠ 1 := hZ₂.1
  have hzm₂ : zeroMult χ₂ ρ₂ ≠ 0 := hZ₂.2.1
  have hbit₂ : |ρ₂.im| ≤ 1 := hZ₂.2.2
  have hχ₃ : χ₃ ≠ 1 := hZ₃.1
  have hzm₃ : zeroMult χ₃ ρ₃ ≠ 0 := hZ₃.2.1
  have hbit₃ : |ρ₃.im| ≤ 1 := hZ₃.2.2
  haveI hc₁ : NeZero χ₁.conductor := ⟨χ₁.conductor_ne_zero⟩
  haveI hc₂ : NeZero χ₂.conductor := ⟨χ₂.conductor_ne_zero⟩
  haveI hc₃ : NeZero χ₃.conductor := ⟨χ₃.conductor_ne_zero⟩
  haveI hc₄ : NeZero (χ₁ * χ₂).conductor := ⟨(χ₁ * χ₂).conductor_ne_zero⟩
  haveI hc₅ : NeZero (χ₁ * χ₂⁻¹).conductor := ⟨(χ₁ * χ₂⁻¹).conductor_ne_zero⟩
  haveI hc₆ : NeZero (χ₁ * χ₃).conductor := ⟨(χ₁ * χ₃).conductor_ne_zero⟩
  haveI hc₇ : NeZero (χ₁ * χ₃⁻¹).conductor := ⟨(χ₁ * χ₃⁻¹).conductor_ne_zero⟩
  haveI hc₈ : NeZero (χ₂ * χ₃).conductor := ⟨(χ₂ * χ₃).conductor_ne_zero⟩
  haveI hc₉ : NeZero (χ₂ * χ₃⁻¹).conductor := ⟨(χ₂ * χ₃⁻¹).conductor_ne_zero⟩
  haveI hc₁₀ : NeZero (χ₁ * χ₂ * χ₃).conductor := ⟨(χ₁ * χ₂ * χ₃).conductor_ne_zero⟩
  haveI hc₁₁ : NeZero (χ₁ * χ₂ * χ₃⁻¹).conductor := ⟨(χ₁ * χ₂ * χ₃⁻¹).conductor_ne_zero⟩
  haveI hc₁₂ : NeZero (χ₁ * χ₂⁻¹ * χ₃).conductor := ⟨(χ₁ * χ₂⁻¹ * χ₃).conductor_ne_zero⟩
  haveI hc₁₃ : NeZero (χ₁⁻¹ * χ₂ * χ₃).conductor := ⟨(χ₁⁻¹ * χ₂ * χ₃).conductor_ne_zero⟩
  obtain ⟨hne4, hne5, hne6, hne7, hne8, hne9⟩ :=
    pairProducts_ne_one h21 h21' h31 h31' h32 h32'
  have hstrip₁ : 0 < ρ₁.re ∧ ρ₁.re < 1 :=
    Work.ZeroFreeTables.re_mem_Ioo_of_zeroMult_v2 χ₁ hχ₁ hzm₁
  have hstrip₂ : 0 < ρ₂.re ∧ ρ₂.re < 1 :=
    Work.ZeroFreeTables.re_mem_Ioo_of_zeroMult_v2 χ₂ hχ₂ hzm₂
  have hstrip₃ : 0 < ρ₃.re ∧ ρ₃.re < 1 :=
    Work.ZeroFreeTables.re_mem_Ioo_of_zeroMult_v2 χ₃ hχ₃ hzm₃
  have hlam₁pos : 0 < lamOf q ρ₁ := by simp only [lamOf]; nlinarith [hstrip₁.2, hLqpos]
  have hlam12 : lamOf q ρ₁ ≤ lamOf q ρ₂ :=
    hR.2 χ₂ ρ₂ ⟨hχ₂, hzm₂, le_trans hbit₂ (by linarith)⟩
  have hlam13 : lamOf q ρ₁ ≤ lamOf q ρ₃ := le_trans hlam12 hlam23
  have hlam₁_le : lamOf q ρ₁ ≤ 6/7 := le_trans hlam12 (le_trans hlam23 hlam3)
  have hlam₁_le1 : lamOf q ρ₁ ≤ 1 := by linarith
  have hlam₁_sqrt : lamOf q ρ₁ ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) :=
    le_trans hlam₁_le1 hsqrt1
  have hlam₂pos : 0 < lamOf q ρ₂ := lt_of_lt_of_le hlam₁pos hlam12
  have hlam₂_le : lamOf q ρ₂ ≤ 6/7 := le_trans hlam23 hlam3
  have hlam₃pos : 0 < lamOf q ρ₃ := lt_of_lt_of_le hlam₁pos hlam13
  have hb1_bd : |ρ₁.re - 1| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) := by
    have h : ρ₁.re - 1 = -(lamOf q ρ₁ / Real.log (q : ℝ)) := by
      simp only [lamOf]; field_simp; ring
    rw [h, abs_neg, abs_of_nonneg (by positivity)]
    exact div_le_div_of_nonneg_right hlam₁_sqrt hLqpos.le
  have hre_low : 1 - Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) ≤ ρ₁.re := by
    have h : 1 - ρ₁.re = lamOf q ρ₁ / Real.log (q : ℝ) := lamOf_eq q ρ₁ hLqpos.ne'
    have h2 : lamOf q ρ₁ / Real.log (q : ℝ)
        ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) :=
      div_le_div_of_nonneg_right hlam₁_sqrt hLqpos.le
    linarith
  have hδbig1 : lamOf q ρ₁ ≤ δ * Real.log (q : ℝ) := le_trans hlam₁_le1 (by linarith)
  have hδbig2 : lamOf q ρ₂ ≤ δ * Real.log (q : ℝ) := le_trans hlam₂_le (by linarith)
  have hδbig3 : lamOf q ρ₃ ≤ δ * Real.log (q : ℝ) := le_trans hlam3 (by linarith)
  have hg1ne : ρ₁.im ≠ 0 := by
    intro h; rw [h, abs_zero] at hoff; linarith
  -- (0) the leading principal-character term
  have hb0 : (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
        ((1 : DirichletCharacter ℂ q) (n : ZMod q) / (n : ℂ) ^ ((ρ₁.re : ℝ) : ℂ)).re
          * T.f (Real.log n / Real.log (q : ℝ)))
      ≤ Real.log (q : ℝ) * T.F (-(lamOf q ρ₁)) + T.f 0 * (ε'/4) * Real.log (q : ℝ) := by
    have hb := hq₀P (q := q) hq0P (β := ρ₁.re) (γ := 0) hb1_bd (by rw [abs_zero]; linarith [hLqpos])
    simp only [Complex.ofReal_zero, zero_mul, add_zero] at hb
    have harg : (((ρ₁.re : ℝ) : ℂ) - 1) * ((Real.log (q : ℝ) : ℂ)) = ((-(lamOf q ρ₁) : ℝ) : ℂ) := by
      rw [show (((ρ₁.re : ℝ) : ℂ) - 1) = (((ρ₁.re - 1 : ℝ)) : ℂ) by push_cast; ring]
      rw [← Complex.ofReal_mul]
      congr 1
      simp only [lamOf]
      ring
    rw [harg] at hb
    have hconv : (∫ t in (0:ℝ)..T.x₀, Complex.exp (-(((-(lamOf q ρ₁) : ℝ) : ℂ) * (t : ℂ)))
          * ((T.f t : ℝ) : ℂ)).re = T.F (-(lamOf q ρ₁)) := Fc_of_exp_eq' T ((-(lamOf q ρ₁) : ℝ) : ℂ)
    rw [hconv] at hb
    exact hb

  -- the leading character term for χ₁
  have hs₁im : |((((ρ₁.re : ℝ) : ℂ) + ((ρ₁.im : ℝ) : ℂ) * Complex.I)).im| ≤ 10 * Real.log (q : ℝ) := by
    rw [show ((((ρ₁.re : ℝ) : ℂ) + ((ρ₁.im : ℝ) : ℂ) * Complex.I)).im = ρ₁.im by simp]
    linarith [hbit₁, hbit₁, hLlog, hLqpos]
  have hwin₁ : ‖(1:ℂ) + (((((ρ₁.re : ℝ) : ℂ) + ((ρ₁.im : ℝ) : ℂ) * Complex.I)).im : ℂ) * Complex.I - ρ₁‖ ≤ δ := by
    rw [one_add_mul_I_sub]
    rw [lamOf_eq q ρ₁ hLqpos.ne']
    rw [show ((((ρ₁.re : ℝ) : ℂ) + ((ρ₁.im : ℝ) : ℂ) * Complex.I)).im - ρ₁.im = (0:ℝ) / Real.log (q : ℝ) by
      rw [show ((((ρ₁.re : ℝ) : ℂ) + ((ρ₁.im : ℝ) : ℂ) * Complex.I)).im = ρ₁.im by simp]; simp]
    exact norm_win hLqpos hδ0 hlam₁pos.le hlam₁_le1 (by norm_num) hδLq5
  have hdiv₁ : (MeromorphicOn.divisor
      (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
      (Metric.closedBall 0 (|((((ρ₁.re : ℝ) : ℂ) + ((ρ₁.im : ℝ) : ℂ) * Complex.I)).im| + 2))) ρ₁ ≠ 0 := by
    rw [show ((((ρ₁.re : ℝ) : ℂ) + ((ρ₁.im : ℝ) : ℂ) * Complex.I)).im = ρ₁.im by simp]
    exact Work.ZeroFreeTables.divisor_ne_zero_of_zeroMult_v2 χ₁ hχ₁
      (Work.ZeroFreeTables.mem_closedBall_of_absre_le_one_v2 (by
        rw [abs_of_pos hstrip₁.1]; linarith [hstrip₁.2])) hzm₁
  have hzw₁ : ∀ u : ℂ, (MeromorphicOn.divisor
      (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
      (Metric.closedBall 0 (|((((ρ₁.re : ℝ) : ℂ) + ((ρ₁.im : ℝ) : ℂ) * Complex.I)).im| + 2))) u ≠ 0 →
      ‖(1:ℂ) + (((((ρ₁.re : ℝ) : ℂ) + ((ρ₁.im : ℝ) : ℂ) * Complex.I)).im : ℂ) * Complex.I - u‖ ≤ δ → u.re ≤ ((((ρ₁.re : ℝ) : ℂ) + ((ρ₁.im : ℝ) : ℂ) * Complex.I)).re := by
    have him : |((((ρ₁.re : ℝ) : ℂ) + ((ρ₁.im : ℝ) : ℂ) * Complex.I)).im| + δ ≤ 10 * L := by
      rw [show ((((ρ₁.re : ℝ) : ℂ) + ((ρ₁.im : ℝ) : ℂ) * Complex.I)).im = ρ₁.im by simp]
      linarith [hbit₁, hbit₁, hδ1, hL1]
    exact IsRectMin.window_left hR hLqpos hχ₁ him (by simp)
  have hb1 : (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
        (χ₁ (n : ZMod q) / (n : ℂ) ^ (((ρ₁.re : ℝ) : ℂ)
            + ((ρ₁.im : ℝ) : ℂ) * Complex.I)).re * T.f (Real.log n / Real.log (q : ℝ)))
      ≤ -Real.log (q : ℝ) * T.F 0 + T.f 0 * (1/6 + ε') * Real.log (q : ℝ) := by
    have hb := hq₀o (q := q) (s := (((ρ₁.re : ℝ) : ℂ) + ((ρ₁.im : ℝ) : ℂ) * Complex.I)) (ρ := ρ₁) hq0o χ₁ hχ₁
      (by rw [show ((((ρ₁.re : ℝ) : ℂ) + ((ρ₁.im : ℝ) : ℂ) * Complex.I)).re = ρ₁.re by simp]; exact hb1_bd) hs₁im (by rw [show ((((ρ₁.re : ℝ) : ℂ) + ((ρ₁.im : ℝ) : ℂ) * Complex.I)).re = ρ₁.re by simp]; exact hre_low) (hL52 χ₁ hχ₁) hdiv₁ hwin₁ hzw₁
    have harg : ((((ρ₁.re : ℝ) : ℂ) + ((ρ₁.im : ℝ) : ℂ) * Complex.I) - ρ₁) * ((Real.log (q : ℝ) : ℂ)) = ((0 : ℝ) : ℂ) := by
      rw [mul_ofReal_re_add_im]
      simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im, Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im, mul_zero, mul_one, zero_mul, zero_add, add_zero, sub_zero, mul_neg]
      push_cast
      ring
    rw [harg] at hb
    have hconv : (∫ t in (0:ℝ)..T.x₀, Complex.exp (-(((0 : ℝ) : ℂ) * (t : ℂ)))
          * ((T.f t : ℝ) : ℂ)).re = T.F 0 := Fc_of_exp_eq' T ((0 : ℝ) : ℂ)
    rw [hconv] at hb
    exact hb

  -- the leading character term for χ₂
  have hs₂im : |((((ρ₁.re : ℝ) : ℂ) + ((ρ₂.im : ℝ) : ℂ) * Complex.I)).im| ≤ 10 * Real.log (q : ℝ) := by
    rw [show ((((ρ₁.re : ℝ) : ℂ) + ((ρ₂.im : ℝ) : ℂ) * Complex.I)).im = ρ₂.im by simp]
    linarith [hbit₁, hbit₂, hLlog, hLqpos]
  have hwin₂ : ‖(1:ℂ) + (((((ρ₁.re : ℝ) : ℂ) + ((ρ₂.im : ℝ) : ℂ) * Complex.I)).im : ℂ) * Complex.I - ρ₂‖ ≤ δ := by
    rw [one_add_mul_I_sub]
    rw [lamOf_eq q ρ₂ hLqpos.ne']
    rw [show ((((ρ₁.re : ℝ) : ℂ) + ((ρ₂.im : ℝ) : ℂ) * Complex.I)).im - ρ₂.im = (0:ℝ) / Real.log (q : ℝ) by
      rw [show ((((ρ₁.re : ℝ) : ℂ) + ((ρ₂.im : ℝ) : ℂ) * Complex.I)).im = ρ₂.im by simp]; simp]
    exact norm_win hLqpos hδ0 hlam₂pos.le (by linarith [hlam₂_le]) (by norm_num) hδLq5
  have hdiv₂ : (MeromorphicOn.divisor
      (DirichletCharacter.completedLFunction χ₂.primitiveCharacter)
      (Metric.closedBall 0 (|((((ρ₁.re : ℝ) : ℂ) + ((ρ₂.im : ℝ) : ℂ) * Complex.I)).im| + 2))) ρ₂ ≠ 0 := by
    rw [show ((((ρ₁.re : ℝ) : ℂ) + ((ρ₂.im : ℝ) : ℂ) * Complex.I)).im = ρ₂.im by simp]
    exact Work.ZeroFreeTables.divisor_ne_zero_of_zeroMult_v2 χ₂ hχ₂
      (Work.ZeroFreeTables.mem_closedBall_of_absre_le_one_v2 (by
        rw [abs_of_pos hstrip₂.1]; linarith [hstrip₂.2])) hzm₂
  have hzw₂ : ∀ u : ℂ, (MeromorphicOn.divisor
      (DirichletCharacter.completedLFunction χ₂.primitiveCharacter)
      (Metric.closedBall 0 (|((((ρ₁.re : ℝ) : ℂ) + ((ρ₂.im : ℝ) : ℂ) * Complex.I)).im| + 2))) u ≠ 0 →
      ‖(1:ℂ) + (((((ρ₁.re : ℝ) : ℂ) + ((ρ₂.im : ℝ) : ℂ) * Complex.I)).im : ℂ) * Complex.I - u‖ ≤ δ → u.re ≤ ((((ρ₁.re : ℝ) : ℂ) + ((ρ₂.im : ℝ) : ℂ) * Complex.I)).re := by
    have him : |((((ρ₁.re : ℝ) : ℂ) + ((ρ₂.im : ℝ) : ℂ) * Complex.I)).im| + δ ≤ 10 * L := by
      rw [show ((((ρ₁.re : ℝ) : ℂ) + ((ρ₂.im : ℝ) : ℂ) * Complex.I)).im = ρ₂.im by simp]
      linarith [hbit₁, hbit₂, hδ1, hL1]
    exact IsRectMin.window_left hR hLqpos hχ₂ him (by simp)
  have hb2 : (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
        (χ₂ (n : ZMod q) / (n : ℂ) ^ (((ρ₁.re : ℝ) : ℂ)
            + ((ρ₂.im : ℝ) : ℂ) * Complex.I)).re * T.f (Real.log n / Real.log (q : ℝ)))
      ≤ -Real.log (q : ℝ) * T.F (lamOf q ρ₂ - lamOf q ρ₁) + T.f 0 * (1/6 + ε') * Real.log (q : ℝ) := by
    have hb := hq₀o (q := q) (s := (((ρ₁.re : ℝ) : ℂ) + ((ρ₂.im : ℝ) : ℂ) * Complex.I)) (ρ := ρ₂) hq0o χ₂ hχ₂
      (by rw [show ((((ρ₁.re : ℝ) : ℂ) + ((ρ₂.im : ℝ) : ℂ) * Complex.I)).re = ρ₁.re by simp]; exact hb1_bd) hs₂im (by rw [show ((((ρ₁.re : ℝ) : ℂ) + ((ρ₂.im : ℝ) : ℂ) * Complex.I)).re = ρ₁.re by simp]; exact hre_low) (hL52 χ₂ hχ₂) hdiv₂ hwin₂ hzw₂
    have harg : ((((ρ₁.re : ℝ) : ℂ) + ((ρ₂.im : ℝ) : ℂ) * Complex.I) - ρ₂) * ((Real.log (q : ℝ) : ℂ)) = (((lamOf q ρ₂ - lamOf q ρ₁) : ℝ) : ℂ) := by
      rw [mul_ofReal_re_add_im]
      simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im, Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im, mul_zero, mul_one, zero_mul, zero_add, add_zero, sub_zero, mul_neg]
      simp only [lamOf]
      push_cast
      ring
    rw [harg] at hb
    have hconv : (∫ t in (0:ℝ)..T.x₀, Complex.exp (-((((lamOf q ρ₂ - lamOf q ρ₁) : ℝ) : ℂ) * (t : ℂ)))
          * ((T.f t : ℝ) : ℂ)).re = T.F (lamOf q ρ₂ - lamOf q ρ₁) := Fc_of_exp_eq' T (((lamOf q ρ₂ - lamOf q ρ₁) : ℝ) : ℂ)
    rw [hconv] at hb
    exact hb

  -- the leading character term for χ₃
  have hs₃im : |((((ρ₁.re : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ) * Complex.I)).im| ≤ 10 * Real.log (q : ℝ) := by
    rw [show ((((ρ₁.re : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ) * Complex.I)).im = ρ₃.im by simp]
    linarith [hbit₁, hbit₃, hLlog, hLqpos]
  have hwin₃ : ‖(1:ℂ) + (((((ρ₁.re : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ) * Complex.I)).im : ℂ) * Complex.I - ρ₃‖ ≤ δ := by
    rw [one_add_mul_I_sub]
    rw [lamOf_eq q ρ₃ hLqpos.ne']
    rw [show ((((ρ₁.re : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ) * Complex.I)).im - ρ₃.im = (0:ℝ) / Real.log (q : ℝ) by
      rw [show ((((ρ₁.re : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ) * Complex.I)).im = ρ₃.im by simp]; simp]
    exact norm_win hLqpos hδ0 hlam₃pos.le (by linarith [hlam3]) (by norm_num) hδLq5
  have hdiv₃ : (MeromorphicOn.divisor
      (DirichletCharacter.completedLFunction χ₃.primitiveCharacter)
      (Metric.closedBall 0 (|((((ρ₁.re : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ) * Complex.I)).im| + 2))) ρ₃ ≠ 0 := by
    rw [show ((((ρ₁.re : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ) * Complex.I)).im = ρ₃.im by simp]
    exact Work.ZeroFreeTables.divisor_ne_zero_of_zeroMult_v2 χ₃ hχ₃
      (Work.ZeroFreeTables.mem_closedBall_of_absre_le_one_v2 (by
        rw [abs_of_pos hstrip₃.1]; linarith [hstrip₃.2])) hzm₃
  have hzw₃ : ∀ u : ℂ, (MeromorphicOn.divisor
      (DirichletCharacter.completedLFunction χ₃.primitiveCharacter)
      (Metric.closedBall 0 (|((((ρ₁.re : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ) * Complex.I)).im| + 2))) u ≠ 0 →
      ‖(1:ℂ) + (((((ρ₁.re : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ) * Complex.I)).im : ℂ) * Complex.I - u‖ ≤ δ → u.re ≤ ((((ρ₁.re : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ) * Complex.I)).re := by
    have him : |((((ρ₁.re : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ) * Complex.I)).im| + δ ≤ 10 * L := by
      rw [show ((((ρ₁.re : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ) * Complex.I)).im = ρ₃.im by simp]
      linarith [hbit₁, hbit₃, hδ1, hL1]
    exact IsRectMin.window_left hR hLqpos hχ₃ him (by simp)
  have hb3 : (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
        (χ₃ (n : ZMod q) / (n : ℂ) ^ (((ρ₁.re : ℝ) : ℂ)
            + ((ρ₃.im : ℝ) : ℂ) * Complex.I)).re * T.f (Real.log n / Real.log (q : ℝ)))
      ≤ -Real.log (q : ℝ) * T.F (lamOf q ρ₃ - lamOf q ρ₁) + T.f 0 * (1/6 + ε') * Real.log (q : ℝ) := by
    have hb := hq₀o (q := q) (s := (((ρ₁.re : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ) * Complex.I)) (ρ := ρ₃) hq0o χ₃ hχ₃
      (by rw [show ((((ρ₁.re : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ) * Complex.I)).re = ρ₁.re by simp]; exact hb1_bd) hs₃im (by rw [show ((((ρ₁.re : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ) * Complex.I)).re = ρ₁.re by simp]; exact hre_low) (hL52 χ₃ hχ₃) hdiv₃ hwin₃ hzw₃
    have harg : ((((ρ₁.re : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ) * Complex.I) - ρ₃) * ((Real.log (q : ℝ) : ℂ)) = (((lamOf q ρ₃ - lamOf q ρ₁) : ℝ) : ℂ) := by
      rw [mul_ofReal_re_add_im]
      simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im, Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im, mul_zero, mul_one, zero_mul, zero_add, add_zero, sub_zero, mul_neg]
      simp only [lamOf]
      push_cast
      ring
    rw [harg] at hb
    have hconv : (∫ t in (0:ℝ)..T.x₀, Complex.exp (-((((lamOf q ρ₃ - lamOf q ρ₁) : ℝ) : ℂ) * (t : ℂ)))
          * ((T.f t : ℝ) : ℂ)).re = T.F (lamOf q ρ₃ - lamOf q ρ₁) := Fc_of_exp_eq' T (((lamOf q ρ₃ - lamOf q ρ₁) : ℝ) : ℂ)
    rw [hconv] at hb
    exact hb

  -- (4)..(7) the four "self" pair terms
  have hs4im : |(((ρ₁.re : ℝ) : ℂ) + (((ρ₁.im : ℝ) : ℂ) + ((ρ₂.im : ℝ) : ℂ)) * Complex.I).im|
      ≤ 10 * Real.log (q : ℝ) := by
    rw [show (((ρ₁.re : ℝ) : ℂ) + (((ρ₁.im : ℝ) : ℂ) + ((ρ₂.im : ℝ) : ℂ)) * Complex.I).im
      = ρ₁.im + ρ₂.im by simp]
    linarith [abs_add_le ρ₁.im ρ₂.im, hbit₁, hbit₂, hLlog, hLqpos]
  have hzw4 : ∀ u : ℂ, (MeromorphicOn.divisor
        (DirichletCharacter.completedLFunction (χ₁ * χ₂).primitiveCharacter)
        (Metric.closedBall 0 (|(((ρ₁.re : ℝ) : ℂ)
          + (((ρ₁.im : ℝ) : ℂ) + ((ρ₂.im : ℝ) : ℂ)) * Complex.I).im| + 2))) u ≠ 0 →
      ‖(1:ℂ) + ((((ρ₁.re : ℝ) : ℂ) + (((ρ₁.im : ℝ) : ℂ) + ((ρ₂.im : ℝ) : ℂ)) * Complex.I).im : ℂ)
        * Complex.I - u‖ ≤ δ →
      u.re ≤ (((ρ₁.re : ℝ) : ℂ) + (((ρ₁.im : ℝ) : ℂ) + ((ρ₂.im : ℝ) : ℂ)) * Complex.I).re := by
    have him : |(((ρ₁.re : ℝ) : ℂ) + (((ρ₁.im : ℝ) : ℂ) + ((ρ₂.im : ℝ) : ℂ)) * Complex.I).im|
        + δ ≤ 10 * L := by
      rw [show (((ρ₁.re : ℝ) : ℂ) + (((ρ₁.im : ℝ) : ℂ) + ((ρ₂.im : ℝ) : ℂ)) * Complex.I).im
        = ρ₁.im + ρ₂.im by simp]
      linarith [abs_add_le ρ₁.im ρ₂.im, hbit₁, hbit₂, hδ1, hL1]
    exact IsRectMin.window_left hR hLqpos hne4 him (by simp)
  have hb4 : (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
        ((χ₁ * χ₂) (n : ZMod q) / (n : ℂ) ^ (((ρ₁.re : ℝ) : ℂ)
            + (((ρ₁.im : ℝ) : ℂ) + ((ρ₂.im : ℝ) : ℂ)) * Complex.I)).re
          * T.f (Real.log n / Real.log (q : ℝ)))
      ≤ T.f 0 * (1/6 + ε') * Real.log (q : ℝ) :=
    hq₀s (q := q) (s := ((ρ₁.re : ℝ) : ℂ) + (((ρ₁.im : ℝ) : ℂ) + ((ρ₂.im : ℝ) : ℂ)) * Complex.I)
      hq0s (χ₁ * χ₂) hne4 (by rw [show ((((ρ₁.re : ℝ) : ℂ) + (((ρ₁.im : ℝ) : ℂ) + ((ρ₂.im : ℝ) : ℂ)) * Complex.I)).re = ρ₁.re by simp]; exact hb1_bd) hs4im (by rw [show ((((ρ₁.re : ℝ) : ℂ) + (((ρ₁.im : ℝ) : ℂ) + ((ρ₂.im : ℝ) : ℂ)) * Complex.I)).re = ρ₁.re by simp]; exact hre_low) (hL52 (χ₁ * χ₂) hne4) hzw4
  have hs5im : |(((ρ₁.re : ℝ) : ℂ) + (((ρ₁.im : ℝ) : ℂ) - ((ρ₂.im : ℝ) : ℂ)) * Complex.I).im|
      ≤ 10 * Real.log (q : ℝ) := by
    rw [show (((ρ₁.re : ℝ) : ℂ) + (((ρ₁.im : ℝ) : ℂ) - ((ρ₂.im : ℝ) : ℂ)) * Complex.I).im
      = ρ₁.im - ρ₂.im by simp]
    linarith [abs_sub ρ₁.im ρ₂.im, hbit₁, hbit₂, hLlog, hLqpos]
  have hzw5 : ∀ u : ℂ, (MeromorphicOn.divisor
        (DirichletCharacter.completedLFunction (χ₁ * χ₂⁻¹).primitiveCharacter)
        (Metric.closedBall 0 (|(((ρ₁.re : ℝ) : ℂ)
          + (((ρ₁.im : ℝ) : ℂ) - ((ρ₂.im : ℝ) : ℂ)) * Complex.I).im| + 2))) u ≠ 0 →
      ‖(1:ℂ) + ((((ρ₁.re : ℝ) : ℂ) + (((ρ₁.im : ℝ) : ℂ) - ((ρ₂.im : ℝ) : ℂ)) * Complex.I).im : ℂ)
        * Complex.I - u‖ ≤ δ →
      u.re ≤ (((ρ₁.re : ℝ) : ℂ) + (((ρ₁.im : ℝ) : ℂ) - ((ρ₂.im : ℝ) : ℂ)) * Complex.I).re := by
    have him : |(((ρ₁.re : ℝ) : ℂ) + (((ρ₁.im : ℝ) : ℂ) - ((ρ₂.im : ℝ) : ℂ)) * Complex.I).im|
        + δ ≤ 10 * L := by
      rw [show (((ρ₁.re : ℝ) : ℂ) + (((ρ₁.im : ℝ) : ℂ) - ((ρ₂.im : ℝ) : ℂ)) * Complex.I).im
        = ρ₁.im - ρ₂.im by simp]
      linarith [abs_sub ρ₁.im ρ₂.im, hbit₁, hbit₂, hδ1, hL1]
    exact IsRectMin.window_left hR hLqpos hne5 him (by simp)
  have hb5 : (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
        ((χ₁ * χ₂⁻¹) (n : ZMod q) / (n : ℂ) ^ (((ρ₁.re : ℝ) : ℂ)
            + (((ρ₁.im : ℝ) : ℂ) - ((ρ₂.im : ℝ) : ℂ)) * Complex.I)).re
          * T.f (Real.log n / Real.log (q : ℝ)))
      ≤ T.f 0 * (1/6 + ε') * Real.log (q : ℝ) :=
    hq₀s (q := q) (s := ((ρ₁.re : ℝ) : ℂ) + (((ρ₁.im : ℝ) : ℂ) - ((ρ₂.im : ℝ) : ℂ)) * Complex.I)
      hq0s (χ₁ * χ₂⁻¹) hne5 (by rw [show ((((ρ₁.re : ℝ) : ℂ) + (((ρ₁.im : ℝ) : ℂ) - ((ρ₂.im : ℝ) : ℂ)) * Complex.I)).re = ρ₁.re by simp]; exact hb1_bd) hs5im (by rw [show ((((ρ₁.re : ℝ) : ℂ) + (((ρ₁.im : ℝ) : ℂ) - ((ρ₂.im : ℝ) : ℂ)) * Complex.I)).re = ρ₁.re by simp]; exact hre_low) (hL52 (χ₁ * χ₂⁻¹) hne5) hzw5
  have hs6im : |(((ρ₁.re : ℝ) : ℂ) + (((ρ₁.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I).im|
      ≤ 10 * Real.log (q : ℝ) := by
    rw [show (((ρ₁.re : ℝ) : ℂ) + (((ρ₁.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I).im
      = ρ₁.im + ρ₃.im by simp]
    linarith [abs_add_le ρ₁.im ρ₃.im, hbit₁, hbit₃, hLlog, hLqpos]
  have hzw6 : ∀ u : ℂ, (MeromorphicOn.divisor
        (DirichletCharacter.completedLFunction (χ₁ * χ₃).primitiveCharacter)
        (Metric.closedBall 0 (|(((ρ₁.re : ℝ) : ℂ)
          + (((ρ₁.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I).im| + 2))) u ≠ 0 →
      ‖(1:ℂ) + ((((ρ₁.re : ℝ) : ℂ) + (((ρ₁.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I).im : ℂ)
        * Complex.I - u‖ ≤ δ →
      u.re ≤ (((ρ₁.re : ℝ) : ℂ) + (((ρ₁.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I).re := by
    have him : |(((ρ₁.re : ℝ) : ℂ) + (((ρ₁.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I).im|
        + δ ≤ 10 * L := by
      rw [show (((ρ₁.re : ℝ) : ℂ) + (((ρ₁.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I).im
        = ρ₁.im + ρ₃.im by simp]
      linarith [abs_add_le ρ₁.im ρ₃.im, hbit₁, hbit₃, hδ1, hL1]
    exact IsRectMin.window_left hR hLqpos hne6 him (by simp)
  have hb6 : (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
        ((χ₁ * χ₃) (n : ZMod q) / (n : ℂ) ^ (((ρ₁.re : ℝ) : ℂ)
            + (((ρ₁.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I)).re
          * T.f (Real.log n / Real.log (q : ℝ)))
      ≤ T.f 0 * (1/6 + ε') * Real.log (q : ℝ) :=
    hq₀s (q := q) (s := ((ρ₁.re : ℝ) : ℂ) + (((ρ₁.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I)
      hq0s (χ₁ * χ₃) hne6 (by rw [show ((((ρ₁.re : ℝ) : ℂ) + (((ρ₁.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I)).re = ρ₁.re by simp]; exact hb1_bd) hs6im (by rw [show ((((ρ₁.re : ℝ) : ℂ) + (((ρ₁.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I)).re = ρ₁.re by simp]; exact hre_low) (hL52 (χ₁ * χ₃) hne6) hzw6
  have hs7im : |(((ρ₁.re : ℝ) : ℂ) + (((ρ₁.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ)) * Complex.I).im|
      ≤ 10 * Real.log (q : ℝ) := by
    rw [show (((ρ₁.re : ℝ) : ℂ) + (((ρ₁.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ)) * Complex.I).im
      = ρ₁.im - ρ₃.im by simp]
    linarith [abs_sub ρ₁.im ρ₃.im, hbit₁, hbit₃, hLlog, hLqpos]
  have hzw7 : ∀ u : ℂ, (MeromorphicOn.divisor
        (DirichletCharacter.completedLFunction (χ₁ * χ₃⁻¹).primitiveCharacter)
        (Metric.closedBall 0 (|(((ρ₁.re : ℝ) : ℂ)
          + (((ρ₁.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ)) * Complex.I).im| + 2))) u ≠ 0 →
      ‖(1:ℂ) + ((((ρ₁.re : ℝ) : ℂ) + (((ρ₁.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ)) * Complex.I).im : ℂ)
        * Complex.I - u‖ ≤ δ →
      u.re ≤ (((ρ₁.re : ℝ) : ℂ) + (((ρ₁.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ)) * Complex.I).re := by
    have him : |(((ρ₁.re : ℝ) : ℂ) + (((ρ₁.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ)) * Complex.I).im|
        + δ ≤ 10 * L := by
      rw [show (((ρ₁.re : ℝ) : ℂ) + (((ρ₁.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ)) * Complex.I).im
        = ρ₁.im - ρ₃.im by simp]
      linarith [abs_sub ρ₁.im ρ₃.im, hbit₁, hbit₃, hδ1, hL1]
    exact IsRectMin.window_left hR hLqpos hne7 him (by simp)
  have hb7 : (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
        ((χ₁ * χ₃⁻¹) (n : ZMod q) / (n : ℂ) ^ (((ρ₁.re : ℝ) : ℂ)
            + (((ρ₁.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ)) * Complex.I)).re
          * T.f (Real.log n / Real.log (q : ℝ)))
      ≤ T.f 0 * (1/6 + ε') * Real.log (q : ℝ) :=
    hq₀s (q := q) (s := ((ρ₁.re : ℝ) : ℂ) + (((ρ₁.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ)) * Complex.I)
      hq0s (χ₁ * χ₃⁻¹) hne7 (by rw [show ((((ρ₁.re : ℝ) : ℂ) + (((ρ₁.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ)) * Complex.I)).re = ρ₁.re by simp]; exact hb1_bd) hs7im (by rw [show ((((ρ₁.re : ℝ) : ℂ) + (((ρ₁.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ)) * Complex.I)).re = ρ₁.re by simp]; exact hre_low) (hL52 (χ₁ * χ₃⁻¹) hne7) hzw7
  -- the triple shift parameters and the (A)-credits
  set mu0 : ℝ := (ρ₁.im + ρ₂.im + ρ₃.im) * Real.log (q : ℝ) with hmu0def
  set mu1 : ℝ := (ρ₁.im + ρ₂.im - ρ₃.im) * Real.log (q : ℝ) with hmu1def
  set mu2 : ℝ := (ρ₁.im - ρ₂.im + ρ₃.im) * Real.log (q : ℝ) with hmu2def
  set mu3 : ℝ := (-ρ₁.im + ρ₂.im + ρ₃.im) * Real.log (q : ℝ) with hmu3def
  set crd0 : ℝ := (if (χ₁ * χ₂ * χ₃ = 1 ∧ |mu0| ≤ 4) then Real.log (q : ℝ)
      * (T.Fc ((mu0 : ℂ) * Complex.I)).re else 0) with hcrd0
  set crd1 : ℝ := (if (χ₁ * χ₂ * χ₃⁻¹ = 1 ∧ |mu1| ≤ 4) then Real.log (q : ℝ)
      * (T.Fc ((mu1 : ℂ) * Complex.I)).re else 0) with hcrd1
  set crd2 : ℝ := (if (χ₁ * χ₂⁻¹ * χ₃ = 1 ∧ |mu2| ≤ 4) then Real.log (q : ℝ)
      * (T.Fc ((mu2 : ℂ) * Complex.I)).re else 0) with hcrd2
  set crd3 : ℝ := (if (χ₁⁻¹ * χ₂ * χ₃ = 1 ∧ |mu3| ≤ 4) then Real.log (q : ℝ)
      * (T.Fc ((mu3 : ℂ) * Complex.I)).re else 0) with hcrd3




  -- (10) the triple character χ₁ * χ₂ * χ₃
  have hγ0 : |ρ₁.im + ρ₂.im + ρ₃.im| ≤ 10 * Real.log (q : ℝ) := by
    linarith [abs_add_le (ρ₁.im + ρ₂.im) ρ₃.im, abs_add_le ρ₁.im ρ₂.im, hbit₁, hbit₂, hbit₃, hLlog, hLqpos]
  have hbt0 : (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
        ((χ₁ * χ₂ * χ₃) (n : ZMod q) / (n : ℂ) ^ (((ρ₁.re : ℝ) : ℂ)
            + (((ρ₁.im : ℝ) : ℂ) + ((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I)).re * T.f (Real.log n / Real.log (q : ℝ)))
      ≤ T.f 0 * (1/6 + ε') * Real.log (q : ℝ) + 2 * crd0 := by
    by_cases h0 : (χ₁ * χ₂ * χ₃ = 1 ∧ |mu0| ≤ 4)
    · have hb := hq₀P (q := q) hq0P (β := ρ₁.re) (γ := ρ₁.im + ρ₂.im + ρ₃.im) hb1_bd hγ0
      rw [h0.1]
      rw [show (((ρ₁.im + ρ₂.im + ρ₃.im : ℝ) : ℂ)) = (((ρ₁.im : ℝ) : ℂ) + ((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) by push_cast; ring] at hb
      have harg : ((((ρ₁.re : ℝ) : ℂ) + (((ρ₁.im : ℝ) : ℂ) + ((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I) - 1) * ((Real.log (q : ℝ) : ℂ)) = ((((-(lamOf q ρ₁) : ℝ) : ℂ) + (mu0 : ℂ) * Complex.I)) := by
        rw [mul_ofReal_re_add_im]
        simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im, Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im, mul_zero, mul_one, zero_mul, zero_add, add_zero, sub_zero, mul_neg]
        rw [hmu0def]
        simp only [lamOf]
        push_cast
        ring
      rw [harg] at hb
      have hconv : (∫ t in (0:ℝ)..T.x₀, Complex.exp (-(((((-(lamOf q ρ₁) : ℝ) : ℂ) + (mu0 : ℂ) * Complex.I)) * (t : ℂ)))
            * ((T.f t : ℝ) : ℂ)).re = (T.Fc ((((-(lamOf q ρ₁) : ℝ) : ℂ) + (mu0 : ℂ) * Complex.I))).re := Fc_of_exp_eq' T ((((-(lamOf q ρ₁) : ℝ) : ℂ) + (mu0 : ℂ) * Complex.I))
      rw [hconv] at hb
      have hcr : crd0 = Real.log (q : ℝ) * (T.Fc ((mu0 : ℂ) * Complex.I)).re := by
        rw [hcrd0, if_pos h0]
      rw [hcr]
      have hAj := hA (lamOf q ρ₁) mu0 hlam₁pos.le hlam₁_le h0.2
      have hmult := mul_le_mul_of_nonneg_left hAj hLqpos.le
      have hfl : 0 ≤ T.f 0 * ε' * Real.log (q : ℝ) :=
        mul_nonneg (mul_nonneg T.f0_pos.le hε'.le) hLqpos.le
      have hsq : T.f 0 * (ε'/4) * Real.log (q : ℝ) ≤ T.f 0 * ε' * Real.log (q : ℝ) := by
        have h1 : (0:ℝ) ≤ T.f 0 * Real.log (q : ℝ) := mul_nonneg T.f0_pos.le hLqpos.le
        nlinarith only [h1, hε']
      have hmult' : Real.log (q : ℝ)
            * (T.Fc ((((-(lamOf q ρ₁) : ℝ) : ℂ) + (mu0 : ℂ) * Complex.I))).re
          ≤ Real.log (q : ℝ) * (2 * (T.Fc ((mu0 : ℂ) * Complex.I)).re)
            + Real.log (q : ℝ) * (T.f 0 / 6) := by
        have h := mul_le_mul_of_nonneg_left hAj hLqpos.le
        linarith only [h]
      have hkey : Real.log (q : ℝ) * (2 * (T.Fc ((mu0 : ℂ) * Complex.I)).re)
            + Real.log (q : ℝ) * (T.f 0 / 6) + T.f 0 * ε' * Real.log (q : ℝ)
          = T.f 0 * (1/6 + ε') * Real.log (q : ℝ)
            + 2 * (Real.log (q : ℝ) * (T.Fc ((mu0 : ℂ) * Complex.I)).re) := by ring
      calc (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
            ((1 : DirichletCharacter ℂ q) (n : ZMod q) / (n : ℂ) ^ (((ρ₁.re : ℝ) : ℂ)
                + (((ρ₁.im : ℝ) : ℂ) + ((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I)).re
              * T.f (Real.log n / Real.log (q : ℝ)))
          ≤ Real.log (q : ℝ) * (T.Fc ((((-(lamOf q ρ₁) : ℝ) : ℂ) + (mu0 : ℂ) * Complex.I))).re
            + T.f 0 * (ε'/4) * Real.log (q : ℝ) := hb
        _ ≤ (Real.log (q : ℝ) * (2 * (T.Fc ((mu0 : ℂ) * Complex.I)).re)
              + Real.log (q : ℝ) * (T.f 0 / 6)) + T.f 0 * ε' * Real.log (q : ℝ) := by
              linarith only [hmult', hsq]
        _ = T.f 0 * (1/6 + ε') * Real.log (q : ℝ)
              + 2 * (Real.log (q : ℝ) * (T.Fc ((mu0 : ℂ) * Complex.I)).re) := hkey
    · rw [hcrd0, if_neg h0]
      by_cases hψ0 : χ₁ * χ₂ * χ₃ = 1
      · have hμ0 : 4 ≤ |mu0| := by
          by_contra hc
          exact h0 ⟨hψ0, le_of_lt (not_le.mp hc)⟩
        have hb := hq₀P (q := q) hq0P (β := ρ₁.re) (γ := ρ₁.im + ρ₂.im + ρ₃.im) hb1_bd hγ0
        rw [hψ0]
        rw [show (((ρ₁.im + ρ₂.im + ρ₃.im : ℝ) : ℂ)) = (((ρ₁.im : ℝ) : ℂ) + ((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) by push_cast; ring] at hb
        have harg : ((((ρ₁.re : ℝ) : ℂ) + (((ρ₁.im : ℝ) : ℂ) + ((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I) - 1) * ((Real.log (q : ℝ) : ℂ)) = ((((-(lamOf q ρ₁) : ℝ) : ℂ) + (mu0 : ℂ) * Complex.I)) := by
          rw [mul_ofReal_re_add_im]
          simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im, Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im, mul_zero, mul_one, zero_mul, zero_add, add_zero, sub_zero, mul_neg]
          rw [hmu0def]
          simp only [lamOf]
          push_cast
          ring
        rw [harg] at hb
        have hconv : (∫ t in (0:ℝ)..T.x₀, Complex.exp (-(((((-(lamOf q ρ₁) : ℝ) : ℂ) + (mu0 : ℂ) * Complex.I)) * (t : ℂ)))
              * ((T.f t : ℝ) : ℂ)).re = (T.Fc ((((-(lamOf q ρ₁) : ℝ) : ℂ) + (mu0 : ℂ) * Complex.I))).re := Fc_of_exp_eq' T ((((-(lamOf q ρ₁) : ℝ) : ℂ) + (mu0 : ℂ) * Complex.I))
        rw [hconv] at hb
        have hBj := hB (lamOf q ρ₁) mu0 hlam₁pos.le hlam₁_le hμ0
        have hmult := mul_le_mul_of_nonneg_left hBj hLqpos.le
        have hfl : 0 ≤ T.f 0 * ε' * Real.log (q : ℝ) :=
          mul_nonneg (mul_nonneg T.f0_pos.le hε'.le) hLqpos.le
        have hsq : T.f 0 * (ε'/4) * Real.log (q : ℝ) ≤ T.f 0 * ε' * Real.log (q : ℝ) := by
          have h1 : (0:ℝ) ≤ T.f 0 * Real.log (q : ℝ) := mul_nonneg T.f0_pos.le hLqpos.le
          nlinarith only [h1, hε']
        nlinarith only [hb, hmult, hsq]
      · have himT0 : |((((ρ₁.re : ℝ) : ℂ) + (((ρ₁.im : ℝ) : ℂ) + ((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I)).im| ≤ 10 * Real.log (q : ℝ) := by
          rw [show ((((ρ₁.re : ℝ) : ℂ) + (((ρ₁.im : ℝ) : ℂ) + ((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I)).im = ρ₁.im + ρ₂.im + ρ₃.im by simp]
          exact hγ0
        have hzwT0 : ∀ u : ℂ, (MeromorphicOn.divisor
            (DirichletCharacter.completedLFunction (χ₁ * χ₂ * χ₃).primitiveCharacter)
            (Metric.closedBall 0 (|((((ρ₁.re : ℝ) : ℂ) + (((ρ₁.im : ℝ) : ℂ) + ((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I)).im| + 2))) u ≠ 0 →
            ‖(1:ℂ) + (((((ρ₁.re : ℝ) : ℂ) + (((ρ₁.im : ℝ) : ℂ) + ((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I)).im : ℂ) * Complex.I - u‖ ≤ δ → u.re ≤ ((((ρ₁.re : ℝ) : ℂ) + (((ρ₁.im : ℝ) : ℂ) + ((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I)).re := by
          have him : |((((ρ₁.re : ℝ) : ℂ) + (((ρ₁.im : ℝ) : ℂ) + ((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I)).im| + δ ≤ 10 * L := by
            rw [show ((((ρ₁.re : ℝ) : ℂ) + (((ρ₁.im : ℝ) : ℂ) + ((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I)).im = ρ₁.im + ρ₂.im + ρ₃.im by simp]
            linarith [abs_add_le (ρ₁.im + ρ₂.im) ρ₃.im, abs_add_le ρ₁.im ρ₂.im, hbit₁, hbit₂, hbit₃, hδ1, hL1]
          exact IsRectMin.window_left hR hLqpos hψ0 him (by simp)
        have hb := hq₀s (q := q) (s := (((ρ₁.re : ℝ) : ℂ) + (((ρ₁.im : ℝ) : ℂ) + ((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I)) hq0s (χ₁ * χ₂ * χ₃) hψ0
          (by rw [show ((((ρ₁.re : ℝ) : ℂ) + (((ρ₁.im : ℝ) : ℂ) + ((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I)).re = ρ₁.re by simp]; exact hb1_bd) himT0
          (by rw [show ((((ρ₁.re : ℝ) : ℂ) + (((ρ₁.im : ℝ) : ℂ) + ((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I)).re = ρ₁.re by simp]; exact hre_low)
          (hL52 (χ₁ * χ₂ * χ₃) hψ0) hzwT0
        simpa using hb


  -- (11) the triple character χ₁ * χ₂ * χ₃⁻¹
  have hγ1 : |ρ₁.im + ρ₂.im - ρ₃.im| ≤ 10 * Real.log (q : ℝ) := by
    linarith [abs_sub (ρ₁.im + ρ₂.im) ρ₃.im, abs_add_le ρ₁.im ρ₂.im, hbit₁, hbit₂, hbit₃, hLlog, hLqpos]
  have hbt1 : (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
        ((χ₁ * χ₂ * χ₃⁻¹) (n : ZMod q) / (n : ℂ) ^ (((ρ₁.re : ℝ) : ℂ)
            + (((ρ₁.im : ℝ) : ℂ) + ((ρ₂.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ)) * Complex.I)).re * T.f (Real.log n / Real.log (q : ℝ)))
      ≤ T.f 0 * (1/6 + ε') * Real.log (q : ℝ) + 2 * crd1 := by
    by_cases h1 : (χ₁ * χ₂ * χ₃⁻¹ = 1 ∧ |mu1| ≤ 4)
    · have hb := hq₀P (q := q) hq0P (β := ρ₁.re) (γ := ρ₁.im + ρ₂.im - ρ₃.im) hb1_bd hγ1
      rw [h1.1]
      rw [show (((ρ₁.im + ρ₂.im - ρ₃.im : ℝ) : ℂ)) = (((ρ₁.im : ℝ) : ℂ) + ((ρ₂.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ)) by push_cast; ring] at hb
      have harg : ((((ρ₁.re : ℝ) : ℂ) + (((ρ₁.im : ℝ) : ℂ) + ((ρ₂.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ)) * Complex.I) - 1) * ((Real.log (q : ℝ) : ℂ)) = ((((-(lamOf q ρ₁) : ℝ) : ℂ) + (mu1 : ℂ) * Complex.I)) := by
        rw [mul_ofReal_re_add_im]
        simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im, Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im, mul_zero, mul_one, zero_mul, zero_add, add_zero, sub_zero, mul_neg]
        rw [hmu1def]
        simp only [lamOf]
        push_cast
        ring
      rw [harg] at hb
      have hconv : (∫ t in (0:ℝ)..T.x₀, Complex.exp (-(((((-(lamOf q ρ₁) : ℝ) : ℂ) + (mu1 : ℂ) * Complex.I)) * (t : ℂ)))
            * ((T.f t : ℝ) : ℂ)).re = (T.Fc ((((-(lamOf q ρ₁) : ℝ) : ℂ) + (mu1 : ℂ) * Complex.I))).re := Fc_of_exp_eq' T ((((-(lamOf q ρ₁) : ℝ) : ℂ) + (mu1 : ℂ) * Complex.I))
      rw [hconv] at hb
      have hcr : crd1 = Real.log (q : ℝ) * (T.Fc ((mu1 : ℂ) * Complex.I)).re := by
        rw [hcrd1, if_pos h1]
      rw [hcr]
      have hAj := hA (lamOf q ρ₁) mu1 hlam₁pos.le hlam₁_le h1.2
      have hmult := mul_le_mul_of_nonneg_left hAj hLqpos.le
      have hfl : 0 ≤ T.f 0 * ε' * Real.log (q : ℝ) :=
        mul_nonneg (mul_nonneg T.f0_pos.le hε'.le) hLqpos.le
      have hsq : T.f 0 * (ε'/4) * Real.log (q : ℝ) ≤ T.f 0 * ε' * Real.log (q : ℝ) := by
        have h1 : (0:ℝ) ≤ T.f 0 * Real.log (q : ℝ) := mul_nonneg T.f0_pos.le hLqpos.le
        nlinarith only [h1, hε']
      nlinarith only [hb, hmult, hsq]
    · rw [hcrd1, if_neg h1]
      by_cases hψ1 : χ₁ * χ₂ * χ₃⁻¹ = 1
      · have hμ1 : 4 ≤ |mu1| := by
          by_contra hc
          exact h1 ⟨hψ1, le_of_lt (not_le.mp hc)⟩
        have hb := hq₀P (q := q) hq0P (β := ρ₁.re) (γ := ρ₁.im + ρ₂.im - ρ₃.im) hb1_bd hγ1
        rw [hψ1]
        rw [show (((ρ₁.im + ρ₂.im - ρ₃.im : ℝ) : ℂ)) = (((ρ₁.im : ℝ) : ℂ) + ((ρ₂.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ)) by push_cast; ring] at hb
        have harg : ((((ρ₁.re : ℝ) : ℂ) + (((ρ₁.im : ℝ) : ℂ) + ((ρ₂.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ)) * Complex.I) - 1) * ((Real.log (q : ℝ) : ℂ)) = ((((-(lamOf q ρ₁) : ℝ) : ℂ) + (mu1 : ℂ) * Complex.I)) := by
          rw [mul_ofReal_re_add_im]
          simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im, Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im, mul_zero, mul_one, zero_mul, zero_add, add_zero, sub_zero, mul_neg]
          rw [hmu1def]
          simp only [lamOf]
          push_cast
          ring
        rw [harg] at hb
        have hconv : (∫ t in (0:ℝ)..T.x₀, Complex.exp (-(((((-(lamOf q ρ₁) : ℝ) : ℂ) + (mu1 : ℂ) * Complex.I)) * (t : ℂ)))
              * ((T.f t : ℝ) : ℂ)).re = (T.Fc ((((-(lamOf q ρ₁) : ℝ) : ℂ) + (mu1 : ℂ) * Complex.I))).re := Fc_of_exp_eq' T ((((-(lamOf q ρ₁) : ℝ) : ℂ) + (mu1 : ℂ) * Complex.I))
        rw [hconv] at hb
        have hBj := hB (lamOf q ρ₁) mu1 hlam₁pos.le hlam₁_le hμ1
        have hmult := mul_le_mul_of_nonneg_left hBj hLqpos.le
        have hfl : 0 ≤ T.f 0 * ε' * Real.log (q : ℝ) :=
          mul_nonneg (mul_nonneg T.f0_pos.le hε'.le) hLqpos.le
        have hsq : T.f 0 * (ε'/4) * Real.log (q : ℝ) ≤ T.f 0 * ε' * Real.log (q : ℝ) := by
          have h1 : (0:ℝ) ≤ T.f 0 * Real.log (q : ℝ) := mul_nonneg T.f0_pos.le hLqpos.le
          nlinarith only [h1, hε']
        nlinarith only [hb, hmult, hsq]
      · have himT1 : |((((ρ₁.re : ℝ) : ℂ) + (((ρ₁.im : ℝ) : ℂ) + ((ρ₂.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ)) * Complex.I)).im| ≤ 10 * Real.log (q : ℝ) := by
          rw [show ((((ρ₁.re : ℝ) : ℂ) + (((ρ₁.im : ℝ) : ℂ) + ((ρ₂.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ)) * Complex.I)).im = ρ₁.im + ρ₂.im - ρ₃.im by simp]
          exact hγ1
        have hzwT1 : ∀ u : ℂ, (MeromorphicOn.divisor
            (DirichletCharacter.completedLFunction (χ₁ * χ₂ * χ₃⁻¹).primitiveCharacter)
            (Metric.closedBall 0 (|((((ρ₁.re : ℝ) : ℂ) + (((ρ₁.im : ℝ) : ℂ) + ((ρ₂.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ)) * Complex.I)).im| + 2))) u ≠ 0 →
            ‖(1:ℂ) + (((((ρ₁.re : ℝ) : ℂ) + (((ρ₁.im : ℝ) : ℂ) + ((ρ₂.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ)) * Complex.I)).im : ℂ) * Complex.I - u‖ ≤ δ → u.re ≤ ((((ρ₁.re : ℝ) : ℂ) + (((ρ₁.im : ℝ) : ℂ) + ((ρ₂.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ)) * Complex.I)).re := by
          have him : |((((ρ₁.re : ℝ) : ℂ) + (((ρ₁.im : ℝ) : ℂ) + ((ρ₂.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ)) * Complex.I)).im| + δ ≤ 10 * L := by
            rw [show ((((ρ₁.re : ℝ) : ℂ) + (((ρ₁.im : ℝ) : ℂ) + ((ρ₂.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ)) * Complex.I)).im = ρ₁.im + ρ₂.im - ρ₃.im by simp]
            linarith [abs_sub (ρ₁.im + ρ₂.im) ρ₃.im, abs_add_le ρ₁.im ρ₂.im, hbit₁, hbit₂, hbit₃, hδ1, hL1]
          exact IsRectMin.window_left hR hLqpos hψ1 him (by simp)
        have hb := hq₀s (q := q) (s := (((ρ₁.re : ℝ) : ℂ) + (((ρ₁.im : ℝ) : ℂ) + ((ρ₂.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ)) * Complex.I)) hq0s (χ₁ * χ₂ * χ₃⁻¹) hψ1
          (by rw [show ((((ρ₁.re : ℝ) : ℂ) + (((ρ₁.im : ℝ) : ℂ) + ((ρ₂.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ)) * Complex.I)).re = ρ₁.re by simp]; exact hb1_bd) himT1
          (by rw [show ((((ρ₁.re : ℝ) : ℂ) + (((ρ₁.im : ℝ) : ℂ) + ((ρ₂.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ)) * Complex.I)).re = ρ₁.re by simp]; exact hre_low)
          (hL52 (χ₁ * χ₂ * χ₃⁻¹) hψ1) hzwT1
        simpa using hb


  -- (12) the triple character χ₁ * χ₂⁻¹ * χ₃
  have hγ2 : |ρ₁.im - ρ₂.im + ρ₃.im| ≤ 10 * Real.log (q : ℝ) := by
    linarith [abs_add_le (ρ₁.im - ρ₂.im) ρ₃.im, abs_sub ρ₁.im ρ₂.im, hbit₁, hbit₂, hbit₃, hLlog, hLqpos]
  have hbt2 : (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
        ((χ₁ * χ₂⁻¹ * χ₃) (n : ZMod q) / (n : ℂ) ^ (((ρ₁.re : ℝ) : ℂ)
            + (((ρ₁.im : ℝ) : ℂ) - ((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I)).re * T.f (Real.log n / Real.log (q : ℝ)))
      ≤ T.f 0 * (1/6 + ε') * Real.log (q : ℝ) + 2 * crd2 := by
    by_cases h2 : (χ₁ * χ₂⁻¹ * χ₃ = 1 ∧ |mu2| ≤ 4)
    · have hb := hq₀P (q := q) hq0P (β := ρ₁.re) (γ := ρ₁.im - ρ₂.im + ρ₃.im) hb1_bd hγ2
      rw [h2.1]
      rw [show (((ρ₁.im - ρ₂.im + ρ₃.im : ℝ) : ℂ)) = (((ρ₁.im : ℝ) : ℂ) - ((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) by push_cast; ring] at hb
      have harg : ((((ρ₁.re : ℝ) : ℂ) + (((ρ₁.im : ℝ) : ℂ) - ((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I) - 1) * ((Real.log (q : ℝ) : ℂ)) = ((((-(lamOf q ρ₁) : ℝ) : ℂ) + (mu2 : ℂ) * Complex.I)) := by
        rw [mul_ofReal_re_add_im]
        simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im, Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im, mul_zero, mul_one, zero_mul, zero_add, add_zero, sub_zero, mul_neg]
        rw [hmu2def]
        simp only [lamOf]
        push_cast
        ring
      rw [harg] at hb
      have hconv : (∫ t in (0:ℝ)..T.x₀, Complex.exp (-(((((-(lamOf q ρ₁) : ℝ) : ℂ) + (mu2 : ℂ) * Complex.I)) * (t : ℂ)))
            * ((T.f t : ℝ) : ℂ)).re = (T.Fc ((((-(lamOf q ρ₁) : ℝ) : ℂ) + (mu2 : ℂ) * Complex.I))).re := Fc_of_exp_eq' T ((((-(lamOf q ρ₁) : ℝ) : ℂ) + (mu2 : ℂ) * Complex.I))
      rw [hconv] at hb
      have hcr : crd2 = Real.log (q : ℝ) * (T.Fc ((mu2 : ℂ) * Complex.I)).re := by
        rw [hcrd2, if_pos h2]
      rw [hcr]
      have hAj := hA (lamOf q ρ₁) mu2 hlam₁pos.le hlam₁_le h2.2
      have hmult := mul_le_mul_of_nonneg_left hAj hLqpos.le
      have hfl : 0 ≤ T.f 0 * ε' * Real.log (q : ℝ) :=
        mul_nonneg (mul_nonneg T.f0_pos.le hε'.le) hLqpos.le
      have hsq : T.f 0 * (ε'/4) * Real.log (q : ℝ) ≤ T.f 0 * ε' * Real.log (q : ℝ) := by
        have h1 : (0:ℝ) ≤ T.f 0 * Real.log (q : ℝ) := mul_nonneg T.f0_pos.le hLqpos.le
        nlinarith only [h1, hε']
      nlinarith only [hb, hmult, hsq]
    · rw [hcrd2, if_neg h2]
      by_cases hψ2 : χ₁ * χ₂⁻¹ * χ₃ = 1
      · have hμ2 : 4 ≤ |mu2| := by
          by_contra hc
          exact h2 ⟨hψ2, le_of_lt (not_le.mp hc)⟩
        have hb := hq₀P (q := q) hq0P (β := ρ₁.re) (γ := ρ₁.im - ρ₂.im + ρ₃.im) hb1_bd hγ2
        rw [hψ2]
        rw [show (((ρ₁.im - ρ₂.im + ρ₃.im : ℝ) : ℂ)) = (((ρ₁.im : ℝ) : ℂ) - ((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) by push_cast; ring] at hb
        have harg : ((((ρ₁.re : ℝ) : ℂ) + (((ρ₁.im : ℝ) : ℂ) - ((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I) - 1) * ((Real.log (q : ℝ) : ℂ)) = ((((-(lamOf q ρ₁) : ℝ) : ℂ) + (mu2 : ℂ) * Complex.I)) := by
          rw [mul_ofReal_re_add_im]
          simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im, Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im, mul_zero, mul_one, zero_mul, zero_add, add_zero, sub_zero, mul_neg]
          rw [hmu2def]
          simp only [lamOf]
          push_cast
          ring
        rw [harg] at hb
        have hconv : (∫ t in (0:ℝ)..T.x₀, Complex.exp (-(((((-(lamOf q ρ₁) : ℝ) : ℂ) + (mu2 : ℂ) * Complex.I)) * (t : ℂ)))
              * ((T.f t : ℝ) : ℂ)).re = (T.Fc ((((-(lamOf q ρ₁) : ℝ) : ℂ) + (mu2 : ℂ) * Complex.I))).re := Fc_of_exp_eq' T ((((-(lamOf q ρ₁) : ℝ) : ℂ) + (mu2 : ℂ) * Complex.I))
        rw [hconv] at hb
        have hBj := hB (lamOf q ρ₁) mu2 hlam₁pos.le hlam₁_le hμ2
        have hmult := mul_le_mul_of_nonneg_left hBj hLqpos.le
        have hfl : 0 ≤ T.f 0 * ε' * Real.log (q : ℝ) :=
          mul_nonneg (mul_nonneg T.f0_pos.le hε'.le) hLqpos.le
        have hsq : T.f 0 * (ε'/4) * Real.log (q : ℝ) ≤ T.f 0 * ε' * Real.log (q : ℝ) := by
          have h1 : (0:ℝ) ≤ T.f 0 * Real.log (q : ℝ) := mul_nonneg T.f0_pos.le hLqpos.le
          nlinarith only [h1, hε']
        nlinarith only [hb, hmult, hsq]
      · have himT2 : |((((ρ₁.re : ℝ) : ℂ) + (((ρ₁.im : ℝ) : ℂ) - ((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I)).im| ≤ 10 * Real.log (q : ℝ) := by
          rw [show ((((ρ₁.re : ℝ) : ℂ) + (((ρ₁.im : ℝ) : ℂ) - ((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I)).im = ρ₁.im - ρ₂.im + ρ₃.im by simp]
          exact hγ2
        have hzwT2 : ∀ u : ℂ, (MeromorphicOn.divisor
            (DirichletCharacter.completedLFunction (χ₁ * χ₂⁻¹ * χ₃).primitiveCharacter)
            (Metric.closedBall 0 (|((((ρ₁.re : ℝ) : ℂ) + (((ρ₁.im : ℝ) : ℂ) - ((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I)).im| + 2))) u ≠ 0 →
            ‖(1:ℂ) + (((((ρ₁.re : ℝ) : ℂ) + (((ρ₁.im : ℝ) : ℂ) - ((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I)).im : ℂ) * Complex.I - u‖ ≤ δ → u.re ≤ ((((ρ₁.re : ℝ) : ℂ) + (((ρ₁.im : ℝ) : ℂ) - ((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I)).re := by
          have him : |((((ρ₁.re : ℝ) : ℂ) + (((ρ₁.im : ℝ) : ℂ) - ((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I)).im| + δ ≤ 10 * L := by
            rw [show ((((ρ₁.re : ℝ) : ℂ) + (((ρ₁.im : ℝ) : ℂ) - ((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I)).im = ρ₁.im - ρ₂.im + ρ₃.im by simp]
            linarith [abs_add_le (ρ₁.im - ρ₂.im) ρ₃.im, abs_sub ρ₁.im ρ₂.im, hbit₁, hbit₂, hbit₃, hδ1, hL1]
          exact IsRectMin.window_left hR hLqpos hψ2 him (by simp)
        have hb := hq₀s (q := q) (s := (((ρ₁.re : ℝ) : ℂ) + (((ρ₁.im : ℝ) : ℂ) - ((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I)) hq0s (χ₁ * χ₂⁻¹ * χ₃) hψ2
          (by rw [show ((((ρ₁.re : ℝ) : ℂ) + (((ρ₁.im : ℝ) : ℂ) - ((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I)).re = ρ₁.re by simp]; exact hb1_bd) himT2
          (by rw [show ((((ρ₁.re : ℝ) : ℂ) + (((ρ₁.im : ℝ) : ℂ) - ((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I)).re = ρ₁.re by simp]; exact hre_low)
          (hL52 (χ₁ * χ₂⁻¹ * χ₃) hψ2) hzwT2
        simpa using hb


  -- (13) the triple character χ₁⁻¹ * χ₂ * χ₃
  have hγ3 : |-ρ₁.im + ρ₂.im + ρ₃.im| ≤ 10 * Real.log (q : ℝ) := by
    linarith [abs_add_le (-ρ₁.im + ρ₂.im) ρ₃.im, abs_add_le (-ρ₁.im) ρ₂.im, abs_neg ρ₁.im, hbit₁, hbit₂, hbit₃, hLlog, hLqpos]
  have hbt3 : (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
        ((χ₁⁻¹ * χ₂ * χ₃) (n : ZMod q) / (n : ℂ) ^ (((ρ₁.re : ℝ) : ℂ)
            + (-((ρ₁.im : ℝ) : ℂ) + ((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I)).re * T.f (Real.log n / Real.log (q : ℝ)))
      ≤ T.f 0 * (1/6 + ε') * Real.log (q : ℝ) + 2 * crd3 := by
    by_cases h3 : (χ₁⁻¹ * χ₂ * χ₃ = 1 ∧ |mu3| ≤ 4)
    · have hb := hq₀P (q := q) hq0P (β := ρ₁.re) (γ := -ρ₁.im + ρ₂.im + ρ₃.im) hb1_bd hγ3
      rw [h3.1]
      rw [show (((-ρ₁.im + ρ₂.im + ρ₃.im : ℝ) : ℂ)) = (-((ρ₁.im : ℝ) : ℂ) + ((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) by push_cast; ring] at hb
      have harg : ((((ρ₁.re : ℝ) : ℂ) + (-((ρ₁.im : ℝ) : ℂ) + ((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I) - 1) * ((Real.log (q : ℝ) : ℂ)) = ((((-(lamOf q ρ₁) : ℝ) : ℂ) + (mu3 : ℂ) * Complex.I)) := by
        rw [mul_ofReal_re_add_im]
        simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im, Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im, mul_zero, mul_one, zero_mul, zero_add, add_zero, sub_zero, mul_neg]
        rw [hmu3def]
        simp only [lamOf]
        push_cast
        ring
      rw [harg] at hb
      have hconv : (∫ t in (0:ℝ)..T.x₀, Complex.exp (-(((((-(lamOf q ρ₁) : ℝ) : ℂ) + (mu3 : ℂ) * Complex.I)) * (t : ℂ)))
            * ((T.f t : ℝ) : ℂ)).re = (T.Fc ((((-(lamOf q ρ₁) : ℝ) : ℂ) + (mu3 : ℂ) * Complex.I))).re := Fc_of_exp_eq' T ((((-(lamOf q ρ₁) : ℝ) : ℂ) + (mu3 : ℂ) * Complex.I))
      rw [hconv] at hb
      have hcr : crd3 = Real.log (q : ℝ) * (T.Fc ((mu3 : ℂ) * Complex.I)).re := by
        rw [hcrd3, if_pos h3]
      rw [hcr]
      have hAj := hA (lamOf q ρ₁) mu3 hlam₁pos.le hlam₁_le h3.2
      have hmult := mul_le_mul_of_nonneg_left hAj hLqpos.le
      have hfl : 0 ≤ T.f 0 * ε' * Real.log (q : ℝ) :=
        mul_nonneg (mul_nonneg T.f0_pos.le hε'.le) hLqpos.le
      have hsq : T.f 0 * (ε'/4) * Real.log (q : ℝ) ≤ T.f 0 * ε' * Real.log (q : ℝ) := by
        have h1 : (0:ℝ) ≤ T.f 0 * Real.log (q : ℝ) := mul_nonneg T.f0_pos.le hLqpos.le
        nlinarith only [h1, hε']
      nlinarith only [hb, hmult, hsq]
    · rw [hcrd3, if_neg h3]
      by_cases hψ3 : χ₁⁻¹ * χ₂ * χ₃ = 1
      · have hμ3 : 4 ≤ |mu3| := by
          by_contra hc
          exact h3 ⟨hψ3, le_of_lt (not_le.mp hc)⟩
        have hb := hq₀P (q := q) hq0P (β := ρ₁.re) (γ := -ρ₁.im + ρ₂.im + ρ₃.im) hb1_bd hγ3
        rw [hψ3]
        rw [show (((-ρ₁.im + ρ₂.im + ρ₃.im : ℝ) : ℂ)) = (-((ρ₁.im : ℝ) : ℂ) + ((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) by push_cast; ring] at hb
        have harg : ((((ρ₁.re : ℝ) : ℂ) + (-((ρ₁.im : ℝ) : ℂ) + ((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I) - 1) * ((Real.log (q : ℝ) : ℂ)) = ((((-(lamOf q ρ₁) : ℝ) : ℂ) + (mu3 : ℂ) * Complex.I)) := by
          rw [mul_ofReal_re_add_im]
          simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im, Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im, mul_zero, mul_one, zero_mul, zero_add, add_zero, sub_zero, mul_neg]
          rw [hmu3def]
          simp only [lamOf]
          push_cast
          ring
        rw [harg] at hb
        have hconv : (∫ t in (0:ℝ)..T.x₀, Complex.exp (-(((((-(lamOf q ρ₁) : ℝ) : ℂ) + (mu3 : ℂ) * Complex.I)) * (t : ℂ)))
              * ((T.f t : ℝ) : ℂ)).re = (T.Fc ((((-(lamOf q ρ₁) : ℝ) : ℂ) + (mu3 : ℂ) * Complex.I))).re := Fc_of_exp_eq' T ((((-(lamOf q ρ₁) : ℝ) : ℂ) + (mu3 : ℂ) * Complex.I))
        rw [hconv] at hb
        have hBj := hB (lamOf q ρ₁) mu3 hlam₁pos.le hlam₁_le hμ3
        have hmult := mul_le_mul_of_nonneg_left hBj hLqpos.le
        have hfl : 0 ≤ T.f 0 * ε' * Real.log (q : ℝ) :=
          mul_nonneg (mul_nonneg T.f0_pos.le hε'.le) hLqpos.le
        have hsq : T.f 0 * (ε'/4) * Real.log (q : ℝ) ≤ T.f 0 * ε' * Real.log (q : ℝ) := by
          have h1 : (0:ℝ) ≤ T.f 0 * Real.log (q : ℝ) := mul_nonneg T.f0_pos.le hLqpos.le
          nlinarith only [h1, hε']
        nlinarith only [hb, hmult, hsq]
      · have himT3 : |((((ρ₁.re : ℝ) : ℂ) + (-((ρ₁.im : ℝ) : ℂ) + ((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I)).im| ≤ 10 * Real.log (q : ℝ) := by
          rw [show ((((ρ₁.re : ℝ) : ℂ) + (-((ρ₁.im : ℝ) : ℂ) + ((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I)).im = -ρ₁.im + ρ₂.im + ρ₃.im by simp]
          exact hγ3
        have hzwT3 : ∀ u : ℂ, (MeromorphicOn.divisor
            (DirichletCharacter.completedLFunction (χ₁⁻¹ * χ₂ * χ₃).primitiveCharacter)
            (Metric.closedBall 0 (|((((ρ₁.re : ℝ) : ℂ) + (-((ρ₁.im : ℝ) : ℂ) + ((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I)).im| + 2))) u ≠ 0 →
            ‖(1:ℂ) + (((((ρ₁.re : ℝ) : ℂ) + (-((ρ₁.im : ℝ) : ℂ) + ((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I)).im : ℂ) * Complex.I - u‖ ≤ δ → u.re ≤ ((((ρ₁.re : ℝ) : ℂ) + (-((ρ₁.im : ℝ) : ℂ) + ((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I)).re := by
          have him : |((((ρ₁.re : ℝ) : ℂ) + (-((ρ₁.im : ℝ) : ℂ) + ((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I)).im| + δ ≤ 10 * L := by
            rw [show ((((ρ₁.re : ℝ) : ℂ) + (-((ρ₁.im : ℝ) : ℂ) + ((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I)).im = -ρ₁.im + ρ₂.im + ρ₃.im by simp]
            linarith [abs_add_le (-ρ₁.im + ρ₂.im) ρ₃.im, abs_add_le (-ρ₁.im) ρ₂.im, abs_neg ρ₁.im, hbit₁, hbit₂, hbit₃, hδ1, hL1]
          exact IsRectMin.window_left hR hLqpos hψ3 him (by simp)
        have hb := hq₀s (q := q) (s := (((ρ₁.re : ℝ) : ℂ) + (-((ρ₁.im : ℝ) : ℂ) + ((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I)) hq0s (χ₁⁻¹ * χ₂ * χ₃) hψ3
          (by rw [show ((((ρ₁.re : ℝ) : ℂ) + (-((ρ₁.im : ℝ) : ℂ) + ((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I)).re = ρ₁.re by simp]; exact hb1_bd) himT3
          (by rw [show ((((ρ₁.re : ℝ) : ℂ) + (-((ρ₁.im : ℝ) : ℂ) + ((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I)).re = ρ₁.re by simp]; exact hre_low)
          (hL52 (χ₁⁻¹ * χ₂ * χ₃) hψ3) hzwT3
        simpa using hb
  -- (8) the pair character χ₂χ₃: companion of the triples (10) and (13)
  have hγ8 : |ρ₂.im + ρ₃.im| ≤ 10 * Real.log (q : ℝ) := by
    linarith [abs_add_le ρ₂.im ρ₃.im, hbit₂, hbit₃, hLlog, hLqpos]
  have him8 : |(((ρ₁.re : ℝ) : ℂ) + (((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ))
      * Complex.I).im| ≤ 10 * Real.log (q : ℝ) := by
    rw [show (((ρ₁.re : ℝ) : ℂ) + (((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I).im
      = ρ₂.im + ρ₃.im by simp]
    exact hγ8
  have hzw8 : ∀ u : ℂ, (MeromorphicOn.divisor
      (DirichletCharacter.completedLFunction (χ₂ * χ₃).primitiveCharacter)
      (Metric.closedBall 0 (|(((ρ₁.re : ℝ) : ℂ)
        + (((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I).im| + 2))) u ≠ 0 →
      ‖(1:ℂ) + ((((ρ₁.re : ℝ) : ℂ)
        + (((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I).im : ℂ) * Complex.I - u‖ ≤ δ →
      u.re ≤ (((ρ₁.re : ℝ) : ℂ) + (((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ))
        * Complex.I).re := by
    have him : |(((ρ₁.re : ℝ) : ℂ) + (((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ))
        * Complex.I).im| + δ ≤ 10 * L := by
      rw [show (((ρ₁.re : ℝ) : ℂ) + (((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ))
        * Complex.I).im = ρ₂.im + ρ₃.im by simp]
      linarith [abs_add_le ρ₂.im ρ₃.im, hbit₁, hbit₂, hbit₃, hδ1, hL1]
    exact IsRectMin.window_left hR hLqpos hne8 him (by simp)
  have hw8a (hμ : |mu0| ≤ 4) : ‖(1:ℂ) + ((((ρ₁.re : ℝ) : ℂ)
      + (((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I).im : ℂ)
      * Complex.I - (starRingEnd ℂ) ρ₁‖ ≤ δ := by
    rw [one_add_mul_I_sub]
    rw [show (1 - ((starRingEnd ℂ) ρ₁).re : ℝ) = lamOf q ρ₁ / Real.log (q : ℝ) by
      rw [Complex.conj_re, lamOf_eq q ρ₁ hLqpos.ne']]
    rw [show ((((ρ₁.re : ℝ) : ℂ) + (((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I).im
        - ((starRingEnd ℂ) ρ₁).im : ℝ) = mu0 / Real.log (q : ℝ) by
      rw [show (((ρ₁.re : ℝ) : ℂ) + (((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I).im
        = ρ₂.im + ρ₃.im by simp, Complex.conj_im, hmu0def]
      field_simp
      ring]
    exact norm_win hLqpos hδ0 hlam₁pos.le hlam₁_le1 hμ hδLq5
  have hw8b (hμ : |mu3| ≤ 4) : ‖(1:ℂ) + ((((ρ₁.re : ℝ) : ℂ)
      + (((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I).im : ℂ)
      * Complex.I - ρ₁‖ ≤ δ := by
    rw [one_add_mul_I_sub]
    rw [show (1 - ρ₁.re : ℝ) = lamOf q ρ₁ / Real.log (q : ℝ) by rw [lamOf_eq q ρ₁ hLqpos.ne']]
    rw [show ((((ρ₁.re : ℝ) : ℂ) + (((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I).im
        - ρ₁.im : ℝ) = mu3 / Real.log (q : ℝ) by
      rw [show (((ρ₁.re : ℝ) : ℂ) + (((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I).im
        = ρ₂.im + ρ₃.im by simp, hmu3def]
      field_simp
      ring]
    exact norm_win hLqpos hδ0 hlam₁pos.le hlam₁_le1 hμ hδLq5
  have hγ9 : |ρ₂.im - ρ₃.im| ≤ 10 * Real.log (q : ℝ) := by
    linarith [abs_sub ρ₂.im ρ₃.im, hbit₂, hbit₃, hLlog, hLqpos]
  have him9 : |(((ρ₁.re : ℝ) : ℂ) + (((ρ₂.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ))
      * Complex.I).im| ≤ 10 * Real.log (q : ℝ) := by
    rw [show (((ρ₁.re : ℝ) : ℂ) + (((ρ₂.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ)) * Complex.I).im
      = ρ₂.im - ρ₃.im by simp]
    exact hγ9
  have hzw9 : ∀ u : ℂ, (MeromorphicOn.divisor
      (DirichletCharacter.completedLFunction (χ₂ * χ₃⁻¹).primitiveCharacter)
      (Metric.closedBall 0 (|(((ρ₁.re : ℝ) : ℂ)
        + (((ρ₂.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ)) * Complex.I).im| + 2))) u ≠ 0 →
      ‖(1:ℂ) + ((((ρ₁.re : ℝ) : ℂ)
        + (((ρ₂.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ)) * Complex.I).im : ℂ) * Complex.I - u‖ ≤ δ →
      u.re ≤ (((ρ₁.re : ℝ) : ℂ) + (((ρ₂.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ))
        * Complex.I).re := by
    have him : |(((ρ₁.re : ℝ) : ℂ) + (((ρ₂.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ))
        * Complex.I).im| + δ ≤ 10 * L := by
      rw [show (((ρ₁.re : ℝ) : ℂ) + (((ρ₂.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ))
        * Complex.I).im = ρ₂.im - ρ₃.im by simp]
      linarith [abs_sub ρ₂.im ρ₃.im, hbit₁, hbit₂, hbit₃, hδ1, hL1]
    exact IsRectMin.window_left hR hLqpos hne9 him (by simp)
  have hw9a (hμ : |mu1| ≤ 4) : ‖(1:ℂ) + ((((ρ₁.re : ℝ) : ℂ)
      + (((ρ₂.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ)) * Complex.I).im : ℂ)
      * Complex.I - (starRingEnd ℂ) ρ₁‖ ≤ δ := by
    rw [one_add_mul_I_sub]
    rw [show (1 - ((starRingEnd ℂ) ρ₁).re : ℝ) = lamOf q ρ₁ / Real.log (q : ℝ) by
      rw [Complex.conj_re, lamOf_eq q ρ₁ hLqpos.ne']]
    rw [show ((((ρ₁.re : ℝ) : ℂ) + (((ρ₂.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ)) * Complex.I).im
        - ((starRingEnd ℂ) ρ₁).im : ℝ) = mu1 / Real.log (q : ℝ) by
      rw [show (((ρ₁.re : ℝ) : ℂ) + (((ρ₂.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ)) * Complex.I).im
        = ρ₂.im - ρ₃.im by simp, Complex.conj_im, hmu1def]
      field_simp
      ring]
    exact norm_win hLqpos hδ0 hlam₁pos.le hlam₁_le1 hμ hδLq5
  have hw9b (hμ : |mu2| ≤ 4) : ‖(1:ℂ) + ((((ρ₁.re : ℝ) : ℂ)
      + (((ρ₂.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ)) * Complex.I).im : ℂ)
      * Complex.I - ρ₁‖ ≤ δ := by
    rw [one_add_mul_I_sub]
    rw [show (1 - ρ₁.re : ℝ) = lamOf q ρ₁ / Real.log (q : ℝ) by rw [lamOf_eq q ρ₁ hLqpos.ne']]
    rw [show ((((ρ₁.re : ℝ) : ℂ) + (((ρ₂.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ)) * Complex.I).im
        - ρ₁.im : ℝ) = (-mu2) / Real.log (q : ℝ) by
      rw [show (((ρ₁.re : ℝ) : ℂ) + (((ρ₂.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ)) * Complex.I).im
        = ρ₂.im - ρ₃.im by simp, hmu2def]
      field_simp
      ring]
    exact norm_win hLqpos hδ0 hlam₁pos.le hlam₁_le1 (by rwa [abs_neg]) hδLq5
  have hb8 : (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
        ((χ₂ * χ₃) (n : ZMod q) / (n : ℂ) ^ (((ρ₁.re : ℝ) : ℂ)
            + (((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I)).re
          * T.f (Real.log n / Real.log (q : ℝ)))
      ≤ T.f 0 * (1/6 + ε') * Real.log (q : ℝ) - crd0 - crd3 := by
    by_cases h0 : (χ₁ * χ₂ * χ₃ = 1 ∧ |mu0| ≤ 4)
    · by_cases h3 : (χ₁⁻¹ * χ₂ * χ₃ = 1 ∧ |mu3| ≤ 4)
      · have heq0 : χ₂ * χ₃ = χ₁⁻¹ := by
          have h : χ₁ * (χ₂ * χ₃) = 1 := by rw [← mul_assoc]; exact h0.1
          exact eq_inv_of_mul_eq_one_right h
        have heq3 : χ₂ * χ₃ = χ₁ := by
          have h : χ₁⁻¹ * (χ₂ * χ₃) = 1 := by rw [← mul_assoc]; exact h3.1
          have h2 := eq_inv_of_mul_eq_one_right h
          rwa [inv_inv] at h2
        have hdivA := Work.ZeroFreeTables.divisor_ne_zero_of_zeroMult_v2 (χ₂ * χ₃) hne8
          (mem_closedBall_of_window (((ρ₁.re : ℝ) : ℂ) + (((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I) δ (hw8a h0.2) hδ1 (by
            rw [Complex.conj_re, abs_of_pos hstrip₁.1]; linarith [hstrip₁.2]))
          (by rw [heq0, Work.A7.zeroMult_conj_inv]; exact hzm₁)
        have hdivB := Work.ZeroFreeTables.divisor_ne_zero_of_zeroMult_v2 (χ₂ * χ₃) hne8
          (mem_closedBall_of_window (((ρ₁.re : ℝ) : ℂ) + (((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I) δ (hw8b h3.2) hδ1 (by
            rw [abs_of_pos hstrip₁.1]; linarith [hstrip₁.2]))
          (by rw [heq3]; exact hzm₁)
        have hnezeros : (starRingEnd ℂ) ρ₁ ≠ ρ₁ := by
          intro hc
          have h := congrArg Complex.im hc
          simp only [Complex.conj_im] at h
          exact hg1ne (by linarith)
        have hra : ((starRingEnd ℂ) ρ₁).re ≤ ((((ρ₁.re : ℝ) : ℂ) + (((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I)).re := by rw [Complex.conj_re]; simp
        have hrb : ρ₁.re ≤ ((((ρ₁.re : ℝ) : ℂ) + (((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I)).re := by simp
        have hb := hq₀t (q := q) (s := (((ρ₁.re : ℝ) : ℂ) + (((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I)) (ρ := (starRingEnd ℂ) ρ₁) (ρ' := ρ₁)
          hq0t (χ₂ * χ₃) hne8 (by rw [show ((((ρ₁.re : ℝ) : ℂ) + (((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I)).re = ρ₁.re by simp]; exact hb1_bd) him8
          (by rw [show ((((ρ₁.re : ℝ) : ℂ) + (((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I)).re = ρ₁.re by simp]; exact hre_low)
          (hL52 (χ₂ * χ₃) hne8) hdivA hdivB hnezeros (hw8a h0.2) (hw8b h3.2) hra hrb
          (fun u h1 h2 => hzw8 u h1 h2)
        have hargA : ((((ρ₁.re : ℝ) : ℂ) + (((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I) - (starRingEnd ℂ) ρ₁) * ((Real.log (q : ℝ) : ℂ)) = (((mu0 : ℂ) * Complex.I)) := by
          rw [mul_ofReal_re_add_im]
          simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im, Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im, mul_zero, mul_one, zero_mul, zero_add, add_zero, sub_zero, mul_neg]
          rw [hmu0def]
          push_cast
          ring
        rw [hargA] at hb
        have hconvA : (∫ t in (0:ℝ)..T.x₀, Complex.exp (-((((mu0 : ℂ) * Complex.I)) * (t : ℂ)))
              * ((T.f t : ℝ) : ℂ)).re = (T.Fc ((mu0 : ℂ) * Complex.I)).re := Fc_of_exp_eq' T (((mu0 : ℂ) * Complex.I))
        rw [hconvA] at hb
        have hargB : ((((ρ₁.re : ℝ) : ℂ) + (((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I) - ρ₁) * ((Real.log (q : ℝ) : ℂ)) = (((mu3 : ℂ) * Complex.I)) := by
          rw [mul_ofReal_re_add_im]
          simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im, Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im, mul_zero, mul_one, zero_mul, zero_add, add_zero, sub_zero, mul_neg]
          rw [hmu3def]
          push_cast
          ring
        rw [hargB] at hb
        have hconvB : (∫ t in (0:ℝ)..T.x₀, Complex.exp (-((((mu3 : ℂ) * Complex.I)) * (t : ℂ)))
              * ((T.f t : ℝ) : ℂ)).re = (T.Fc ((mu3 : ℂ) * Complex.I)).re := Fc_of_exp_eq' T (((mu3 : ℂ) * Complex.I))
        rw [hconvB] at hb
        have hcr0 : crd0 = Real.log (q : ℝ) * (T.Fc ((mu0 : ℂ) * Complex.I)).re := by
          rw [hcrd0, if_pos h0]
        have hcr3 : crd3 = Real.log (q : ℝ) * (T.Fc ((mu3 : ℂ) * Complex.I)).re := by
          rw [hcrd3, if_pos h3]
        linarith only [hb, hcr0, hcr3]
      · have heq0 : χ₂ * χ₃ = χ₁⁻¹ := by
          have h : χ₁ * (χ₂ * χ₃) = 1 := by rw [← mul_assoc]; exact h0.1
          exact eq_inv_of_mul_eq_one_right h
        have hdivA := Work.ZeroFreeTables.divisor_ne_zero_of_zeroMult_v2 (χ₂ * χ₃) hne8
          (mem_closedBall_of_window (((ρ₁.re : ℝ) : ℂ) + (((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I) δ (hw8a h0.2) hδ1 (by
            rw [Complex.conj_re, abs_of_pos hstrip₁.1]; linarith [hstrip₁.2]))
          (by rw [heq0, Work.A7.zeroMult_conj_inv]; exact hzm₁)
        have hb := hq₀o (q := q) (s := (((ρ₁.re : ℝ) : ℂ) + (((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I)) (ρ := (starRingEnd ℂ) ρ₁) hq0o
          (χ₂ * χ₃) hne8 (by rw [show ((((ρ₁.re : ℝ) : ℂ) + (((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I)).re = ρ₁.re by simp]; exact hb1_bd) him8
          (by rw [show ((((ρ₁.re : ℝ) : ℂ) + (((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I)).re = ρ₁.re by simp]; exact hre_low)
          (hL52 (χ₂ * χ₃) hne8) hdivA (hw8a h0.2) hzw8
        have hargA : ((((ρ₁.re : ℝ) : ℂ) + (((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I) - (starRingEnd ℂ) ρ₁) * ((Real.log (q : ℝ) : ℂ)) = (((mu0 : ℂ) * Complex.I)) := by
          rw [mul_ofReal_re_add_im]
          simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im, Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im, mul_zero, mul_one, zero_mul, zero_add, add_zero, sub_zero, mul_neg]
          rw [hmu0def]
          push_cast
          ring
        rw [hargA] at hb
        have hconvA : (∫ t in (0:ℝ)..T.x₀, Complex.exp (-((((mu0 : ℂ) * Complex.I)) * (t : ℂ)))
              * ((T.f t : ℝ) : ℂ)).re = (T.Fc ((mu0 : ℂ) * Complex.I)).re := Fc_of_exp_eq' T (((mu0 : ℂ) * Complex.I))
        rw [hconvA] at hb
        have hcr0 : crd0 = Real.log (q : ℝ) * (T.Fc ((mu0 : ℂ) * Complex.I)).re := by
          rw [hcrd0, if_pos h0]
        have hz3 : crd3 = 0 := by rw [hcrd3, if_neg h3]
        linarith only [hb, hcr0, hz3]
    · by_cases h3 : (χ₁⁻¹ * χ₂ * χ₃ = 1 ∧ |mu3| ≤ 4)
      · have heq3 : χ₂ * χ₃ = χ₁ := by
          have h : χ₁⁻¹ * (χ₂ * χ₃) = 1 := by rw [← mul_assoc]; exact h3.1
          have h2 := eq_inv_of_mul_eq_one_right h
          rwa [inv_inv] at h2
        have hdivB := Work.ZeroFreeTables.divisor_ne_zero_of_zeroMult_v2 (χ₂ * χ₃) hne8
          (mem_closedBall_of_window (((ρ₁.re : ℝ) : ℂ) + (((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I) δ (hw8b h3.2) hδ1 (by
            rw [abs_of_pos hstrip₁.1]; linarith [hstrip₁.2]))
          (by rw [heq3]; exact hzm₁)
        have hb := hq₀o (q := q) (s := (((ρ₁.re : ℝ) : ℂ) + (((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I)) (ρ := ρ₁) hq0o
          (χ₂ * χ₃) hne8 (by rw [show ((((ρ₁.re : ℝ) : ℂ) + (((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I)).re = ρ₁.re by simp]; exact hb1_bd) him8
          (by rw [show ((((ρ₁.re : ℝ) : ℂ) + (((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I)).re = ρ₁.re by simp]; exact hre_low)
          (hL52 (χ₂ * χ₃) hne8) hdivB (hw8b h3.2) hzw8
        have hargB : ((((ρ₁.re : ℝ) : ℂ) + (((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I) - ρ₁) * ((Real.log (q : ℝ) : ℂ)) = (((mu3 : ℂ) * Complex.I)) := by
          rw [mul_ofReal_re_add_im]
          simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im, Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im, mul_zero, mul_one, zero_mul, zero_add, add_zero, sub_zero, mul_neg]
          rw [hmu3def]
          push_cast
          ring
        rw [hargB] at hb
        have hconvB : (∫ t in (0:ℝ)..T.x₀, Complex.exp (-((((mu3 : ℂ) * Complex.I)) * (t : ℂ)))
              * ((T.f t : ℝ) : ℂ)).re = (T.Fc ((mu3 : ℂ) * Complex.I)).re := Fc_of_exp_eq' T (((mu3 : ℂ) * Complex.I))
        rw [hconvB] at hb
        have hcr3 : crd3 = Real.log (q : ℝ) * (T.Fc ((mu3 : ℂ) * Complex.I)).re := by
          rw [hcrd3, if_pos h3]
        have hz0 : crd0 = 0 := by rw [hcrd0, if_neg h0]
        linarith only [hb, hcr3, hz0]
      · have hb := hq₀s (q := q) (s := (((ρ₁.re : ℝ) : ℂ) + (((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I)) hq0s (χ₂ * χ₃) hne8
          (by rw [show ((((ρ₁.re : ℝ) : ℂ) + (((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I)).re = ρ₁.re by simp]; exact hb1_bd) him8
          (by rw [show ((((ρ₁.re : ℝ) : ℂ) + (((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I)).re = ρ₁.re by simp]; exact hre_low)
          (hL52 (χ₂ * χ₃) hne8) hzw8

        have hz0 : crd0 = 0 := by rw [hcrd0, if_neg h0]
        have hz3 : crd3 = 0 := by rw [hcrd3, if_neg h3]
        linarith only [hb, hz0, hz3]
  have hγ9 : |ρ₂.im - ρ₃.im| ≤ 10 * Real.log (q : ℝ) := by
    linarith [abs_sub ρ₂.im ρ₃.im, hbit₂, hbit₃, hLlog, hLqpos]
  have him9 : |(((ρ₁.re : ℝ) : ℂ) + (((ρ₂.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ))
      * Complex.I).im| ≤ 10 * Real.log (q : ℝ) := by
    rw [show (((ρ₁.re : ℝ) : ℂ) + (((ρ₂.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ)) * Complex.I).im
      = ρ₂.im - ρ₃.im by simp]
    exact hγ9
  have hzw9 : ∀ u : ℂ, (MeromorphicOn.divisor
      (DirichletCharacter.completedLFunction (χ₂ * χ₃⁻¹).primitiveCharacter)
      (Metric.closedBall 0 (|(((ρ₁.re : ℝ) : ℂ)
        + (((ρ₂.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ)) * Complex.I).im| + 2))) u ≠ 0 →
      ‖(1:ℂ) + ((((ρ₁.re : ℝ) : ℂ)
        + (((ρ₂.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ)) * Complex.I).im : ℂ) * Complex.I - u‖ ≤ δ →
      u.re ≤ (((ρ₁.re : ℝ) : ℂ) + (((ρ₂.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ))
        * Complex.I).re := by
    have him : |(((ρ₁.re : ℝ) : ℂ) + (((ρ₂.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ))
        * Complex.I).im| + δ ≤ 10 * L := by
      rw [show (((ρ₁.re : ℝ) : ℂ) + (((ρ₂.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ))
        * Complex.I).im = ρ₂.im - ρ₃.im by simp]
      linarith [abs_sub ρ₂.im ρ₃.im, hbit₁, hbit₂, hbit₃, hδ1, hL1]
    exact IsRectMin.window_left hR hLqpos hne9 him (by simp)
  have hw9a (hμ : |mu1| ≤ 4) : ‖(1:ℂ) + ((((ρ₁.re : ℝ) : ℂ)
      + (((ρ₂.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ)) * Complex.I).im : ℂ)
      * Complex.I - (starRingEnd ℂ) ρ₁‖ ≤ δ := by
    rw [one_add_mul_I_sub]
    rw [show (1 - ((starRingEnd ℂ) ρ₁).re : ℝ) = lamOf q ρ₁ / Real.log (q : ℝ) by
      rw [Complex.conj_re, lamOf_eq q ρ₁ hLqpos.ne']]
    rw [show ((((ρ₁.re : ℝ) : ℂ) + (((ρ₂.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ)) * Complex.I).im
        - ((starRingEnd ℂ) ρ₁).im : ℝ) = mu1 / Real.log (q : ℝ) by
      rw [show (((ρ₁.re : ℝ) : ℂ) + (((ρ₂.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ)) * Complex.I).im
        = ρ₂.im - ρ₃.im by simp, Complex.conj_im, hmu1def]
      field_simp
      ring]
    exact norm_win hLqpos hδ0 hlam₁pos.le hlam₁_le1 hμ hδLq5
  have hw9b (hμ : |mu2| ≤ 4) : ‖(1:ℂ) + ((((ρ₁.re : ℝ) : ℂ)
      + (((ρ₂.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ)) * Complex.I).im : ℂ)
      * Complex.I - ρ₁‖ ≤ δ := by
    rw [one_add_mul_I_sub]
    rw [show (1 - ρ₁.re : ℝ) = lamOf q ρ₁ / Real.log (q : ℝ) by rw [lamOf_eq q ρ₁ hLqpos.ne']]
    rw [show ((((ρ₁.re : ℝ) : ℂ) + (((ρ₂.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ)) * Complex.I).im
        - ρ₁.im : ℝ) = (-mu2) / Real.log (q : ℝ) by
      rw [show (((ρ₁.re : ℝ) : ℂ) + (((ρ₂.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ)) * Complex.I).im
        = ρ₂.im - ρ₃.im by simp, hmu2def]
      field_simp
      ring]
    exact norm_win hLqpos hδ0 hlam₁pos.le hlam₁_le1 (by rwa [abs_neg]) hδLq5
  have hb9 : (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
        ((χ₂ * χ₃⁻¹) (n : ZMod q) / (n : ℂ) ^ (((ρ₁.re : ℝ) : ℂ)
            + (((ρ₂.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ)) * Complex.I)).re
          * T.f (Real.log n / Real.log (q : ℝ)))
      ≤ T.f 0 * (1/6 + ε') * Real.log (q : ℝ) - crd1 - crd2 := by
    by_cases h1 : (χ₁ * χ₂ * χ₃⁻¹ = 1 ∧ |mu1| ≤ 4)
    · by_cases h2 : (χ₁ * χ₂⁻¹ * χ₃ = 1 ∧ |mu2| ≤ 4)
      · have heq1 : χ₂ * χ₃⁻¹ = χ₁⁻¹ := by
          have h : χ₁ * (χ₂ * χ₃⁻¹) = 1 := by rw [← mul_assoc]; exact h1.1
          exact eq_inv_of_mul_eq_one_right h
        have heq2 : χ₂ * χ₃⁻¹ = χ₁ := by
          have h : χ₁ * (χ₂⁻¹ * χ₃) = 1 := by rw [← mul_assoc]; exact h2.1
          have h2' := eq_inv_of_mul_eq_one_right h
          have h3' := congrArg (fun z : DirichletCharacter ℂ q => z⁻¹) h2'
          rw [mul_inv_rev, inv_inv, inv_inv] at h3'
          rw [mul_comm] at h3'
          exact h3'
        have hdivA := Work.ZeroFreeTables.divisor_ne_zero_of_zeroMult_v2 (χ₂ * χ₃⁻¹) hne9
          (mem_closedBall_of_window (((ρ₁.re : ℝ) : ℂ) + (((ρ₂.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ)) * Complex.I) δ (hw9a h1.2) hδ1 (by
            rw [Complex.conj_re, abs_of_pos hstrip₁.1]; linarith [hstrip₁.2]))
          (by rw [heq1, Work.A7.zeroMult_conj_inv]; exact hzm₁)
        have hdivB := Work.ZeroFreeTables.divisor_ne_zero_of_zeroMult_v2 (χ₂ * χ₃⁻¹) hne9
          (mem_closedBall_of_window (((ρ₁.re : ℝ) : ℂ) + (((ρ₂.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ)) * Complex.I) δ (hw9b h2.2) hδ1 (by
            rw [abs_of_pos hstrip₁.1]; linarith [hstrip₁.2]))
          (by rw [heq2]; exact hzm₁)
        have hnezeros : (starRingEnd ℂ) ρ₁ ≠ ρ₁ := by
          intro hc
          have h := congrArg Complex.im hc
          simp only [Complex.conj_im] at h
          exact hg1ne (by linarith)
        have hra : ((starRingEnd ℂ) ρ₁).re ≤ ((((ρ₁.re : ℝ) : ℂ) + (((ρ₂.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ)) * Complex.I)).re := by rw [Complex.conj_re]; simp
        have hrb : ρ₁.re ≤ ((((ρ₁.re : ℝ) : ℂ) + (((ρ₂.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ)) * Complex.I)).re := by simp
        have hb := hq₀t (q := q) (s := (((ρ₁.re : ℝ) : ℂ) + (((ρ₂.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ)) * Complex.I)) (ρ := (starRingEnd ℂ) ρ₁) (ρ' := ρ₁)
          hq0t (χ₂ * χ₃⁻¹) hne9 (by rw [show ((((ρ₁.re : ℝ) : ℂ) + (((ρ₂.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ)) * Complex.I)).re = ρ₁.re by simp]; exact hb1_bd) him9 (by rw [show ((((ρ₁.re : ℝ) : ℂ) + (((ρ₂.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ)) * Complex.I)).re = ρ₁.re by simp]; exact hre_low) (hL52 (χ₂ * χ₃⁻¹) hne9) hdivA hdivB
          hnezeros (hw9a h1.2) (hw9b h2.2) hra hrb (fun u h1' h2' => hzw9 u h1' h2')
        have hargA : ((((ρ₁.re : ℝ) : ℂ) + (((ρ₂.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ)) * Complex.I) - (starRingEnd ℂ) ρ₁) * ((Real.log (q : ℝ) : ℂ)) = (mu1 : ℂ) * Complex.I := by
          rw [mul_ofReal_re_add_im]
          have hre : ((((ρ₁.re : ℝ) : ℂ) + (((ρ₂.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ)) * Complex.I) - (starRingEnd ℂ) ρ₁).re = 0 := by simp
          have him : ((((ρ₁.re : ℝ) : ℂ) + (((ρ₂.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ)) * Complex.I) - (starRingEnd ℂ) ρ₁).im = ρ₂.im - ρ₃.im + ρ₁.im := by simp
          have himm : ((ρ₂.im - ρ₃.im + ρ₁.im) * Real.log (q : ℝ)) = mu1 := by
            rw [hmu1def]; ring
          rw [hre, him, himm]
          simp only [zero_mul, Complex.ofReal_zero, zero_add]
        rw [hargA] at hb
        have hconvA : (∫ t in (0:ℝ)..T.x₀, Complex.exp (-(((mu1 : ℂ) * Complex.I) * (t : ℂ)))
              * ((T.f t : ℝ) : ℂ)).re = (T.Fc ((mu1 : ℂ) * Complex.I)).re := Fc_of_exp_eq' T ((mu1 : ℂ) * Complex.I)
        have hargB : ((((ρ₁.re : ℝ) : ℂ) + (((ρ₂.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ)) * Complex.I) - ρ₁) * ((Real.log (q : ℝ) : ℂ)) = (-(mu2 : ℂ)) * Complex.I := by
          rw [mul_ofReal_re_add_im]
          have hre : ((((ρ₁.re : ℝ) : ℂ) + (((ρ₂.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ)) * Complex.I) - ρ₁).re = 0 := by simp
          have him : ((((ρ₁.re : ℝ) : ℂ) + (((ρ₂.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ)) * Complex.I) - ρ₁).im = ρ₂.im - ρ₃.im - ρ₁.im := by simp
          have himm : ((ρ₂.im - ρ₃.im - ρ₁.im) * Real.log (q : ℝ)) = -mu2 := by
            rw [hmu2def]; ring
          rw [hre, him, himm]
          simp only [zero_mul, Complex.ofReal_zero, zero_add, Complex.ofReal_neg]
        rw [hargB] at hb
        have hconvB : (∫ t in (0:ℝ)..T.x₀, Complex.exp (-(((-(mu2 : ℂ)) * Complex.I) * (t : ℂ)))
              * ((T.f t : ℝ) : ℂ)).re = (T.Fc ((mu2 : ℂ) * Complex.I)).re := (Fc_of_exp_eq' T ((-(mu2 : ℂ)) * Complex.I)).trans (TestFn.Fc_neg_I_re T mu2)
        have hcr1 : crd1 = Real.log (q : ℝ) * (T.Fc ((mu1 : ℂ) * Complex.I)).re := by
          rw [hcrd1, if_pos h1]
        have hcr2 : crd2 = Real.log (q : ℝ) * (T.Fc ((mu2 : ℂ) * Complex.I)).re := by
          rw [hcrd2, if_pos h2]
        rw [hconvA, hconvB] at hb
        linarith only [hb, hcr1, hcr2]
      · have heq1 : χ₂ * χ₃⁻¹ = χ₁⁻¹ := by
          have h : χ₁ * (χ₂ * χ₃⁻¹) = 1 := by rw [← mul_assoc]; exact h1.1
          exact eq_inv_of_mul_eq_one_right h
        have hdivA := Work.ZeroFreeTables.divisor_ne_zero_of_zeroMult_v2 (χ₂ * χ₃⁻¹) hne9
          (mem_closedBall_of_window (((ρ₁.re : ℝ) : ℂ) + (((ρ₂.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ)) * Complex.I) δ (hw9a h1.2) hδ1 (by
            rw [Complex.conj_re, abs_of_pos hstrip₁.1]; linarith [hstrip₁.2]))
          (by rw [heq1, Work.A7.zeroMult_conj_inv]; exact hzm₁)
        have hb := hq₀o (q := q) (s := (((ρ₁.re : ℝ) : ℂ) + (((ρ₂.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ)) * Complex.I)) (ρ := (starRingEnd ℂ) ρ₁) hq0o
          (χ₂ * χ₃⁻¹) hne9 (by rw [show ((((ρ₁.re : ℝ) : ℂ) + (((ρ₂.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ)) * Complex.I)).re = ρ₁.re by simp]; exact hb1_bd) him9 (by rw [show ((((ρ₁.re : ℝ) : ℂ) + (((ρ₂.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ)) * Complex.I)).re = ρ₁.re by simp]; exact hre_low) (hL52 (χ₂ * χ₃⁻¹) hne9) hdivA
          (hw9a h1.2) hzw9
        have hargA : ((((ρ₁.re : ℝ) : ℂ) + (((ρ₂.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ)) * Complex.I) - (starRingEnd ℂ) ρ₁) * ((Real.log (q : ℝ) : ℂ)) = (mu1 : ℂ) * Complex.I := by
          rw [mul_ofReal_re_add_im]
          have hre : ((((ρ₁.re : ℝ) : ℂ) + (((ρ₂.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ)) * Complex.I) - (starRingEnd ℂ) ρ₁).re = 0 := by simp
          have him : ((((ρ₁.re : ℝ) : ℂ) + (((ρ₂.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ)) * Complex.I) - (starRingEnd ℂ) ρ₁).im = ρ₂.im - ρ₃.im + ρ₁.im := by simp
          have himm : ((ρ₂.im - ρ₃.im + ρ₁.im) * Real.log (q : ℝ)) = mu1 := by
            rw [hmu1def]; ring
          rw [hre, him, himm]
          simp only [zero_mul, Complex.ofReal_zero, zero_add]
        rw [hargA] at hb
        have hconvA : (∫ t in (0:ℝ)..T.x₀, Complex.exp (-(((mu1 : ℂ) * Complex.I) * (t : ℂ)))
              * ((T.f t : ℝ) : ℂ)).re = (T.Fc ((mu1 : ℂ) * Complex.I)).re := Fc_of_exp_eq' T ((mu1 : ℂ) * Complex.I)
        have hcr1 : crd1 = Real.log (q : ℝ) * (T.Fc ((mu1 : ℂ) * Complex.I)).re := by
          rw [hcrd1, if_pos h1]
        have hz2 : crd2 = 0 := by rw [hcrd2, if_neg h2]
        rw [hconvA] at hb
        linarith only [hb, hcr1, hz2]
    · by_cases h2 : (χ₁ * χ₂⁻¹ * χ₃ = 1 ∧ |mu2| ≤ 4)
      · have heq2 : χ₂ * χ₃⁻¹ = χ₁ := by
          have h : χ₁ * (χ₂⁻¹ * χ₃) = 1 := by rw [← mul_assoc]; exact h2.1
          have h2' := eq_inv_of_mul_eq_one_right h
          have h3' := congrArg (fun z : DirichletCharacter ℂ q => z⁻¹) h2'
          rw [mul_inv_rev, inv_inv, inv_inv] at h3'
          rw [mul_comm] at h3'
          exact h3'
        have hdivB := Work.ZeroFreeTables.divisor_ne_zero_of_zeroMult_v2 (χ₂ * χ₃⁻¹) hne9
          (mem_closedBall_of_window (((ρ₁.re : ℝ) : ℂ) + (((ρ₂.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ)) * Complex.I) δ (hw9b h2.2) hδ1 (by
            rw [abs_of_pos hstrip₁.1]; linarith [hstrip₁.2]))
          (by rw [heq2]; exact hzm₁)
        have hb := hq₀o (q := q) (s := (((ρ₁.re : ℝ) : ℂ) + (((ρ₂.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ)) * Complex.I)) (ρ := ρ₁) hq0o (χ₂ * χ₃⁻¹) hne9 (by rw [show (((ρ₁.re : ℝ) : ℂ) + (((ρ₂.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ)) * Complex.I).re = ρ₁.re by simp]; exact hb1_bd) him9
          (by rw [show (((ρ₁.re : ℝ) : ℂ) + (((ρ₂.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ)) * Complex.I).re = ρ₁.re by simp]; exact hre_low) (hL52 (χ₂ * χ₃⁻¹) hne9) hdivB (hw9b h2.2) hzw9
        have hargB : ((((ρ₁.re : ℝ) : ℂ) + (((ρ₂.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ)) * Complex.I) - ρ₁) * ((Real.log (q : ℝ) : ℂ)) = (-(mu2 : ℂ)) * Complex.I := by
          rw [mul_ofReal_re_add_im]
          have hre : ((((ρ₁.re : ℝ) : ℂ) + (((ρ₂.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ)) * Complex.I) - ρ₁).re = 0 := by simp
          have him : ((((ρ₁.re : ℝ) : ℂ) + (((ρ₂.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ)) * Complex.I) - ρ₁).im = ρ₂.im - ρ₃.im - ρ₁.im := by simp
          have himm : ((ρ₂.im - ρ₃.im - ρ₁.im) * Real.log (q : ℝ)) = -mu2 := by
            rw [hmu2def]; ring
          rw [hre, him, himm]
          simp only [zero_mul, Complex.ofReal_zero, zero_add, Complex.ofReal_neg]
        rw [hargB] at hb
        have hconvB : (∫ t in (0:ℝ)..T.x₀, Complex.exp (-(((-(mu2 : ℂ)) * Complex.I) * (t : ℂ)))
              * ((T.f t : ℝ) : ℂ)).re = (T.Fc ((mu2 : ℂ) * Complex.I)).re := (Fc_of_exp_eq' T ((-(mu2 : ℂ)) * Complex.I)).trans (TestFn.Fc_neg_I_re T mu2)
        have hcr2 : crd2 = Real.log (q : ℝ) * (T.Fc ((mu2 : ℂ) * Complex.I)).re := by
          rw [hcrd2, if_pos h2]
        have hz1 : crd1 = 0 := by rw [hcrd1, if_neg h1]
        rw [hconvB] at hb
        linarith only [hb, hcr2, hz1]
      · have hb := hq₀s (q := q) (s := (((ρ₁.re : ℝ) : ℂ) + (((ρ₂.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ)) * Complex.I)) hq0s (χ₂ * χ₃⁻¹) hne9 (by rw [show ((((ρ₁.re : ℝ) : ℂ) + (((ρ₂.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ)) * Complex.I)).re = ρ₁.re by simp]; exact hb1_bd) him9 (by rw [show ((((ρ₁.re : ℝ) : ℂ) + (((ρ₂.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ)) * Complex.I)).re = ρ₁.re by simp]; exact hre_low)
          (hL52 (χ₂ * χ₃⁻¹) hne9) hzw9
        have hz1 : crd1 = 0 := by rw [hcrd1, if_neg h1]
        have hz2 : crd2 = 0 := by rw [hcrd2, if_neg h2]
        linarith only [hb, hz1, hz2]
  -- ======================= the positivity and the assembly =======================
  have hpos := Work.ZeroFreeTables.Ksum_positivity_three (q := q) (f := T.f) T.f_nonneg
    (x₀ := T.x₀) (L := Real.log (q : ℝ)) (β := ρ₁.re) (γ₁ := ρ₁.im) (γ₂ := ρ₂.im)
    (γ₃ := ρ₃.im) T.x₀_pos hLqpos T.f_supp χ₁ χ₂ χ₃
  have hbP : (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
        ((χ₁ * χ₂) (n : ZMod q) / (n : ℂ) ^ (((ρ₁.re : ℝ) : ℂ)
            + (((ρ₁.im : ℝ) : ℂ) + ((ρ₂.im : ℝ) : ℂ)) * Complex.I)).re
          * T.f (Real.log n / Real.log (q : ℝ)))
      + (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
        ((χ₁ * χ₂⁻¹) (n : ZMod q) / (n : ℂ) ^ (((ρ₁.re : ℝ) : ℂ)
            + (((ρ₁.im : ℝ) : ℂ) - ((ρ₂.im : ℝ) : ℂ)) * Complex.I)).re
          * T.f (Real.log n / Real.log (q : ℝ)))
      + (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
        ((χ₁ * χ₃) (n : ZMod q) / (n : ℂ) ^ (((ρ₁.re : ℝ) : ℂ)
            + (((ρ₁.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I)).re
          * T.f (Real.log n / Real.log (q : ℝ)))
      + (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
        ((χ₁ * χ₃⁻¹) (n : ZMod q) / (n : ℂ) ^ (((ρ₁.re : ℝ) : ℂ)
            + (((ρ₁.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ)) * Complex.I)).re
          * T.f (Real.log n / Real.log (q : ℝ)))
      + (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
        ((χ₂ * χ₃) (n : ZMod q) / (n : ℂ) ^ (((ρ₁.re : ℝ) : ℂ)
            + (((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I)).re
          * T.f (Real.log n / Real.log (q : ℝ)))
      + (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
        ((χ₂ * χ₃⁻¹) (n : ZMod q) / (n : ℂ) ^ (((ρ₁.re : ℝ) : ℂ)
            + (((ρ₂.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ)) * Complex.I)).re
          * T.f (Real.log n / Real.log (q : ℝ)))
      ≤ 6 * (T.f 0 * (1/6 + ε') * Real.log (q : ℝ)) - (crd0 + crd1 + crd2 + crd3) := by
    linarith only [hb4, hb5, hb6, hb7, hb8, hb9]
  have hb0' : (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
        ((1 : DirichletCharacter ℂ q) (n : ZMod q) / (n : ℂ) ^ ((ρ₁.re : ℝ) : ℂ)).re
          * T.f (Real.log n / Real.log (q : ℝ)))
      ≤ Real.log (q : ℝ) * T.F (-(lamOf q ρ₁)) + T.f 0 * ε' * Real.log (q : ℝ) := by
    have hfl : T.f 0 * (ε'/4) * Real.log (q : ℝ) ≤ T.f 0 * ε' * Real.log (q : ℝ) := by
      have h1 : 0 ≤ T.f 0 * Real.log (q : ℝ) := mul_nonneg T.f0_pos.le hLqpos.le
      nlinarith only [h1, hε']
    linarith only [hb0, hfl]
  exact hb103_kernel T ε' hε' (Lq := Real.log (q : ℝ)) (lam1 := lamOf q ρ₁)
    (lam2 := lamOf q ρ₂) (lam3 := lamOf q ρ₃) hLqpos
    (crd0 := crd0) (crd1 := crd1) (crd2 := crd2) (crd3 := crd3)
    (bt0 := (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
        ((χ₁ * χ₂ * χ₃) (n : ZMod q) / (n : ℂ) ^ (((ρ₁.re : ℝ) : ℂ)
            + (((ρ₁.im : ℝ) : ℂ) + ((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I)).re
          * T.f (Real.log n / Real.log (q : ℝ))))
    (bt1 := (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
        ((χ₁ * χ₂ * χ₃⁻¹) (n : ZMod q) / (n : ℂ) ^ (((ρ₁.re : ℝ) : ℂ)
            + (((ρ₁.im : ℝ) : ℂ) + ((ρ₂.im : ℝ) : ℂ) - ((ρ₃.im : ℝ) : ℂ)) * Complex.I)).re
          * T.f (Real.log n / Real.log (q : ℝ))))
    (bt2 := (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
        ((χ₁ * χ₂⁻¹ * χ₃) (n : ZMod q) / (n : ℂ) ^ (((ρ₁.re : ℝ) : ℂ)
            + (((ρ₁.im : ℝ) : ℂ) - ((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I)).re
          * T.f (Real.log n / Real.log (q : ℝ))))
    (bt3 := (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
        ((χ₁⁻¹ * χ₂ * χ₃) (n : ZMod q) / (n : ℂ) ^ (((ρ₁.re : ℝ) : ℂ)
            + (-((ρ₁.im : ℝ) : ℂ) + ((ρ₂.im : ℝ) : ℂ) + ((ρ₃.im : ℝ) : ℂ)) * Complex.I)).re
          * T.f (Real.log n / Real.log (q : ℝ))))
    (K0 := (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
        ((1 : DirichletCharacter ℂ q) (n : ZMod q) / (n : ℂ) ^ ((ρ₁.re : ℝ) : ℂ)).re
          * T.f (Real.log n / Real.log (q : ℝ))))
    (K1 := (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
        (χ₁ (n : ZMod q) / (n : ℂ) ^ (((ρ₁.re : ℝ) : ℂ)
            + ((ρ₁.im : ℝ) : ℂ) * Complex.I)).re * T.f (Real.log n / Real.log (q : ℝ))))
    (K2 := (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
        (χ₂ (n : ZMod q) / (n : ℂ) ^ (((ρ₁.re : ℝ) : ℂ)
            + ((ρ₂.im : ℝ) : ℂ) * Complex.I)).re * T.f (Real.log n / Real.log (q : ℝ))))
    (K3 := (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
        (χ₃ (n : ZMod q) / (n : ℂ) ^ (((ρ₁.re : ℝ) : ℂ)
            + ((ρ₃.im : ℝ) : ℂ) * Complex.I)).re * T.f (Real.log n / Real.log (q : ℝ))))
    hb0' hb1 hb2 hb3 hbt0 hbt1 hbt2 hbt3 hbP (by linarith only [hpos])

end Work.ZeroFreeTables.OffAxis

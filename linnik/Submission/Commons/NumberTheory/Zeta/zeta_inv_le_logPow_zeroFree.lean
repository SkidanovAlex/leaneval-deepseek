import Mathlib
import Submission.Commons.NumberTheory.Zeta.zeta_zeroFreeRegion_logDeriv_bound
import Submission.Commons.NumberTheory.Zeta.zeta_lower_bound_right_of_one
import Submission.Commons.NumberTheory.LSeries.norm_riemannZeta_lower_of_three_four_one
import Submission.Commons.NumberTheory.LSeries.exists_bound_norm_riemannZeta_fractional
import Submission.Commons.NumberTheory.LSeries.norm_riemannZeta_le_five_mul_log
import Submission.Commons.Analysis.Complex.logDeriv_zeroFree_ball_bound_analytic

/-!
# `1/ζ` is bounded by a power of `log |t|` in the zero-free region

See `Submission.Commons.NumberTheory.Zeta.zeta_zeroFreeRegion_logDeriv_bound` for the zero-free
region input.  Here we show that on `σ ≥ 1 - c/log(|t|+2)`, `σ ≤ 2`, `|t| ≥ 3`, the reciprocal
of `ζ` is bounded by a power of `log(|t|+2)`.
-/

open Complex Metric Set
open scoped Real

namespace Commons.NumberTheory.Zeta

noncomputable section

set_option maxHeartbeats 8000000

/-- `w = (w.re : ℂ) + (w.im : ℂ) * I`. -/
private lemma re_add_im_eq (w : ℂ) : ((w.re : ℂ) + (w.im : ℂ) * Complex.I) = w := by
  apply Complex.ext <;> simp

/-- **Mean-value bound for a holomorphic logarithm along a segment.**  Let `F` be a primitive of
`f'/f` on the ball `B(c,R)` and assume `‖f'/f‖ ≤ K` on the segment `[x,y]`.  Then
`‖F y - F x‖ ≤ K ‖y - x‖`. -/
private theorem norm_sub_le_of_segment {F f : ℂ → ℂ} {c x y : ℂ} {R K : ℝ}
    (hx : x ∈ Metric.ball c R) (hy : y ∈ Metric.ball c R)
    (hF : ∀ w ∈ Metric.ball c R, HasDerivAt F (deriv f w / f w) w)
    (hK : ∀ w ∈ segment ℝ x y, ‖deriv f w / f w‖ ≤ K) :
    ‖F y - F x‖ ≤ K * ‖y - x‖ := by
  have hsub : segment ℝ x y ⊆ Metric.ball c R :=
    (convex_ball c R).segment_subset hx hy
  exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := F) (s := segment ℝ x y) (C := K)
    (f' := fun w => ContinuousLinearMap.toSpanSingleton ℂ (deriv f w / f w))
    (x := x) (y := y)
    (fun w hw => ((hF w (hsub hw)).hasFDerivAt).hasFDerivWithinAt)
    (fun w hw => by
      rw [ContinuousLinearMap.norm_toSpanSingleton]
      exact hK w hw)
    (convex_segment x y) (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)

/-- For `σ ≤ σ₂`, every point of the segment from `σ + it` to `σ₂ + it` is at distance at most
`σ₂ - σ` from `σ₂ + it`. -/
private lemma segment_dist_endpoint_le {σ σ₂ t : ℝ} (hσσ₂ : σ ≤ σ₂) {w : ℂ}
    (hw : w ∈ segment ℝ ((σ : ℂ) + (t : ℂ) * Complex.I) ((σ₂ : ℂ) + (t : ℂ) * Complex.I)) :
    ‖w - ((σ₂ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ σ₂ - σ := by
  rw [segment_eq_image'] at hw
  obtain ⟨θ, hθ, rfl⟩ := hw
  have hθ1 : (0 : ℝ) ≤ 1 - θ := by linarith [hθ.2]
  have hxy : ‖(((σ : ℂ) + (t : ℂ) * Complex.I)) - (((σ₂ : ℂ) + (t : ℂ) * Complex.I))‖
      = σ₂ - σ := by
    have h : (((σ : ℂ) + (t : ℂ) * Complex.I)) - (((σ₂ : ℂ) + (t : ℂ) * Complex.I))
        = (((σ - σ₂ : ℝ)) : ℂ) := by
      apply Complex.ext <;> simp
    rw [h, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    ring
  have hrewrite : ((σ : ℂ) + (t : ℂ) * Complex.I)
        + θ • ((((σ₂ : ℂ) + (t : ℂ) * Complex.I)) - (((σ : ℂ) + (t : ℂ) * Complex.I)))
        - (((σ₂ : ℂ) + (t : ℂ) * Complex.I)) = (1 - θ) • ((((σ : ℂ) + (t : ℂ) * Complex.I))
        - (((σ₂ : ℂ) + (t : ℂ) * Complex.I))) := by
    module
  rw [hrewrite, norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ1, hxy]
  have hle : (1 - θ) * (σ₂ - σ) ≤ 1 * (σ₂ - σ) :=
    mul_le_mul_of_nonneg_right (by linarith [hθ.1]) (by linarith)
  linarith [hle]

/-- Case `σ ≥ 1`: the classical `3`–`4`–`1` lower bound, with explicit constant
`‖ζ(σ+it)‖ ≥ 1/(10 log(|t|+2))` for `1 + 1/(4 log(|t|+2)) ≤ σ ≤ 2`, `|t| ≥ 1`. -/
private lemma zeta_norm_ge_inv_log_of_ge_one {σ t : ℝ}
    (hσ : 1 + 1 / (4 * Real.log (|t| + 2)) ≤ σ) (hσ2 : σ ≤ 2) (ht : 1 ≤ |t|) :
    1 / (10 * Real.log (|t| + 2)) ≤ ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
  set L : ℝ := Real.log (|t| + 2) with hL
  have hL1 : 1 ≤ L := by
    rw [hL]
    have h3 : Real.log 3 ≤ Real.log (|t| + 2) :=
      Real.log_le_log (by norm_num) (by linarith [abs_nonneg t, ht])
    linarith [Real.log_three_gt_d9]
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL1
  have hσ1 : 1 < σ := by
    have : 0 < 1 / (4 * L) := by positivity
    linarith
  have hmain : ((σ - 1) ^ 3 / (100 * L)) ^ (1 / 4 : ℝ) ≤
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
    have h := Commons.NumberTheory.LSeries.norm_riemannZeta_lower_of_three_four_one
      (σ := σ) (t := t) hσ1 hσ2 ht
    rw [← hL] at h
    exact h
  have hsm1 : 1 / (4 * L) ≤ σ - 1 := by linarith
  have hcube : (1 / (4 * L)) ^ 3 ≤ (σ - 1) ^ 3 :=
    pow_le_pow_left₀ (by positivity) hsm1 3
  have hA : (1 / (4 * L)) ^ 3 / (100 * L) = 1 / (6400 * L ^ 4) := by
    field_simp
    ring
  have hnum1 : 1 / (6400 * L ^ 4) ≤ (σ - 1) ^ 3 / (100 * L) := by
    rw [← hA]
    exact div_le_div_of_nonneg_right hcube (by positivity)
  have hnum2 : 1 / (10000 * L ^ 4) ≤ 1 / (6400 * L ^ 4) :=
    one_div_le_one_div_of_le (by positivity) (by
      have hL4 : (1:ℝ) ≤ L ^ 4 := one_le_pow₀ hL1
      nlinarith [hL4])
  have hnum : 1 / (10000 * L ^ 4) ≤ (σ - 1) ^ 3 / (100 * L) := le_trans hnum2 hnum1
  have hbase : (1 / (10000 * L ^ 4)) ^ (1 / 4 : ℝ) = 1 / (10 * L) := by
    have hy : (0 : ℝ) ≤ 1 / (10 * L) := by positivity
    have h4 : (1 / (10 * L)) ^ 4 = 1 / (10000 * L ^ 4) := by
      rw [div_pow]
      norm_num
      ring
    rw [← h4, ← Real.rpow_natCast (1 / (10 * L)) 4, ← Real.rpow_mul hy]
    norm_num
  calc 1 / (10 * L) = (1 / (10000 * L ^ 4)) ^ (1 / 4 : ℝ) := hbase.symm
    _ ≤ ((σ - 1) ^ 3 / (100 * L)) ^ (1 / 4 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hnum (by norm_num)
    _ ≤ ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := hmain

/-- Case `σ < 1 + 1/(4L)`: Borel–Carathéodory on a ball around `1 + 1/(4L) + it` inside the
zero-free region. -/
private lemma zeta_inv_le_logpow_of_lt_one (c₁ cL Cfr : ℝ) (hc₁pos : 0 < c₁) (hc₁le1 : c₁ ≤ 1)
    (hcLpos : 0 < cL)
    (hlowB : ∀ (h t : ℝ), 0 < h → h ≤ 1 / 4 →
      cL * h ≤ ‖riemannZeta (((1 + h : ℝ) : ℂ) + Complex.I * (t : ℂ))‖)
    (hCfrpos : 0 < Cfr)
    (hfr : ∀ (σ t : ℝ), 1 / 2 ≤ σ → σ ≤ 1 → 1 ≤ |t| →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ Cfr * |t| ^ (1 - σ) * Real.log (|t| + 2))
    (hZF₁ : ∀ t : ℝ, 1 ≤ |t| → ∀ σ : ℝ, 1 - c₁ / Real.log (|t| + 3) ≤ σ →
      riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ t : ℝ, 3 ≤ |t| →
      1 - (c₁ / 10) / Real.log (|t| + 2) ≤ σ → σ ≤ 1 + 1 / (4 * Real.log (|t| + 2)) →
        1 / ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          C * (Real.log (|t| + 2)) ^ C := by
  set cT : ℝ := c₁ / 10 with hcTdef
  have hcTpos : 0 < cT := by positivity
  have hcTle : cT ≤ 1 / 10 := by rw [hcTdef]; linarith
  set CM : ℝ := max 10 (max (2 * Cfr * Real.exp (1 / 5)) cL) + 1 with hCMdef
  have hCM10 : 10 ≤ CM := by
    rw [hCMdef]
    linarith [le_max_left 10 (max (2 * Cfr * Real.exp (1 / 5)) cL)]
  have hCMfr : 2 * Cfr * Real.exp (1 / 5) ≤ CM := by
    rw [hCMdef]
    linarith [le_max_right 10 (max (2 * Cfr * Real.exp (1 / 5)) cL),
      le_max_left (2 * Cfr * Real.exp (1 / 5)) cL]
  have hCMcL : cL ≤ CM := by
    rw [hCMdef]
    linarith [le_max_right 10 (max (2 * Cfr * Real.exp (1 / 5)) cL),
      le_max_right (2 * Cfr * Real.exp (1 / 5)) cL]
  have hCMpos : 0 < CM := lt_of_lt_of_le (by norm_num : (0:ℝ) < 10) hCM10
  set CA : ℝ := 2 * |Real.log (8 * CM / cL)| + 4 with hCAdef
  have hCA4 : 4 ≤ CA := by rw [hCAdef]; linarith [abs_nonneg (Real.log (8*CM/cL))]
  have hCApos : 0 < CA := by linarith
  set GEOM : ℝ := (1 + 6 * cT) / cT ^ 2 with hGEOMdef
  have hGEOMpos : 0 < GEOM := by rw [hGEOMdef]; positivity
  set CB : ℝ := |Real.log (cL / 4)| + 1 + CA * GEOM * (1 / 4 + cT) with hCBdef
  have hCBpos : 0 < CB := by
    rw [hCBdef]
    have h1 : 0 < CA * GEOM * (1 / 4 + cT) := by positivity
    have h2 := abs_nonneg (Real.log (cL / 4))
    linarith
  refine ⟨max CB (3 ^ CB) + 1, by positivity, ?_⟩
  intro σ t ht hσlo hσhi
  set L : ℝ := Real.log (|t| + 2) with hLdef
  have hL1 : 1 ≤ L := by
    rw [hLdef]
    have h3 : Real.log 3 ≤ Real.log (|t| + 2) :=
      Real.log_le_log (by norm_num) (by linarith [abs_nonneg t, ht])
    linarith [Real.log_three_gt_d9]
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL1
  have hL2pos : 0 < L + 2 := by linarith
  have hlog2ge1 : 1 ≤ Real.log (L + 2) := by
    rw [Real.le_log_iff_exp_le hL2pos]
    linarith [Real.exp_one_lt_d9]
  -- reference point
  set hh : ℝ := 1 / (4 * L) with hhhdef
  have hhpos : 0 < hh := by rw [hhhdef]; positivity
  have hhle : hh ≤ 1 / 4 := by
    rw [hhhdef, div_le_iff₀ (by positivity)]; linarith
  set σ₂ : ℝ := 1 + hh with hσ₂def
  have hσσ₂ : σ ≤ σ₂ := by rw [hσ₂def]; linarith
  set R : ℝ := (1 / 4 + 2 * cT) / L with hRdef
  have hRpos : 0 < R := by rw [hRdef]; positivity
  have hRle1 : R ≤ 1 := by
    rw [hRdef, div_le_one (by positivity)]
    nlinarith [hcTle, hL1]
  have hdist : σ₂ - σ ≤ (1 / 4 + cT) / L := by
    have h2 : σ₂ = 1 + 1 / (4 * L) := by rw [hσ₂def, hhhdef]
    rw [h2]
    have h3 : (1 + 1 / (4 * L)) - (1 - cT / L) = (1 / 4 + cT) / L := by
      field_simp
      ring
    linarith [hσlo, h3]
  set c : ℂ := (σ₂ : ℂ) + (t : ℂ) * Complex.I with hcdef
  set x : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hxdef
  have hxdist : ‖x - c‖ = σ₂ - σ := by
    rw [hxdef, hcdef]
    have h : ((σ : ℂ) + (t : ℂ) * Complex.I) - ((σ₂ : ℂ) + (t : ℂ) * Complex.I)
        = (((σ - σ₂ : ℝ)) : ℂ) := by
      apply Complex.ext <;> simp
    rw [h, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    ring
  have hxball : x ∈ Metric.ball c R := by
    rw [Metric.mem_ball, dist_eq_norm, hxdist]
    refine lt_of_le_of_lt hdist ?_
    rw [hRdef]
    exact div_lt_div_of_pos_right (by linarith) hLpos
  have hyball : c ∈ Metric.ball c R := Metric.mem_ball_self hRpos
  -- the ball avoids `1`
  have hne1 : ∀ w ∈ Metric.ball c R, w ≠ 1 := by
    intro w hw hcon
    have h1 : ‖w - c‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using hw
    have h2 : ‖w - c‖ = ‖(1 : ℂ) - c‖ := by rw [hcon]
    have h3 : (3:ℝ) ≤ ‖(1 : ℂ) - c‖ := by
      have h : (1 : ℂ) - c = (((-hh : ℝ)) : ℂ) + (((-t : ℝ)) : ℂ) * Complex.I := by
        rw [hcdef, hσ₂def]; push_cast; ring
      rw [h]
      have hnorm : |(-t)| ≤ ‖(((-hh : ℝ)) : ℂ) + (((-t : ℝ)) : ℂ) * Complex.I‖ := by
        have := Complex.abs_im_le_norm ((((-hh : ℝ)) : ℂ) + (((-t : ℝ)) : ℂ) * Complex.I)
        simpa using this
      calc (3:ℝ) ≤ |t| := ht
        _ = |-t| := by rw [abs_neg]
        _ ≤ _ := hnorm
    linarith [hRle1]
  have hAn : AnalyticOnNhd ℂ riemannZeta (Metric.ball c R) := by
    rw [Complex.analyticOnNhd_iff_differentiableOn Metric.isOpen_ball]
    intro w hw
    exact (differentiableAt_riemannZeta (hne1 w hw)).differentiableWithinAt
  -- geometry
  have hball_re : ∀ w ∈ Metric.ball c R, 1 - 2 * cT / L ≤ w.re := by
    intro w hw
    have h1 : ‖w - c‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using hw
    have h2 : |w.re - σ₂| ≤ ‖w - c‖ := by
      have h := Complex.abs_re_le_norm (w - c)
      rwa [show (w - c).re = w.re - σ₂ by simp [hcdef]] at h
    have h3 : σ₂ - ‖w - c‖ ≤ w.re := by
      rw [abs_le] at h2; linarith [h2.1]
    have h4 : σ₂ - R < σ₂ - ‖w - c‖ := by linarith
    have h5 : σ₂ - R = 1 - 2 * cT / L := by
      rw [hσ₂def, hhhdef, hRdef]; field_simp; ring
    rw [h5] at h4
    linarith [h4, h3]
  have hball_im_ge : ∀ w ∈ Metric.ball c R, |t| - R ≤ |w.im| := by
    intro w hw
    have h1 : ‖w - c‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using hw
    have h2 : |w.im - t| ≤ ‖w - c‖ := by
      have h := Complex.abs_im_le_norm (w - c)
      rwa [show (w - c).im = w.im - t by simp [hcdef]] at h
    have h3 : |t| - |w.im| ≤ |w.im - t| := by
      simpa [abs_sub_comm] using abs_sub_abs_le_abs_sub t w.im
    linarith
  have hball_im_le : ∀ w ∈ Metric.ball c R, |w.im| ≤ |t| + 1 := by
    intro w hw
    have h1 : ‖w - c‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using hw
    have h2 : |w.im - t| ≤ ‖w - c‖ := by
      have h := Complex.abs_im_le_norm (w - c)
      rwa [show (w - c).im = w.im - t by simp [hcdef]] at h
    have h3 : |w.im| - |t| ≤ |w.im - t| := by
      simpa [abs_sub_comm] using abs_sub_abs_le_abs_sub w.im t
    linarith
  have hball_im1 : ∀ w ∈ Metric.ball c R, 1 ≤ |w.im| := by
    intro w hw
    have := hball_im_ge w hw
    linarith [hRle1, ht]
  have hball_re_half : ∀ w ∈ Metric.ball c R, (1/2 : ℝ) ≤ w.re := by
    intro w hw
    have h1 := hball_re w hw
    have h2 : cT / L ≤ 1 / 10 := by
      rw [div_le_iff₀ hLpos]
      have h3 : (1:ℝ) / 10 ≤ (1 / 10) * L := by nlinarith [hL1]
      linarith [hcTle, h3]
    have h4 : 2 * (cT / L) ≤ 2 * (1 / 10) := mul_le_mul_of_nonneg_left h2 (by norm_num)
    have h5 : 2 * cT / L = 2 * (cT / L) := by ring
    linarith [h1, h4, h5]
  -- zero-freeness on the ball
  have hne : ∀ w ∈ Metric.ball c R, riemannZeta w ≠ 0 := by
    intro w hw
    have hre := hball_re w hw
    have hτ1 := hball_im1 w hw
    have hτle := hball_im_le w hw
    have hlog : Real.log (|w.im| + 3) ≤ 2 * L := by
      have hle : |w.im| + 3 ≤ 2 * (|t| + 2) := by linarith [hτle]
      calc Real.log (|w.im| + 3) ≤ Real.log (2 * (|t| + 2)) :=
            Real.log_le_log (by linarith [abs_nonneg w.im]) hle
        _ = Real.log 2 + Real.log (|t| + 2) :=
            Real.log_mul (by norm_num) (by linarith [abs_nonneg t])
        _ ≤ L + L := by
            have h2 : Real.log 2 ≤ L := by
              rw [hLdef]
              exact Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
            linarith
        _ = 2 * L := by ring
    have hlog2 : 0 < Real.log (|w.im| + 3) := Real.log_pos (by linarith [abs_nonneg w.im])
    have hz := hZF₁ w.im hτ1 w.re (by
      have h5L : Real.log (|w.im| + 3) ≤ 5 * L := by linarith
      have hc5 : c₁ / (5 * L) ≤ c₁ / Real.log (|w.im| + 3) := by
        rw [div_le_div_iff₀ (by positivity) hlog2]
        nlinarith [hc₁pos, h5L]
      have hw5 : 1 - c₁ / (5 * L) ≤ w.re := by
        have h4 : c₁ / (5 * L) = 2 * cT / L := by rw [hcTdef]; field_simp; ring
        rw [h4]; linarith
      linarith)
    simpa [re_add_im_eq w] using hz
  -- sup bound `M`
  set M : ℝ := CM * (L + 1) with hMdef
  have hMpos : 0 < M := by rw [hMdef]; positivity
  have hMge : ∀ w ∈ Metric.ball c R, ‖riemannZeta w‖ ≤ M := by
    intro w hw
    have hre := hball_re w hw
    have hτ1 := hball_im1 w hw
    have hτle := hball_im_le w hw
    have hlog2 : Real.log (|w.im| + 2) ≤ 2 * L := by
      have hle : |w.im| + 2 ≤ 2 * (|t| + 2) := by linarith [hτle]
      calc Real.log (|w.im| + 2) ≤ Real.log (2 * (|t| + 2)) :=
            Real.log_le_log (by linarith [abs_nonneg w.im]) hle
        _ = Real.log 2 + Real.log (|t| + 2) :=
            Real.log_mul (by norm_num) (by linarith [abs_nonneg t])
        _ ≤ L + L := by
            have h2 : Real.log 2 ≤ L := by
              rw [hLdef]
              exact Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
            linarith
        _ = 2 * L := by ring
    by_cases hge : (1:ℝ) ≤ w.re
    · have hb := Commons.NumberTheory.LSeries.norm_riemannZeta_le_five_mul_log
          (σ := w.re) (t := w.im) hge hτ1
      have hb' : ‖riemannZeta w‖ ≤ 5 * Real.log (|w.im| + 2) := by
        simpa [re_add_im_eq w] using hb
      calc ‖riemannZeta w‖ ≤ 5 * Real.log (|w.im| + 2) := hb'
        _ ≤ 5 * (2 * L) := by linarith
        _ = 10 * L := by ring
        _ ≤ CM * (L + 1) := by
            have h1 : 10 * L ≤ CM * L := mul_le_mul_of_nonneg_right hCM10 (by linarith)
            have h2 : CM * L ≤ CM * (L + 1) :=
              mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hCMpos)
            linarith
        _ = M := hMdef.symm
    · have hhalf := hball_re_half w hw
      have hlt1 : w.re < 1 := lt_of_not_ge hge
      have hb := hfr w.re w.im hhalf (le_of_lt hlt1) hτ1
      have hb' : ‖riemannZeta w‖ ≤ Cfr * |w.im| ^ (1 - w.re) * Real.log (|w.im| + 2) := by
        simpa [re_add_im_eq w] using hb
      have hpow : |w.im| ^ (1 - w.re) ≤ Real.exp (1 / 5) := by
        have him0 : 0 < |w.im| := lt_of_lt_of_le one_pos hτ1
        rw [Real.rpow_def_of_pos him0]
        apply Real.exp_le_exp.mpr
        have hlogim : Real.log |w.im| ≤ L := by
          rw [hLdef]
          apply Real.log_le_log him0
          linarith
        have h1a : 1 - w.re ≤ 2 * cT / L := by linarith
        have h1ann : 0 ≤ 1 - w.re := by linarith
        have h1 : Real.log |w.im| * (1 - w.re) ≤ L * (2 * cT / L) :=
          mul_le_mul hlogim h1a h1ann (le_of_lt hLpos)
        have h2 : L * (2 * cT / L) = 2 * cT := by field_simp
        linarith [h1, h2, hcTle]
      have hlog2nn : 0 ≤ Real.log (|w.im| + 2) := Real.log_nonneg (by linarith [abs_nonneg w.im])
      have hc : 0 ≤ Cfr := le_of_lt hCfrpos
      calc ‖riemannZeta w‖ ≤ Cfr * |w.im| ^ (1 - w.re) * Real.log (|w.im| + 2) := hb'
        _ ≤ Cfr * Real.exp (1 / 5) * (2 * L) := by
            have h1 : Cfr * |w.im| ^ (1 - w.re) ≤ Cfr * Real.exp (1 / 5) :=
              mul_le_mul_of_nonneg_left hpow hc
            calc Cfr * |w.im| ^ (1 - w.re) * Real.log (|w.im| + 2)
                ≤ (Cfr * Real.exp (1 / 5)) * (2 * L) :=
                  mul_le_mul h1 hlog2 hlog2nn (by positivity)
              _ = Cfr * Real.exp (1 / 5) * (2 * L) := by ring
        _ = 2 * Cfr * Real.exp (1 / 5) * L := by ring
        _ ≤ CM * (L + 1) := by
            have h1 : 2 * Cfr * Real.exp (1 / 5) * L ≤ CM * L :=
              mul_le_mul_of_nonneg_right hCMfr (by linarith)
            have h2 : CM * L ≤ CM * (L + 1) :=
              mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hCMpos)
            linarith
        _ = M := hMdef.symm
  -- lower bound at the centre
  have hm_le : cL * hh ≤ ‖riemannZeta c‖ := by
    have h := hlowB hh t hhpos hhle
    have harg : (((1 + hh : ℝ) : ℂ) + Complex.I * (t : ℂ)) = c := by
      rw [hcdef, hσ₂def]; push_cast; ring
    rwa [harg] at h
  have hmM : cL * hh ≤ M := by
    rw [hMdef, hhhdef]
    have h1 : cL / (4 * L) ≤ CM := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [hCMcL, hL1]
    nlinarith [h1, hL1, hcLpos]
  -- Borel–Carathéodory
  have hBC : ∀ ⦃z₀ : ℂ⦄, z₀ ∈ Metric.ball c R → ∀ ρ : ℝ, 0 < ρ → ρ < R - ‖z₀ - c‖ →
      ‖deriv riemannZeta z₀ / riemannZeta z₀‖ ≤
        2 * (Real.log (2 * M) - Real.log (cL * hh)) *
          (‖z₀ - c‖ + ρ) / ((R - ‖z₀ - c‖ - ρ) * ρ) :=
    Commons.Analysis.Complex.logDeriv_zeroFree_ball_bound_analytic
      (c := c) (R := R) (m := cL * hh) (M := M)
      hRpos (by positivity) hmM hAn hne hMge hm_le
  set K : ℝ := CA * Real.log (L + 2) * GEOM * L with hKdef
  have hsegK : ∀ w ∈ segment ℝ x c, ‖deriv riemannZeta w / riemannZeta w‖ ≤ K := by
    intro w hw
    have hwd : ‖w - c‖ ≤ σ₂ - σ := by
      rw [hxdef, hcdef] at hw
      exact segment_dist_endpoint_le hσσ₂ hw
    have hwball : w ∈ Metric.ball c R := by
      rw [Metric.mem_ball, dist_eq_norm]
      refine lt_of_le_of_lt hwd ?_
      refine lt_of_le_of_lt hdist ?_
      rw [hRdef]
      exact div_lt_div_of_pos_right (by linarith) hLpos
    set ρ : ℝ := cT / (2 * L) with hρdef
    have hρpos : 0 < ρ := by rw [hρdef]; positivity
    have hRsub : cT / L ≤ R - (σ₂ - σ) := by
      have h2 : R - (1/4 + cT)/L = cT / L := by rw [hRdef]; field_simp; ring
      linarith [hdist, h2]
    have hρlt : ρ < R - ‖w - c‖ := by
      have h2 : ρ < cT / L := by
        rw [hρdef]
        have h3 : cT / (2 * L) = (cT / 2) / L := by ring
        rw [h3]
        exact div_lt_div_of_pos_right (by linarith) hLpos
      have h1 : cT / L ≤ R - ‖w - c‖ := by linarith [hwd, hRsub]
      linarith
    have hbc := hBC hwball ρ hρpos hρlt
    have hnum1 : ‖w - c‖ + ρ ≤ (1/4 + 3*cT/2) / L := by
      rw [hρdef]
      have h1 : ‖w - c‖ ≤ (1/4 + cT) / L := le_trans hwd hdist
      have h2 : (1/4 + cT)/L + cT/(2*L) = (1/4 + 3*cT/2)/L := by field_simp; ring
      linarith [h1]
    have hden1 : cT / (2 * L) ≤ R - ‖w - c‖ - ρ := by
      rw [hρdef]
      have h1 : cT / L ≤ R - ‖w - c‖ := by linarith [hwd, hRsub]
      have h3 : cT / L - cT / (2 * L) = cT / (2 * L) := by field_simp; ring
      linarith [h1, h3]
    have hden2 : (cT / (2 * L)) * ρ = cT ^ 2 / (4 * L ^ 2) := by
      rw [hρdef]; field_simp; ring
    have hden_le : cT ^ 2 / (4 * L ^ 2) ≤ (R - ‖w - c‖ - ρ) * ρ := by
      rw [← hden2]
      exact mul_le_mul_of_nonneg_right hden1 (le_of_lt hρpos)
    have hfac : (‖w - c‖ + ρ) / ((R - ‖w - c‖ - ρ) * ρ) ≤ GEOM * L := by
      have hdenpos : 0 < (R - ‖w - c‖ - ρ) * ρ := by nlinarith [hden1, hρpos]
      have hDpos : 0 < cT ^ 2 / (4 * L ^ 2) := by positivity
      have hAD : ((1/4 + 3*cT/2) / L) / (cT ^ 2 / (4 * L ^ 2)) = (1 + 6*cT) / cT ^ 2 * L := by
        field_simp; ring
      rw [hGEOMdef, ← hAD]
      calc (‖w - c‖ + ρ) / ((R - ‖w - c‖ - ρ) * ρ)
          ≤ ((1/4 + 3*cT/2) / L) / ((R - ‖w - c‖ - ρ) * ρ) :=
            div_le_div_of_nonneg_right hnum1 (le_of_lt hdenpos)
        _ ≤ ((1/4 + 3*cT/2) / L) / (cT ^ 2 / (4 * L ^ 2)) := by
            rw [div_le_div_iff₀ hdenpos hDpos]
            exact mul_le_mul_of_nonneg_left hden_le (by positivity)
    have hlogbd : 2 * (Real.log (2 * M) - Real.log (cL * hh)) ≤ CA * Real.log (L + 2) := by
      have h2M : 2 * M = 2 * CM * (L + 1) := by rw [hMdef]; ring
      have hm : cL * hh = cL / (4 * L) := by rw [hhhdef]; ring
      have hratio : 2 * M / (cL * hh) = (8 * CM / cL) * (L * (L + 1)) := by
        rw [h2M, hm]
        field_simp
        ring
      have hlogratio : Real.log (2 * M) - Real.log (cL * hh)
          = Real.log (2 * M / (cL * hh)) := by
        rw [Real.log_div (by positivity) (by positivity)]
      rw [hlogratio, hratio]
      have hlogmul : Real.log ((8 * CM / cL) * (L * (L + 1)))
          = Real.log (8 * CM / cL) + Real.log L + Real.log (L + 1) := by
        have h1 : (8 * CM / cL) ≠ 0 := by positivity
        have h2 : L * (L + 1) ≠ 0 := by
          exact mul_ne_zero hLpos.ne' (ne_of_gt (by linarith)) 
        have h3 : (L + 1 : ℝ) ≠ 0 := ne_of_gt (by linarith)
        rw [Real.log_mul h1 h2, Real.log_mul hLpos.ne' h3]
        ring
      rw [hlogmul]
      have hlogL : Real.log L ≤ Real.log (L + 2) := Real.log_le_log hLpos (by linarith)
      have hlogL1 : Real.log (L + 1) ≤ Real.log (L + 2) :=
        Real.log_le_log (by linarith) (by linarith)
      have hlogabs : Real.log (8 * CM / cL) ≤ |Real.log (8 * CM / cL)| := le_abs_self _
      have hAnn : 0 ≤ |Real.log (8 * CM / cL)| := abs_nonneg _
      have hstep1 : 2 * (Real.log (8 * CM / cL) + Real.log L + Real.log (L + 1))
          ≤ 2 * |Real.log (8 * CM / cL)| + 4 * Real.log (L + 2) := by linarith
      have hstep2 : 2 * |Real.log (8 * CM / cL)| + 4 * Real.log (L + 2)
          ≤ CA * Real.log (L + 2) := by
        rw [hCAdef]
        have h1 : 2 * |Real.log (8 * CM / cL)| ≤ 2 * |Real.log (8 * CM / cL)| * Real.log (L + 2) := by
          have := mul_le_mul_of_nonneg_left hlog2ge1 hAnn
          linarith
        nlinarith [h1]
      linarith
    calc ‖deriv riemannZeta w / riemannZeta w‖
        ≤ 2 * (Real.log (2 * M) - Real.log (cL * hh)) *
            (‖w - c‖ + ρ) / ((R - ‖w - c‖ - ρ) * ρ) := hbc
      _ = 2 * (Real.log (2 * M) - Real.log (cL * hh)) *
            ((‖w - c‖ + ρ) / ((R - ‖w - c‖ - ρ) * ρ)) := by ring
      _ ≤ (CA * Real.log (L + 2)) * (GEOM * L) := by
          apply mul_le_mul hlogbd hfac (by positivity) (by positivity)
      _ = K := by rw [hKdef]; ring
  -- primitive, mean-value bound
  obtain ⟨F, _hFdiff, hFder, _hFc, hFre⟩ :=
    Commons.Analysis.Complex.logPrimitiveOnBall_analytic (g := riemannZeta) hAn hRpos hne
  have hmv := norm_sub_le_of_segment (F := F) (f := riemannZeta) (c := c)
    (x := x) (y := c) (R := R) (K := K) hxball hyball (fun w hw => hFder w hw) hsegK
  have hre : (F c).re - (F x).re ≤ K * ‖c - x‖ := by
    have h1 : (F c - F x).re ≤ ‖F c - F x‖ := Complex.re_le_norm _
    rw [Complex.sub_re] at h1
    linarith [hmv]
  rw [hFre c hyball, hFre x hxball] at hre
  have hcx : ‖c - x‖ = σ₂ - σ := by
    rw [norm_sub_rev c x, hxdist]
  rw [hcx] at hre
  -- final chain
  have h5 : K * (σ₂ - σ) ≤ CA * Real.log (L + 2) * GEOM * (1 / 4 + cT) := by
    rw [hKdef]
    have h7 : 0 ≤ CA * Real.log (L + 2) * GEOM * L := by
      have h8 : 0 ≤ Real.log (L + 2) := Real.log_nonneg (by linarith)
      positivity
    calc CA * Real.log (L + 2) * GEOM * L * (σ₂ - σ)
        ≤ CA * Real.log (L + 2) * GEOM * L * ((1 / 4 + cT) / L) :=
          mul_le_mul_of_nonneg_left hdist h7
      _ = CA * Real.log (L + 2) * GEOM * (1 / 4 + cT) := by
          field_simp
  have hlow : Real.log (‖riemannZeta x‖) ≥ -CB * Real.log (L + 2) := by
    have h1 : Real.log (cL * hh) = Real.log (cL / 4) - Real.log L := by
      have h1a : cL * hh = (cL / 4) / L := by rw [hhhdef]; ring
      rw [h1a, Real.log_div (div_ne_zero hcLpos.ne' (by norm_num)) hLpos.ne']
    have h2 : -Real.log (cL / 4) ≤ |Real.log (cL / 4)| := neg_le_abs _
    have h3 : Real.log L ≤ Real.log (L + 2) := Real.log_le_log hLpos (by linarith)
    have hAnL : 0 ≤ |Real.log (cL / 4)| := abs_nonneg _
    have hlgc : Real.log (cL * hh) ≤ Real.log ‖riemannZeta c‖ :=
      Real.log_le_log (by positivity) hm_le
    have hB : Real.log ‖riemannZeta x‖ ≥ Real.log (cL * hh) - K * (σ₂ - σ) := by
      linarith [hre, hlgc]
    have hAB : |Real.log (cL / 4)| ≤ |Real.log (cL / 4)| * Real.log (L + 2) := by
      have := mul_le_mul_of_nonneg_left hlog2ge1 hAnL
      linarith
    have hC : Real.log (cL * hh) - K * (σ₂ - σ) ≥ -CB * Real.log (L + 2) := by
      rw [h1, hCBdef]
      nlinarith [h2, h3, h5, hAB]
    linarith
  have hxne : riemannZeta x ≠ 0 := hne x hxball
  have hxnormpos : 0 < ‖riemannZeta x‖ := norm_pos_iff.mpr hxne
  have hexp : Real.exp (-CB * Real.log (L + 2)) ≤ ‖riemannZeta x‖ := by
    have := Real.exp_le_exp.mpr hlow
    rwa [Real.exp_log hxnormpos] at this
  have hfinal : 1 / ‖riemannZeta x‖ ≤ (3 ^ CB) * L ^ CB := by
    have h1 : 1 / ‖riemannZeta x‖ ≤ 1 / Real.exp (-CB * Real.log (L + 2)) :=
      one_div_le_one_div_of_le (Real.exp_pos _) hexp
    have h2 : 1 / Real.exp (-CB * Real.log (L + 2)) = (L + 2) ^ CB := by
      rw [show (-CB * Real.log (L + 2)) = -(CB * Real.log (L + 2)) by ring]
      rw [one_div, Real.exp_neg, inv_inv]
      rw [Real.rpow_def_of_pos hL2pos]
      congr 1
      ring
    rw [h2] at h1
    calc 1 / ‖riemannZeta x‖ ≤ (L + 2) ^ CB := h1
      _ ≤ (3 * L) ^ CB := Real.rpow_le_rpow (by linarith) (by linarith) hCBpos.le
      _ = 3 ^ CB * L ^ CB := Real.mul_rpow (by norm_num) hLpos.le
  have hxeq : x = (σ : ℂ) + (t : ℂ) * Complex.I := hxdef
  rw [hxeq] at hfinal
  have hK_ge : 3 ^ CB ≤ max CB (3 ^ CB) + 1 := by
    have := le_max_right CB (3 ^ CB); linarith
  have hK_geCB : CB ≤ max CB (3 ^ CB) + 1 := by
    have := le_max_left CB (3 ^ CB); linarith
  calc 1 / ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ 3 ^ CB * L ^ CB := hfinal
    _ ≤ (max CB (3 ^ CB) + 1) * L ^ (max CB (3 ^ CB) + 1) := by
        apply mul_le_mul hK_ge (Real.rpow_le_rpow_of_exponent_le hL1 hK_geCB)
          (by positivity) (by positivity)

/-- **Main theorem.** -/
theorem zeta_inv_le_logPow_zeroFree :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ σ t : ℝ, 3 ≤ |t| →
      1 - c / Real.log (|t| + 2) ≤ σ → σ ≤ 2 →
        1 / ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          C * (Real.log (|t| + 2)) ^ C := by
  obtain ⟨c₀, C₀, hc₀pos, hC₀pos, hZF₀, hDeriv₀⟩ := zeta_zeroFreeRegion_logDeriv_bound
  obtain ⟨cL, hcLpos, hlowB⟩ := zeta_lower_bound_right_of_one
  obtain ⟨Cfr, hCfrpos, hfr⟩ :=
    Commons.NumberTheory.LSeries.exists_bound_norm_riemannZeta_fractional
  set c₁ : ℝ := min c₀ 1 with hc₁def
  have hc₁pos : 0 < c₁ := lt_min hc₀pos one_pos
  have hc₁le : c₁ ≤ c₀ := min_le_left _ _
  have hc₁le1 : c₁ ≤ 1 := min_le_right _ _
  have hZF₁ : ∀ t : ℝ, 1 ≤ |t| → ∀ σ : ℝ, 1 - c₁ / Real.log (|t| + 3) ≤ σ →
      riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    intro t ht σ hσ
    have hlog : 0 < Real.log (|t| + 3) := Real.log_pos (by linarith [abs_nonneg t])
    have hle : c₁ / Real.log (|t| + 3) ≤ c₀ / Real.log (|t| + 3) :=
      div_le_div_of_nonneg_right hc₁le (le_of_lt hlog)
    simpa [mul_comm] using hZF₀ t ht σ (by linarith)
  obtain ⟨CB, hCBpos, hCBbound⟩ :=
    zeta_inv_le_logpow_of_lt_one c₁ cL Cfr hc₁pos hc₁le1 hcLpos hlowB hCfrpos hfr hZF₁
  set CT : ℝ := max CB 10 + 1 with hCTdef
  have hCT1 : 1 ≤ CT := by rw [hCTdef]; linarith [le_max_right CB 10]
  have hCT10 : 10 ≤ CT := by rw [hCTdef]; linarith [le_max_right CB 10]
  have hCTCB : CB ≤ CT := by rw [hCTdef]; linarith [le_max_left CB 10]
  refine ⟨c₁ / 10, CT, by positivity, by linarith, ?_⟩
  intro σ t ht hσlo hσhi
  have hL1 : 1 ≤ Real.log (|t| + 2) := by
    have h3 : Real.log 3 ≤ Real.log (|t| + 2) :=
      Real.log_le_log (by norm_num) (by linarith [abs_nonneg t, ht])
    linarith [Real.log_three_gt_d9]
  have hLnn : 0 ≤ Real.log (|t| + 2) := by linarith
  by_cases hcase : σ ≤ 1 + 1 / (4 * Real.log (|t| + 2))
  · have hb := hCBbound σ t ht hσlo hcase
    calc 1 / ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ CB * (Real.log (|t| + 2)) ^ CB := hb
      _ ≤ CT * (Real.log (|t| + 2)) ^ CT :=
          mul_le_mul hCTCB (Real.rpow_le_rpow_of_exponent_le hL1 hCTCB)
            (Real.rpow_nonneg hLnn _) (by positivity)
  · have hge : 1 + 1 / (4 * Real.log (|t| + 2)) ≤ σ :=
      le_of_lt (lt_of_not_ge hcase)
    have hza := zeta_norm_ge_inv_log_of_ge_one hge hσhi (by linarith)
    have hb : 1 / ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ 10 * Real.log (|t| + 2) := by
      have hpos : 0 < 1 / (10 * Real.log (|t| + 2)) := by positivity
      have := one_div_le_one_div_of_le hpos hza
      rwa [one_div_one_div] at this
    calc 1 / ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ 10 * Real.log (|t| + 2) := hb
      _ ≤ CT * (Real.log (|t| + 2)) ^ CT := by
          have hLle : Real.log (|t| + 2) ≤ (Real.log (|t| + 2)) ^ CT := by
            calc Real.log (|t| + 2) = (Real.log (|t| + 2)) ^ (1:ℝ) := (Real.rpow_one _).symm
              _ ≤ (Real.log (|t| + 2)) ^ CT := Real.rpow_le_rpow_of_exponent_le hL1 hCT1
          nlinarith [hCT10, hLle, Real.rpow_nonneg hLnn CT]

end

end Commons.NumberTheory.Zeta

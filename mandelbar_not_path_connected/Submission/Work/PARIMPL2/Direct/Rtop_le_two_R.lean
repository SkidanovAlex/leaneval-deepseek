import Mathlib
import Submission.Work.Implosion.All
import Submission.Work.Implosion.Approx
import Submission.Work.PARIMPL2.Direct.approxEcal_re_level
import Submission.Work.PARIMPL2.Direct.sinh_chart_norm

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL2.Direct

open Complex

set_option maxHeartbeats 4000000

/-! ## Two elementary real-analysis bounds

`Real.sinh t ≤ 2 t` on `[0,1]` (by antitonicity of `sinh x - 2x` there), and
`Real.log R ≤ R/4 + 3` for `R ≥ 4`. -/

private lemma sinh_le_two_mul (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Real.sinh t ≤ 2 * t := by
  have hanti : AntitoneOn (fun x : ℝ => Real.sinh x - 2 * x) (Set.Icc 0 1) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 1) ?_ ?_ ?_
    · exact (Real.continuous_sinh.sub (continuous_const.mul continuous_id)).continuousOn
    · intro x hx
      exact ((Real.differentiableAt_sinh).sub
        ((differentiableAt_const (2:ℝ)).mul differentiableAt_id)).differentiableWithinAt
    · intro x hx
      rw [interior_Icc, Set.mem_Ioo] at hx
      have hd : HasDerivAt (fun y : ℝ => Real.sinh y - 2 * y) (Real.cosh x - 2) x := by
        have h2 : HasDerivAt (fun y : ℝ => Real.sinh y) (Real.cosh x) x :=
          Real.hasDerivAt_sinh x
        have h3 : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
          simpa using (hasDerivAt_id x).const_mul (2:ℝ)
        exact h2.sub h3
      rw [hd.deriv]
      have hcx : Real.cosh x ≤ 2 := by
        have hle : Real.cosh x ≤ Real.cosh 1 := (Real.cosh_le_cosh).mpr (by
          rw [abs_of_nonneg (le_of_lt hx.1), abs_one]; exact hx.2.le)
        have hc1 : Real.cosh 1 ≤ 2 := by
          rw [Real.cosh_eq]
          have h3 : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
          have h4 : Real.exp 1 < 3 := Real.exp_one_lt_three
          linarith
        linarith
      linarith
  have h := hanti (Set.mem_Icc.mpr ⟨le_rfl, by norm_num⟩) (Set.mem_Icc.mpr ⟨ht0, ht1⟩) ht0
  simp only [Real.sinh_zero, mul_zero, sub_zero] at h
  linarith

private lemma abs_sinh_le_two_mul (s : ℝ) (hs : |s| ≤ 1) : |Real.sinh s| ≤ 2 * |s| := by
  rw [Real.abs_sinh]
  exact sinh_le_two_mul |s| (abs_nonneg s) hs

private lemma log_le_quarter_add_three (R : ℝ) (hR : 4 ≤ R) : Real.log R ≤ R / 4 + 3 := by
  have h1 : Real.log (R / 4) ≤ R / 4 - 1 := Real.log_le_sub_one_of_pos (by linarith)
  rw [Real.log_div (by linarith : R ≠ 0) (by norm_num : (4:ℝ) ≠ 0)] at h1
  have h2 : Real.log 4 ≤ 3 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 4)
    linarith
  linarith

theorem Rtop_le_two_R (lam R H : ℝ) (hlam : 0 < lam) (hR : 128 ≤ R) (hlamR : lam * R ^ 2 ≤ 1)
    (hH : 0 ≤ H) (hHR : 8 * (H + 2) ≤ R)
    (τ h1 κ : ℂ) (hτ1 : ‖τ - 1‖ ≤ 1 / 8) (hκ : κ = τ - h1 / τ) (hκI : |κ.im| ≤ 1 / 4)
    (hκlog : ‖κ‖ * (1 + Real.log R) ≤ 3 * R / 4)
    (u : ℂ) (huim : |u.im| ≤ 2 * H + 8 + Real.log R)
    (hx1 : R / 4 ≤ u.re) (hx2 : u.re ≤ Real.pi / lam - R / 4)
    (hlev : (Work.Implosion.approxEcal ((lam : ℂ) * Complex.I) κ u).re ∈
      Set.Icc (Real.pi / lam - R - 2) (Real.pi / lam - R)) :
    Real.pi / lam - 2 * R ≤ u.re := by
  have hR0 : 0 < R := by linarith
  have hlogR0 : 0 ≤ Real.log R := Real.log_nonneg (by linarith)
  have hlogR1 : 0 < 1 + Real.log R := by linarith
  set M : ℝ := 2 * H + 8 + Real.log R with hMdef
  set b : ℝ := Real.pi / lam - u.re with hbdef
  set Z : ℂ := Complex.sinh (((lam : ℂ) * Complex.I) * u) / ((lam : ℂ) * Complex.I) with hZdef
  have hM0 : 0 ≤ M := by rw [hMdef]; linarith
  have huimM : |u.im| ≤ M := by rw [hMdef]; exact huim
  have hbge : R / 4 ≤ b := by rw [hbdef]; linarith [hx2]
  have hbpos : 0 < b := by linarith
  have hMle : M ≤ R / 2 + 7 := by
    rw [hMdef]
    have h1 : 2 * H + 8 ≤ R / 4 + 4 := by linarith [hHR]
    have h2 : Real.log R ≤ R / 4 + 3 := log_le_quarter_add_three R (by linarith)
    linarith
  have hlamR0 : lam ≤ 1 / R ^ 2 := by
    rw [le_div_iff₀ (by positivity : (0:ℝ) < R ^ 2)]
    linarith [hlamR]
  have hlamM : lam * M ≤ 1 := by
    have h1 : lam * M ≤ lam * (R / 2 + 7) := mul_le_mul_of_nonneg_left hMle (le_of_lt hlam)
    have h2 : lam * (R / 2 + 7) ≤ (1 / R ^ 2) * (R / 2 + 7) :=
      mul_le_mul_of_nonneg_right hlamR0 (by linarith)
    have h3 : (1 / R ^ 2) * (R / 2 + 7) ≤ 1 := by
      have he : (1 / R ^ 2) * (R / 2 + 7) = (R / 2 + 7) / R ^ 2 := by ring
      rw [he, div_le_iff₀ (by positivity : (0:ℝ) < R ^ 2)]
      nlinarith [hR]
    linarith
  have hlamuim : lam * |u.im| ≤ 1 := by
    have h1 : lam * |u.im| ≤ lam * M := mul_le_mul_of_nonneg_left huimM (le_of_lt hlam)
    linarith
  -- the chart point and its squared modulus
  have hZ2 : ‖Z‖ ^ 2 = (Real.sin (lam * u.re) ^ 2 + Real.sinh (lam * u.im) ^ 2) / lam ^ 2 := by
    rw [hZdef]; exact sinh_chart_norm lam u
  have hlamx : lam * u.re = Real.pi - lam * b := by
    rw [hbdef]; field_simp
    ring
  have hsin_sq : Real.sin (lam * u.re) ^ 2 ≤ (lam * b) ^ 2 := by
    have h1 : Real.sin (lam * u.re) = Real.sin (lam * b) := by
      rw [hlamx]; exact Real.sin_pi_sub (lam * b)
    rw [h1, ← sq_abs (Real.sin (lam * b)), ← sq_abs (lam * b)]
    exact pow_le_pow_left₀ (abs_nonneg _) Real.abs_sin_le_abs 2
  have hsinh_sq : Real.sinh (lam * u.im) ^ 2 ≤ (2 * (lam * M)) ^ 2 := by
    have h1 : |Real.sinh (lam * u.im)| ≤ 2 * (lam * |u.im|) := by
      have hs : |lam * u.im| ≤ 1 := by
        rw [abs_mul, abs_of_pos hlam]; exact hlamuim
      have h2 := abs_sinh_le_two_mul (lam * u.im) hs
      rw [abs_mul, abs_of_pos hlam] at h2
      exact h2
    have h3 : 2 * (lam * |u.im|) ≤ 2 * (lam * M) := by
      have h := mul_le_mul_of_nonneg_left huimM (le_of_lt hlam)
      linarith
    have h4 : |Real.sinh (lam * u.im)| ≤ |2 * (lam * M)| := by
      rw [abs_of_nonneg (by nlinarith [hM0, hlam] : (0:ℝ) ≤ 2 * (lam * M))]
      exact le_trans h1 h3
    exact sq_le_sq.mpr h4
  have hZsq_le : ‖Z‖ ^ 2 ≤ (b + 2 * M) ^ 2 := by
    rw [hZ2, div_le_iff₀ (by positivity : (0:ℝ) < lam ^ 2)]
    have h3 : (lam * b) ^ 2 + (2 * (lam * M)) ^ 2 ≤ lam ^ 2 * (b + 2 * M) ^ 2 := by
      nlinarith [hbpos, hM0, hlam, sq_nonneg (b - 2 * M)]
    linarith [hsin_sq, hsinh_sq, h3]
  have hZle : ‖Z‖ ≤ b + 2 * M := by
    have h := sq_le_sq.mp hZsq_le
    rw [abs_of_nonneg (norm_nonneg Z), abs_of_nonneg (by linarith : (0:ℝ) ≤ b + 2 * M)] at h
    exact h
  -- lower bound `1 ≤ ‖Z‖`
  have hsin_ge : lam * R / (2 * Real.pi) ≤ Real.sin (lam * u.re) := by
    have hc : 0 ≤ 2 / Real.pi := by positivity
    have hx_ge : lam * R / 4 ≤ lam * u.re := by nlinarith [hx1, hlam]
    rcases le_total (lam * u.re) (Real.pi / 2) with hcase | hcase
    · have h1 := Real.mul_le_sin (by nlinarith [hx1, hlam, hR0] : 0 ≤ lam * u.re) hcase
      have h2 : 2 / Real.pi * (lam * R / 4) ≤ 2 / Real.pi * (lam * u.re) :=
        mul_le_mul_of_nonneg_left hx_ge hc
      have h3 : 2 / Real.pi * (lam * R / 4) = lam * R / (2 * Real.pi) := by ring
      linarith [h1, h2, h3]
    · have h2 : lam * b ≤ Real.pi / 2 := by
        have h : lam * b = Real.pi - lam * u.re := by linarith [hlamx]
        linarith
      have h3 : Real.sin (lam * u.re) = Real.sin (lam * b) := by
        rw [hlamx]; exact Real.sin_pi_sub (lam * b)
      rw [h3]
      have h4 := Real.mul_le_sin (by nlinarith [hlam, hbpos] : 0 ≤ lam * b) h2
      have h5 : 2 / Real.pi * (lam * R / 4) ≤ 2 / Real.pi * (lam * b) := by
        have h6 : lam * R / 4 ≤ lam * b := by nlinarith [hbge, hlam]
        exact mul_le_mul_of_nonneg_left h6 hc
      have h6 : 2 / Real.pi * (lam * R / 4) = lam * R / (2 * Real.pi) := by ring
      linarith [h4, h5, h6]
  have hZge : 1 ≤ ‖Z‖ := by
    have h1 : (Real.sin (lam * u.re) / lam) ^ 2 ≤ ‖Z‖ ^ 2 := by
      rw [hZ2, div_pow]
      apply div_le_div_of_nonneg_right _ (sq_nonneg lam)
      linarith [sq_nonneg (Real.sinh (lam * u.im))]
    have h2 : (R / (2 * Real.pi)) ^ 2 ≤ (Real.sin (lam * u.re) / lam) ^ 2 := by
      have h4 : R / (2 * Real.pi) ≤ Real.sin (lam * u.re) / lam := by
        rw [le_div_iff₀ hlam]
        have h5 : lam * (R / (2 * Real.pi)) = lam * R / (2 * Real.pi) := by ring
        linarith [hsin_ge, h5]
      exact pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ R / (2 * Real.pi)) h4 2
    have h5 : (1:ℝ) ≤ R / (2 * Real.pi) := by
      rw [le_div_iff₀ (by positivity : (0:ℝ) < 2 * Real.pi)]
      linarith [Real.pi_lt_d2, hR]
    have h6 := sq_le_sq.mp (le_trans h2 h1)
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ R / (2 * Real.pi)), abs_of_nonneg (norm_nonneg Z)] at h6
    linarith
  have hZpos : 0 < ‖Z‖ := by linarith
  have hlogZ_nonneg : 0 ≤ Real.log ‖Z‖ := Real.log_nonneg hZge
  have hlogZ_le : Real.log ‖Z‖ ≤ Real.log (b + 2 * M) := Real.log_le_log hZpos hZle
  -- the level identity
  have hdecomp : (Work.Implosion.approxEcal ((lam : ℂ) * Complex.I) κ u).re
      = u.re + (κ * Complex.log Z).re := by
    rw [Work.Implosion.approxEcal_apply, Complex.add_re, ← hZdef]
  have hlogre : (κ * Complex.log Z).re = κ.re * Real.log ‖Z‖ - κ.im * Z.arg := by
    rw [Complex.mul_re, Complex.log_re, Complex.log_im]
  have hb_le : b ≤ R + 2 + κ.re * Real.log ‖Z‖ - κ.im * Z.arg := by
    have h1 := hlev.1
    rw [hdecomp, hlogre] at h1
    rw [hbdef]
    linarith
  set k : ℝ := 3 * R / (4 * (1 + Real.log R)) with hkdef
  have hk0 : 0 ≤ k := by rw [hkdef]; exact div_nonneg (by linarith) (by linarith)
  have hkre_le : κ.re ≤ k := by
    have h1 : ‖κ‖ ≤ k := by
      rw [hkdef, le_div_iff₀ (by positivity : (0:ℝ) < 4 * (1 + Real.log R))]
      linarith [hκlog]
    linarith [Complex.re_le_norm κ]
  have hkre_log : κ.re * Real.log ‖Z‖ ≤ k * Real.log (b + 2 * M) := by
    have h1 : κ.re * Real.log ‖Z‖ ≤ k * Real.log ‖Z‖ :=
      mul_le_mul_of_nonneg_right hkre_le hlogZ_nonneg
    have h2 : k * Real.log ‖Z‖ ≤ k * Real.log (b + 2 * M) :=
      mul_le_mul_of_nonneg_left hlogZ_le hk0
    linarith
  have harg : -κ.im * Z.arg ≤ Real.pi / 4 := by
    have h1 : -(κ.im * Z.arg) ≤ |κ.im * Z.arg| := neg_le_abs _
    rw [abs_mul] at h1
    have h2 : |κ.im| * |Z.arg| ≤ (1 / 4) * Real.pi :=
      mul_le_mul hκI (Complex.abs_arg_le_pi Z) (abs_nonneg _) (by norm_num)
    have h3 : (1 / 4 : ℝ) * Real.pi = Real.pi / 4 := by ring
    linarith
  have hb_le2 : b ≤ R + 2 + Real.pi / 4 + k * Real.log (b + 2 * M) := by
    linarith [hb_le, hkre_log, harg]
  -- numeric input: `k * log (2R + 2M) ≤ R - 3`
  have hL4 : (4:ℝ) ≤ Real.log R := by
    have hexp4 : Real.exp 4 < (3:ℝ) ^ 4 := by
      have h1 : Real.exp 4 = Real.exp 1 ^ 4 := by
        rw [show (4:ℝ) = (4:ℕ) * 1 by norm_num, Real.exp_nat_mul]
      rw [h1]
      exact pow_lt_pow_left₀ Real.exp_one_lt_three (le_of_lt (Real.exp_pos 1)) (by norm_num)
    exact (Real.le_log_iff_exp_le hR0).mpr (by nlinarith [hexp4, hR])
  have hlog2R : Real.log (2 * R + 2 * M) ≤ Real.log R + 3 / 2 := by
    have h1 : 2 * R + 2 * M ≤ (28 / 9) * R := by
      have h3 : (14:ℝ) ≤ R / 9 := by linarith [hR]
      linarith [hMle]
    have h2 : Real.log (2 * R + 2 * M) ≤ Real.log ((28 / 9) * R) :=
      Real.log_le_log (by linarith) h1
    have h3 : Real.log ((28 / 9) * R) ≤ Real.log R + 3 / 2 := by
      rw [Real.log_mul (by norm_num : ((28:ℝ) / 9) ≠ 0) (ne_of_gt hR0)]
      have h4 : Real.log ((28:ℝ) / 9) ≤ 3 / 2 := by
        have h5 : Real.log ((28:ℝ) / 9) ≤ Real.log 4 :=
          Real.log_le_log (by norm_num) (by norm_num)
        have h6 : Real.log 4 = 2 * Real.log 2 := by
          rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
        have h7 : Real.log 2 ≤ 0.6931471808 := le_of_lt Real.log_two_lt_d9
        linarith
      linarith
    linarith
  have hklog2R : k * Real.log (2 * R + 2 * M) ≤ R - 3 := by
    have h1 : k * Real.log (2 * R + 2 * M) ≤ k * (Real.log R + 3 / 2) :=
      mul_le_mul_of_nonneg_left hlog2R hk0
    have h2 : k * (Real.log R + 3 / 2) ≤ R - 3 := by
      rw [hkdef, div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0:ℝ) < 4 * (1 + Real.log R))]
      nlinarith [hL4, hR]
    linarith
  have hk_half : k ≤ R / 2 := by
    rw [hkdef, div_le_iff₀ (by positivity : (0:ℝ) < 4 * (1 + Real.log R))]
    nlinarith [hL4]
  -- the final estimate
  have hb2R : b ≤ 2 * R := by
    by_cases hcase : b ≤ 2 * R
    · exact hcase
    · simp only [not_le] at hcase
      have hC0 : (0:ℝ) ≤ 2 * M := by linarith
      have hpos1 : 0 < b + 2 * M := by linarith
      have hpos2 : 0 < 2 * R + 2 * M := by linarith
      have hsplit : Real.log (b + 2 * M) ≤ Real.log (2 * R + 2 * M) + (b - 2 * R) / (2 * R + 2 * M) := by
        have h0 := Real.log_le_sub_one_of_pos (div_pos hpos1 hpos2)
        rw [Real.log_div (ne_of_gt hpos1) (ne_of_gt hpos2)] at h0
        have heq : (b + 2 * M) / (2 * R + 2 * M) - 1 = (b - 2 * R) / (2 * R + 2 * M) := by
          field_simp
          ring
        linarith
      have hfrac : k * ((b - 2 * R) / (2 * R + 2 * M)) ≤ (b - 2 * R) / 2 := by
        have h1 : (b - 2 * R) / (2 * R + 2 * M) ≤ (b - 2 * R) / (2 * R) :=
          div_le_div_of_nonneg_left (by linarith) (by linarith) (by linarith)
        have hc0 : 0 ≤ (b - 2 * R) / (2 * R + 2 * M) := div_nonneg (by linarith) (by linarith)
        have hd0 : (0:ℝ) ≤ R / 2 := by linarith
        have h2 : k * ((b - 2 * R) / (2 * R + 2 * M)) ≤ (R / 2) * ((b - 2 * R) / (2 * R)) :=
          mul_le_mul hk_half h1 hc0 hd0
        have h3 : (R / 2) * ((b - 2 * R) / (2 * R)) = (b - 2 * R) / 4 := by
          field_simp
          ring
        linarith
      have h4 : k * Real.log (b + 2 * M)
          ≤ k * Real.log (2 * R + 2 * M) + k * ((b - 2 * R) / (2 * R + 2 * M)) := by
        have h := mul_le_mul_of_nonneg_left hsplit hk0
        linarith
      linarith [hb_le2, h4, hklog2R, hfrac, Real.pi_lt_d2]
  rw [hbdef] at hb2R
  linarith

end Work.PARIMPL2.Direct

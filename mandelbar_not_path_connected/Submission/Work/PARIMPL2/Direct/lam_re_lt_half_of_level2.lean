import Mathlib
import Submission.Work.Implosion.All
import Submission.Work.Implosion.Approx
import Submission.Work.PARIMPL2.Direct.approxEcal_re_level
import Submission.Work.PARIMPL2.Direct.sinh_chart_norm
import Submission.Work.PARIMPL2.Direct.log_inv_le_two_log_add

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The level bound forces the level below the half strip (drift-free version)

Same conclusion as `Direct.lam_re_lt_half_of_level`, but the transverse drift bound
`|Im u|` is supplied directly through `|u.im| ≤ M` with `lam * M ≤ 1`, so that
`lam * |u.im| ≤ 1`.  The level analysis is identical; only the arithmetic endgame differs
(same bound `B ≤ 1` instead of the `1024 (5R/2+36)/R²` obtained from the exponential drift
estimate).

On the half strip `lam * u.re ≥ π/2` the chart point satisfies `‖Z‖ ≥ R/(2π) ≥ 1` with
`Z = sinh(iλu)/(iλ)`, so `log ‖Z‖ ≤ log(1/lam) + lam |Im u|`, and combining with the level
bound `Re Ũ ≤ R + 2` and `x₂` gives the contradiction
`(1/lam)(π/2) ≤ R + 2 + π/4 + ‖κ‖ (log(1/lam) + 1)`,
which is impossible because `lam R² ≤ 1` forces `1/lam ≥ R²` and `C (1 + log R) ≤ 3R/4`
keeps the right-hand side `O(R)`.
-/

namespace Work.PARIMPL2.Direct

open Complex

set_option maxHeartbeats 1000000

/-- Arithmetic endgame of the drift-free level bound: `lam R² ≤ 1`, `C (1 + log R) ≤ 3R/4`,
`0 ≤ B ≤ 1` and the key inequality are jointly unsatisfiable for `R ≥ 128`. -/
theorem arith_final_direct2 (lam R C B : ℝ) (hlam : 0 < lam) (hR : 128 ≤ R)
    (hlamR : lam * R ^ 2 ≤ 1) (hC0 : 0 ≤ C) (hC : C * (1 + Real.log R) ≤ 3 * R / 4)
    (hB0 : 0 ≤ B) (hB : B ≤ 1)
    (hineq : (1 / lam) * (Real.pi / 2) ≤ R + 2 + Real.pi / 4 + C * (Real.log (1 / lam) + B)) :
    False := by
  have hRpos : (0:ℝ) < R := by linarith
  have h1R : (1:ℝ) ≤ R := by linarith
  have hlogR : 0 ≤ Real.log R := Real.log_nonneg h1R
  have hC_le : C ≤ 3 * R / 4 := by
    have : C ≤ C * (1 + Real.log R) := by nlinarith [hC0, hlogR]
    linarith
  have hClog : 2 * C * Real.log R ≤ 3 * R / 2 := by
    have h1 : 2 * C * Real.log R ≤ 2 * (C * (1 + Real.log R)) := by nlinarith [hC0]
    linarith
  have hCB : C * B ≤ 3 * R / 4 := by
    have h1 : C * B ≤ C * 1 := mul_le_mul_of_nonneg_left hB hC0
    rw [mul_one] at h1
    linarith
  have hlog := Work.PARIMPL2.Direct.log_inv_le_two_log_add lam R hlam h1R hlamR
  have hmain : C * (Real.log (1 / lam) + B) ≤ 2 * C * Real.log R + C / (lam * R ^ 2) + C * B := by
    have hh := mul_le_mul_of_nonneg_left hlog hC0
    have hdist1 : C * (2 * Real.log R + 1 / (lam * R ^ 2)) =
        2 * C * Real.log R + C / (lam * R ^ 2) := by ring
    rw [hdist1] at hh
    have hdist : C * (Real.log (1 / lam) + B) = C * Real.log (1 / lam) + C * B := by ring
    linarith [hh]
  have hA : (1 / lam) * (Real.pi / 2) - C / (lam * R ^ 2) ≤
      R + 2 + Real.pi / 4 + 2 * C * Real.log R + C * B := by
    linarith [hineq, hmain]
  have hR2pos : (0:ℝ) < R ^ 2 := by positivity
  have hR2b : 128 * R ≤ R ^ 2 := by nlinarith [hR]
  have hx : R ^ 2 ≤ 1 / lam := by rw [le_div_iff₀ hlam]; linarith [hlamR]
  have hfac : 0 ≤ Real.pi / 2 - C / R ^ 2 := by
    have hCRle : C / R ^ 2 ≤ Real.pi / 2 := by
      rw [div_le_iff₀ hR2pos]
      nlinarith [hC_le, hR2b, Real.pi_gt_three]
    linarith
  have hprod : R ^ 2 * (Real.pi / 2 - C / R ^ 2) ≤ (1 / lam) * (Real.pi / 2 - C / R ^ 2) :=
    mul_le_mul_of_nonneg_right hx hfac
  have e1 : R ^ 2 * (Real.pi / 2 - C / R ^ 2) = Real.pi / 2 * R ^ 2 - C := by field_simp
  have e2 : (1 / lam) * (Real.pi / 2 - C / R ^ 2) =
      (1 / lam) * (Real.pi / 2) - C / (lam * R ^ 2) := by field_simp
  have hBh : Real.pi / 2 * R ^ 2 - C ≤
      R + 2 + Real.pi / 4 + 2 * C * Real.log R + C * B := by
    linarith [hprod, hA, e1, e2]
  have hfinal : Real.pi / 2 * R ^ 2 ≤ 4 * R + 2 + Real.pi / 4 := by
    linarith [hBh, hClog, hC_le, hCB]
  have hcontra : 4 * R + 2 + Real.pi / 4 < Real.pi / 2 * R ^ 2 := by
    nlinarith [hR, hR2b, Real.pi_gt_three, Real.pi_lt_four]
  linarith [hfinal, hcontra]

theorem lam_re_lt_half_of_level2 (lam R H A M : ℝ) (hlam : 0 < lam) (hR : 128 ≤ R) (hlamR : lam * R ^ 2 ≤ 1)
    (τ h1 κ : ℂ) (hτ1 : ‖τ - 1‖ ≤ 1 / 8) (hκ : κ = τ - h1 / τ) (hκI : |κ.im| ≤ 1 / 4)
    (hκlog : ‖κ‖ * (1 + Real.log R) ≤ 3 * R / 4)
    (hH : 0 ≤ H) (hHR : 8 * (H + 2) ≤ R) (hA0 : 0 ≤ A) (hAr : 16 * A / R ^ 2 ≤ 3 / 8)
    (u : ℂ) (hx2 : u.re ≤ Real.pi / lam - R / 4)
    (hL : (Work.Implosion.approxEcal ((lam : ℂ) * Complex.I) κ u).re ≤ R + 2)
    (hy : |u.im| ≤ M) (hM : lam * M ≤ 1) :
    lam * u.re < Real.pi / 2 := by
  by_contra hcon
  have hge : Real.pi / 2 ≤ lam * u.re := not_lt.mp hcon
  have hR0 : 0 < R := by linarith
  set Z : ℂ := Complex.sinh (((lam : ℂ) * Complex.I) * u) / ((lam : ℂ) * Complex.I) with hZdef
  -- the chart point is `sin (λu)/λ`
  have hZsin : Z = Complex.sin ((lam : ℂ) * u) / (lam : ℂ) := by
    rw [hZdef]
    have h : ((lam : ℂ) * Complex.I) * u = ((lam : ℂ) * u) * Complex.I := by ring
    rw [h, Complex.sinh_mul_I, mul_div_mul_right _ _ Complex.I_ne_zero]
  -- ### `u.re ≥ π/(2λ)`
  have hure : Real.pi / (2 * lam) ≤ u.re := by
    have h : (Real.pi / 2) * (1 / lam) ≤ (lam * u.re) * (1 / lam) :=
      mul_le_mul_of_nonneg_right hge (by positivity)
    have h2 : (lam * u.re) * (1 / lam) = u.re := by field_simp
    have h3 : (Real.pi / 2) * (1 / lam) = Real.pi / (2 * lam) := by ring
    rw [h3, h2] at h
    exact h
  -- ### `sin (λ u.re) ≥ λR/(2π)`
  have hsin_ge : lam * R / (2 * Real.pi) ≤ Real.sin (lam * u.re) := by
    set t : ℝ := Real.pi - lam * u.re with ht
    have htge : lam * R / 4 ≤ t := by
      have h : lam * u.re ≤ lam * (Real.pi / lam - R / 4) :=
        mul_le_mul_of_nonneg_left hx2 hlam.le
      have h2 : lam * (Real.pi / lam - R / 4) = Real.pi - lam * R / 4 := by
        field_simp
      rw [ht]
      linarith [h, h2]
    have ht0 : 0 ≤ t := le_trans (by positivity) htge
    have htle : t ≤ Real.pi / 2 := by rw [ht]; linarith
    have hsin_t : 2 / Real.pi * t ≤ Real.sin t := Real.mul_le_sin ht0 htle
    have hsin_eq : Real.sin (lam * u.re) = Real.sin t := by rw [ht, Real.sin_pi_sub]
    rw [hsin_eq]
    have h2pi : 0 ≤ 2 / Real.pi := by positivity
    have hstep : 2 / Real.pi * (lam * R / 4) ≤ 2 / Real.pi * t :=
      mul_le_mul_of_nonneg_left htge h2pi
    have heq : 2 / Real.pi * (lam * R / 4) = lam * R / (2 * Real.pi) := by ring
    linarith [hsin_t, hstep, heq.le]
  -- ### the modulus of the chart point
  have hZnorm : ‖Z‖ ^ 2 = (Real.sin (lam * u.re) ^ 2 + Real.sinh (lam * u.im) ^ 2) / lam ^ 2 := by
    rw [hZdef]
    exact Work.PARIMPL2.Direct.sinh_chart_norm lam u
  have hZ_ge : R / (2 * Real.pi) ≤ ‖Z‖ := by
    have hsin0 : 0 ≤ Real.sin (lam * u.re) :=
      le_trans (by positivity : (0 : ℝ) ≤ lam * R / (2 * Real.pi)) hsin_ge
    have hsq : (Real.sin (lam * u.re) / lam) ^ 2 ≤ ‖Z‖ ^ 2 := by
      rw [hZnorm, div_pow, div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < lam ^ 2)]
      linarith [sq_nonneg (Real.sinh (lam * u.im))]
    have h1 : Real.sin (lam * u.re) / lam ≤ ‖Z‖ := by
      have h := sq_le_sq.mp hsq
      rwa [abs_of_nonneg (div_nonneg hsin0 hlam.le), abs_of_nonneg (norm_nonneg Z)] at h
    have h2 : R / (2 * Real.pi) ≤ Real.sin (lam * u.re) / lam := by
      rw [le_div_iff₀ hlam]
      have heq : R / (2 * Real.pi) * lam = lam * R / (2 * Real.pi) := by ring
      linarith [hsin_ge, heq.le]
    linarith
  have hR2pi : (1 : ℝ) ≤ R / (2 * Real.pi) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [Real.pi_lt_four, hR]
  have hZlog_ge : 0 ≤ Real.log ‖Z‖ := Real.log_nonneg (le_trans hR2pi hZ_ge)
  have hZpos : 0 < ‖Z‖ := lt_of_lt_of_le (div_pos hR0 (by positivity)) hZ_ge
  -- ### upper bound for `log ‖Z‖`
  have hZ_ub : ‖Z‖ ≤ Real.exp (lam * |u.im|) / lam := by
    have hsin_cosh : ‖Complex.sin ((lam : ℂ) * u)‖ ≤ Real.cosh (lam * u.im) := by
      have hn : Complex.normSq (Complex.sin ((lam : ℂ) * u))
          = Real.sin (lam * u.re) ^ 2 + Real.sinh (lam * u.im) ^ 2 := by
        rw [Work.PARIMPL2.Direct.normSq_sin]
        simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          zero_mul, sub_zero, add_zero]
      have h1 : ‖Complex.sin ((lam : ℂ) * u)‖ ^ 2 ≤ Real.cosh (lam * u.im) ^ 2 := by
        rw [Complex.sq_norm, hn, Real.cosh_sq]
        linarith [Real.sin_sq_le_one (lam * u.re), sq_nonneg (Real.sinh (lam * u.im))]
      have h := sq_le_sq.mp h1
      rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (Real.cosh_pos _).le] at h
    have hcosh : Real.cosh (lam * u.im) ≤ Real.exp (lam * |u.im|) := by
      have hx : lam * |u.im| = |lam * u.im| := by rw [abs_mul, abs_of_pos hlam]
      have h1 : Real.cosh (lam * |u.im|) ≤ Real.exp (lam * |u.im|) := by
        have h3 := Real.cosh_add_sinh (lam * |u.im|)
        have h4 : 0 ≤ Real.sinh (lam * |u.im|) :=
          Real.sinh_nonneg_iff.mpr (by positivity)
        linarith
      have h2 : Real.cosh (lam * u.im) = Real.cosh (lam * |u.im|) := by
        rw [hx, Real.cosh_abs]
      linarith [h1, h2.le, h2.ge]
    calc ‖Z‖ = ‖Complex.sin ((lam : ℂ) * u)‖ / lam := by
          rw [hZsin, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlam]
      _ ≤ Real.cosh (lam * u.im) / lam := by gcongr
      _ ≤ Real.exp (lam * |u.im|) / lam := by gcongr
  have hZlog_le : Real.log ‖Z‖ ≤ Real.log (1 / lam) + lam * |u.im| := by
    have h1 : Real.log ‖Z‖ ≤ Real.log (Real.exp (lam * |u.im|) / lam) :=
      Real.log_le_log hZpos hZ_ub
    have h2 : Real.log (Real.exp (lam * |u.im|) / lam) = lam * |u.im| + Real.log (1 / lam) := by
      rw [Real.log_div (Real.exp_ne_zero _) (ne_of_gt hlam), Real.log_exp]
      have h3 : Real.log (1 / lam) = -Real.log lam := by
        rw [show (1 : ℝ) / lam = lam⁻¹ by ring, Real.log_inv]
      rw [h3]; ring
    linarith [h1, h2.le, h2.ge]
  have habs_log : |Real.log ‖Z‖| ≤ Real.log (1 / lam) + lam * |u.im| :=
    abs_le.mpr ⟨by linarith, hZlog_le⟩
  -- ### the level, first form: `u.re + κ.re * log ‖Z‖ ≤ R + 2 + π/4`
  have hlev := Work.PARIMPL2.Direct.approxEcal_re_level lam κ u
  rw [← hZdef] at hlev
  have hre_ub : u.re + κ.re * Real.log ‖Z‖ ≤ R + 2 + Real.pi / 4 := by
    have h := (abs_le.mp hlev).1
    have h2 : |κ.im| * Real.pi ≤ Real.pi / 4 := by
      nlinarith [Real.pi_pos, abs_nonneg κ.im, hκI]
    linarith [h, hL, h2]
  have hkre_ge : -(‖κ‖ * (Real.log (1 / lam) + lam * |u.im|)) ≤ κ.re * Real.log ‖Z‖ := by
    have h2 : -(‖κ‖ * |Real.log ‖Z‖|) ≤ κ.re * Real.log ‖Z‖ := by
      have h3 : -|κ.re * Real.log ‖Z‖| ≤ κ.re * Real.log ‖Z‖ := neg_abs_le _
      have h4 : |κ.re * Real.log ‖Z‖| ≤ ‖κ‖ * |Real.log ‖Z‖| := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm κ) (abs_nonneg _)
      linarith
    have h5 : ‖κ‖ * |Real.log ‖Z‖| ≤ ‖κ‖ * (Real.log (1 / lam) + lam * |u.im|) :=
      mul_le_mul_of_nonneg_left habs_log (norm_nonneg κ)
    linarith
  have hure_ub : u.re ≤ R + 2 + Real.pi / 4 + ‖κ‖ * (Real.log (1 / lam) + lam * |u.im|) := by
    linarith [hre_ub, hkre_ge]
  have hineq : (1 / lam) * (Real.pi / 2) ≤
      R + 2 + Real.pi / 4 + ‖κ‖ * (Real.log (1 / lam) + lam * |u.im|) := by
    have h1 : (1 / lam) * (Real.pi / 2) = Real.pi / (2 * lam) := by ring
    rw [h1]
    linarith [hure, hure_ub]
  -- ### the drift bound `lam * |Im u| ≤ 1`, and the arithmetic endgame
  have hB : lam * |u.im| ≤ 1 := by
    have h1 : lam * |u.im| ≤ lam * M := mul_le_mul_of_nonneg_left hy hlam.le
    linarith [hM]
  exact arith_final_direct2 lam R ‖κ‖ (lam * |u.im|) hlam hR hlamR (norm_nonneg κ) hκlog
    (mul_nonneg hlam.le (abs_nonneg _)) hB hineq

end Work.PARIMPL2.Direct

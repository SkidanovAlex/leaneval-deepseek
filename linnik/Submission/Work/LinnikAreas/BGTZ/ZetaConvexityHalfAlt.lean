/-
# Convexity bound for `ζ` on the critical strip

`∃ C > 0, ∀ σ t, 1/2 ≤ σ → σ ≤ 1 → 1 ≤ |t| → ‖ζ(σ+it)‖ ≤ C (1+|t|)^{1/4} (log(2+|t|)+2)`.

Proved by the Phragmén--Lindelöf principle on the strip `0 ≤ Re s ≤ 1` applied to the
function `ζ(s)/ZW(s)`, where

  `ZW s = (s+2) * (Γ(1-s/4)/Γ(1/2+s/4)) * log(s+2)`

is chosen so that `ZW` has no zeros in the closed strip, grows like `|Im s|^{3/2 - Re s/2}`,
and is *at least* `|Im s|` (times a log) on the critical line and at least a constant times
`|Im s|^{1/2}` on `Re s = 1`; this makes the boundary values of `ζ/ZW` bounded on the two edges
of the strip.  All inputs (functional equation, growth of ζ, growth of Γ) are in the shared
`Submission.Commons` library.

This file is a self-contained alternative to
`Submission.Work.LinnikAreas.BGTZ.ZetaConvexityHalf` (same statement, different proof),
used by `Submission.Work.LinnikAreas.BGTZ.DetIntBound`.
-/
import Mathlib
import Submission.Commons.Analysis.Complex.Gamma_vertical_norm_bounds
import Submission.Commons.Analysis.SpecialFunctions.Gamma.gamma_abs_sq_half
import Submission.Commons.Analysis.SpecialFunctions.Gamma.gammaR_log_norm_sub_le
import Submission.Commons.NumberTheory.Zeta.zeta_strip_polyGrowth
import Submission.Commons.NumberTheory.LSeries.norm_riemannZeta_le_five_mul_log

open Complex
open scoped Real Topology

noncomputable section

set_option maxHeartbeats 2000000

namespace Work.LinnikAreas.BGTZ

/-- The weight used in the convexity (Phragmén--Lindelöf) argument for `ζ`. -/
def ZW (s : ℂ) : ℂ :=
  (s + 2) * (Complex.Gamma (1 - s / 4) / Complex.Gamma (1 / 2 + s / 4))
    * Complex.log (s + 2)

lemma gamma_ne_zero_of_re_pos {z : ℂ} (hz : 0 < z.re) : Complex.Gamma z ≠ 0 := by
  apply Complex.Gamma_ne_zero
  intro m hm
  have hre := congrArg Complex.re hm
  simp at hre
  have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  linarith

lemma norm_Gamma_star' (w : ℂ) : ‖Complex.Gamma (star w)‖ = ‖Complex.Gamma w‖ :=
  Commons.Analysis.Complex.norm_Gamma_conj w

/-- Upper bound for the Gamma-ratio in the strip. -/
lemma ZW_ratio_upper {s : ℂ} (hs0 : 0 ≤ s.re) (hs1 : s.re ≤ 1) :
    ‖Complex.Gamma (1 - s / 4) / Complex.Gamma (1 / 2 + s / 4)‖
      ≤ Real.exp ((1 / 2 - s.re / 2) * (Real.log (2 + |s.im|) + 2)) := by
  set u₂ : ℝ := 1 - s.re / 4 with hu₂
  set u₁ : ℝ := 1 / 2 + s.re / 4 with hu₁
  set τ : ℝ := s.im / 4 with hτ
  have hu1 : (1 : ℝ) / 2 ≤ u₁ := by rw [hu₁]; linarith
  have h12 : u₁ ≤ u₂ := by rw [hu₁, hu₂]; linarith
  have h2 : u₂ ≤ 8 := by rw [hu₂]; linarith
  have hu2m1 : u₂ - u₁ = 1 / 2 - s.re / 2 := by rw [hu₂, hu₁]; ring
  have hnum : (1 - s / 4) = star (((u₂ : ℝ) : ℂ) + ((τ : ℝ) : ℂ) * I) := by
    rw [hu₂, hτ]
    apply Complex.ext <;> simp [Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im] <;> ring
  have hden : (1 / 2 + s / 4) = ((u₁ : ℝ) : ℂ) + ((τ : ℝ) : ℂ) * I := by
    rw [hu₁, hτ]
    apply Complex.ext <;> simp [Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im] <;> ring
  have hA : Complex.Gamma (((u₂ : ℝ) : ℂ) + ((τ : ℝ) : ℂ) * I) ≠ 0 := by
    apply gamma_ne_zero_of_re_pos
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_one, mul_zero, sub_zero]
    linarith
  have hB : Complex.Gamma (((u₁ : ℝ) : ℂ) + ((τ : ℝ) : ℂ) * I) ≠ 0 := by
    apply gamma_ne_zero_of_re_pos
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_one, mul_zero, sub_zero]
    linarith
  have hApos : 0 < ‖Complex.Gamma (((u₂ : ℝ) : ℂ) + ((τ : ℝ) : ℂ) * I)‖ := norm_pos_iff.mpr hA
  have hBpos : 0 < ‖Complex.Gamma (((u₁ : ℝ) : ℂ) + ((τ : ℝ) : ℂ) * I)‖ := norm_pos_iff.mpr hB
  have hinc := Commons.Analysis.SpecialFunctions.Gamma.log_norm_Gamma_sub_le u₁ u₂ τ hu1 h12 h2
  have hτabs : |τ| = |s.im| / 4 := by rw [hτ, abs_div]; norm_num
  have hlog : Real.log (2 + |τ|) ≤ Real.log (2 + |s.im|) := by
    apply Real.log_le_log (by positivity); rw [hτabs]; linarith [abs_nonneg s.im]
  have hratio : ‖Complex.Gamma (((u₂ : ℝ) : ℂ) + ((τ : ℝ) : ℂ) * I)‖ /
      ‖Complex.Gamma (((u₁ : ℝ) : ℂ) + ((τ : ℝ) : ℂ) * I)‖ ≤
      Real.exp ((u₂ - u₁) * (Real.log (2 + |s.im|) + 2)) := by
    have h := Real.exp_le_exp.mpr hinc
    rw [Real.exp_sub, Real.exp_log hApos, Real.exp_log hBpos] at h
    refine h.trans (Real.exp_le_exp.mpr ?_)
    have h0 : 0 ≤ u₂ - u₁ := by rw [hu2m1]; linarith
    nlinarith [hlog, h0]
  rw [hnum, hden, norm_div, norm_Gamma_star']
  refine hratio.trans (le_of_eq ?_)
  rw [hu2m1]

/-- Lower bound for `‖log (s + 2)‖` in the strip. -/
lemma ZW_log_lower {s : ℂ} (hre0 : 0 ≤ s.re) (hb : 1 ≤ |s.im|) :
    (1 / 2) * Real.log (2 + |s.im|) ≤ ‖Complex.log (s + 2)‖ := by
  have hnorm : (2 + |s.im|) ≤ ‖s + 2‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    have h1 : (s + 2).re = s.re + 2 := by rw [Complex.add_re]; norm_num
    have h2 : (s + 2).im = s.im := by rw [Complex.add_im]; norm_num
    rw [h1, h2]
    nlinarith [hre0, abs_nonneg s.im, sq_abs s.im, sq_nonneg (s.re), hb]
  have hpos2 : (0 : ℝ) < 2 + |s.im| := by linarith [abs_nonneg s.im]
  have h1 : Real.log (2 + |s.im|) ≤ 2 * Real.log ‖s + 2‖ := by
    have h := Real.log_le_log hpos2 hnorm
    rwa [Real.log_pow] at h
  have h2 : Real.log ‖s + 2‖ = (Complex.log (s + 2)).re := (Complex.log_re _).symm
  calc (1 / 2) * Real.log (2 + |s.im|) ≤ (1 / 2) * (2 * Real.log ‖s + 2‖) := by linarith
    _ = Real.log ‖s + 2‖ := by ring
    _ = (Complex.log (s + 2)).re := h2
    _ ≤ ‖Complex.log (s + 2)‖ := Complex.re_le_norm _

/-- Upper bound for the weight in the strip. -/
lemma ZW_norm_upper {s : ℂ} (hs0 : 0 ≤ s.re) (hs1 : s.re ≤ 1) (hb : 1 ≤ |s.im|) :
    ‖ZW s‖ ≤ 100 * (2 + |s.im|) ^ ((3 : ℝ) / 2 - s.re / 2)
      * (Real.log (2 + |s.im|) + 2) := by
  have hxpos : (0 : ℝ) < 2 + |s.im| := by linarith [abs_nonneg s.im]
  have hx1 : (1 : ℝ) ≤ 2 + |s.im| := by linarith [abs_nonneg s.im]
  have h1 : ‖s + 2‖ ≤ 4 * (2 + |s.im|) := by
    have h := Complex.norm_le_abs_re_add_abs_im (s + 2)
    have hre : (s + 2).re = s.re + 2 := by rw [Complex.add_re]; norm_num
    have him : (s + 2).im = s.im := by rw [Complex.add_im]; norm_num
    rw [hre, him] at h
    have hr : |s.re + 2| = s.re + 2 := abs_of_nonneg (by linarith)
    rw [hr] at h
    nlinarith [abs_nonneg s.im, h]
  have h2 : ‖Complex.log (s + 2)‖ ≤ 5 * (Real.log (2 + |s.im|) + 2) := by
    have hz2 : (2 : ℝ) ≤ ‖s + 2‖ := by
      have h := Complex.re_le_norm (s + 2)
      have hre : (s + 2).re = s.re + 2 := by rw [Complex.add_re]; norm_num
      rw [hre] at h
      linarith
    have hlog : |Real.log ‖s + 2‖| ≤ Real.log (2 + |s.im|) + 2 := by
      have hpos : (0 : ℝ) < ‖s + 2‖ := by linarith
      have hle1 : Real.log ‖s + 2‖ ≤ Real.log 4 + Real.log (2 + |s.im|) := by
        have hle := Real.log_le_log hpos h1
        rw [Real.log_mul (by norm_num) (ne_of_gt hxpos)] at hle
        exact hle
      have hlog4 : Real.log 4 ≤ 2 := by
        rw [Real.log_le_iff_le_exp (by norm_num)]
        have h2' : (4 : ℝ) ≤ Real.exp 2 := by
          have h := Real.exp_one_gt_d9
          have he : Real.exp 2 = Real.exp 1 ^ 2 := by
            rw [show (2:ℝ) = ((2:ℕ):ℝ) * 1 by norm_num, Real.exp_nat_mul]
          rw [he]; nlinarith
        exact h2'
      have hge : Real.log 2 ≤ Real.log (2 + |s.im|) := by
        apply Real.log_le_log (by norm_num); linarith [abs_nonneg s.im]
      have hpos' : (0 : ℝ) ≤ Real.log ‖s + 2‖ := Real.log_nonneg (by linarith)
      rw [abs_le]
      constructor <;> linarith
    have hargle : |Complex.arg (s + 2)| ≤ Real.pi := Complex.abs_arg_le_pi _
    have hlogr : (Complex.log (s + 2)).re = Real.log ‖s + 2‖ := Complex.log_re _
    calc ‖Complex.log (s + 2)‖ ≤ ‖(Complex.log (s + 2)).re‖ + |(Complex.log (s + 2)).im| := by
          have h := Complex.norm_le_abs_re_add_abs_im (Complex.log (s + 2))
          simpa using h
      _ = |Real.log ‖s + 2‖| + |Complex.arg (s + 2)| := by
            rw [hlogr, Complex.log_im, Real.norm_eq_abs]
      _ ≤ (Real.log (2 + |s.im|) + 2) + 4 := by
            have hpi : Real.pi ≤ 4 := by linarith [Real.pi_lt_four]
            linarith
      _ ≤ 5 * (Real.log (2 + |s.im|) + 2) := by
            have h3 : (0 : ℝ) ≤ Real.log (2 + |s.im|) := Real.log_nonneg hx1
            linarith
  have h3 := ZW_ratio_upper hs0 hs1
  have h4 : Real.exp ((1 / 2 - s.re / 2) * (Real.log (2 + |s.im|) + 2))
      ≤ Real.exp 1 * (2 + |s.im|) ^ ((1 : ℝ) / 2 - s.re / 2) := by
    have hsplit : Real.exp ((1 / 2 - s.re / 2) * (Real.log (2 + |s.im|) + 2))
        = (2 + |s.im|) ^ ((1 : ℝ) / 2 - s.re / 2)
            * Real.exp ((1 / 2 - s.re / 2) * 2) := by
      rw [mul_add, Real.exp_add, mul_comm (1 / 2 - s.re / 2) (Real.log (2 + |s.im|)),
        Real.exp_mul, Real.exp_log hxpos]
    rw [hsplit]
    have h2a : Real.exp ((1 / 2 - s.re / 2) * 2) ≤ Real.exp 1 :=
      Real.exp_le_exp.mpr (by linarith)
    have hna : (0 : ℝ) ≤ (2 + |s.im|) ^ ((1 : ℝ) / 2 - s.re / 2) :=
      Real.rpow_nonneg (by positivity) _
    calc (2 + |s.im|) ^ ((1 : ℝ) / 2 - s.re / 2) * Real.exp ((1 / 2 - s.re / 2) * 2)
        ≤ (2 + |s.im|) ^ ((1 : ℝ) / 2 - s.re / 2) * Real.exp 1 :=
          mul_le_mul_of_nonneg_left h2a hna
      _ = Real.exp 1 * (2 + |s.im|) ^ ((1 : ℝ) / 2 - s.re / 2) := by ring
  have h5 : ‖Complex.Gamma (1 - s / 4) / Complex.Gamma (1 / 2 + s / 4)‖
      ≤ Real.exp 1 * (2 + |s.im|) ^ ((1 : ℝ) / 2 - s.re / 2) := h3.trans h4
  rw [ZW, norm_mul, norm_mul]
  have hxa : (2 + |s.im|) * (2 + |s.im|) ^ ((1 : ℝ) / 2 - s.re / 2)
      = (2 + |s.im|) ^ ((3 : ℝ) / 2 - s.re / 2) := by
    have h3 : (3 : ℝ) / 2 - s.re / 2 = 1 + ((1 : ℝ) / 2 - s.re / 2) := by ring
    rw [h3, Real.rpow_add hxpos, Real.rpow_one]
  have hL : (4 * (2 + |s.im|)) * (Real.exp 1 * (2 + |s.im|) ^ ((1 : ℝ) / 2 - s.re / 2))
        * (5 * (Real.log (2 + |s.im|) + 2))
      = (20 * Real.exp 1) * ((2 + |s.im|) * (2 + |s.im|) ^ ((1 : ℝ) / 2 - s.re / 2))
        * (Real.log (2 + |s.im|) + 2) := by ring
  calc ‖s + 2‖ * ‖Complex.Gamma (1 - s / 4) / Complex.Gamma (1 / 2 + s / 4)‖
        * ‖Complex.log (s + 2)‖
      ≤ (4 * (2 + |s.im|))
          * (Real.exp 1 * (2 + |s.im|) ^ ((1 : ℝ) / 2 - s.re / 2))
          * (5 * (Real.log (2 + |s.im|) + 2)) := by
        apply mul_le_mul
        · exact mul_le_mul h1 h5 (norm_nonneg _) (by positivity)
        · exact h2
        · positivity
        · positivity
    _ = (20 * Real.exp 1) * (2 + |s.im|) ^ ((3 : ℝ) / 2 - s.re / 2)
          * (Real.log (2 + |s.im|) + 2) := by rw [hL, hxa]
    _ ≤ 100 * (2 + |s.im|) ^ ((3 : ℝ) / 2 - s.re / 2)
          * (Real.log (2 + |s.im|) + 2) := by
        have hX : (0 : ℝ) ≤ (2 + |s.im|) ^ ((3 : ℝ) / 2 - s.re / 2) :=
          Real.rpow_nonneg (by positivity) _
        have hlg : (0 : ℝ) ≤ Real.log (2 + |s.im|) + 2 := by
          have := Real.log_nonneg hx1; linarith
        have he : 20 * Real.exp 1 ≤ 100 := by
          have := Real.exp_one_lt_three; linarith
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right he hX) hlg

lemma log_two_add_nonneg (t : ℝ) : (0 : ℝ) ≤ Real.log (2 + |t|) :=
  Real.log_nonneg (by linarith [abs_nonneg t])

lemma log_two_add_pos (t : ℝ) : (0 : ℝ) < Real.log (2 + |t|) :=
  Real.log_pos (by linarith [abs_nonneg t])

lemma add_norm_sq (a t : ℝ) : ‖(a : ℂ) + (t : ℂ) * I‖ ^ 2 = a ^ 2 + t ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  have hre : ((a : ℂ) + (t : ℂ) * I).re = a := by
    rw [Complex.add_re, Complex.mul_re]; simp
  have him : ((a : ℂ) + (t : ℂ) * I).im = t := by
    rw [Complex.add_im, Complex.mul_im]; simp
  rw [hre, him]; ring

lemma add_norm_ge (a t : ℝ) (ha : 1 ≤ a) : (1 + |t|) / 2 ≤ ‖(a : ℂ) + (t : ℂ) * I‖ := by
  have h := add_norm_sq a t
  have h2 : ((1 + |t|) / 2) ^ 2 ≤ a ^ 2 + t ^ 2 := by
    have h1 : (1 + |t|) ^ 2 ≤ 4 * (1 + t ^ 2) := by nlinarith [abs_nonneg t, sq_abs t]
    have h3 : (1 : ℝ) ≤ a ^ 2 := by nlinarith [ha]
    nlinarith [h1, h3, sq_nonneg t]
  have h3 : ((1 + |t|) / 2) ^ 2 ≤ ‖(a : ℂ) + (t : ℂ) * I‖ ^ 2 := by rw [h]; exact h2
  rw [show ((1 + |t|) / 2) = Real.sqrt (((1 + |t|) / 2) ^ 2) from
        (Real.sqrt_sq (by positivity)).symm,
      show ‖(a : ℂ) + (t : ℂ) * I‖ = Real.sqrt (‖(a : ℂ) + (t : ℂ) * I‖ ^ 2) from
        (Real.sqrt_sq (norm_nonneg _)).symm]
  exact Real.sqrt_le_sqrt h3

lemma gamma_half_norm_sq (v : ℝ) :
    ‖Complex.Gamma ((1 / 2 : ℂ) + ((v : ℝ) : ℂ) * I)‖ ^ 2
      = Real.pi / Real.cosh (Real.pi * v) := by
  rw [show ((1 / 2 : ℂ) + ((v : ℝ) : ℂ) * I) = ((1 / 2 : ℂ) + I * ((v : ℝ) : ℂ)) by
    rw [mul_comm]]
  exact Commons.Analysis.SpecialFunctions.Gamma.gamma_abs_sq_half v

lemma gamma_one_norm_sq' (v : ℝ) (hv : v ≠ 0) :
    ‖Complex.Gamma ((1 : ℂ) + ((v : ℝ) : ℂ) * I)‖ ^ 2
      = Real.pi * |v| / Real.sinh (Real.pi * |v|) := by
  rw [show ((1 : ℂ) + ((v : ℝ) : ℂ) * I) = ((1 : ℂ) + I * ((v : ℝ) : ℂ)) by rw [mul_comm]]
  exact Commons.Analysis.Complex.gamma_one_norm_sq v hv

lemma cosh_pi_abs' (v : ℝ) : Real.cosh (Real.pi * v) = Real.cosh (Real.pi * |v|) := by
  by_cases h : 0 ≤ v
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg (lt_of_not_ge h)]
    rw [show Real.pi * v = -(Real.pi * (-v)) by ring, Real.cosh_neg]

lemma tanh_pi_abs_pos (v : ℝ) (hv : v ≠ 0) : 0 < Real.tanh (Real.pi * |v|) := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_pos (Real.sinh_pos_iff.mpr (by positivity)) (Real.cosh_pos _)

lemma sqrt_div_four {x : ℝ} (hx : 0 ≤ x) : Real.sqrt (x / 4) = Real.sqrt x / 2 := by
  have h4 : (0 : ℝ) ≤ x / 4 := by positivity
  have hval : Real.sqrt (x / 4) ^ 2 = (Real.sqrt x / 2) ^ 2 := by
    rw [Real.sq_sqrt h4, div_pow, Real.sq_sqrt hx]; norm_num
  have h1 : (0 : ℝ) ≤ Real.sqrt (x / 4) := Real.sqrt_nonneg _
  have h2 : (0 : ℝ) ≤ Real.sqrt x / 2 := by positivity
  nlinarith [hval, h1, h2]

/-- Sharp lower bound for the Gamma-ratio on the imaginary axis. -/
lemma gamma_ratio_lower (v : ℝ) (hv : v ≠ 0) :
    Real.sqrt |v| ≤ ‖Complex.Gamma ((1 : ℂ) + ((v : ℝ) : ℂ) * I)
      / Complex.Gamma ((1 / 2 : ℂ) + ((v : ℝ) : ℂ) * I)‖ := by
  have ha : 0 < |v| := abs_pos.mpr hv
  have htpos : 0 < Real.tanh (Real.pi * |v|) := tanh_pi_abs_pos v hv
  have hr : ‖Complex.Gamma ((1 : ℂ) + ((v : ℝ) : ℂ) * I)
      / Complex.Gamma ((1 / 2 : ℂ) + ((v : ℝ) : ℂ) * I)‖ ^ 2
      = |v| / Real.tanh (Real.pi * |v|) := by
    rw [norm_div, div_pow, gamma_one_norm_sq' v hv, gamma_half_norm_sq v, cosh_pi_abs' v,
      Real.tanh_eq_sinh_div_cosh]
    have hs : Real.sinh (Real.pi * |v|) ≠ 0 :=
      ne_of_gt (Real.sinh_pos_iff.mpr (by positivity))
    have hc : Real.cosh (Real.pi * |v|) ≠ 0 := ne_of_gt (Real.cosh_pos _)
    field_simp
  have hle : |v| ≤ |v| / Real.tanh (Real.pi * |v|) := by
    rw [le_div_iff₀ htpos]
    have h1 : Real.tanh (Real.pi * |v|) ≤ 1 := le_of_lt (Real.tanh_lt_one _)
    nlinarith [h1, ha]
  rw [← Real.sqrt_sq (norm_nonneg _), hr]
  exact Real.sqrt_le_sqrt hle

lemma half_le_sqrt_abs {t : ℝ} (ht : 1 ≤ |t|) :
    (1 + |t|) ^ ((1 : ℝ) / 2) / 2 ≤ Real.sqrt |t| := by
  calc (1 + |t|) ^ ((1 : ℝ) / 2) / 2 = Real.sqrt (1 + |t|) / 2 := by rw [Real.sqrt_eq_rpow]
    _ = Real.sqrt ((1 + |t|) / 4) := (sqrt_div_four (by linarith [abs_nonneg t])).symm
    _ ≤ Real.sqrt |t| := by
        apply Real.sqrt_le_sqrt
        linarith [ht, abs_nonneg t]

/-- Lower bound for the weight at `σ = 0`. -/
lemma ZW_lower_zero {t : ℝ} (ht : 1 ≤ |t|) :
    (1 / 64) * (1 + |t|) ^ ((3 : ℝ) / 2) * Real.log (2 + |t|) ≤ ‖ZW ((t : ℂ) * I)‖ := by
  have h1 : (1 + |t|) / 2 ≤ ‖((t : ℂ) * I) + 2‖ := by
    have he : ((t : ℂ) * I) + 2 = (2 : ℂ) + (t : ℂ) * I := by ring
    rw [he]; exact add_norm_ge 2 t (by norm_num)
  have hR : Real.sqrt |t| / 2 ≤
      ‖Complex.Gamma (1 - ((t : ℂ) * I) / 4) / Complex.Gamma (1 / 2 + ((t : ℂ) * I) / 4)‖ := by
    have hv : (-(t / 4)) ≠ 0 := by
      intro h
      have ht0 : t = 0 := by linarith
      rw [ht0] at ht; norm_num at ht
    have h := gamma_ratio_lower (-(t / 4)) hv
    have habs : |-(t / 4)| = |t| / 4 := by rw [abs_neg, abs_div]; norm_num
    rw [habs, sqrt_div_four (abs_nonneg t)] at h
    refine le_trans h (le_of_eq ?_)
    have e1 : ((1 : ℂ) + ((-(t / 4) : ℝ) : ℂ) * I) = 1 - ((t : ℂ) * I) / 4 := by
      push_cast; ring
    have e2 : ((1 / 2 : ℂ) + ((-(t / 4) : ℝ) : ℂ) * I)
        = star (1 / 2 + ((t : ℂ) * I) / 4) := by
      apply Complex.ext <;> simp <;> ring
    simp only [e1, e2, norm_div, norm_Gamma_star']
  have hlog : (1 / 2) * Real.log (2 + |t|) ≤ ‖Complex.log (((t : ℂ) * I) + 2)‖ := by
    have h := ZW_log_lower (s := (t : ℂ) * I) (by simp) (by simpa using ht)
    simpa using h
  have hmain : ((1 + |t|) / 2) * (Real.sqrt |t| / 2) * ((1 / 2) * Real.log (2 + |t|))
      ≤ ‖ZW ((t : ℂ) * I)‖ := by
    rw [ZW, norm_mul, norm_mul]
    refine mul_le_mul (mul_le_mul h1 hR (by positivity) (by positivity)) hlog ?_ ?_
    · exact mul_nonneg (by norm_num) (log_two_add_nonneg t)
    · positivity
  have hprod : (1 / 64) * (1 + |t|) ^ ((3 : ℝ) / 2) * Real.log (2 + |t|)
      ≤ ((1 + |t|) / 2) * (Real.sqrt |t| / 2) * ((1 / 2) * Real.log (2 + |t|)) := by
    have hs := half_le_sqrt_abs ht
    have hpow : (1 + |t|) ^ ((3 : ℝ) / 2) = (1 + |t|) * (1 + |t|) ^ ((1 : ℝ) / 2) := by
      rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num,
        Real.rpow_add (by linarith [abs_nonneg t]), Real.rpow_one]
    rw [hpow]
    have hAn : (0 : ℝ) ≤ 1 + |t| := by linarith [abs_nonneg t]
    have hCn : (0 : ℝ) ≤ Real.sqrt |t| := Real.sqrt_nonneg _
    have hLn : (0 : ℝ) ≤ Real.log (2 + |t|) := log_two_add_nonneg t
    have h4 : (1 / 64) * ((1 + |t|) * (1 + |t|) ^ ((1 : ℝ) / 2)) * Real.log (2 + |t|)
        ≤ ((1 + |t|) / 2) * (Real.sqrt |t| / 2) * ((1 / 2) * Real.log (2 + |t|)) := by
      have hstep : ((1 + |t|) * ((1 + |t|) ^ ((1 : ℝ) / 2) / 2)) * (Real.log (2 + |t|) / 32)
          ≤ ((1 + |t|) * Real.sqrt |t|) * (Real.log (2 + |t|) / 32) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left hs hAn
      have hstep2 : ((1 + |t|) * Real.sqrt |t|) * (Real.log (2 + |t|) / 32)
          ≤ ((1 + |t|) / 2) * (Real.sqrt |t| / 2) * ((1 / 2) * Real.log (2 + |t|)) := by
        have e1 : (1 + |t|) * Real.sqrt |t| * (Real.log (2 + |t|) / 32)
            = (1 + |t|) * Real.sqrt |t| * Real.log (2 + |t|) / 32 := by ring
        have e2 : ((1 + |t|) / 2) * (Real.sqrt |t| / 2) * ((1 / 2) * Real.log (2 + |t|))
            = (1 + |t|) * Real.sqrt |t| * Real.log (2 + |t|) / 8 := by ring
        rw [e1, e2]
        exact div_le_div_of_nonneg_left (mul_nonneg (mul_nonneg hAn hCn) hLn) (by norm_num)
          (by norm_num)
      have heq : (1 / 64) * ((1 + |t|) * (1 + |t|) ^ ((1 : ℝ) / 2)) * Real.log (2 + |t|)
          = ((1 + |t|) * ((1 + |t|) ^ ((1 : ℝ) / 2) / 2)) * (Real.log (2 + |t|) / 32) := by
        ring
      rw [heq]; exact le_trans hstep hstep2
    exact h4
  linarith [hmain, hprod]

/-- Lower bound for the weight at `σ = 1`. -/
lemma ZW_lower_one {t : ℝ} (ht : 1 ≤ |t|) :
    (1 / 8) * (1 + |t|) * Real.log (2 + |t|) ≤ ‖ZW (1 + (t : ℂ) * I)‖ := by
  have h1 : (1 + |t|) / 2 ≤ ‖(1 : ℂ) + (t : ℂ) * I + 2‖ := by
    have he : (1 : ℂ) + (t : ℂ) * I + 2 = (3 : ℂ) + (t : ℂ) * I := by ring
    rw [he]; exact add_norm_ge 3 t (by norm_num)
  have hR : ‖Complex.Gamma (1 - (1 + (t : ℂ) * I) / 4)
      / Complex.Gamma (1 / 2 + (1 + (t : ℂ) * I) / 4)‖ = 1 := by
    have hconj : (1 - (1 + (t : ℂ) * I) / 4) = star (1 / 2 + (1 + (t : ℂ) * I) / 4) := by
      apply Complex.ext <;> simp <;> ring
    rw [hconj, norm_div, norm_Gamma_star']
    apply div_self
    apply norm_ne_zero_iff.mpr
    apply gamma_ne_zero_of_re_pos
    rw [Complex.add_re, Complex.div_re]; simp
    norm_num
  have hlog : (1 / 2) * Real.log (2 + |t|) ≤ ‖Complex.log ((1 : ℂ) + (t : ℂ) * I + 2)‖ := by
    have h := ZW_log_lower (s := (1 : ℂ) + (t : ℂ) * I) (by simp) (by simpa using ht)
    simpa using h
  have hmain : ((1 + |t|) / 2) * 1 * ((1 / 2) * Real.log (2 + |t|))
      ≤ ‖ZW (1 + (t : ℂ) * I)‖ := by
    rw [ZW, norm_mul, norm_mul, hR]
    refine mul_le_mul (mul_le_mul_of_nonneg_right h1 (by norm_num)) hlog ?_ ?_
    · exact mul_nonneg (by norm_num) (log_two_add_nonneg t)
    · positivity
  have hprod : (1 / 8) * (1 + |t|) * Real.log (2 + |t|)
      ≤ ((1 + |t|) / 2) * 1 * ((1 / 2) * Real.log (2 + |t|)) := by
    have h3n : (0 : ℝ) < Real.log (2 + |t|) := log_two_add_pos t
    nlinarith [h3n]
  linarith [hmain, hprod]

/-- The `σ = 0` boundary bound, from the functional equation. -/
lemma zeta_zero_bound {t : ℝ} (ht : 1 ≤ |t|) :
    ‖riemannZeta ((t : ℂ) * I)‖ ≤ 40 * (1 + |t|) ^ ((1 : ℝ) / 2) * (Real.log (2 + |t|) + 2) := by
  have ht0 : t ≠ 0 := by intro h; rw [h] at ht; norm_num at ht
  have hne1 : (1 - (t : ℂ) * I) ≠ 1 := by
    intro h
    have h2 := congrArg Complex.im h
    have h3 : (1 - (t : ℂ) * I).im = -t := by simp
    have h4 : ((1 : ℂ)).im = 0 := by simp
    rw [h3, h4] at h2
    exact ht0 (neg_eq_zero.mp h2)
  have hnneg : ∀ n : ℕ, (1 - (t : ℂ) * I) ≠ -((n : ℕ) : ℂ) := by
    intro n h
    have h2 := congrArg Complex.im h
    have h3 : (1 - (t : ℂ) * I).im = -t := by simp
    have h4 : (-((n : ℕ) : ℂ)).im = 0 := by simp
    rw [h3, h4] at h2
    exact ht0 (neg_eq_zero.mp h2)
  have hFE := riemannZeta_one_sub hnneg hne1
  have harg : 1 - (1 - (t : ℂ) * I) = (t : ℂ) * I := by ring
  rw [harg] at hFE
  have hnorm1 : ‖(2 * (Real.pi : ℂ)) ^ (-(1 - (t : ℂ) * I))‖ = (2 * Real.pi)⁻¹ := by
    rw [show (2 * (Real.pi : ℂ)) = (((2 * Real.pi) : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    have hre : (-(1 - (t : ℂ) * I)).re = -1 := by simp
    rw [hre, Real.rpow_neg_one]
  have hsq : ‖Complex.Gamma (1 - (t : ℂ) * I)‖ ^ 2
      = Real.pi * |t| / Real.sinh (Real.pi * |t|) := by
    have hv : (-t) ≠ 0 := by intro h; exact ht0 (neg_eq_zero.mp h)
    have h := Commons.Analysis.Complex.gamma_one_norm_sq (-t) hv
    have harg2 : (1 : ℂ) + I * (((-t) : ℝ) : ℂ) = 1 - (t : ℂ) * I := by push_cast; ring
    rw [harg2, abs_neg] at h
    exact h
  have hnegsinh : 0 < Real.sinh (Real.pi * |t|) := Real.sinh_pos_iff.mpr (by positivity)
  have hx1 : (1 : ℝ) ≤ Real.pi * |t| := by nlinarith [Real.pi_gt_three, ht]
  have hxpos : (0 : ℝ) < Real.pi * |t| := by linarith
  have hsinh : Real.exp (Real.pi * |t|) / 4 ≤ Real.sinh (Real.pi * |t|) := by
    rw [Real.sinh_eq]
    have hexp : Real.exp (-(Real.pi * |t|)) ≤ Real.exp (Real.pi * |t|) / 2 := by
      rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos _)]
      have h2 : (2 : ℝ) ≤ Real.exp (Real.pi * |t|) := by
        have h3 : Real.exp 1 ≤ Real.exp (Real.pi * |t|) := Real.exp_le_exp.mpr hx1
        linarith [Real.exp_one_gt_d9]
      have hmul : Real.exp (Real.pi * |t|) * Real.exp (Real.pi * |t|)
          = Real.exp (2 * (Real.pi * |t|)) := by rw [← Real.exp_add]; ring_nf
      nlinarith [hmul, h2]
    linarith [hexp]
  have hkey : (1 : ℝ) / 4 ≤ Real.exp (-(Real.pi * |t|)) * Real.sinh (Real.pi * |t|) := by
    have h1 := mul_le_mul_of_nonneg_left hsinh (Real.exp_pos (-(Real.pi * |t|))).le
    have h2 : Real.exp (-(Real.pi * |t|)) * (Real.exp (Real.pi * |t|) / 4) = 1 / 4 := by
      rw [show Real.exp (-(Real.pi * |t|)) * (Real.exp (Real.pi * |t|) / 4)
            = (Real.exp (-(Real.pi * |t|)) * Real.exp (Real.pi * |t|)) / 4 by ring,
        ← Real.exp_add, show -(Real.pi * |t|) + Real.pi * |t| = 0 by ring, Real.exp_zero]
    linarith [h1, h2]
  have hG : ‖Complex.Gamma (1 - (t : ℂ) * I)‖
      ≤ 4 * (1 + |t|) ^ ((1 : ℝ) / 2) * Real.exp (-(Real.pi / 2) * |t|) := by
    have h4 : Real.pi ≤ 4 := by linarith [Real.pi_lt_four]
    have hx : (0 : ℝ) ≤ |t| := abs_nonneg t
    have hXp : 0 < (1 + |t|) ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos (by linarith) _
    have hEp : 0 < Real.exp (-(Real.pi / 2) * |t|) := Real.exp_pos _
    have hEp2 : 0 < Real.exp (-(Real.pi * |t|)) := Real.exp_pos _
    have hX2 : (1 + |t|) ^ ((1 : ℝ) / 2) * (1 + |t|) ^ ((1 : ℝ) / 2) = 1 + |t| := by
      rw [← Real.rpow_add (by linarith)]; norm_num
    have hE2 : Real.exp (-(Real.pi / 2) * |t|) * Real.exp (-(Real.pi / 2) * |t|)
        = Real.exp (-(Real.pi * |t|)) := by
      rw [← Real.exp_add]; ring_nf
    have hsq2 : ‖Complex.Gamma (1 - (t : ℂ) * I)‖ ^ 2
        ≤ (4 * (1 + |t|) ^ ((1 : ℝ) / 2) * Real.exp (-(Real.pi / 2) * |t|)) ^ 2 := by
      have hexpand : (4 * (1 + |t|) ^ ((1 : ℝ) / 2) * Real.exp (-(Real.pi / 2) * |t|)) ^ 2
          = 16 * (1 + |t|) * Real.exp (-(Real.pi * |t|)) := by
        rw [pow_two, show (4 * (1 + |t|) ^ ((1 : ℝ) / 2) * Real.exp (-(Real.pi / 2) * |t|))
              * (4 * (1 + |t|) ^ ((1 : ℝ) / 2) * Real.exp (-(Real.pi / 2) * |t|))
            = 16 * ((1 + |t|) ^ ((1 : ℝ) / 2) * (1 + |t|) ^ ((1 : ℝ) / 2))
              * (Real.exp (-(Real.pi / 2) * |t|) * Real.exp (-(Real.pi / 2) * |t|)) by ring,
          hX2, hE2]
      rw [hsq, hexpand, div_le_iff₀ hnegsinh]
      have hkey' : (1 : ℝ) / 4 ≤ Real.exp (-(Real.pi * |t|)) * Real.sinh (Real.pi * |t|) := hkey
      have h1 : Real.pi * |t| ≤ 16 * (1 + |t|) * (1 / 4) := by nlinarith [h4, hx]
      have h2 : 16 * (1 + |t|) * (1 / 4)
          ≤ 16 * (1 + |t|) * (Real.exp (-(Real.pi * |t|)) * Real.sinh (Real.pi * |t|)) := by
        have h1n : (0 : ℝ) ≤ 16 * (1 + |t|) := by linarith [hx]
        exact mul_le_mul_of_nonneg_left hkey' h1n
      linarith [h1, h2]
    have h2 : (0 : ℝ) ≤ 4 * (1 + |t|) ^ ((1 : ℝ) / 2) * Real.exp (-(Real.pi / 2) * |t|) := by
      positivity
    nlinarith [hsq2, norm_nonneg (Complex.Gamma (1 - (t : ℂ) * I)), h2]
  have hc : ‖Complex.cos ((Real.pi : ℂ) * (1 - (t : ℂ) * I) / 2)‖
      ≤ Real.exp ((Real.pi / 2) * |t|) := by
    have hargc : (Real.pi : ℂ) * (1 - (t : ℂ) * I) / 2
        = (Real.pi : ℂ) / 2 - (Real.pi : ℂ) * (((t : ℂ) * I) / 2) := by ring
    rw [hargc, Complex.cos_pi_div_two_sub]
    have h := Commons.Analysis.Complex.norm_sin_pi_le (((t : ℂ) * I) / 2)
    have him : ((((t : ℂ) * I) / 2)).im = t / 2 := by simp
    rw [him, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
    refine le_trans h (Real.exp_le_exp.mpr ?_)
    nlinarith [abs_nonneg t, Real.pi_pos]
  have hz : ‖riemannZeta (1 - (t : ℂ) * I)‖ ≤ 5 * Real.log (|t| + 2) := by
    have h := Commons.NumberTheory.LSeries.norm_riemannZeta_le_five_mul_log (σ := (1 : ℝ)) (t := -t)
      (by norm_num) (by simpa using ht)
    have hargz : ((1 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I = 1 - (t : ℂ) * I := by push_cast; ring
    rw [hargz, abs_neg] at h
    exact h
  have hcancel : Real.exp ((Real.pi / 2) * |t|) * Real.exp (-(Real.pi / 2) * |t|) = 1 := by
    rw [← Real.exp_add]; ring_nf; rw [Real.exp_zero]
  have hlogabs : Real.log (|t| + 2) = Real.log (2 + |t|) := by rw [add_comm]
  calc ‖riemannZeta ((t : ℂ) * I)‖
      = ‖2 * (2 * (Real.pi : ℂ)) ^ (-(1 - (t : ℂ) * I)) * Complex.Gamma (1 - (t : ℂ) * I)
          * Complex.cos ((Real.pi : ℂ) * (1 - (t : ℂ) * I) / 2) * riemannZeta (1 - (t : ℂ) * I)‖ := by
        rw [hFE]
    _ = 2 * ‖(2 * (Real.pi : ℂ)) ^ (-(1 - (t : ℂ) * I))‖ * ‖Complex.Gamma (1 - (t : ℂ) * I)‖
          * ‖Complex.cos ((Real.pi : ℂ) * (1 - (t : ℂ) * I) / 2)‖
          * ‖riemannZeta (1 - (t : ℂ) * I)‖ := by
        rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_ofNat]
    _ ≤ 2 * (2 * Real.pi)⁻¹ * (4 * (1 + |t|) ^ ((1 : ℝ) / 2) * Real.exp (-(Real.pi / 2) * |t|))
          * Real.exp ((Real.pi / 2) * |t|) * (5 * Real.log (|t| + 2)) := by
        apply mul_le_mul
        · apply mul_le_mul
          · apply mul_le_mul
            · rw [hnorm1]
            · exact hG
            · positivity
            · positivity
          · exact hc
          · positivity
          · positivity
        · exact hz
        · positivity
        · positivity
    _ = (2 * (2 * Real.pi)⁻¹ * 4 * 5) * (1 + |t|) ^ ((1 : ℝ) / 2)
          * (Real.exp (-(Real.pi / 2) * |t|) * Real.exp ((Real.pi / 2) * |t|))
          * Real.log (2 + |t|) := by
        rw [hlogabs]; ring
    _ = (2 * (2 * Real.pi)⁻¹ * 4 * 5) * (1 + |t|) ^ ((1 : ℝ) / 2) * 1
          * Real.log (2 + |t|) := by rw [mul_comm (Real.exp (-(Real.pi / 2) * |t|)), hcancel]
    _ ≤ 40 * (1 + |t|) ^ ((1 : ℝ) / 2) * (Real.log (2 + |t|) + 2) := by
        have hX : (0 : ℝ) ≤ (1 + |t|) ^ ((1 : ℝ) / 2) := Real.rpow_nonneg (by linarith) _
        have hL : (0 : ℝ) ≤ Real.log (2 + |t|) := log_two_add_nonneg t
        have hcoef : 2 * (2 * Real.pi)⁻¹ * 4 * 5 ≤ 40 := by
          rw [show (2:ℝ) * (2 * Real.pi)⁻¹ * 4 * 5 = 40 / (2 * Real.pi) by
            field_simp; ring]
          rw [div_le_iff₀ (by positivity)]
          nlinarith [Real.pi_gt_three]
        have h1 : (2 * (2 * Real.pi)⁻¹ * 4 * 5) * (1 + |t|) ^ ((1 : ℝ) / 2) * 1
            ≤ 40 * (1 + |t|) ^ ((1 : ℝ) / 2) := by
          rw [mul_one]
          exact mul_le_mul_of_nonneg_right hcoef hX
        have h2 : (2 * (2 * Real.pi)⁻¹ * 4 * 5) * (1 + |t|) ^ ((1 : ℝ) / 2) * 1
              * Real.log (2 + |t|)
            ≤ 40 * (1 + |t|) ^ ((1 : ℝ) / 2) * Real.log (2 + |t|) :=
          mul_le_mul_of_nonneg_right h1 hL
        have h3 : 40 * (1 + |t|) ^ ((1 : ℝ) / 2) * Real.log (2 + |t|)
            ≤ 40 * (1 + |t|) ^ ((1 : ℝ) / 2) * (Real.log (2 + |t|) + 2) :=
          mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (by norm_num) hX)
        linarith [h2, h3]
lemma ZW_differentiableAt (z : ℂ) (hlo : -2 < z.re) (hhi : z.re < 4) : DifferentiableAt ℂ ZW z := by
  unfold ZW
  refine DifferentiableAt.mul (DifferentiableAt.mul ?_ ?_) ?_
  · fun_prop
  · refine DifferentiableAt.div ?_ ?_ ?_
    · refine (Complex.differentiableAt_Gamma (1 - z / 4) ?_).comp z (by fun_prop)
      intro m hm
      have hre := congrArg Complex.re hm
      rw [Complex.sub_re, Complex.div_re] at hre
      simp at hre
      have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    · refine (Complex.differentiableAt_Gamma (1 / 2 + z / 4) ?_).comp z (by fun_prop)
      intro m hm
      have hre := congrArg Complex.re hm
      rw [Complex.add_re, Complex.div_re] at hre
      simp at hre
      have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    · apply gamma_ne_zero_of_re_pos
      rw [Complex.add_re, Complex.div_re]; simp; linarith
  · have hmem : z + 2 ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]; left
      rw [Complex.add_re]; simp; linarith
    exact (Complex.differentiableAt_log hmem).comp z
      (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => w + 2) z)

lemma ZW_ne_zero (z : ℂ) (hlo : 0 ≤ z.re) (hhi : z.re ≤ 1) : ZW z ≠ 0 := by
  unfold ZW
  refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
  · intro h
    have hre := congrArg Complex.re h
    rw [Complex.add_re] at hre
    simp at hre
    linarith
  · refine div_ne_zero (gamma_ne_zero_of_re_pos ?_) (gamma_ne_zero_of_re_pos ?_)
    · rw [Complex.sub_re, Complex.div_re]; simp; linarith
    · rw [Complex.add_re, Complex.div_re]; simp; linarith
  · intro h
    have hre := congrArg Complex.re h
    rw [Complex.log_re, Complex.zero_re] at hre
    have h2 : (2 : ℝ) ≤ ‖z + 2‖ := by
      have h := Complex.re_le_norm (z + 2)
      rw [Complex.add_re] at h; simp at h; linarith
    have h3 : 0 < Real.log ‖z + 2‖ := Real.log_pos (by linarith)
    linarith

lemma log_two_add_ge_one {t : ℝ} (ht : 1 ≤ |t|) : (1 : ℝ) ≤ Real.log (2 + |t|) := by
  rw [Real.le_log_iff_exp_le (by linarith [abs_nonneg t])]
  have h3 : (3 : ℝ) ≤ 2 + |t| := by linarith
  linarith [Real.exp_one_lt_three]

lemma rpow_three_halves (t σ : ℝ) :
    (1 + |t|) ^ ((3 : ℝ) / 2 - σ / 2) / (1 + |t|) = (1 + |t|) ^ ((1 : ℝ) / 2 - σ / 2) := by
  have hX : (0 : ℝ) < 1 + |t| := by linarith [abs_nonneg t]
  have hthis : (3 : ℝ) / 2 - σ / 2 = ((1 : ℝ) / 2 - σ / 2) + 1 := by ring
  rw [hthis, Real.rpow_add hX, Real.rpow_one]
  field_simp

lemma zeta_ratio_zero : ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ |t| →
    ‖riemannZeta₁ ((t : ℂ) * I) / ZW ((t : ℂ) * I)‖ ≤ C := by
  refine ⟨7680, by norm_num, ?_⟩
  intro t ht
  have ht0 : t ≠ 0 := by intro h; rw [h] at ht; norm_num at ht
  have hs : ((t : ℂ) * I) ≠ 1 := by
    intro h
    have h2 := congrArg Complex.im h
    have h3 : ((t : ℂ) * I).im = t := by simp
    have h4 : (1 : ℂ).im = 0 := by simp
    rw [h3, h4] at h2
    exact ht0 h2
  have hmul : riemannZeta₁ ((t : ℂ) * I) = (((t : ℂ) * I) - 1) * riemannZeta ((t : ℂ) * I) := by
    have h := riemannZeta_eq_inv_sub_mul (s := (t : ℂ) * I) hs
    have hne : (((t : ℂ) * I) - 1) ≠ 0 := sub_ne_zero.mpr hs
    calc riemannZeta₁ ((t : ℂ) * I)
        = (((t : ℂ) * I) - 1) * ((((t : ℂ) * I) - 1)⁻¹ * riemannZeta₁ ((t : ℂ) * I)) := by
          rw [mul_inv_cancel_left₀ hne]
      _ = (((t : ℂ) * I) - 1) * riemannZeta ((t : ℂ) * I) := by rw [← h]
  have h1 : ‖((t : ℂ) * I) - 1‖ ≤ 1 + |t| := by
    have h := Complex.norm_le_abs_re_add_abs_im (((t : ℂ) * I) - 1)
    have hre : (((t : ℂ) * I) - 1).re = -1 := by simp
    have him : (((t : ℂ) * I) - 1).im = t := by simp
    rw [hre, him] at h
    simp only [abs_neg, abs_one] at h
    linarith
  have hnum : ‖riemannZeta₁ ((t : ℂ) * I)‖
      ≤ (1 + |t|) * (40 * (1 + |t|) ^ ((1 : ℝ) / 2) * (Real.log (2 + |t|) + 2)) := by
    rw [hmul, norm_mul]
    exact mul_le_mul h1 (zeta_zero_bound ht) (norm_nonneg _) (by positivity)
  have hden : (1 / 64) * (1 + |t|) ^ ((3 : ℝ) / 2) * Real.log (2 + |t|) ≤ ‖ZW ((t : ℂ) * I)‖ :=
    ZW_lower_zero ht
  have hdenpos : 0 < (1 / 64) * (1 + |t|) ^ ((3 : ℝ) / 2) * Real.log (2 + |t|) := by
    refine mul_pos (mul_pos (by norm_num) (Real.rpow_pos_of_pos (by linarith [abs_nonneg t]) _)) ?_
    exact log_two_add_pos t
  have hWpos : 0 < ‖ZW ((t : ℂ) * I)‖ := lt_of_lt_of_le hdenpos hden
  have hL := log_two_add_pos t
  have hL1 := log_two_add_ge_one ht
  have hX : (0 : ℝ) < (1 + |t|) ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos (by linarith [abs_nonneg t]) _
  have hX3 : (0 : ℝ) < (1 + |t|) ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos (by linarith [abs_nonneg t]) _
  have hsplit : (1 + |t|) ^ ((3 : ℝ) / 2) = (1 + |t|) * (1 + |t|) ^ ((1 : ℝ) / 2) := by
    have hthis : (3 : ℝ) / 2 = 1 + ((1 : ℝ) / 2) := by ring
    rw [hthis, Real.rpow_add (by linarith [abs_nonneg t]), Real.rpow_one]
  rw [norm_div]
  refine le_trans (div_le_div_of_nonneg_right hnum (norm_nonneg _)) ?_
  refine le_trans (div_le_div_of_nonneg_left (by positivity) hdenpos hden) ?_
  rw [div_le_iff₀ (by positivity)]
  have hgoal : (1 + |t|) * (40 * (1 + |t|) ^ ((1 : ℝ) / 2) * (Real.log (2 + |t|) + 2))
      = 40 * ((1 + |t|) * (1 + |t|) ^ ((1 : ℝ) / 2)) * (Real.log (2 + |t|) + 2) := by ring
  rw [hgoal, ← hsplit]
  have hb : 7680 * ((1 / 64) * (1 + |t|) ^ ((3 : ℝ) / 2) * Real.log (2 + |t|))
      = 120 * ((1 + |t|) ^ ((3 : ℝ) / 2) * Real.log (2 + |t|)) := by ring
  rw [hb]
  nlinarith [hL, hL1, hX3]

lemma zeta_ratio_one : ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ |t| →
    ‖riemannZeta₁ (1 + (t : ℂ) * I) / ZW (1 + (t : ℂ) * I)‖ ≤ C := by
  refine ⟨40, by norm_num, ?_⟩
  intro t ht
  have ht0 : t ≠ 0 := by intro h; rw [h] at ht; norm_num at ht
  have hs : (1 + (t : ℂ) * I) ≠ 1 := by
    intro h
    have h2 := congrArg Complex.im h
    have h3 : (1 + (t : ℂ) * I).im = t := by simp
    have h4 : (1 : ℂ).im = 0 := by simp
    rw [h3, h4] at h2
    exact ht0 h2
  have hmul : riemannZeta₁ (1 + (t : ℂ) * I)
      = ((t : ℂ) * I) * riemannZeta (1 + (t : ℂ) * I) := by
    have h := riemannZeta_eq_inv_sub_mul (s := 1 + (t : ℂ) * I) hs
    have hne : ((1 + (t : ℂ) * I) - 1) ≠ 0 := sub_ne_zero.mpr hs
    have hsub : (1 + (t : ℂ) * I) - 1 = (t : ℂ) * I := by ring
    calc riemannZeta₁ (1 + (t : ℂ) * I)
        = ((1 + (t : ℂ) * I) - 1) * (((1 + (t : ℂ) * I) - 1)⁻¹ * riemannZeta₁ (1 + (t : ℂ) * I)) := by
          rw [mul_inv_cancel_left₀ hne]
      _ = ((1 + (t : ℂ) * I) - 1) * riemannZeta (1 + (t : ℂ) * I) := by rw [← h]
      _ = ((t : ℂ) * I) * riemannZeta (1 + (t : ℂ) * I) := by rw [hsub]
  have h1 : ‖(t : ℂ) * I‖ = |t| := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have h2 : |t| ≤ 1 + |t| := by linarith [abs_nonneg t]
  have hz : ‖riemannZeta (1 + (t : ℂ) * I)‖ ≤ 5 * Real.log (2 + |t|) := by
    have h := Commons.NumberTheory.LSeries.norm_riemannZeta_le_five_mul_log (σ := (1:ℝ)) (t := t)
      (by norm_num) (by simpa using ht)
    have hargz : ((1 : ℝ) : ℂ) + ((t : ℝ) : ℂ) * I = 1 + (t : ℂ) * I := by push_cast; ring
    rw [hargz] at h
    have hlog : Real.log (|t| + 2) = Real.log (2 + |t|) := by rw [add_comm]
    rwa [hlog] at h
  have hnum : ‖riemannZeta₁ (1 + (t : ℂ) * I)‖ ≤ (1 + |t|) * (5 * Real.log (2 + |t|)) := by
    rw [hmul, norm_mul, h1]
    exact mul_le_mul h2 hz (norm_nonneg _) (by positivity)
  have hden : (1 / 8) * (1 + |t|) * Real.log (2 + |t|) ≤ ‖ZW (1 + (t : ℂ) * I)‖ :=
    ZW_lower_one ht
  have hdenpos : 0 < (1 / 8) * (1 + |t|) * Real.log (2 + |t|) := by
    refine mul_pos (mul_pos (by norm_num) (by linarith [abs_nonneg t])) ?_
    exact log_two_add_pos t
  have hL := log_two_add_pos t
  rw [norm_div]
  refine le_trans (div_le_div_of_nonneg_right hnum (norm_nonneg _)) ?_
  refine le_trans (div_le_div_of_nonneg_left (by positivity) hdenpos hden) ?_
  rw [div_le_iff₀ (by positivity)]
  have hgoal : (1 + |t|) * (5 * Real.log (2 + |t|)) = 5 * ((1 + |t|) * Real.log (2 + |t|)) := by ring
  have hb : 40 * ((1 / 8) * (1 + |t|) * Real.log (2 + |t|))
      = 5 * ((1 + |t|) * Real.log (2 + |t|)) := by ring
  rw [hgoal, hb]

lemma zeta_ratio_compact :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 → |z.im| ≤ 1 →
      ‖riemannZeta₁ z / ZW z‖ ≤ C := by
  have hKc : IsCompact (Complex.re ⁻¹' (Set.Icc (0:ℝ) 1) ∩ Complex.im ⁻¹' (Set.Icc (-1:ℝ) 1)) := by
    rw [Metric.isCompact_iff_isClosed_bounded]
    refine ⟨?_, ?_⟩
    · exact (IsClosed.preimage continuous_re isClosed_Icc).inter
        (IsClosed.preimage continuous_im isClosed_Icc)
    · apply Bornology.IsBounded.subset (Metric.isBounded_closedBall (x := (0:ℂ)) (r := 3))
      intro z hz
      obtain ⟨hz1, hz2⟩ := hz
      simp only [Set.mem_preimage, Set.mem_Icc] at hz1 hz2
      rw [Metric.mem_closedBall, dist_zero_right]
      have h1 : |z.re| ≤ 1 := by rw [abs_le]; exact ⟨by linarith [hz1.1], hz1.2⟩
      have h2 : |z.im| ≤ 1 := abs_le.mpr hz2
      calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
        _ ≤ 2 := by linarith
        _ ≤ 3 := by norm_num
  have hcont : ContinuousOn (fun z : ℂ => riemannZeta₁ z / ZW z)
      (Complex.re ⁻¹' (Set.Icc (0:ℝ) 1) ∩ Complex.im ⁻¹' (Set.Icc (-1:ℝ) 1)) := by
    intro z hz
    obtain ⟨hz1, hz2⟩ := hz
    simp only [Set.mem_preimage, Set.mem_Icc] at hz1 hz2
    exact ContinuousAt.continuousWithinAt
      (((differentiable_riemannZeta₁ z).continuousAt).div
        ((ZW_differentiableAt z (by linarith [hz1.1]) (by linarith [hz1.2])).continuousAt)
        (ZW_ne_zero z (by linarith [hz1.1]) (by linarith [hz1.2])))
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hcont
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro z h1 h2 h3
  have hz : z ∈ Complex.re ⁻¹' (Set.Icc (0:ℝ) 1) ∩ Complex.im ⁻¹' (Set.Icc (-1:ℝ) 1) := by
    refine ⟨?_, ?_⟩
    · simp only [Set.mem_preimage, Set.mem_Icc]; exact ⟨h1, h2⟩
    · simp only [Set.mem_preimage, Set.mem_Icc]; exact abs_le.mp h3
  exact le_trans (hC z hz) (le_max_left _ _)
lemma ZW_growth :
    ∃ B : ℝ, (fun z : ℂ => riemannZeta₁ z / ZW z) =O[
      Filter.comap (abs ∘ Complex.im) Filter.atTop ⊓ Filter.principal (Complex.re ⁻¹' Set.Ioo 0 1)]
      (fun z : ℂ => Real.exp (B * Real.exp (1 * |z.im|))) := by
  obtain ⟨Cz, hCzpos, hCz⟩ := Commons.NumberTheory.Zeta.zeta_strip_polyGrowth
  obtain ⟨Ag, Bg, hAgpos, hBgpos, hGn⟩ := Commons.Analysis.Complex.Gamma_vertical_norm_bounds
  refine ⟨|Real.log (768 * Cz * Bg / (2 * Ag))| + 46, ?_⟩
  rw [Asymptotics.isBigO_iff]
  refine ⟨1, ?_⟩
  rw [Filter.eventually_inf_principal, Filter.eventually_comap]
  filter_upwards [Filter.eventually_ge_atTop (4:ℝ)] with b hb
  intro z hzim hz
  have h1 : (4 : ℝ) ≤ |z.im| := by
    have h := hb
    simp only [Function.comp_apply] at hzim
    rw [← hzim] at h
    exact h
  have hb1 : (1 : ℝ) ≤ |z.im| := by linarith
  have hzre : 0 ≤ z.re ∧ z.re ≤ 1 := by
    simp only [Set.mem_preimage, Set.mem_Ioo] at hz
    exact ⟨le_of_lt hz.1, le_of_lt hz.2⟩
  have hbpos : (0 : ℝ) < 1 + |z.im| := by linarith [abs_nonneg z.im]
  -- the zeta factor
  have hzeta : ‖riemannZeta₁ z‖ ≤ 768 * Cz * (1 + |z.im|) ^ 5 := by
    have hz1 : ‖riemannZeta z‖ ≤ Cz * (|z.im| + 3) ^ 4 := by
      have h := hCz z.re z.im (by linarith [hzre.1]) (by linarith [hzre.2]) (by linarith)
      have hargz : (z.re : ℂ) + I * (z.im : ℂ) = z := by apply Complex.ext <;> simp
      rwa [hargz] at h
    have hsub : ‖z - 1‖ ≤ 3 * (1 + |z.im|) := by
      have h := Complex.norm_le_abs_re_add_abs_im (z - 1)
      have hre : (z - 1).re = z.re - 1 := by simp
      have him : (z - 1).im = z.im := by simp
      rw [hre, him] at h
      have h2 : |z.re - 1| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hzre.1, hzre.2]
      nlinarith [h, h2]
    have h3 : (|z.im| + 3) ^ 4 ≤ 256 * (1 + |z.im|) ^ 4 := by
      have h4 : |z.im| + 3 ≤ 4 * (1 + |z.im|) := by linarith
      have h5 : (0 : ℝ) ≤ |z.im| + 3 := by linarith
      calc (|z.im| + 3) ^ 4 ≤ (4 * (1 + |z.im|)) ^ 4 := pow_le_pow_left₀ h5 h4 4
        _ = 256 * (1 + |z.im|) ^ 4 := by ring
    have hs : z ≠ 1 := by
      intro h; rw [h] at h1; simp at h1; linarith
    have hEq : riemannZeta₁ z = (z - 1) * riemannZeta z := by
      have h := riemannZeta_eq_inv_sub_mul (s := z) hs
      have hne : (z - 1) ≠ 0 := sub_ne_zero.mpr hs
      calc riemannZeta₁ z = (z - 1) * ((z - 1)⁻¹ * riemannZeta₁ z) := by rw [mul_inv_cancel_left₀ hne]
        _ = (z - 1) * riemannZeta z := by rw [← h]
    rw [hEq, norm_mul]
    calc ‖z - 1‖ * ‖riemannZeta z‖ ≤ (3 * (1 + |z.im|)) * (Cz * (|z.im| + 3) ^ 4) :=
          mul_le_mul hsub hz1 (norm_nonneg _) (by positivity)
      _ ≤ (3 * (1 + |z.im|)) * (Cz * (256 * (1 + |z.im|) ^ 4)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 hCzpos.le) (by positivity)
      _ = 768 * Cz * (1 + |z.im|) ^ 5 := by ring
  -- the weight factor
  have hy1 : |(1 - z / 4).im| = |z.im| / 4 := by
    have h : (1 - z / 4).im = -(z.im / 4) := by
      rw [Complex.sub_im, Complex.div_im]; simp; try ring
    calc |(1 - z / 4).im| = |-(z.im / 4)| := by rw [h]
      _ = |z.im / 4| := abs_neg _
      _ = |z.im| / 4 := by
        rw [show z.im / 4 = z.im * (1/4) by ring, abs_mul,
          abs_of_pos (by norm_num : (0:ℝ) < 1/4)]
        ring
  have hy2 : |(1 / 2 + z / 4).im| = |z.im| / 4 := by
    have h : (1 / 2 + z / 4).im = z.im / 4 := by
      rw [Complex.add_im, Complex.div_im]; simp; try ring
    calc |(1 / 2 + z / 4).im| = |z.im / 4| := by rw [h]
      _ = |z.im| / 4 := by
        rw [show z.im / 4 = z.im * (1/4) by ring, abs_mul,
          abs_of_pos (by norm_num : (0:ℝ) < 1/4)]
        ring
  have hre1 : (1 - z / 4).re ∈ Set.Icc (-5:ℝ) 5 := by
    rw [Complex.sub_re, Complex.div_re]; simp
    constructor <;> linarith [hzre.1, hzre.2]
  have hre2 : (1 / 2 + z / 4).re ∈ Set.Icc (-5:ℝ) 5 := by
    rw [Complex.add_re, Complex.div_re]; simp
    constructor <;> linarith [hzre.1, hzre.2]
  have him1 : 1 ≤ |(1 - z / 4).im| := by rw [hy1]; linarith
  have him2 : 1 ≤ |(1 / 2 + z / 4).im| := by rw [hy2]; linarith
  have hx1 : ((1 - z / 4).re : ℂ) + I * ((1 - z / 4).im : ℂ) = 1 - z / 4 := by
    rw [mul_comm I (((1 - z / 4).im : ℝ)), Complex.re_add_im]
  have hx2 : ((1 / 2 + z / 4).re : ℂ) + I * ((1 / 2 + z / 4).im : ℂ) = 1 / 2 + z / 4 := by
    rw [mul_comm I (((1 / 2 + z / 4).im : ℝ)), Complex.re_add_im]
  have hb1 : Ag * Real.exp (-(Real.pi / 2) * (|z.im| / 4)) / (1 + |z.im| / 4) ^ 20
      ≤ ‖Complex.Gamma (1 - z / 4)‖ := by
    have h := (hGn (1 - z / 4).re hre1 (1 - z / 4).im him1).1
    rw [hy1] at h
    rwa [hx1] at h
  have hb2 : ‖Complex.Gamma (1 / 2 + z / 4)‖
      ≤ Bg * Real.exp (-(Real.pi / 2) * (|z.im| / 4)) * (1 + |z.im| / 4) ^ 20 := by
    have h := (hGn (1 / 2 + z / 4).re hre2 (1 / 2 + z / 4).im him2).2
    rw [hy2] at h
    rwa [hx2] at h
  have hG2pos : 0 < ‖Complex.Gamma (1 / 2 + z / 4)‖ := by
    apply norm_pos_iff.mpr
    apply gamma_ne_zero_of_re_pos
    rw [Complex.add_re, Complex.div_re]; simp; linarith [hzre.1]
  have hN : (0 : ℝ) < 1 + |z.im| / 4 := by positivity
  have hNle : (1 + |z.im| / 4) ≤ 1 + |z.im| := by linarith [abs_nonneg z.im]
  have hratio : Ag / Bg * (1 + |z.im| / 4) ^ (-(40:ℝ))
      ≤ ‖Complex.Gamma (1 - z / 4) / Complex.Gamma (1 / 2 + z / 4)‖ := by
    have hident : Ag / Bg * (1 + |z.im| / 4) ^ (-(40:ℝ))
        = (Ag * Real.exp (-(Real.pi / 2) * (|z.im| / 4)) / (1 + |z.im| / 4) ^ 20)
          / (Bg * Real.exp (-(Real.pi / 2) * (|z.im| / 4)) * (1 + |z.im| / 4) ^ 20) := by
      rw [Real.rpow_neg (le_of_lt hN),
        show (1 + |z.im| / 4) ^ (40:ℝ) = (1 + |z.im| / 4) ^ 40 by norm_num]
      field_simp
    rw [hident]
    have hstep1 : (Ag * Real.exp (-(Real.pi / 2) * (|z.im| / 4)) / (1 + |z.im| / 4) ^ 20)
          / (Bg * Real.exp (-(Real.pi / 2) * (|z.im| / 4)) * (1 + |z.im| / 4) ^ 20)
        ≤ ‖Complex.Gamma (1 - z / 4)‖
          / (Bg * Real.exp (-(Real.pi / 2) * (|z.im| / 4)) * (1 + |z.im| / 4) ^ 20) :=
      div_le_div_of_nonneg_right hb1 (by positivity)
    have hstep2 : ‖Complex.Gamma (1 - z / 4)‖
          / (Bg * Real.exp (-(Real.pi / 2) * (|z.im| / 4)) * (1 + |z.im| / 4) ^ 20)
        ≤ ‖Complex.Gamma (1 - z / 4)‖ / ‖Complex.Gamma (1 / 2 + z / 4)‖ :=
      div_le_div_of_nonneg_left (norm_nonneg _) hG2pos hb2
    exact le_trans (le_trans hstep1 hstep2) (le_of_eq (norm_div _ _).symm)
  have hpowN : (1 + |z.im|) ^ (-(40:ℝ)) ≤ (1 + |z.im| / 4) ^ (-(40:ℝ)) := by
    rw [Real.rpow_neg (by linarith [abs_nonneg z.im]), Real.rpow_neg (le_of_lt hN),
      show (1 + |z.im|) ^ (40:ℝ) = (1 + |z.im|) ^ 40 by norm_num,
      show (1 + |z.im| / 4) ^ (40:ℝ) = (1 + |z.im| / 4) ^ 40 by norm_num,
      inv_eq_one_div, inv_eq_one_div]
    exact one_div_le_one_div_of_le (pow_pos hN 40) (pow_le_pow_left₀ hN.le hNle 40)
  have hlog1 : (1 : ℝ) ≤ ‖Complex.log (z + 2)‖ := by
    have h3v : (3 : ℝ) ≤ ‖z + 2‖ := by
      have h := Complex.abs_im_le_norm (z + 2)
      have him : (z + 2).im = z.im := by simp
      rw [him] at h
      linarith
    have hlog3 : (1 : ℝ) < Real.log 3 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      exact Real.exp_one_lt_three
    have h3 : (1 : ℝ) ≤ Real.log ‖z + 2‖ := by
      have := Real.log_le_log (by norm_num : (0:ℝ) < 3) h3v
      linarith
    calc (1 : ℝ) ≤ (Complex.log (z + 2)).re := by rw [Complex.log_re]; exact h3
      _ ≤ ‖Complex.log (z + 2)‖ := Complex.re_le_norm _
  have hW : (2 * Ag / Bg) * (1 + |z.im|) ^ (-(40:ℝ)) ≤ ‖ZW z‖ := by
    have h2 : (2 : ℝ) ≤ ‖z + 2‖ := by
      have h := Complex.re_le_norm (z + 2)
      rw [Complex.add_re] at h; simp at h; linarith [hzre.1]
    have hW0 : 2 * (Ag / Bg) * (1 + |z.im| / 4) ^ (-(40:ℝ)) ≤ ‖ZW z‖ := by
      unfold ZW
      rw [norm_mul, norm_mul]
      calc 2 * (Ag / Bg) * (1 + |z.im| / 4) ^ (-(40:ℝ))
          = 2 * (Ag / Bg * (1 + |z.im| / 4) ^ (-(40:ℝ))) * 1 := by ring
        _ ≤ ‖z + 2‖ * ‖Complex.Gamma (1 - z / 4) / Complex.Gamma (1 / 2 + z / 4)‖
              * ‖Complex.log (z + 2)‖ := by
            apply mul_le_mul
            · apply mul_le_mul
              · linarith
              · exact hratio
              · positivity
              · positivity
            · exact hlog1
            · positivity
            · positivity
    have hstep : 2 * Ag / Bg * (1 + |z.im|) ^ (-(40:ℝ))
        ≤ 2 * (Ag / Bg) * (1 + |z.im| / 4) ^ (-(40:ℝ)) := by
      have h2' : (2 : ℝ) * (Ag / Bg) = 2 * Ag / Bg := by ring
      rw [← h2']
      exact mul_le_mul_of_nonneg_left hpowN (by positivity)
    calc 2 * Ag / Bg * (1 + |z.im|) ^ (-(40:ℝ))
        ≤ 2 * (Ag / Bg) * (1 + |z.im| / 4) ^ (-(40:ℝ)) := hstep
      _ ≤ ‖ZW z‖ := hW0
  -- combine
  have hWpos : (0 : ℝ) < (2 * Ag / Bg) * (1 + |z.im|) ^ (-(40:ℝ)) := by
    apply mul_pos (div_pos (by linarith) hBgpos)
    exact Real.rpow_pos_of_pos hbpos _
  have hF : ‖riemannZeta₁ z / ZW z‖ ≤ (768 * Cz * Bg / (2 * Ag)) * (1 + |z.im|) ^ 45 := by
    have hstep1 : ‖riemannZeta₁ z / ZW z‖ ≤ (768 * Cz * (1 + |z.im|) ^ 5) / ‖ZW z‖ := by
      rw [norm_div]
      exact div_le_div_of_nonneg_right hzeta (norm_nonneg _)
    have hstep2 : (768 * Cz * (1 + |z.im|) ^ 5) / ‖ZW z‖
        ≤ (768 * Cz * (1 + |z.im|) ^ 5) / ((2 * Ag / Bg) * (1 + |z.im|) ^ (-(40:ℝ))) :=
      div_le_div_of_nonneg_left (by positivity) hWpos hW
    have hstep3 : (768 * Cz * (1 + |z.im|) ^ 5) / ((2 * Ag / Bg) * (1 + |z.im|) ^ (-(40:ℝ)))
        = (768 * Cz * Bg / (2 * Ag)) * (1 + |z.im|) ^ 45 := by
      rw [Real.rpow_neg hbpos.le,
        show (1 + |z.im|) ^ (40:ℝ) = (1 + |z.im|) ^ 40 by norm_num]
      first | (field_simp; ring) | field_simp
    exact le_trans (le_trans hstep1 hstep2) (le_of_eq hstep3)
  have hexp : (768 * Cz * Bg / (2 * Ag)) * (1 + |z.im|) ^ 45
      ≤ Real.exp ((|Real.log (768 * Cz * Bg / (2 * Ag))| + 46) * Real.exp (1 * |z.im|)) := by
    have hCpos : 0 < 768 * Cz * Bg / (2 * Ag) := by positivity
    rw [one_mul]
    have hCe : (768 * Cz * Bg / (2 * Ag)) * (1 + |z.im|) ^ 45
        = Real.exp (Real.log (768 * Cz * Bg / (2 * Ag)) + 45 * Real.log (1 + |z.im|)) := by
      rw [Real.exp_add, Real.exp_log hCpos]
      rw [show Real.exp (45 * Real.log (1 + |z.im|)) = (1 + |z.im|) ^ 45 from by
        rw [show (45:ℝ) * Real.log (1 + |z.im|) = ((45:ℕ):ℝ) * Real.log (1 + |z.im|) by norm_num,
          Real.exp_nat_mul, Real.exp_log hbpos]]
      try ring
    rw [hCe]
    apply Real.exp_le_exp.mpr
    have hl2 : Real.log (1 + |z.im|) ≤ Real.exp |z.im| := by
      have h := Real.log_le_self hbpos.le
      have h2 := Real.add_one_le_exp |z.im|
      linarith
    have hex : (1 : ℝ) ≤ Real.exp |z.im| := Real.one_le_exp (abs_nonneg _)
    have hlogC : Real.log (768 * Cz * Bg / (2 * Ag))
        ≤ |Real.log (768 * Cz * Bg / (2 * Ag))| := le_abs_self _
    have habs0 : (0 : ℝ) ≤ |Real.log (768 * Cz * Bg / (2 * Ag))| := abs_nonneg _
    nlinarith [hl2, hex, hlogC, habs0]
  calc ‖riemannZeta₁ z / ZW z‖ ≤ (768 * Cz * Bg / (2 * Ag)) * (1 + |z.im|) ^ 45 := hF
    _ ≤ Real.exp ((|Real.log (768 * Cz * Bg / (2 * Ag))| + 46) * Real.exp (1 * |z.im|)) := hexp
    _ = 1 * ‖Real.exp ((|Real.log (768 * Cz * Bg / (2 * Ag))| + 46) * Real.exp (1 * |z.im|))‖ := by
        rw [Real.norm_of_nonneg (Real.exp_pos _).le]; ring
theorem ZetaConvexityHalfAlt :
    ∃ C : ℝ, 0 < C ∧ ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ 1 → 1 ≤ |t| →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ C * (1 + |t|) ^ ((1 : ℝ) / 4) * (Real.log (2 + |t|) + 2) := by
  obtain ⟨C0, hC0pos, hC0⟩ := zeta_ratio_zero
  obtain ⟨C1, hC1pos, hC1⟩ := zeta_ratio_one
  obtain ⟨C2, hC2pos, hC2⟩ := zeta_ratio_compact
  obtain ⟨Bg, hBg⟩ := ZW_growth
  set Cg : ℝ := max (max C0 C1) C2 + 1 with hCgdef
  have hCgpos : 0 < Cg := by rw [hCgdef]; positivity
  have hb0 : ∀ z : ℂ, z.re = 0 → ‖riemannZeta₁ z / ZW z‖ ≤ Cg := by
    intro z hz
    by_cases h : 1 ≤ |z.im|
    · have hz' : z = ((z.im : ℝ) : ℂ) * I := by apply Complex.ext <;> simp [hz]
      rw [hz']
      refine le_trans (hC0 z.im h) ?_
      rw [hCgdef]
      have ha : C0 ≤ max C0 C1 := le_max_left _ _
      have hb : max C0 C1 ≤ max (max C0 C1) C2 := le_max_left _ _
      linarith
    · push_neg at h
      refine le_trans (hC2 z (by linarith [hz]) (by linarith [hz]) h.le) ?_
      rw [hCgdef]
      have ha : C2 ≤ max (max C0 C1) C2 := le_max_right _ _
      linarith
  have hb1 : ∀ z : ℂ, z.re = 1 → ‖riemannZeta₁ z / ZW z‖ ≤ Cg := by
    intro z hz
    by_cases h : 1 ≤ |z.im|
    · have hz' : z = 1 + ((z.im : ℝ) : ℂ) * I := by apply Complex.ext <;> simp [hz]
      rw [hz']
      refine le_trans (hC1 z.im h) ?_
      rw [hCgdef]
      have ha : C1 ≤ max C0 C1 := le_max_right _ _
      have hb : max C0 C1 ≤ max (max C0 C1) C2 := le_max_left _ _
      linarith
    · push_neg at h
      refine le_trans (hC2 z (by linarith [hz]) (by linarith [hz]) h.le) ?_
      rw [hCgdef]
      have ha : C2 ≤ max (max C0 C1) C2 := le_max_right _ _
      linarith
  have hclos : closure (Complex.re ⁻¹' Set.Ioo (0:ℝ) 1) ⊆ Complex.re ⁻¹' Set.Icc (0:ℝ) 1 := by
    apply closure_minimal _ (isClosed_Icc.preimage continuous_re)
    intro w hw
    simp only [Set.mem_preimage, Set.mem_Icc] at hw ⊢
    exact ⟨le_of_lt hw.1, le_of_lt hw.2⟩
  have hcontOn : ContinuousOn (fun z : ℂ => riemannZeta₁ z / ZW z)
      (Complex.re ⁻¹' Set.Icc (0:ℝ) 1) := by
    intro z hz
    rw [Set.mem_preimage, Set.mem_Icc] at hz
    exact ContinuousAt.continuousWithinAt
      (((differentiable_riemannZeta₁ z).continuousAt).div
        ((ZW_differentiableAt z (by linarith [hz.1]) (by linarith [hz.2])).continuousAt)
        (ZW_ne_zero z hz.1 hz.2))
  have hfd : DiffContOnCl ℂ (fun z : ℂ => riemannZeta₁ z / ZW z) (Complex.re ⁻¹' Set.Ioo 0 1) := by
    refine ⟨fun z hz => ?_, hcontOn.mono hclos⟩
    rw [Set.mem_preimage, Set.mem_Ioo] at hz
    exact ((differentiable_riemannZeta₁ z).differentiableWithinAt).div
      ((ZW_differentiableAt z (by linarith [hz.1]) (by linarith [hz.2])).differentiableWithinAt)
      (ZW_ne_zero z (le_of_lt hz.1) (le_of_lt hz.2))
  refine ⟨800 * Cg, by positivity, ?_⟩
  intro σ t hσ1 hσ2 ht
  set s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hs
  have hsre : s.re = σ := by rw [hs]; simp
  have hsim : s.im = t := by rw [hs]; simp
  have hsne : s ≠ 1 := by
    intro h
    have h2 := congrArg Complex.im h
    rw [hsim] at h2
    simp at h2
    rw [h2] at ht
    norm_num at ht
  have hPL : ‖riemannZeta₁ s / ZW s‖ ≤ Cg :=
    PhragmenLindelof.vertical_strip (a := 0) (b := 1) (C := Cg)
      (f := fun z : ℂ => riemannZeta₁ z / ZW z) (z := s) hfd
      (by
        refine ⟨1, by rw [sub_zero, div_one]; linarith [Real.pi_gt_three], Bg, ?_⟩
        simpa using hBg)
      hb0 hb1 (by rw [hsre]; linarith) (by rw [hsre]; exact hσ2)
  have hZne : ZW s ≠ 0 := ZW_ne_zero s (by rw [hsre]; linarith) (by rw [hsre]; exact hσ2)
  have hW : ‖ZW s‖ ≤ 100 * (2 + |t|) ^ ((3:ℝ)/2 - σ/2) * (Real.log (2 + |t|) + 2) := by
    have h := ZW_norm_upper (s := s) (by rw [hsre]; linarith) (by rw [hsre]; exact hσ2)
      (by rw [hsim]; exact ht)
    rwa [hsre, hsim] at h
  have hs1 : |t| ≤ ‖s - 1‖ := by
    have h := Complex.abs_im_le_norm (s - 1)
    have him : (s - 1).im = t := by rw [hs]; simp
    rwa [him] at h
  have htpos : (0:ℝ) < |t| := by linarith [ht]
  have hζ1 : ‖riemannZeta₁ s‖ ≤ ‖ZW s‖ * Cg := by
    have h1 : ‖riemannZeta₁ s‖ = ‖ZW s‖ * ‖riemannZeta₁ s / ZW s‖ := by
      rw [norm_div]
      have hZpos : 0 < ‖ZW s‖ := norm_pos_iff.mpr hZne
      field_simp
    rw [h1]
    exact mul_le_mul_of_nonneg_left hPL (norm_nonneg _)
  have hmain : ‖riemannZeta s‖ ≤ 800 * Cg * (1 + |t|) ^ ((1:ℝ)/4) * (Real.log (2 + |t|) + 2) := by
    have hζ : ‖riemannZeta s‖ = ‖(s - 1)⁻¹‖ * ‖riemannZeta₁ s‖ := by
      rw [riemannZeta_eq_inv_sub_mul hsne, norm_mul]
    rw [hζ]
    calc ‖(s - 1)⁻¹‖ * ‖riemannZeta₁ s‖
        = ‖riemannZeta₁ s‖ / ‖s - 1‖ := by rw [norm_inv]; ring
      _ ≤ (‖ZW s‖ * Cg) / |t| := by
          refine le_trans (div_le_div_of_nonneg_right hζ1 (norm_nonneg _)) ?_
          exact div_le_div_of_nonneg_left (by positivity) htpos hs1
      _ ≤ (100 * (2 + |t|) ^ ((3:ℝ)/2 - σ/2) * (Real.log (2 + |t|) + 2) * Cg) / |t| := by
          apply div_le_div_of_nonneg_right _ htpos.le
          have h := mul_le_mul_of_nonneg_right hW (le_of_lt hCgpos)
          linarith
      _ ≤ 800 * Cg * (1 + |t|) ^ ((1:ℝ)/4) * (Real.log (2 + |t|) + 2) := by
          have hX : (0:ℝ) < 1 + |t| := by linarith [abs_nonneg t]
          have hL : (0:ℝ) ≤ Real.log (2 + |t|) + 2 := by have := log_two_add_nonneg t; linarith
          have hCgn : (0:ℝ) ≤ 100 * Cg := by positivity
          have hA : (2 + |t|) ^ ((3:ℝ)/2 - σ/2) / |t| ≤ 8 * (1 + |t|) ^ ((1:ℝ)/4) := by
            have h1 : (2 + |t|) ^ ((3:ℝ)/2 - σ/2) ≤ 4 * (1 + |t|) ^ ((3:ℝ)/2 - σ/2) := by
              have hp : (2 + |t|) ≤ 2 * (1 + |t|) := by linarith [abs_nonneg t]
              have hb : (2 + |t|) ^ ((3:ℝ)/2 - σ/2) ≤ (2 * (1 + |t|)) ^ ((3:ℝ)/2 - σ/2) :=
                Real.rpow_le_rpow (by linarith [abs_nonneg t]) hp (by linarith)
              have hm : (2 * (1 + |t|)) ^ ((3:ℝ)/2 - σ/2)
                  = (2:ℝ) ^ ((3:ℝ)/2 - σ/2) * (1 + |t|) ^ ((3:ℝ)/2 - σ/2) :=
                Real.mul_rpow (by norm_num) (by linarith [abs_nonneg t])
              rw [hm] at hb
              have h2p : (2:ℝ) ^ ((3:ℝ)/2 - σ/2) ≤ 4 := by
                have hexp : ((3:ℝ)/2 - σ/2) ≤ 2 := by linarith
                calc (2:ℝ) ^ ((3:ℝ)/2 - σ/2) ≤ (2:ℝ) ^ (2:ℝ) :=
                      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
                  _ = 4 := by norm_num [Real.rpow_two]
              have h3 : (2:ℝ) ^ ((3:ℝ)/2 - σ/2) * (1 + |t|) ^ ((3:ℝ)/2 - σ/2)
                  ≤ 4 * (1 + |t|) ^ ((3:ℝ)/2 - σ/2) :=
                mul_le_mul_of_nonneg_right h2p (by positivity)
              exact le_trans hb h3
            have h2 : (|t|)⁻¹ ≤ 2 / (1 + |t|) := by
              rw [inv_eq_one_div]
              have hden : 0 < (1 + |t|)/2 := by linarith [abs_nonneg t]
              have hle : (1 + |t|)/2 ≤ |t| := by linarith [ht]
              have h1' := one_div_le_one_div_of_le hden hle
              refine le_trans h1' ?_
              rw [one_div_div]
            have h3 : (1 + |t|) ^ ((3:ℝ)/2 - σ/2) / (1 + |t|) = (1 + |t|) ^ ((1:ℝ)/2 - σ/2) :=
              rpow_three_halves t σ
            calc (2 + |t|) ^ ((3:ℝ)/2 - σ/2) / |t|
                = (2 + |t|) ^ ((3:ℝ)/2 - σ/2) * (|t|)⁻¹ := by rw [div_eq_mul_inv]
              _ ≤ (4 * (1 + |t|) ^ ((3:ℝ)/2 - σ/2)) * (2 / (1 + |t|)) := by
                  exact mul_le_mul h1 h2 (inv_nonneg.mpr (by linarith [ht])) (by positivity)
              _ = 8 * ((1 + |t|) ^ ((3:ℝ)/2 - σ/2) / (1 + |t|)) := by ring
              _ = 8 * (1 + |t|) ^ ((1:ℝ)/2 - σ/2) := by rw [h3]
              _ ≤ 8 * (1 + |t|) ^ ((1:ℝ)/4) := by
                  apply mul_le_mul_of_nonneg_left _ (by norm_num)
                  exact Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg t]) (by linarith)
          have hcoef : (100 * (2 + |t|) ^ ((3:ℝ)/2 - σ/2) * (Real.log (2 + |t|) + 2) * Cg) / |t|
              = 100 * Cg * ((2 + |t|) ^ ((3:ℝ)/2 - σ/2) / |t|)
                * (Real.log (2 + |t|) + 2) := by ring
          rw [hcoef]
          calc 100 * Cg * ((2 + |t|) ^ ((3:ℝ)/2 - σ/2) / |t|) * (Real.log (2 + |t|) + 2)
              ≤ 100 * Cg * (8 * (1 + |t|) ^ ((1:ℝ)/4)) * (Real.log (2 + |t|) + 2) := by
                apply mul_le_mul_of_nonneg_right _ hL
                exact mul_le_mul_of_nonneg_left hA hCgn
            _ = 800 * Cg * (1 + |t|) ^ ((1:ℝ)/4) * (Real.log (2 + |t|) + 2) := by ring
  exact hmain

end Work.LinnikAreas.BGTZ

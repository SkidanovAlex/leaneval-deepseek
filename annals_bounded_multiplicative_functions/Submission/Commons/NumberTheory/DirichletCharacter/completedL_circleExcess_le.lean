import Mathlib
import Mathlib.Analysis.Complex.JensenFormula
import Submission.Commons.Analysis.SpecialFunctions.Gamma.gammaR_log_norm_sub_le_im
import Submission.Commons.Analysis.SpecialFunctions.Trigonometric.norm_sin_le_exp_im
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_norm_half_plane
import Submission.Commons.Analysis.SpecialFunctions.Gamma.gamma_vertical_exp_decay_explicit
import Submission.Commons.Analysis.SpecialFunctions.Gamma.log_Gamma_le
import Submission.Commons.NumberTheory.DirichletCharacter.completedLFunction_eq
import Submission.Commons.NumberTheory.DirichletCharacter.rootNumber_norm_eq_one
import Submission.Commons.NumberTheory.Linnik.completedL_growth_circle
import Submission.Commons.NumberTheory.DirichletCharacter.Even_inv
import Submission.Commons.NumberTheory.DirichletCharacter.Odd_inv
import Submission.Commons.NumberTheory.DirichletCharacter.norm_LFunction_le_re_ge_one
import Submission.Commons.NumberTheory.DirichletCharacter.zerosInStrip
import Submission.Commons.NumberTheory.DirichletCharacter.completedL_divisor_le_L
import Submission.Commons.NumberTheory.DirichletCharacter.L_lower_re_two_explicit
import Submission.Commons.Analysis.SpecialFunctions.Log.log_two_ge_two_thirds

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 0

open Complex DirichletCharacter Metric MeromorphicOn Real MeasureTheory
open scoped Real Topology

namespace Commons.NumberTheory.DirichletCharacter


-- ============ Gamma helpers ============

lemma cosh_le_exp_abs (x : ℝ) : Real.cosh x ≤ Real.exp |x| := by
  rw [Real.cosh_eq]
  have h1 : Real.exp x ≤ Real.exp |x| := Real.exp_le_exp.mpr (le_abs_self x)
  have h2 : Real.exp (-x) ≤ Real.exp |x| := Real.exp_le_exp.mpr (neg_le_abs x)
  linarith

lemma exp_le_two_mul_cosh (x : ℝ) : Real.exp x ≤ 2 * Real.cosh x := by
  rw [Real.cosh_eq]
  have := Real.exp_pos (-x)
  linarith

lemma cosh_pi_abs (v : ℝ) : Real.cosh (Real.pi * |v|) = Real.cosh (Real.pi * v) := by
  rcases le_total 0 v with hv | hv
  · rw [abs_of_nonneg hv]
  · rw [abs_of_nonpos hv,
      show Real.pi * -v = -(Real.pi * v) by ring, Real.cosh_neg]

lemma normSq_Gamma_half (v : ℝ) :
    Complex.normSq (Complex.Gamma ((1/2 : ℂ) + Complex.I * (v : ℂ)))
      = Real.pi / Real.cosh (Real.pi * v) := by
  have hconj : (starRingEnd ℂ) ((1/2 : ℂ) + Complex.I * (v : ℂ)) = 1 - ((1/2 : ℂ) + Complex.I * (v:ℂ)) := by
    apply Complex.ext <;> simp <;> ring
  have hrefl := Complex.Gamma_mul_Gamma_one_sub ((1/2 : ℂ) + Complex.I * (v : ℂ))
  have hL : (Complex.normSq (Complex.Gamma ((1/2 : ℂ) + Complex.I * (v : ℂ))) : ℂ)
      = Real.pi / Complex.sin (Real.pi * ((1/2 : ℂ) + Complex.I * (v : ℂ))) := by
    rw [Complex.normSq_eq_conj_mul_self, ← Complex.Gamma_conj, hconj, ← hrefl]
    ring
  have hsin : Complex.sin (Real.pi * ((1/2 : ℂ) + Complex.I * (v : ℂ)))
      = ((Real.cosh (Real.pi * v) : ℝ) : ℂ) := by
    have hthis : Real.pi * ((1/2 : ℂ) + Complex.I * (v : ℂ))
        = Complex.I * ((Real.pi * v : ℝ) : ℂ) + (Real.pi : ℂ) / 2 := by
      push_cast; ring
    rw [hthis, Complex.sin_add_pi_div_two, mul_comm Complex.I _, Complex.cos_mul_I,
      ← Complex.ofReal_cosh]
  rw [hsin] at hL
  have hL' : (Complex.normSq (Complex.Gamma ((1/2 : ℂ) + Complex.I * (v : ℂ))) : ℂ)
      = ((Real.pi / Real.cosh (Real.pi * v) : ℝ) : ℂ) := by
    rw [hL]; push_cast; ring
  exact Complex.ofReal_inj.mp hL'

theorem log_Gamma_half_vertical_le (v : ℝ) :
    Real.log ‖Complex.Gamma ((1/2 : ℂ) + Complex.I * (v : ℂ))‖ ≤
      (1/2) * Real.log (2 * Real.pi) - (Real.pi / 2) * |v| := by
  have hns := normSq_Gamma_half v
  have h2 : 0 < ‖Complex.Gamma ((1/2 : ℂ) + Complex.I * (v : ℂ))‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, hns]; positivity
  have hlogsq : Real.log (Complex.normSq (Complex.Gamma ((1/2 : ℂ) + Complex.I * (v : ℂ))))
      = 2 * Real.log ‖Complex.Gamma ((1/2 : ℂ) + Complex.I * (v : ℂ))‖ := by
    rw [Complex.normSq_eq_norm_sq, Real.log_pow]; norm_num
  rw [hns] at hlogsq
  have hdiv : Real.log (Real.pi / Real.cosh (Real.pi * v))
      = Real.log Real.pi - Real.log (Real.cosh (Real.pi * v)) :=
    Real.log_div (by positivity) (by positivity)
  rw [hdiv] at hlogsq
  have hcosh : Real.exp (Real.pi * |v|) / 2 ≤ Real.cosh (Real.pi * v) := by
    have h2' := exp_le_two_mul_cosh (Real.pi * |v|)
    rw [cosh_pi_abs v] at h2'
    linarith
  have hlogcosh : Real.pi * |v| - Real.log 2 ≤ Real.log (Real.cosh (Real.pi * v)) := by
    have hpos : 0 < Real.exp (Real.pi * |v|) / 2 := by positivity
    have := Real.log_le_log hpos hcosh
    rw [Real.log_div (by positivity) (by norm_num), Real.log_exp] at this
    linarith
  have hmain : 2 * Real.log ‖Complex.Gamma ((1/2 : ℂ) + Complex.I * (v : ℂ))‖
      ≤ Real.log Real.pi - (Real.pi * |v| - Real.log 2) := by
    rw [← hlogsq]; linarith
  have hexp : Real.log Real.pi - (Real.pi * |v| - Real.log 2)
      = Real.log (2 * Real.pi) - Real.pi * |v| := by
    rw [Real.log_mul (by norm_num) (by positivity)]; ring
  rw [hexp] at hmain
  nlinarith [hmain]

theorem log_Gamma_half_vertical_lower (v : ℝ) :
    (1/2) * Real.log Real.pi - (Real.pi / 2) * |v| ≤
      Real.log ‖Complex.Gamma ((1/2 : ℂ) + Complex.I * (v : ℂ))‖ := by
  have hns := normSq_Gamma_half v
  have hlogsq : Real.log (Complex.normSq (Complex.Gamma ((1/2 : ℂ) + Complex.I * (v : ℂ))))
      = 2 * Real.log ‖Complex.Gamma ((1/2 : ℂ) + Complex.I * (v : ℂ))‖ := by
    rw [Complex.normSq_eq_norm_sq, Real.log_pow]; norm_num
  rw [hns] at hlogsq
  have hdiv : Real.log (Real.pi / Real.cosh (Real.pi * v))
      = Real.log Real.pi - Real.log (Real.cosh (Real.pi * v)) :=
    Real.log_div (by positivity) (by positivity)
  rw [hdiv] at hlogsq
  have hcosh : Real.cosh (Real.pi * v) ≤ Real.exp (Real.pi * |v|) := by
    have h := cosh_le_exp_abs (Real.pi * v)
    rw [abs_mul, abs_of_pos Real.pi_pos] at h
    exact h
  have hlogcosh : Real.log (Real.cosh (Real.pi * v)) ≤ Real.pi * |v| := by
    have := Real.log_le_log (Real.cosh_pos _) hcosh
    rwa [Real.log_exp] at this
  have hmain : Real.log Real.pi - Real.pi * |v|
      ≤ 2 * Real.log ‖Complex.Gamma ((1/2 : ℂ) + Complex.I * (v : ℂ))‖ := by
    rw [← hlogsq]; linarith
  nlinarith [hmain]

theorem log_Gamma_reflection_lower (u v : ℝ) (h1 : u ≤ 1/2) (h2 : -(2:ℝ) ≤ u)
    (hG : Complex.Gamma ((u : ℂ) + Complex.I * (v : ℂ)) ≠ 0)
    (hs : Complex.sin (Real.pi * ((u : ℂ) + Complex.I * (v : ℂ))) ≠ 0) :
    Real.log Real.pi - (1/2) * Real.log (2 * Real.pi) - (Real.pi / 2) * |v|
      - (1/2 - u) * (Real.log (2 + |v|) + 2) ≤
      Real.log ‖Complex.Gamma ((u : ℂ) + Complex.I * (v : ℂ))‖ := by
  set z : ℂ := (u : ℂ) + (v : ℂ) * Complex.I with hzdef
  have hzeq : (u : ℂ) + Complex.I * (v : ℂ) = z := by rw [hzdef]; ring
  rw [hzeq] at hs hG
  rw [hzeq]
  have hz_re : z.re = u := by simp [hzdef]
  have hz_im : z.im = v := by simp [hzdef]
  have hone : (1 : ℂ) - z = ((1 - u : ℝ) : ℂ) + ((-v : ℝ) : ℂ) * Complex.I := by
    rw [hzdef]; push_cast; ring
  have hg1z : Complex.Gamma (1 - z) ≠ 0 := by
    refine Complex.Gamma_ne_zero (fun m hm => ?_)
    have h := congrArg Complex.re hm
    have h2' : (1:ℝ) - u = -(m:ℝ) := by
      simpa [Complex.sub_re, Complex.one_re, hz_re, Complex.neg_re] using h
    have : (0:ℝ) < 1 - u := by linarith
    have : (m:ℝ) < 0 := by linarith [h2']
    exact absurd this (not_lt.mpr (Nat.cast_nonneg m))
  have hrefl := Complex.Gamma_mul_Gamma_one_sub z
  have hnorm : ‖Complex.Gamma z‖ * ‖Complex.Gamma (1 - z)‖
      = Real.pi / ‖Complex.sin (Real.pi * z)‖ := by
    rw [← norm_mul, hrefl, norm_div]
    congr 1
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hlog : Real.log ‖Complex.Gamma z‖
      = Real.log Real.pi - Real.log ‖Complex.sin (Real.pi * z)‖ - Real.log ‖Complex.Gamma (1 - z)‖ := by
    have key : Real.log ‖Complex.Gamma z‖ + Real.log ‖Complex.Gamma (1 - z)‖
        = Real.log Real.pi - Real.log ‖Complex.sin (Real.pi * z)‖ := by
      rw [← Real.log_mul (norm_ne_zero_iff.mpr hG) (norm_ne_zero_iff.mpr hg1z),
        hnorm, Real.log_div (by positivity) (norm_ne_zero_iff.mpr hs)]
    linarith
  rw [hlog]
  have hsin_le : Real.log ‖Complex.sin (Real.pi * z)‖ ≤ Real.pi * |v| := by
    have hle : ‖Complex.sin (Real.pi * z)‖ ≤ Real.exp (Real.pi * |v|) := by
      have h := Commons.Analysis.SpecialFunctions.Trigonometric.norm_sin_le_exp_im (Real.pi * u) (Real.pi * v)
      have harg : Real.pi * z = ((Real.pi * u : ℝ) : ℂ) + Complex.I * (((Real.pi * v) : ℝ) : ℂ) := by
        rw [hzdef]; push_cast; ring
      rw [harg]
      simpa [abs_mul, abs_of_pos Real.pi_pos] using h
    calc Real.log ‖Complex.sin (Real.pi * z)‖
        ≤ Real.log (Real.exp (Real.pi * |v|)) :=
          Real.log_le_log (norm_pos_iff.mpr hs) hle
      _ = Real.pi * |v| := Real.log_exp _
  have htrans := Commons.Analysis.SpecialFunctions.Gamma.log_norm_Gamma_sub_abs_le
    (1 - u) (1/2 : ℝ) (-v) (by linarith) (by linarith) (by norm_num) (by norm_num)
  have hform1 : ((1 - u : ℝ) : ℂ) + ((-v : ℝ) : ℂ) * Complex.I = 1 - z := hone.symm
  have hform2 : ((1/2 : ℝ) : ℂ) + ((-v : ℝ) : ℂ) * Complex.I
      = (1/2 : ℂ) + Complex.I * ((-v : ℂ)) := by push_cast; ring
  rw [hform1, hform2] at htrans
  have hconjnorm : ‖Complex.Gamma ((1/2 : ℂ) + Complex.I * ((-v : ℂ)))‖
      = ‖Complex.Gamma ((1/2 : ℂ) + Complex.I * (v : ℂ))‖ := by
    have h : (1/2 : ℂ) + Complex.I * ((-v : ℂ)) = (starRingEnd ℂ) ((1/2 : ℂ) + Complex.I * (v : ℂ)) := by
      apply Complex.ext <;> simp
    rw [h, Complex.Gamma_conj, Complex.norm_conj]
  have htrans' : Real.log ‖Complex.Gamma (1 - z)‖
      - Real.log ‖Complex.Gamma ((1/2 : ℂ) + Complex.I * (v:ℂ))‖
      ≤ (1/2 - u) * (Real.log (2 + |v|) + 2) := by
    rw [hconjnorm] at htrans
    have h := (abs_le.mp htrans).2
    simp only [abs_neg] at h
    rw [show (1 - u - 1/2 : ℝ) = 1/2 - u by ring,
      abs_of_nonneg (by linarith : (0:ℝ) ≤ 1/2 - u)] at h
    linarith
  have hhalf := log_Gamma_half_vertical_le v
  have hgl : Real.log ‖Complex.Gamma (1 - z)‖
      ≤ (1/2) * Real.log (2 * Real.pi) - (Real.pi / 2) * |v| + (1/2 - u) * (Real.log (2 + |v|) + 2) := by
    linarith
  linarith



open Commons.Analysis.SpecialFunctions.Gamma in
lemma log_Gamma_le_transfer (x t : ℝ) (hx1 : (1:ℝ)/2 ≤ x) (hx2 : x ≤ 8) :
    Real.log ‖Complex.Gamma ((x:ℂ) + Complex.I*(t:ℂ))‖ ≤
      (1/2)*Real.log (2*Real.pi) - (Real.pi/2)*|t| + (x - 1/2)*(Real.log (2+|t|)+2) := by
  have h := log_norm_Gamma_sub_abs_le x (1/2) t hx1 hx2 (by norm_num) (by norm_num)
  have harg1 : ((x:ℝ):ℂ) + ((t:ℝ):ℂ) * Complex.I = (x:ℂ) + Complex.I*(t:ℂ) := by ring
  have harg2 : (((1/2:ℝ)):ℂ) + ((t:ℝ):ℂ) * Complex.I = (1/2:ℂ) + Complex.I*(t:ℂ) := by
    push_cast; ring
  rw [harg1, harg2] at h
  have h2 : Real.log ‖Complex.Gamma ((x:ℂ) + Complex.I*(t:ℂ))‖
      - Real.log ‖Complex.Gamma ((1/2:ℂ) + Complex.I*(t:ℂ))‖
      ≤ |x - 1/2| * (Real.log (2+|t|)+2) := (abs_le.mp h).2
  have hx : |x - 1/2| = x - 1/2 := abs_of_nonneg (by linarith)
  rw [hx] at h2
  have hbase := log_Gamma_half_vertical_le t
  linarith

open Commons.Analysis.SpecialFunctions.Gamma in
lemma log_Gamma_ge_transfer (x t : ℝ) (hx1 : (1:ℝ)/2 ≤ x) (hx2 : x ≤ 8) :
    (1/2)*Real.log Real.pi - (Real.pi/2)*|t| - (x - 1/2)*(Real.log (2+|t|)+2) ≤
      Real.log ‖Complex.Gamma ((x:ℂ) + Complex.I*(t:ℂ))‖ := by
  have h := log_norm_Gamma_sub_abs_le x (1/2) t hx1 hx2 (by norm_num) (by norm_num)
  have harg1 : ((x:ℝ):ℂ) + ((t:ℝ):ℂ) * Complex.I = (x:ℂ) + Complex.I*(t:ℂ) := by ring
  have harg2 : (((1/2:ℝ)):ℂ) + ((t:ℝ):ℂ) * Complex.I = (1/2:ℂ) + Complex.I*(t:ℂ) := by
    push_cast; ring
  rw [harg1, harg2] at h
  have h2 : -(|x - 1/2| * (Real.log (2+|t|)+2))
      ≤ Real.log ‖Complex.Gamma ((x:ℂ) + Complex.I*(t:ℂ))‖
      - Real.log ‖Complex.Gamma ((1/2:ℂ) + Complex.I*(t:ℂ))‖ := (abs_le.mp h).1
  have hx : |x - 1/2| = x - 1/2 := abs_of_nonneg (by linarith)
  rw [hx] at h2
  have hbase := log_Gamma_half_vertical_lower t
  linarith

lemma log_norm_GammaR (w : ℂ) (h : Complex.Gamma (w/2) ≠ 0) :
    Real.log ‖Complex.Gammaℝ w‖ = -(w.re/2)*Real.log Real.pi + Real.log ‖Complex.Gamma (w/2)‖ := by
  rw [Complex.Gammaℝ_def, norm_mul]
  have hpi : ‖(Real.pi:ℂ)^(-w/2)‖ = Real.pi^((-w/2).re) :=
    Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos (-w/2)
  rw [hpi]
  have hre : (-w/2).re = -(w.re)/2 := by simp [Complex.neg_re]
  rw [hre]
  rw [Real.log_mul (by positivity) (norm_ne_zero_iff.mpr h), Real.log_rpow Real.pi_pos]
  ring



lemma gamma_ne_zero_imp_sin {u v : ℝ} (h1 : u ≤ 1/2)
    (h : Complex.Gamma ((u:ℂ) + Complex.I*(v:ℂ)) ≠ 0) :
    Complex.sin (Real.pi * ((u:ℂ) + Complex.I*(v:ℂ))) ≠ 0 := by
  intro h0
  rw [Complex.sin_eq_zero_iff] at h0
  obtain ⟨k, hk⟩ := h0
  have hπ : (Real.pi:ℂ) ≠ 0 := by simpa using Real.pi_ne_zero
  have hk' : ((u:ℂ) + Complex.I*(v:ℂ)) = (k:ℂ) := by
    have hthis : (Real.pi:ℂ) * ((u:ℂ) + Complex.I*(v:ℂ)) = (Real.pi:ℂ) * (k:ℂ) := by rw [hk]; ring
    exact mul_left_cancel₀ hπ hthis
  have hv : v = 0 := by
    have h := congrArg Complex.im hk'
    simpa [Complex.add_im, Complex.mul_im] using h
  have hu : u = (k:ℝ) := by
    have h := congrArg Complex.re hk'
    simpa [Complex.add_re, Complex.mul_re] using h
  have hk0 : (k:ℤ) ≤ 0 := by
    have hk1 : (k:ℤ) < 1 := by
      have hrs : (k:ℝ) < 1 := by
        linarith [show (k:ℝ) ≤ 1/2 by rw [← hu]; exact h1]
      exact_mod_cast hrs
    omega
  have hsub : ((u:ℂ) : ℂ) = ((k:ℤ) : ℂ) := by
    rw [hu]; norm_num
  rw [hv, Complex.ofReal_zero, mul_zero, add_zero, hsub] at h
  apply h
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (k:ℤ) = -(m:ℤ) := ⟨(-k).toNat, by omega⟩
  refine Complex.Gamma_eq_zero_iff _ |>.mpr ⟨m, ?_⟩
  show ((k:ℤ) : ℂ) = -((m:ℤ) : ℂ)
  rw [hm]; push_cast; ring



lemma div_two_eq (z : ℂ) : z/2 = ((z.re/2:ℝ):ℂ) + Complex.I * ((z.im/2:ℝ):ℂ) := by
  apply Complex.ext <;>
    simp [Complex.div_re, Complex.div_im, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im] <;> ring

open Commons.Analysis.SpecialFunctions.Gamma in
theorem gammaFactor_ratio_le_of_re_nonpos {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {z : ℂ} (hσ : z.re ≤ 0) (hσ2 : -(3:ℝ) ≤ z.re) (hγ : gammaFactor χ z ≠ 0) :
    Real.log ‖gammaFactor χ (1 - z)‖ - Real.log ‖gammaFactor χ z‖ ≤
      (1/2 - z.re) * (Real.log (2 + |z.im/2|) + 2) + (z.re - 3/2) * Real.log Real.pi
        + Real.log (2 * Real.pi) := by
  rcases χ.even_or_odd with hE | hO
  · simp only [Even.gammaFactor_def hE] at hγ ⊢
    have hGz : Complex.Gamma (z/2) ≠ 0 := by
      intro h0; apply hγ; rw [Complex.Gammaℝ_def, h0, mul_zero]
    have hG1z : Complex.Gamma ((1-z)/2) ≠ 0 := by
      apply Complex.Gamma_ne_zero_of_re_pos
      have h : ((1-z)/2).re = (1 - z.re)/2 := by rw [div_two_eq]; simp
      rw [h]; linarith
    have hGex : Complex.Gamma (((z.re/2:ℝ):ℂ) + Complex.I*((z.im/2:ℝ):ℂ)) ≠ 0 := by
      rwa [← div_two_eq]
    have hs : Complex.sin (Real.pi * (((z.re/2:ℝ):ℂ) + Complex.I*((z.im/2:ℝ):ℂ))) ≠ 0 :=
      gamma_ne_zero_imp_sin (by linarith) hGex
    have hU := log_Gamma_le_transfer ((1-z).re/2) ((1-z).im/2)
      (by simp only [Complex.sub_re, Complex.one_re]; linarith)
      (by simp only [Complex.sub_re, Complex.one_re]; linarith)
    have hL := log_Gamma_reflection_lower (z.re/2) (z.im/2)
      (by linarith) (by linarith) hGex hs
    rw [log_norm_GammaR z hGz, log_norm_GammaR (1-z) hG1z, div_two_eq, div_two_eq]
    have habs : |(1-z).im/2| = |z.im/2| := by
      rw [Complex.sub_im, Complex.one_im, zero_sub, show -z.im/2 = -(z.im/2) by ring, abs_neg]
    have hre1z : (1-z).re/2 = (1-z.re)/2 := by rw [Complex.sub_re, Complex.one_re]
    rw [habs, hre1z] at hU
    rw [hre1z]
    linarith
  · simp only [Odd.gammaFactor_def hO] at hγ ⊢
    rw [show (1:ℂ)-z+1 = 2-z by ring]
    have hGz : Complex.Gamma ((z+1)/2) ≠ 0 := by
      intro h0; apply hγ; rw [Complex.Gammaℝ_def, h0, mul_zero]
    have hG1z : Complex.Gamma ((2-z)/2) ≠ 0 := by
      apply Complex.Gamma_ne_zero_of_re_pos
      have h : ((2-z)/2).re = (2 - z.re)/2 := by rw [div_two_eq]; simp
      rw [h]; linarith
    have hGex : Complex.Gamma ((((z+1).re/2:ℝ):ℂ) + Complex.I*(((z+1).im/2:ℝ):ℂ)) ≠ 0 := by
      rwa [← div_two_eq]
    have hs : Complex.sin (Real.pi * ((((z+1).re/2:ℝ):ℂ) + Complex.I*(((z+1).im/2:ℝ):ℂ))) ≠ 0 :=
      gamma_ne_zero_imp_sin (by simp only [Complex.add_re, Complex.one_re]; linarith) hGex
    have hU := log_Gamma_le_transfer ((2-z).re/2) ((2-z).im/2)
      (by simp [Complex.sub_re]; linarith)
      (by simp [Complex.sub_re]; linarith)
    have hL := log_Gamma_reflection_lower ((z+1).re/2) ((z+1).im/2)
      (by simp only [Complex.add_re, Complex.one_re]; linarith)
      (by simp only [Complex.add_re, Complex.one_re]; linarith) hGex hs
    rw [log_norm_GammaR (z+1) hGz, log_norm_GammaR (2-z) hG1z, div_two_eq, div_two_eq]
    have h2im : (2:ℂ).im = 0 := by norm_num
    have habs : |(2-z).im/2| = |(z+1).im/2| := by
      rw [Complex.sub_im, h2im, zero_sub, Complex.add_im, Complex.one_im, add_zero,
        show -z.im/2 = -(z.im/2) by ring, abs_neg]
    have hre : (2-z).re/2 = (2-z.re)/2 := by rw [Complex.sub_re]; norm_num
    have him : (z+1).im = z.im := by simp [Complex.add_im]
    have hre2 : (z+1).re = z.re + 1 := by simp [Complex.add_re]
    rw [habs, hre, him] at hU
    rw [him, hre2] at hL
    rw [hre, him, hre2]
    linarith



lemma gammaFactor_inv_eq' {N : ℕ} (χ : DirichletCharacter ℂ N) (s : ℂ) :
    gammaFactor χ⁻¹ s = gammaFactor χ s := by
  rcases χ.even_or_odd with hE | hO
  · rw [Even.gammaFactor_def hE, Even.gammaFactor_def (Even_inv hE)]
  · rw [Odd.gammaFactor_def hO, Odd.gammaFactor_def (Odd_inv hO)]

lemma ne_one_of_char_ne_one {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) : N ≠ 1 := by
  intro h
  subst h
  exact hχ (Subsingleton.elim _ _)

/-- Norm version of the functional equation for the ordinary L-function, in the half plane
`Re z < 1`. -/
theorem LFunction_norm_FE {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) {z : ℂ} (hz : z.re < 1) (hγ : gammaFactor χ z ≠ 0) :
    ‖LFunction χ z‖ = (N : ℝ)^(1/2 - z.re) * ‖LFunction χ⁻¹ (1-z)‖
      * (‖gammaFactor χ (1-z)‖ / ‖gammaFactor χ z‖) := by
  have hN : N ≠ 1 := ne_one_of_char_ne_one hχ
  have hroot : ‖χ.rootNumber‖ = 1 := rootNumber_norm_eq_one χ hχprim
  have hre1z : 0 < (1 - z).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have hFE := Commons.NumberTheory.DirichletCharacter.completedLFunction_eq χ hχprim z
  -- L(z) = Lambda(z)/gamma(z) and Lambda(z) = N^{1/2-z} rootNumber Lambda(chi^-1)(1-z)
  have hLz := LFunction_eq_completed_div_gammaFactor χ z (.inr hN)
  have hLz' : LFunction χ z = completedLFunction χ z / gammaFactor χ z := hLz
  have h1 : LFunction χ⁻¹ (1-z) * gammaFactor χ⁻¹ (1-z) = completedLFunction χ⁻¹ (1-z) :=
    (Commons.NumberTheory.Linnik.completedLFunction_eq_mul_gammaFactor_re_pos χ⁻¹ hre1z).symm
  have hγinv : gammaFactor χ⁻¹ (1-z) = gammaFactor χ (1-z) := gammaFactor_inv_eq' χ (1-z)
  have hcomp : completedLFunction χ z = (N:ℂ)^(1/2 - z) * χ.rootNumber * completedLFunction χ⁻¹ (1-z) := hFE
  have hmain : LFunction χ z = (N:ℂ)^(1/2 - z) * χ.rootNumber * LFunction χ⁻¹ (1-z)
      * (gammaFactor χ (1-z) / gammaFactor χ z) := by
    rw [hLz']
    rw [show completedLFunction χ z = (N:ℂ)^(1/2 - z) * χ.rootNumber *
      completedLFunction χ⁻¹ (1-z) from hcomp]
    rw [← h1, hγinv]
    field_simp
  rw [hmain, norm_mul, norm_mul, norm_mul, norm_div]
  rw [hroot, mul_one]
  have hNpos : 0 < (N:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hpow : ‖(N:ℂ)^(1/2 - z)‖ = (N:ℝ)^(1/2 - z.re) := by
    rw [show (N:ℂ) = ((N:ℝ):ℂ) by push_cast; rfl]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hNpos]
    simp
  rw [hpow]





lemma inv_ne_one_of_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    χ⁻¹ ≠ 1 := by
  intro h
  apply hχ
  have hh := congrArg (fun ψ : DirichletCharacter ℂ N => ψ⁻¹) h
  simpa using hh

/-- Upper bound for `log ‖L z‖` when `Re z ≤ 0`. -/
theorem LFunction_log_le_of_re_nonpos {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) {z : ℂ}
    (hσ : z.re ≤ 0) (hσ2 : -(3:ℝ) ≤ z.re) (hγ : gammaFactor χ z ≠ 0) :
    Real.log ‖LFunction χ z‖ ≤ (1/2 - z.re)*Real.log (N:ℝ)
      + Real.log (Real.log (N:ℝ) + Real.log (2 + |z.im|) + 6)
      + ((1/2 - z.re)*(Real.log (2 + |z.im/2|) + 2) + (z.re - 3/2)*Real.log Real.pi
          + Real.log (2*Real.pi)) := by
  have hN : N ≠ 1 := ne_one_of_char_ne_one hχ
  have hlt1 : z.re < 1 := by linarith
  have hFE := LFunction_norm_FE χ hχ hχprim hlt1 hγ
  have hNpos : 0 < (N:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne N))
  have hγpos : 0 < ‖gammaFactor χ z‖ := norm_pos_iff.mpr hγ
  have hre1z : (1-z).re > 0 := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have hγ1ne : gammaFactor χ (1-z) ≠ 0 := by
    rcases χ.even_or_odd with hE | hO
    · rw [Even.gammaFactor_def hE]; exact Complex.Gammaℝ_ne_zero_of_re_pos hre1z
    · rw [Odd.gammaFactor_def hO]
      exact Complex.Gammaℝ_ne_zero_of_re_pos (by simp only [Complex.add_re, Complex.one_re]; linarith)
  have hγ1pos : 0 < ‖gammaFactor χ (1-z)‖ := norm_pos_iff.mpr hγ1ne
  have hLne : LFunction χ⁻¹ (1-z) ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re (χ⁻¹) (Or.inl (inv_ne_one_of_one χ hχ)) (by
      simp only [Complex.sub_re, Complex.one_re]; linarith)
  have h1 : (0:ℝ) < (N:ℝ)^(1/2-z.re) := Real.rpow_pos_of_pos hNpos _
  have h2 : (0:ℝ) < ‖LFunction χ⁻¹ (1-z)‖ := norm_pos_iff.mpr hLne
  have hlogFE : Real.log ‖LFunction χ z‖
      = (1/2 - z.re)*Real.log (N:ℝ) + Real.log ‖LFunction χ⁻¹ (1-z)‖
        + (Real.log ‖gammaFactor χ (1-z)‖ - Real.log ‖gammaFactor χ z‖) := by
    rw [hFE]
    rw [Real.log_mul (mul_ne_zero h1.ne' h2.ne') ((div_pos hγ1pos hγpos).ne'),
        Real.log_mul h1.ne' h2.ne',
        Real.log_div hγ1pos.ne' hγpos.ne',
        Real.log_rpow hNpos]
  have hnorm1z : Real.log ‖LFunction χ⁻¹ (1-z)‖ ≤ Real.log (Real.log (N:ℝ) + Real.log (2+|z.im|) + 6) := by
    have hb := norm_LFunction_le_re_ge_one χ⁻¹ (inv_ne_one_of_one χ hχ) (1-z) (by
      simp only [Complex.sub_re, Complex.one_re]; linarith)
    have him : (1-z).im = -z.im := by simp
    rw [him, abs_neg] at hb
    exact Real.log_le_log (norm_pos_iff.mpr hLne) hb
  have hratio := gammaFactor_ratio_le_of_re_nonpos χ hσ hσ2 hγ
  have hB : Real.log ‖LFunction χ⁻¹ (1 - z)‖
        + (Real.log ‖gammaFactor χ (1 - z)‖ - Real.log ‖gammaFactor χ z‖)
      ≤ Real.log (Real.log (N:ℝ) + Real.log (2 + |z.im|) + 6)
        + ((1 / 2 - z.re) * (Real.log (2 + |z.im / 2|) + 2) + (z.re - 3 / 2) * Real.log Real.pi
            + Real.log (2 * Real.pi)) := add_le_add hnorm1z hratio
  have hfin := add_le_add (le_refl ((1/2 - z.re)*Real.log (N:ℝ))) hB
  rw [hlogFE]
  simpa only [add_assoc] using hfin



theorem LFunction_log_le_strip {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) {z : ℂ} (h1 : 0 < z.re) (h2 : z.re ≤ 1) :
    Real.log ‖LFunction χ z‖ ≤ Real.log 2 + Real.log (N:ℝ) + Real.log (1 + |z.im|) - Real.log z.re := by
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne N))
  have hb := LFunction_norm_half_plane χ hχ (s := z) h1
  have hnorm : ‖z‖ ≤ z.re + |z.im| := by
    have := Complex.norm_le_abs_re_add_abs_im z
    rwa [abs_of_pos h1] at this
  have hpos : 0 < 1 + |z.im| := by positivity
  have hLp : 0 < 2*(N:ℝ)*(1+|z.im|) / z.re := by positivity
  have hle : ‖LFunction χ z‖ ≤ 2*(N:ℝ)*(1+|z.im|) / z.re := by
    calc ‖LFunction χ z‖ ≤ 2*(N:ℝ)*‖z‖/z.re := hb
      _ ≤ 2*(N:ℝ)*(z.re+|z.im|)/z.re := by
          apply div_le_div_of_nonneg_right _ h1.le
          exact mul_le_mul_of_nonneg_left hnorm (by positivity)
      _ ≤ 2*(N:ℝ)*(1+|z.im|)/z.re := by
          apply div_le_div_of_nonneg_right _ h1.le
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith
  rcases eq_or_lt_of_le (norm_nonneg (LFunction χ z)) with h0 | h0
  · rw [← h0, Real.log_zero]
    have hloge : Real.log (2*(N:ℝ)*(1+|z.im|)/z.re)
        = Real.log 2 + Real.log (N:ℝ) + Real.log (1 + |z.im|) - Real.log z.re := by
      have hNnz : (N:ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
      have hqnz : (1 + |z.im|) ≠ 0 := by positivity
      rw [Real.log_div (mul_ne_zero (mul_ne_zero (by norm_num) hNnz) hqnz) h1.ne',
        Real.log_mul (mul_ne_zero (by norm_num) hNnz) hqnz, Real.log_mul (by norm_num) hNnz]
    have h6 : 0 ≤ Real.log (2*(N:ℝ)*(1+|z.im|)/z.re) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ h1]
      nlinarith [hN1, h2, abs_nonneg z.im]
    rw [hloge] at h6
    linarith
  · have hlog := Real.log_le_log h0 hle
    have hNnz : (N:ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
    have hqnz : (1 + |z.im|) ≠ 0 := by positivity
    rw [Real.log_div (mul_ne_zero (mul_ne_zero (by norm_num) hNnz) hqnz) h1.ne',
      Real.log_mul (mul_ne_zero (by norm_num) hNnz) hqnz, Real.log_mul (by norm_num) hNnz] at hlog
    linarith [hlog]



theorem LFunction_log_le_right {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) {z : ℂ} (h1 : 1 ≤ z.re) :
    Real.log ‖LFunction χ z‖ ≤ Real.log (Real.log (N:ℝ) + Real.log (2+|z.im|) + 6) := by
  have hb := norm_LFunction_le_re_ge_one χ hχ z h1
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne N))
  have hposl : 1 ≤ Real.log (N:ℝ) + Real.log (2+|z.im|) + 6 := by
    have h1' : 0 ≤ Real.log (N:ℝ) := Real.log_nonneg hN1
    have h2' : 0 ≤ Real.log (2+|z.im|) := Real.log_nonneg (by linarith [abs_nonneg z.im])
    linarith
  rcases eq_or_lt_of_le (norm_nonneg (LFunction χ z)) with h0 | h0
  · rw [← h0, Real.log_zero]
    exact Real.log_nonneg hposl
  · exact Real.log_le_log h0 hb



open Commons.Analysis.SpecialFunctions.Gamma in
theorem gammaFactor_ratio_le_S1 {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {z : ℂ} (h1 : 0 ≤ z.re) (h2 : z.re ≤ 1/2) (hγ : gammaFactor χ z ≠ 0) :
    Real.log ‖gammaFactor χ (1-z)‖ - Real.log ‖gammaFactor χ z‖ ≤ Real.log (2 + |z.im|) + 10 := by
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
  have hlogpi : Real.log Real.pi ≤ 2 := by
    have h : Real.log Real.pi ≤ Real.log 4 := Real.log_le_log Real.pi_pos (by linarith [Real.pi_lt_four])
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2*2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]; ring
    linarith
  have hlog2nn : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlogpi2 : Real.log (Real.pi/2) ≤ 1 := by
    rw [Real.log_le_iff_le_exp (by positivity : (0:ℝ) < Real.pi/2)]
    have := Real.exp_one_gt_two
    linarith [Real.pi_lt_four]
  have hlog2pi : Real.log (2*Real.pi) ≤ 3 := by
    rw [Real.log_mul (by norm_num) (by positivity)]; linarith
  have hlogN : 0 ≤ Real.log (2 + |z.im|) :=
    Real.log_nonneg (by linarith [abs_nonneg z.im])
  rcases χ.even_or_odd with hE | hO
  · simp only [Even.gammaFactor_def hE] at hγ ⊢
    have hGz : Complex.Gamma (z/2) ≠ 0 := by
      intro h0; apply hγ; rw [Complex.Gammaℝ_def, h0, mul_zero]
    have hG1z : Complex.Gamma ((1-z)/2) ≠ 0 := by
      apply Complex.Gamma_ne_zero_of_re_pos
      have h : ((1-z)/2).re = (1 - z.re)/2 := by rw [div_two_eq]; simp
      rw [h]; linarith
    have hGex : Complex.Gamma (((z.re/2:ℝ):ℂ) + Complex.I*((z.im/2:ℝ):ℂ)) ≠ 0 := by
      rwa [← div_two_eq]
    have hsd : Complex.sin (Real.pi * (((z.re/2:ℝ):ℂ) + Complex.I*((z.im/2:ℝ):ℂ))) ≠ 0 :=
      gamma_ne_zero_imp_sin (by linarith) hGex
    have h1zre : ((1-z).re) = 1 - z.re := by simp
    have hu'pos : 0 < ((1-z).re)/2 := by rw [h1zre]; linarith
    have hu'le : ((1-z).re)/2 ≤ 1/2 := by rw [h1zre]; linarith
    have hG1z' : Complex.Gamma ((((1-z).re)/2 : ℝ) + Complex.I*((((1-z).im)/2):ℝ)) ≠ 0 := by
      apply Complex.Gamma_ne_zero_of_re_pos
      simp only [Complex.add_re, Complex.ofReal_re, Complex.I_mul_re, Complex.ofReal_im]
      linarith
    have hU := gamma_vertical_exp_decay_explicit (((1-z).re)/2) hu'pos (((1-z).im)/2)
    have hUlog : Real.log ‖Complex.Gamma ((((1-z).re)/2 : ℝ) + Complex.I*((((1-z).im)/2):ℝ))‖
        ≤ Real.log (Real.Gamma (((1-z).re)/2)) + 1
          + (((1-z).re)/2)*Real.log (Real.pi/2)
          + (((1-z).re)/2)*Real.log (1 + |((1-z).im)/2|)
          - (Real.pi/2)*|((1-z).im)/2| := by
      have hpos : 0 < Real.Gamma (((1-z).re)/2) := Real.Gamma_pos_of_pos hu'pos
      have h1e : 0 < Real.exp 1 := Real.exp_pos 1
      have hπ2 : 0 < (Real.pi/2)^(((1-z).re)/2) := Real.rpow_pos_of_pos (by positivity) _
      have hpp : 0 < (1 + |((1-z).im)/2|)^(((1-z).re)/2) :=
        Real.rpow_pos_of_pos (by positivity) _
      have hlog := Real.log_le_log (norm_pos_iff.mpr hG1z') hU
      rw [Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity),
        Real.log_exp, Real.log_rpow (by positivity), Real.log_rpow (by positivity),
        Real.log_exp] at hlog
      linarith
    have hL := log_Gamma_reflection_lower (z.re/2) (z.im/2) (by linarith) (by linarith) hGex hsd
    have hlogG : Real.log (Real.Gamma (((1-z).re)/2)) ≤ 15/4 := by
      have hmem : (1:ℝ)/4 ≤ ((1-z).re)/2 := by rw [h1zre]; linarith
      have hle := log_Gamma_le hmem
      have hpos : (0:ℝ) < ((1-z).re)/2 + 2 := by rw [h1zre]; linarith
      have hlogle : Real.log (((1-z).re)/2 + 2) ≤ ((1-z).re)/2 + 1 := by
        have := Real.log_le_sub_one_of_pos hpos; linarith
      have hb : (((1-z).re)/2 + 2) ≤ 5/2 := by rw [h1zre]; linarith
      have hA : (((1-z).re)/2 + 2) * Real.log (((1-z).re)/2 + 2)
          ≤ (((1-z).re)/2 + 2) * (((1-z).re)/2 + 1) :=
        mul_le_mul_of_nonneg_left hlogle (by linarith)
      have hB : (((1-z).re)/2 + 2) * (((1-z).re)/2 + 1)
          ≤ (5/2) * (((1-z).re)/2 + 1) := mul_le_mul_of_nonneg_right hb (by linarith)
      have hfin : (5/2) * (((1-z).re)/2 + 1) ≤ 15/4 := by rw [h1zre]; linarith
      linarith [hle, hA, hB, hfin]
    rw [log_norm_GammaR z hGz, log_norm_GammaR (1-z) hG1z, div_two_eq, div_two_eq]
    have habs1 : |((1-z).im)/2| = |z.im/2| := by
      rw [Complex.sub_im, Complex.one_im, zero_sub, show -z.im/2 = -(z.im/2) by ring, abs_neg]
    have habs2 : |z.im/2| = |z.im|/2 := by rw [abs_div]; norm_num
    rw [habs1, habs2, h1zre] at hUlog
    have habs3 : |z.im/2| = |z.im|/2 := habs2
    rw [habs3] at hL
    rw [h1zre]
    -- numeric side conditions
    have hlog1 : Real.log (1 + |z.im|/2) ≤ Real.log (2 + |z.im|) := by
      apply Real.log_le_log (by positivity); linarith [abs_nonneg z.im]
    have hlog2m : Real.log (2 + |z.im|/2) ≤ Real.log (2 + |z.im|) := by
      apply Real.log_le_log (by positivity); linarith [abs_nonneg z.im]
    have hlogF : Real.log (2 + |z.im|/2) ≤ Real.log (2 + |z.im|) := hlog2m
    rw [h1zre] at hlogG
    have hA : ((1-z.re)/2)*Real.log (1+|z.im|/2) ≤ ((1-z.re)/2)*Real.log (2+|z.im|) :=
      mul_le_mul_of_nonneg_left hlog1 (by linarith)
    have hB : (1/2-z.re/2)*(Real.log (2+|z.im|/2)+2) ≤ (1/2-z.re/2)*(Real.log (2+|z.im|)+2) :=
      mul_le_mul_of_nonneg_left (add_le_add hlog2m le_rfl) (by linarith)
    have hC : ((1-z.re)/2)*Real.log (2+|z.im|) + (1/2-z.re/2)*(Real.log (2+|z.im|)+2)
        ≤ Real.log (2+|z.im|) + 1 := by
      nlinarith [hlogN, h1, h2]
    have hu'log : ((1-z.re)/2) * Real.log (Real.pi/2) ≤ 1/2 := by
      have h0 : 0 ≤ (1-z.re)/2 := by linarith
      have h1' : (1-z.re)/2 ≤ 1/2 := by linarith
      nlinarith [hlogpi2, h0, h1']
    have hlogpi0 : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
    have hsig : (z.re - 3/2)*Real.log Real.pi ≤ 0 := by nlinarith [h2, hlogpi0]
    linarith [hUlog, hL, hlogG, hlogpi2, hlogpi, hlog2, hlog2pi, hA, hB, hC, hlogN, hu'log,
      hlogpi0, hsig, h1, h2]
  · simp only [Odd.gammaFactor_def hO] at hγ ⊢
    rw [show (1:ℂ)-z+1 = 2-z by ring]
    have hGz : Complex.Gamma ((z+1)/2) ≠ 0 := by
      intro h0; apply hγ; rw [Complex.Gammaℝ_def, h0, mul_zero]
    have hG1z : Complex.Gamma ((2-z)/2) ≠ 0 := by
      apply Complex.Gamma_ne_zero_of_re_pos
      have h : ((2-z)/2).re = (2 - z.re)/2 := by rw [div_two_eq]; simp
      rw [h]; linarith
    have hU := log_Gamma_le_transfer ((2-z).re/2) ((2-z).im/2)
      (by simp [Complex.sub_re]; linarith) (by simp [Complex.sub_re]; linarith)
    have hL := log_Gamma_ge_transfer ((z+1).re/2) ((z+1).im/2)
      (by simp [Complex.add_re]; linarith) (by simp [Complex.add_re]; linarith)
    have h2im : (2:ℂ).im = 0 := by norm_num
    have habs : |(2-z).im/2| = |(z+1).im/2| := by
      rw [Complex.sub_im, h2im, zero_sub, Complex.add_im, Complex.one_im, add_zero,
        show -z.im/2 = -(z.im/2) by ring, abs_neg]
    have hre : (2-z).re/2 = (2-z.re)/2 := by rw [Complex.sub_re]; norm_num
    have him : (z+1).im = z.im := by simp [Complex.add_im]
    have hre2 : (z+1).re = z.re + 1 := by simp [Complex.add_re]
    rw [log_norm_GammaR (z+1) hGz, log_norm_GammaR (2-z) hG1z, div_two_eq, div_two_eq]
    rw [habs, hre, him] at hU
    rw [him, hre2] at hL
    rw [hre, him, hre2]
    have hlogpi0 : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
    have hlog2m : Real.log (2 + |z.im|/2) ≤ Real.log (2 + |z.im|) := by
      apply Real.log_le_log (by positivity); linarith [abs_nonneg z.im]
    have hP : ((2-z.re)/2 - 1/2) * (Real.log (2+|z.im|/2)+2) + ((z.re+1)/2 - 1/2) * (Real.log (2+|z.im|/2)+2)
        ≤ Real.log (2+|z.im|) + 2 := by
      have hrew : ((2-z.re)/2 - 1/2) * (Real.log (2+|z.im|/2)+2) + ((z.re+1)/2 - 1/2) * (Real.log (2+|z.im|/2)+2)
          = (1/2) * (Real.log (2+|z.im|/2)+2) := by
        rw [← add_mul]; congr 1; ring
      rw [hrew]
      nlinarith [hlog2m, hlogN]
    have hsig : (z.re - 1)*Real.log Real.pi ≤ 0 := by nlinarith [h2, hlogpi0]
    have habs4 : |z.im/2| = |z.im|/2 := by rw [abs_div]; norm_num
    rw [habs4] at hU hL
    linarith [hU, hL, hlogpi, hlog2, hlog2pi, hP, hlogN, hlogpi0, hsig, h1, h2]



theorem circleExcess_le_L_excess {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) (T₀ : ℝ) :
    Real.circleAverage (fun z : ℂ => Real.log ‖completedLFunction χ z‖) ((2 : ℂ) + I*(T₀:ℂ)) 5
      - Real.log ‖completedLFunction χ ((2:ℂ)+I*(T₀:ℂ))‖
    ≤ Real.circleAverage (fun z : ℂ => Real.log ‖LFunction χ z‖) ((2:ℂ)+I*(T₀:ℂ)) 5
      - Real.log ‖LFunction χ ((2:ℂ)+I*(T₀:ℂ))‖ := by
  set a : ℂ := (2:ℂ) + I*(T₀:ℂ) with ha
  have hΛdiff : Differentiable ℂ (completedLFunction χ) := differentiable_completedLFunction hχ
  have habs : |(5:ℝ)| = 5 := by norm_num
  have hΛan : AnalyticOnNhd ℂ (completedLFunction χ) (closedBall a |(5:ℝ)|) := fun z _ => hΛdiff.analyticAt z
  have hΛan5 : AnalyticOnNhd ℂ (completedLFunction χ) (closedBall a 5) := by rw [← habs]; exact hΛan
  have hΛa : completedLFunction χ a ≠ 0 := by
    intro h0
    have hz := zerosInStrip χ hχ hχprim a h0
    have h2 : a.re = 2 := by simp [a]
    linarith [hz.2, h2]
  have hLdiff : Differentiable ℂ (LFunction χ) := DirichletCharacter.differentiable_LFunction hχ
  have hLan : AnalyticOnNhd ℂ (LFunction χ) (closedBall a |(5:ℝ)|) := fun z _ => hLdiff.analyticAt z
  have hLan5 : AnalyticOnNhd ℂ (LFunction χ) (closedBall a 5) := by rw [← habs]; exact hLan
  have hLa : LFunction χ a ≠ 0 := by
    intro h0
    have h := L_lower_re_two_explicit χ hχ T₀
    have h0' : LFunction χ ((2:ℂ) + I*(T₀:ℂ)) = 0 := by rw [← ha]; exact h0
    rw [h0', norm_zero] at h
    norm_num at h
  have jΛ := AnalyticOnNhd.circleAverage_log_norm (f := completedLFunction χ) (c := a) (R := (5:ℝ))
    (by norm_num) hΛan hΛa
  have jL := AnalyticOnNhd.circleAverage_log_norm (f := LFunction χ) (c := a) (R := (5:ℝ))
    (by norm_num) hLan hLa
  rw [jΛ, jL, habs]
  -- divisor comparison
  have hdivle : ∀ u : ℂ, (MeromorphicOn.divisor (completedLFunction χ) (closedBall a 5)) u
      ≤ (MeromorphicOn.divisor (LFunction χ) (closedBall a 5)) u := by
    intro u
    by_cases huU : u ∈ closedBall a 5
    · by_cases hre : 0 < u.re
      · exact completedL_divisor_le_L χ hχ (closedBall a 5) huU hre
      · have hD0 : (MeromorphicOn.divisor (completedLFunction χ) (closedBall a 5)) u = 0 := by
          rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hΛan5 huU]
          have hne : completedLFunction χ u ≠ 0 := by
            intro h0
            have hz := zerosInStrip χ hχ hχprim u h0
            linarith [hz.1, not_lt.mp hre]
          have : analyticOrderAt (completedLFunction χ) u = 0 :=
            analyticOrderAt_eq_zero.mpr (Or.inr hne)
          rw [this]; simp
        rw [hD0]
        exact hLan5.divisor_nonneg u
    · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ huU,
          Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ huU]
  have key : (∑ᶠ u : ℂ, ((MeromorphicOn.divisor (completedLFunction χ) (closedBall a 5)) u : ℝ)
        * Real.log (5 * ‖a - u‖⁻¹))
      ≤ (∑ᶠ u : ℂ, ((MeromorphicOn.divisor (LFunction χ) (closedBall a 5)) u : ℝ)
        * Real.log (5 * ‖a - u‖⁻¹)) := by
    apply finsum_le_finsum'
    · exact ((MeromorphicOn.divisor (completedLFunction χ) (closedBall a 5)).finiteSupport
        (isCompact_closedBall a 5)).subset (fun u hu => by
          simp only [Function.mem_support] at hu ⊢
          exact fun hd => hu (by simp [hd]))
    · exact ((MeromorphicOn.divisor (LFunction χ) (closedBall a 5)).finiteSupport
        (isCompact_closedBall a 5)).subset (fun u hu => by
          simp only [Function.mem_support] at hu ⊢
          exact fun hd => hu (by simp [hd]))
    · intro u
      by_cases hu : u ∈ closedBall a 5
      · have hnorm : ‖a - u‖ ≤ 5 := by
          simpa [mem_closedBall, dist_eq_norm, norm_sub_rev] using hu
        have hlog : 0 ≤ Real.log (5 * ‖a - u‖⁻¹) := by
          rcases eq_or_ne ‖a - u‖ 0 with h0 | h0
          · simp [h0]
          · have hpos : 0 < ‖a - u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
            apply Real.log_nonneg
            rw [show (5:ℝ) * ‖a - u‖⁻¹ = 5 / ‖a - u‖ by rw [div_eq_mul_inv]]
            rw [le_div_iff₀ hpos]; linarith
        have hle := hdivle u
        have hleR : ((MeromorphicOn.divisor (completedLFunction χ) (closedBall a 5)) u : ℝ)
            ≤ ((MeromorphicOn.divisor (LFunction χ) (closedBall a 5)) u : ℝ) := by
          exact_mod_cast hle
        exact mul_le_mul_of_nonneg_right hleR hlog
      · change ((MeromorphicOn.divisor (completedLFunction χ) (closedBall a 5)) u : ℝ)
              * Real.log (5 * ‖a - u‖⁻¹)
            ≤ ((MeromorphicOn.divisor (LFunction χ) (closedBall a 5)) u : ℝ)
              * Real.log (5 * ‖a - u‖⁻¹)
        rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem
              (MeromorphicOn.divisor (completedLFunction χ) (closedBall a 5)) hu,
            Function.locallyFinsuppWithin.apply_eq_zero_of_notMem
              (MeromorphicOn.divisor (LFunction χ) (closedBall a 5)) hu]
  linarith [key]



/-!
## Estimates for `arccos`
-/

/-- `arccos` is decreasing; on an interval `[a,b]` with `a ≤ b ≤ 0` the drop is at most
`(b-a)/sqrt(1-a^2)`. -/
lemma arccos_sub_arccos_le {a b : ℝ} (ha : -1 < a) (hab : a ≤ b) (hb : b ≤ 0) :
    Real.arccos a - Real.arccos b ≤ (b - a) / Real.sqrt (1 - a ^ 2) := by
  rcases eq_or_lt_of_le hab with h | h
  · subst h; simp
  · obtain ⟨c, hc, hderiv⟩ := exists_deriv_eq_slope Real.arccos h
      Real.continuous_arccos.continuousOn
      (fun x hx => (Real.hasDerivAt_arccos (by linarith [hx.1])
        (by linarith [hx.2])).differentiableAt.differentiableWithinAt)
    have hc0 : c ≤ 0 := le_trans hc.2.le hb
    have hca : a ≤ c := hc.1.le
    have hc_gt : -1 < c := lt_trans ha hc.1
    have hpos1 : 0 < 1 - c ^ 2 := by
      have : (0:ℝ) < (c + 1) * (1 - c) := mul_pos (by linarith) (by linarith)
      nlinarith [this]
    have hpos2 : 0 < 1 - a ^ 2 := by
      have : (0:ℝ) < (a + 1) * (1 - a) := mul_pos (by linarith) (by linarith)
      nlinarith [this]
    have hsq : c ^ 2 ≤ a ^ 2 := by nlinarith [hc0, hca, hb]
    rw [Real.deriv_arccos] at hderiv
    have hkey : Real.arccos a - Real.arccos b = (b - a) / Real.sqrt (1 - c ^ 2) := by
      have hs : Real.sqrt (1 - c ^ 2) ≠ 0 := (Real.sqrt_pos_of_pos hpos1).ne'
      have hba : b - a ≠ 0 := by linarith
      field_simp at hderiv ⊢
      linarith
    rw [hkey]
    apply div_le_div_of_nonneg_left (by linarith) (Real.sqrt_pos_of_pos hpos2)
    exact Real.sqrt_le_sqrt (by linarith)

/-- `1 / sqrt 91 ≤ 21 / 200`. -/
lemma inv_sqrt91_le : (1:ℝ) / Real.sqrt 91 ≤ 21 / 200 := by
  have hs : (200/21 : ℝ) ≤ Real.sqrt 91 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  rw [div_le_iff₀ (Real.sqrt_pos_of_pos (by norm_num : (0:ℝ) < 91))]
  nlinarith [hs]

/-- `1 / (2 * sqrt 21) ≤ 11 / 100`. -/
lemma inv_two_sqrt21_le : (1:ℝ) / (2 * Real.sqrt 21) ≤ 11 / 100 := by
  have hs : (50/11 : ℝ) ≤ Real.sqrt 21 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 * Real.sqrt 21)]
  nlinarith [hs]

lemma arccos_neg_three_tenths_sub_arccos_neg_one_fifth_le :
    Real.arccos (-(3:ℝ)/10) - Real.arccos (-(1:ℝ)/5) ≤ 21/200 := by
  have h := arccos_sub_arccos_le (a := -(3:ℝ)/10) (b := -(1:ℝ)/5)
    (by norm_num) (by norm_num) (by norm_num)
  have h2 : Real.sqrt (1 - (-(3:ℝ)/10)^2) = Real.sqrt 91 / 10 := by
    have h100 : (100:ℝ) = 10^2 := by norm_num
    rw [show (1:ℝ) - (-(3:ℝ)/10)^2 = 91/100 by norm_num, Real.sqrt_div (by norm_num),
      h100, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 10)]
  rw [h2] at h
  have h3 : ((-(1:ℝ)/5) - (-(3:ℝ)/10)) / (Real.sqrt 91 / 10) = 1 / Real.sqrt 91 := by
    field_simp
    ring
  rw [h3] at h
  exact h.trans inv_sqrt91_le

lemma arccos_neg_two_fifths_sub_arccos_neg_three_tenths_le :
    Real.arccos (-(2:ℝ)/5) - Real.arccos (-(3:ℝ)/10) ≤ 11/100 := by
  have h := arccos_sub_arccos_le (a := -(2:ℝ)/5) (b := -(3:ℝ)/10)
    (by norm_num) (by norm_num) (by norm_num)
  have h2 : Real.sqrt (1 - (-(2:ℝ)/5)^2) = Real.sqrt 21 / 5 := by
    have h25 : (25:ℝ) = 5^2 := by norm_num
    rw [show (1:ℝ) - (-(2:ℝ)/5)^2 = 21/25 by norm_num, Real.sqrt_div (by norm_num),
      h25, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 5)]
  rw [h2] at h
  have h3 : ((-(3:ℝ)/10) - (-(2:ℝ)/5)) / (Real.sqrt 21 / 5) = 1 / (2 * Real.sqrt 21) := by
    field_simp
    ring
  rw [h3] at h
  exact h.trans inv_two_sqrt21_le

/-!
## The explicit upper bound function for `log ‖L(·,χ)‖` on a circle
-/

/-- `A = log(log N + log(|T₀|+7) + 6)`, the size bound valid for `Re z ≥ 1`. -/
noncomputable def circleA (N : ℕ) (T₀ : ℝ) : ℝ :=
  Real.log (Real.log (N : ℝ) + Real.log (|T₀| + 7) + 6)

/-- `B`, the size bound valid for `1/2 ≤ Re z ≤ 1`. -/
noncomputable def circleB (N : ℕ) (T₀ : ℝ) : ℝ :=
  2 * Real.log 2 + Real.log (N : ℝ) + Real.log (|T₀| + 7)

/-- `C`, the size bound valid for `0 ≤ Re z ≤ 1/2`. -/
noncomputable def circleC (N : ℕ) (T₀ : ℝ) : ℝ :=
  2 * Real.log 2 + 10 + (3 / 2) * Real.log (N : ℝ) + 2 * Real.log (|T₀| + 7)

/-- `P`, the coefficient of `1/2 - Re z` in the left half-plane bound. -/
noncomputable def circleP (N : ℕ) (T₀ : ℝ) : ℝ :=
  Real.log (N : ℝ) + Real.log ((|T₀| + 9) / 2) + 2 - Real.log Real.pi

/-- A piecewise explicit upper bound for `log ‖L(χ,·)‖` on the disk `|z - a| ≤ 5`,
`a = 2 + i T₀`, depending only on `Re z`. -/
noncomputable def circleUBσ (N : ℕ) (T₀ : ℝ) (σ : ℝ) : ℝ :=
  if 1 ≤ σ then circleA N T₀
  else if 1 / 2 ≤ σ then circleB N T₀
  else if 0 ≤ σ then circleC N T₀
  else (1 / 2 - σ) * circleP N T₀ + (Real.log 2 + circleA N T₀)

lemma log_two_nonneg : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)

lemma circleA_nonneg (N : ℕ) [NeZero N] (T₀ : ℝ) : 0 ≤ circleA N T₀ := by
  unfold circleA
  apply Real.log_nonneg
  have h1 : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N))
  have h2 : 0 ≤ Real.log (|T₀| + 7) := Real.log_nonneg (by linarith [abs_nonneg T₀])
  linarith

lemma circleB_nonneg (N : ℕ) [NeZero N] (T₀ : ℝ) : 0 ≤ circleB N T₀ := by
  unfold circleB
  have h1 : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N))
  have h2 : 0 ≤ Real.log (|T₀| + 7) := Real.log_nonneg (by linarith [abs_nonneg T₀])
  linarith [log_two_nonneg]

lemma circleC_nonneg (N : ℕ) [NeZero N] (T₀ : ℝ) : 0 ≤ circleC N T₀ := by
  unfold circleC
  have h1 : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N))
  have h2 : 0 ≤ Real.log (|T₀| + 7) := Real.log_nonneg (by linarith [abs_nonneg T₀])
  linarith [log_two_nonneg]

lemma log_pi_le_two : Real.log Real.pi ≤ 2 := by
  have h1 : Real.log Real.pi ≤ Real.log 4 := Real.log_le_log Real.pi_pos (by linarith [Real.pi_lt_four])
  have h2 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]; ring
  have h3 : Real.log 2 ≤ 1 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]; linarith [Real.exp_one_gt_two]
  linarith

lemma circleP_nonneg (N : ℕ) [NeZero N] (T₀ : ℝ) : 0 ≤ circleP N T₀ := by
  unfold circleP
  have h1 : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N))
  have h2 : 0 ≤ Real.log ((|T₀| + 9) / 2) := Real.log_nonneg (by linarith [abs_nonneg T₀])
  linarith [log_pi_le_two]

lemma circleUBσ_nonneg (N : ℕ) [NeZero N] (T₀ : ℝ) (σ : ℝ) : 0 ≤ circleUBσ N T₀ σ := by
  unfold circleUBσ
  split_ifs with h1 h2 h3
  · exact circleA_nonneg N T₀
  · exact circleB_nonneg N T₀
  · exact circleC_nonneg N T₀
  · have hp := circleP_nonneg N T₀
    have ha := circleA_nonneg N T₀
    have h4 : σ ≤ 0 := le_of_not_ge h3
    have h5 : (0:ℝ) ≤ 1/2 - σ := by linarith
    have := mul_nonneg h5 hp
    linarith [log_two_nonneg]

/-- Upper bound for `log ‖L(χ,z)‖` when `0 ≤ Re z ≤ 1/2`, obtained from the functional
equation and the bounds on the two remaining regions. -/
theorem LFunction_log_le_of_re_le_half {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) {z : ℂ}
    (h1 : 0 ≤ z.re) (h2 : z.re ≤ 1/2) :
    Real.log ‖LFunction χ z‖ ≤ (3 / 2) * Real.log (N : ℝ) + Real.log (2 + |z.im|)
      + Real.log (1 + |z.im|) + (2 * Real.log 2 + 10) := by
  have hN : N ≠ 1 := ne_one_of_char_ne_one hχ
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
  have hlog20 : 0 ≤ Real.log (2 + |z.im|) := Real.log_nonneg (by linarith [abs_nonneg z.im])
  have hlog10 : 0 ≤ Real.log (1 + |z.im|) := Real.log_nonneg (by linarith [abs_nonneg z.im])
  have hlt1 : z.re < 1 := by linarith
  rcases eq_or_ne (gammaFactor χ z) 0 with hγ | hγ
  · have hL0 : LFunction χ z = 0 := by
      rw [LFunction_eq_completed_div_gammaFactor χ z (Or.inr hN), hγ, div_zero]
    rw [hL0, norm_zero, Real.log_zero]
    linarith [log_two_nonneg]
  · have hFE := LFunction_norm_FE χ hχ hχprim hlt1 hγ
    have hre1z : (1 - z).re = 1 - z.re := by simp
    have hpow : 0 < (N : ℝ) ^ (1/2 - z.re) := Real.rpow_pos_of_pos hNpos _
    have hBne : gammaFactor χ (1 - z) ≠ 0 := by
      have hre : 0 < (1 - z).re := by rw [hre1z]; linarith
      rcases χ.even_or_odd with hE | hO
      · rw [Even.gammaFactor_def hE]; exact Complex.Gammaℝ_ne_zero_of_re_pos hre
      · rw [Odd.gammaFactor_def hO]
        exact Complex.Gammaℝ_ne_zero_of_re_pos (by
          rw [Complex.add_re, Complex.one_re, hre1z]; linarith)
    have hBpos : 0 < ‖gammaFactor χ (1 - z)‖ := norm_pos_iff.mpr hBne
    have hCpos : 0 < ‖gammaFactor χ z‖ := norm_pos_iff.mpr hγ
    rcases eq_or_ne ‖LFunction χ⁻¹ (1 - z)‖ 0 with hA0 | hA
    · have hz : ‖LFunction χ z‖ = 0 := by rw [hFE, hA0, mul_zero, zero_mul]
      rw [hz, Real.log_zero]
      linarith [log_two_nonneg]
    · have hApos : 0 < ‖LFunction χ⁻¹ (1 - z)‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hA)
      have hlogle : Real.log ‖LFunction χ z‖
          = (1/2 - z.re) * Real.log (N : ℝ) + Real.log ‖LFunction χ⁻¹ (1 - z)‖
            + (Real.log ‖gammaFactor χ (1 - z)‖ - Real.log ‖gammaFactor χ z‖) := by
        rw [hFE, Real.log_mul (mul_ne_zero hpow.ne' hApos.ne') (div_ne_zero hBpos.ne' hCpos.ne'),
          Real.log_mul hpow.ne' hApos.ne', Real.log_div hBpos.ne' hCpos.ne', Real.log_rpow hNpos]
      have hstrip := LFunction_log_le_strip χ⁻¹ (inv_ne_one_of_one χ hχ) (z := 1 - z)
        (by rw [hre1z]; linarith) (by rw [hre1z]; linarith)
      have him1 : (1 - z).im = -z.im := by simp
      rw [him1, abs_neg] at hstrip
      have hb : (1:ℝ)/2 ≤ (1 - z).re := by rw [hre1z]; linarith
      have hlogsub : -Real.log ((1 - z).re) ≤ Real.log 2 := by
        have h := Real.log_le_log (by norm_num : (0:ℝ) < 1/2) hb
        rw [Real.log_div (by norm_num) (by norm_num), Real.log_one, zero_sub] at h
        linarith
      have hlogstrip : Real.log ‖LFunction χ⁻¹ (1 - z)‖ ≤ Real.log 2 + Real.log (N : ℝ)
          + Real.log (1 + |z.im|) + Real.log 2 := by
        linarith [hstrip, hlogsub]
      have hratio := gammaFactor_ratio_le_S1 χ h1 h2 hγ
      have hmul : (1/2 - z.re) * Real.log (N : ℝ) ≤ (1/2) * Real.log (N : ℝ) := by
        nlinarith [mul_nonneg h1 hlogN, hlogN]
      linarith [hlogle, hlogstrip, hratio, hmul]

/-- Pointwise bound: on the sphere `|z - (2 + i T₀)| = 5` the logarithm of `‖L(χ,z)‖` is
bounded by `circleUBσ`. -/
lemma LFunction_log_le_circleUBσ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) (T₀ : ℝ) {z : ℂ}
    (hre1 : -(3:ℝ) ≤ z.re) (him : |z.im| ≤ |T₀| + 5) :
    Real.log ‖LFunction χ z‖ ≤ circleUBσ N T₀ z.re := by
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
  have hbound2 : 2 + |z.im| ≤ |T₀| + 7 := by linarith
  have hbound1 : 1 + |z.im| ≤ |T₀| + 7 := by linarith
  have hboundh : 2 + |z.im/2| ≤ (|T₀| + 9)/2 := by
    rw [abs_div]
    have : |z.im| / 2 ≤ (|T₀| + 5)/2 := by linarith
    linarith
  have hlogmono2 : Real.log (2 + |z.im|) ≤ Real.log (|T₀| + 7) :=
    Real.log_le_log (by linarith [abs_nonneg z.im]) hbound2
  have hlogmono1 : Real.log (1 + |z.im|) ≤ Real.log (|T₀| + 7) :=
    Real.log_le_log (by linarith [abs_nonneg z.im]) hbound1
  have hpos12 : 0 < Real.log (N:ℝ) + Real.log (2 + |z.im|) + 6 := by
    have : 0 ≤ Real.log (2 + |z.im|) := Real.log_nonneg (by linarith [abs_nonneg z.im])
    linarith
  have hlogAA : Real.log (Real.log (N:ℝ) + Real.log (2 + |z.im|) + 6) ≤ circleA N T₀ := by
    unfold circleA
    apply Real.log_le_log hpos12
    linarith
  unfold circleUBσ
  by_cases h1 : 1 ≤ z.re
  · rw [if_pos h1]
    have h := LFunction_log_le_right χ hχ (z := z) h1
    linarith
  · rw [if_neg h1]
    by_cases h2 : 1/2 ≤ z.re
    · rw [if_pos h2]
      have hz1 : 0 < z.re := by linarith
      have hz2 : z.re ≤ 1 := by linarith [not_le.mp h1]
      have h := LFunction_log_le_strip χ hχ (z := z) hz1 hz2
      have hlogsub : -Real.log z.re ≤ Real.log 2 := by
        have hh := Real.log_le_log (by norm_num : (0:ℝ) < 1/2) h2
        rw [Real.log_div (by norm_num) (by norm_num), Real.log_one, zero_sub] at hh
        linarith
      unfold circleB
      linarith
    · rw [if_neg h2]
      by_cases h3 : 0 ≤ z.re
      · rw [if_pos h3]
        have h := LFunction_log_le_of_re_le_half χ hχ hχprim h3 (le_of_lt (not_le.mp h2))
        unfold circleC
        linarith
      · rw [if_neg h3]
        have hz0 : z.re ≤ 0 := le_of_not_ge h3
        rcases eq_or_ne (gammaFactor χ z) 0 with hγ | hγ
        · have hL0 : LFunction χ z = 0 := by
            rw [LFunction_eq_completed_div_gammaFactor χ z (Or.inr (ne_one_of_char_ne_one hχ)),
              hγ, div_zero]
          rw [hL0, norm_zero, Real.log_zero]
          have hp := circleP_nonneg N T₀
          have ha := circleA_nonneg N T₀
          have h5 : (0:ℝ) ≤ 1/2 - z.re := by linarith
          have := mul_nonneg h5 hp
          linarith [log_two_nonneg]
        · have h := LFunction_log_le_of_re_nonpos χ hχ hχprim hz0 hre1 hγ
          have e2 : Real.log (2 + |z.im/2|) ≤ Real.log ((|T₀| + 9)/2) :=
            Real.log_le_log (by linarith [abs_nonneg (z.im/2)]) hboundh
          have hprod : (1/2 - z.re) * (Real.log (2 + |z.im/2|) + 2)
              ≤ (1/2 - z.re) * (Real.log ((|T₀| + 9)/2) + 2) :=
            mul_le_mul_of_nonneg_left (add_le_add e2 le_rfl) (by linarith)
          have key : (1/2 - z.re) * Real.log (N : ℝ) + circleA N T₀
                + (1/2 - z.re) * (Real.log ((|T₀| + 9)/2) + 2)
                + (z.re - 3/2) * Real.log Real.pi + Real.log (2 * Real.pi)
              = (1/2 - z.re) * circleP N T₀ + (Real.log 2 + circleA N T₀) := by
            unfold circleP
            rw [Real.log_mul (by norm_num) Real.pi_ne_zero]
            ring
          linarith [h, hlogAA, hprod, key]

/-!
## Integrability and integration of `circleUBσ` on circles
-/

lemma measurable_circleUBσ (N : ℕ) (T₀ : ℝ) : Measurable (fun σ : ℝ => circleUBσ N T₀ σ) := by
  unfold circleUBσ
  refine Measurable.ite measurableSet_Ici measurable_const ?_
  refine Measurable.ite measurableSet_Ici measurable_const ?_
  refine Measurable.ite measurableSet_Ici measurable_const ?_
  exact ((measurable_const.sub measurable_id).mul measurable_const).add measurable_const

lemma circleUBσ_eq_A (N : ℕ) (T₀ : ℝ) {σ : ℝ} (h : 1 ≤ σ) :
    circleUBσ N T₀ σ = circleA N T₀ := by
  unfold circleUBσ; rw [if_pos h]

lemma circleUBσ_eq_B (N : ℕ) (T₀ : ℝ) {σ : ℝ} (h1 : ¬ 1 ≤ σ) (h2 : 1/2 ≤ σ) :
    circleUBσ N T₀ σ = circleB N T₀ := by
  unfold circleUBσ; rw [if_neg h1, if_pos h2]

lemma circleUBσ_eq_C (N : ℕ) (T₀ : ℝ) {σ : ℝ} (h1 : ¬ 1 ≤ σ) (h2 : ¬ 1/2 ≤ σ)
    (h3 : 0 ≤ σ) : circleUBσ N T₀ σ = circleC N T₀ := by
  unfold circleUBσ; rw [if_neg h1, if_neg h2, if_pos h3]

lemma circleUBσ_eq_D (N : ℕ) (T₀ : ℝ) {σ : ℝ} (h1 : ¬ 1 ≤ σ) (h2 : ¬ 1/2 ≤ σ)
    (h3 : ¬ 0 ≤ σ) :
    circleUBσ N T₀ σ = (1/2 - σ) * circleP N T₀ + (Real.log 2 + circleA N T₀) := by
  unfold circleUBσ; rw [if_neg h1, if_neg h2, if_neg h3]

lemma circleMap_re (c : ℂ) (R θ : ℝ) : (circleMap c R θ).re = c.re + R * Real.cos θ := by
  rw [circleMap]
  simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]

lemma intervalIntegrable_circleUB_cos (N : ℕ) [NeZero N] (T₀ : ℝ) (a b : ℝ) :
    IntervalIntegrable (fun θ : ℝ => circleUBσ N T₀ (2 + 5 * Real.cos θ)) volume a b := by
  apply MeasureTheory.IntegrableOn.intervalIntegrable
  refine MeasureTheory.IntegrableOn.of_bound isCompact_uIcc.measure_lt_top ?_
    (circleA N T₀ + circleB N T₀ + circleC N T₀ + (7/2) * circleP N T₀
      + (Real.log 2 + circleA N T₀)) ?_
  · exact ((measurable_circleUBσ N T₀).comp
      (by fun_prop : Measurable fun θ : ℝ => 2 + 5 * Real.cos θ)).aestronglyMeasurable
  · filter_upwards with θ
    have hc : Real.cos θ ≤ 1 := Real.cos_le_one θ
    have hc' : -1 ≤ Real.cos θ := Real.neg_one_le_cos θ
    rw [Real.norm_of_nonneg (circleUBσ_nonneg N T₀ _)]
    by_cases h1 : 1 ≤ 2 + 5 * Real.cos θ
    · rw [circleUBσ_eq_A N T₀ h1]
      have a1 := circleB_nonneg N T₀
      have a2 := circleC_nonneg N T₀
      have a3 := mul_nonneg (by linarith : (0:ℝ) ≤ 7/2) (circleP_nonneg N T₀)
      have a4 := circleA_nonneg N T₀
      have a5 := log_two_nonneg
      linarith
    · by_cases h2 : (1:ℝ)/2 ≤ 2 + 5 * Real.cos θ
      · rw [circleUBσ_eq_B N T₀ h1 h2]
        have a1 := circleA_nonneg N T₀
        have a2 := circleC_nonneg N T₀
        have a3 := mul_nonneg (by linarith : (0:ℝ) ≤ 7/2) (circleP_nonneg N T₀)
        have a4 := circleA_nonneg N T₀
        have a5 := log_two_nonneg
        linarith
      · by_cases h3 : (0:ℝ) ≤ 2 + 5 * Real.cos θ
        · rw [circleUBσ_eq_C N T₀ h1 h2 h3]
          have a1 := circleB_nonneg N T₀
          have a3 := mul_nonneg (by linarith : (0:ℝ) ≤ 7/2) (circleP_nonneg N T₀)
          have a4 := circleA_nonneg N T₀
          have a5 := log_two_nonneg
          linarith
        · rw [circleUBσ_eq_D N T₀ h1 h2 h3]
          have a1 := circleB_nonneg N T₀
          have a2 := circleC_nonneg N T₀
          have hp := circleP_nonneg N T₀
          have ha := circleA_nonneg N T₀
          have hl2 := log_two_nonneg
          have hcoef : 1/2 - (2 + 5 * Real.cos θ) ≤ 7/2 := by linarith
          have hml := mul_le_mul_of_nonneg_right hcoef hp
          linarith

lemma circleIntegrable_circleUB (N : ℕ) [NeZero N] (T₀ : ℝ) (c : ℂ) (hc : c.re = 2) :
    CircleIntegrable (fun z : ℂ => circleUBσ N T₀ z.re) c 5 := by
  rw [CircleIntegrable]
  have heq : (fun θ : ℝ => (fun z : ℂ => circleUBσ N T₀ z.re) (circleMap c (5:ℝ) θ))
      = (fun θ : ℝ => circleUBσ N T₀ (2 + 5 * Real.cos θ)) := by
    funext θ
    show circleUBσ N T₀ (circleMap c (5:ℝ) θ).re = circleUBσ N T₀ (2 + 5 * Real.cos θ)
    rw [circleMap_re, hc]
  rw [heq]
  exact intervalIntegrable_circleUB_cos N T₀ 0 (2 * Real.pi)

lemma integral_cos_symm (H : ℝ → ℝ)
    (hint : IntervalIntegrable (fun θ : ℝ => H (Real.cos θ)) volume 0 (2 * Real.pi)) :
    ∫ θ in (0:ℝ)..(2 * Real.pi), H (Real.cos θ) = 2 * ∫ θ in (0:ℝ)..Real.pi, H (Real.cos θ) := by
  have hmem1 : Set.uIcc (0:ℝ) Real.pi ⊆ Set.uIcc (0:ℝ) (2 * Real.pi) := by
    rw [Set.uIcc_of_le Real.pi_nonneg, Set.uIcc_of_le (by linarith [Real.pi_pos] : (0:ℝ) ≤ 2 * Real.pi)]
    intro x hx
    exact ⟨hx.1, le_trans hx.2 (by linarith [Real.pi_pos])⟩
  have hmem2 : Set.uIcc Real.pi (2 * Real.pi) ⊆ Set.uIcc (0:ℝ) (2 * Real.pi) := by
    rw [Set.uIcc_of_le (by linarith [Real.pi_pos] : Real.pi ≤ 2 * Real.pi),
      Set.uIcc_of_le (by linarith [Real.pi_pos] : (0:ℝ) ≤ 2 * Real.pi)]
    intro x hx
    exact ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩
  have h0pi : IntervalIntegrable (fun θ : ℝ => H (Real.cos θ)) volume 0 Real.pi :=
    hint.mono hmem1 le_rfl
  have hpi2pi : IntervalIntegrable (fun θ : ℝ => H (Real.cos θ)) volume Real.pi (2 * Real.pi) :=
    hint.mono hmem2 le_rfl
  have hadj := intervalIntegral.integral_add_adjacent_intervals h0pi hpi2pi
  have hcomp := intervalIntegral.integral_comp_sub_left (a := Real.pi) (b := 2 * Real.pi)
    (fun u : ℝ => H (Real.cos u)) (2 * Real.pi)
  rw [show (2:ℝ) * Real.pi - 2 * Real.pi = 0 by ring,
    show (2:ℝ) * Real.pi - Real.pi = Real.pi by ring] at hcomp
  have hsub : ∫ θ in Real.pi..(2 * Real.pi), H (Real.cos θ)
      = ∫ θ in Real.pi..(2 * Real.pi), H (Real.cos (2 * Real.pi - θ)) := by
    apply intervalIntegral.integral_congr
    intro x _
    simp only
    rw [Real.cos_two_pi_sub]
  have hmain := hadj.symm
  rw [hmain, hsub, hcomp]
  ring

lemma circleAverage_circleUB (N : ℕ) [NeZero N] (T₀ : ℝ) (c : ℂ) (hc : c.re = 2) :
    Real.circleAverage (fun z : ℂ => circleUBσ N T₀ z.re) c 5
      = (1/Real.pi) * ∫ θ in (0:ℝ)..Real.pi, circleUBσ N T₀ (2 + 5 * Real.cos θ) := by
  rw [Real.circleAverage_def]
  have hInt := intervalIntegrable_circleUB_cos N T₀ 0 (2 * Real.pi)
  have heq : (fun θ : ℝ => (fun z : ℂ => circleUBσ N T₀ z.re) (circleMap c (5:ℝ) θ))
      = (fun θ : ℝ => circleUBσ N T₀ (2 + 5 * Real.cos θ)) := by
    funext θ
    show circleUBσ N T₀ (circleMap c (5:ℝ) θ).re = circleUBσ N T₀ (2 + 5 * Real.cos θ)
    rw [circleMap_re, hc]
  rw [heq, integral_cos_symm (fun x : ℝ => circleUBσ N T₀ (2 + 5 * x)) hInt, smul_eq_mul]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

/-! ## The arc estimates -/

lemma arccos_neg_half : Real.arccos (-(1:ℝ)/2) = 2 * Real.pi / 3 := by
  have hcos : Real.cos (2 * Real.pi / 3) = -(1:ℝ)/2 := by
    rw [show (2:ℝ) * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub,
      Real.cos_pi_div_three]
    norm_num
  rw [← hcos]
  exact Real.arccos_cos (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

lemma arccos_neg_one_fifth_le_two_pi_div_three :
    Real.arccos (-(1:ℝ)/5) ≤ 2 * Real.pi / 3 := by
  rw [← arccos_neg_half]
  exact Real.arccos_le_arccos (by norm_num : -(1:ℝ)/2 ≤ -(1:ℝ)/5)

lemma arccos_zero : Real.arccos 0 = Real.pi/2 := by
  rw [← Real.cos_pi_div_two]
  exact Real.arccos_cos (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

lemma pi_div_two_le_arccos_neg_two_fifths : Real.pi/2 ≤ Real.arccos (-(2:ℝ)/5) := by
  rw [← arccos_zero]
  exact Real.arccos_le_arccos (by norm_num : -(2:ℝ)/5 ≤ 0)

lemma pi_div_three_le_arccos_two_fifths : Real.pi/3 ≤ Real.arccos ((2:ℝ)/5) := by
  have h : Real.arccos ((1:ℝ)/2) = Real.pi/3 := by
    rw [← Real.cos_pi_div_three]
    exact Real.arccos_cos (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  rw [← h]
  exact Real.arccos_le_arccos (by norm_num : (2:ℝ)/5 ≤ 1/2)

lemma integral_leftHalf :
    ∫ x in Real.arccos (-(2:ℝ)/5)..Real.pi, (1/2 - (2 + 5 * Real.cos x))
      = Real.sqrt 21 - (3/2) * Real.arccos (2/5) := by
  have hc1 : Continuous fun x : ℝ => (1/2 - 2 : ℝ) := continuous_const
  have hc2 : Continuous fun x : ℝ => 5 * Real.cos x := by fun_prop
  have hrewrite : (fun x : ℝ => 1/2 - (2 + 5 * Real.cos x))
      = (fun x : ℝ => (1/2 - 2) - 5 * Real.cos x) := by
    funext x; ring
  rw [hrewrite, intervalIntegral.integral_sub (hc1.intervalIntegrable _ _) (hc2.intervalIntegrable _ _),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_cos]
  simp only [smul_eq_mul, Real.sin_pi, zero_sub]
  have hsin : Real.sin (Real.arccos (-(2:ℝ)/5)) = Real.sqrt 21 / 5 := by
    rw [Real.sin_arccos]
    rw [show (1:ℝ) - (-(2:ℝ)/5)^2 = 21/25 by norm_num, Real.sqrt_div (by norm_num),
      show (25:ℝ) = 5^2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 5)]
  have harccos : Real.arccos (-(2:ℝ)/5) = Real.pi - Real.arccos (2/5) := by
    rw [show (-(2:ℝ)/5) = -(2/5) by ring]
    exact Real.arccos_neg (2/5)
  rw [hsin, harccos]
  ring

lemma integral_leftHalf_le : Real.sqrt 21 - (3/2) * Real.arccos (2/5) ≤ 303/100 := by
  have harc : Real.pi/3 ≤ Real.arccos (2/5) := pi_div_three_le_arccos_two_fifths
  have hs : Real.sqrt 21 ≤ 4.6 := by
    calc Real.sqrt 21 ≤ Real.sqrt ((4.6:ℝ)^2) := Real.sqrt_le_sqrt (by norm_num)
      _ = 4.6 := Real.sqrt_sq (by norm_num)
  linarith [Real.pi_gt_d2]

/-!
## The main integral estimate on `[0,π]`
-/

lemma integral_circleUB_le (N : ℕ) [NeZero N] (T₀ : ℝ) :
    ∫ θ in (0:ℝ)..Real.pi, circleUBσ N T₀ (2 + 5 * Real.cos θ)
      ≤ (2 * Real.pi / 3) * circleA N T₀ + (21 / 200) * circleB N T₀
        + (11 / 100) * circleC N T₀ + (303 / 100) * circleP N T₀
        + (Real.pi / 2) * (Real.log 2 + circleA N T₀) := by
  set θ1 := Real.arccos (-(1:ℝ)/5) with hθ1def
  set θh := Real.arccos (-(3:ℝ)/10) with hθhdef
  set θ0 := Real.arccos (-(2:ℝ)/5) with hθ0def
  have hθ1nn : 0 ≤ θ1 := by rw [hθ1def]; exact Real.arccos_nonneg _
  have hθ1pi : θ1 ≤ Real.pi := by rw [hθ1def]; exact Real.arccos_le_pi _
  have hθhnn : 0 ≤ θh := by rw [hθhdef]; exact Real.arccos_nonneg _
  have hθhpi : θh ≤ Real.pi := by rw [hθhdef]; exact Real.arccos_le_pi _
  have hθ0nn : 0 ≤ θ0 := by rw [hθ0def]; exact Real.arccos_nonneg _
  have hθ0pi : θ0 ≤ Real.pi := by rw [hθ0def]; exact Real.arccos_le_pi _
  have hcosθ1 : Real.cos θ1 = -(1:ℝ)/5 := by
    rw [hθ1def]; exact Real.cos_arccos (by norm_num) (by norm_num)
  have hcosθh : Real.cos θh = -(3:ℝ)/10 := by
    rw [hθhdef]; exact Real.cos_arccos (by norm_num) (by norm_num)
  have hcosθ0 : Real.cos θ0 = -(2:ℝ)/5 := by
    rw [hθ0def]; exact Real.cos_arccos (by norm_num) (by norm_num)
  have h1h : θ1 ≤ θh := by
    rw [hθ1def, hθhdef]
    exact Real.arccos_le_arccos (x := -(3:ℝ)/10) (y := -(1:ℝ)/5) (by norm_num)
  have hh0 : θh ≤ θ0 := by
    rw [hθhdef, hθ0def]
    exact Real.arccos_le_arccos (x := -(2:ℝ)/5) (y := -(3:ℝ)/10) (by norm_num)
  have hθ1_23 : θ1 ≤ 2 * Real.pi / 3 := by
    rw [hθ1def]; exact arccos_neg_one_fifth_le_two_pi_div_three
  have hδ1 : θh - θ1 ≤ 21/200 := by
    rw [hθhdef, hθ1def]; exact arccos_neg_three_tenths_sub_arccos_neg_one_fifth_le
  have hδ2 : θ0 - θh ≤ 11/100 := by
    rw [hθ0def, hθhdef]; exact arccos_neg_two_fifths_sub_arccos_neg_three_tenths_le
  have hπθ0 : Real.pi - θ0 ≤ Real.pi/2 := by
    have h := pi_div_two_le_arccos_neg_two_fifths
    rw [← hθ0def] at h
    linarith
  have hFint : ∀ a b : ℝ, IntervalIntegrable
      (fun θ : ℝ => circleUBσ N T₀ (2 + 5 * Real.cos θ)) volume a b :=
    fun a b => intervalIntegrable_circleUB_cos N T₀ a b
  have p1 : ∫ θ in (0:ℝ)..θ1, circleUBσ N T₀ (2 + 5 * Real.cos θ) = θ1 * circleA N T₀ := by
    have heq : ∫ θ in (0:ℝ)..θ1, circleUBσ N T₀ (2 + 5 * Real.cos θ)
        = ∫ θ in (0:ℝ)..θ1, circleA N T₀ := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards with x hx
      rw [Set.uIoc_of_le hθ1nn, Set.mem_Ioc] at hx
      exact circleUBσ_eq_A N T₀ (by
        have hx1 : 0 ≤ x := le_of_lt hx.1
        have hx2 : x ≤ Real.pi := le_trans hx.2 hθ1pi
        have hcos : Real.cos θ1 ≤ Real.cos x :=
          Real.antitoneOn_cos ⟨hx1, hx2⟩ ⟨hθ1nn, hθ1pi⟩ hx.2
        rw [hcosθ1] at hcos
        linarith)
    rw [heq, intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  have p2 : ∫ θ in θ1..θh, circleUBσ N T₀ (2 + 5 * Real.cos θ) = (θh - θ1) * circleB N T₀ := by
    have heq : ∫ θ in θ1..θh, circleUBσ N T₀ (2 + 5 * Real.cos θ)
        = ∫ θ in θ1..θh, circleB N T₀ := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards with x hx
      rw [Set.uIoc_of_le h1h, Set.mem_Ioc] at hx
      have hx1 : 0 ≤ x := le_trans hθ1nn hx.1.le
      have hx2 : x ≤ Real.pi := le_trans hx.2 hθhpi
      refine circleUBσ_eq_B N T₀ (not_le.mpr ?_) ?_
      · have hlt := Real.cos_lt_cos_of_nonneg_of_le_pi hθ1nn hx2 hx.1
        rw [hcosθ1] at hlt
        linarith
      · have hcos : Real.cos θh ≤ Real.cos x :=
          Real.antitoneOn_cos ⟨hx1, hx2⟩ ⟨hθhnn, hθhpi⟩ hx.2
        rw [hcosθh] at hcos
        linarith
    rw [heq, intervalIntegral.integral_const, smul_eq_mul]
  have p3 : ∫ θ in θh..θ0, circleUBσ N T₀ (2 + 5 * Real.cos θ) = (θ0 - θh) * circleC N T₀ := by
    have heq : ∫ θ in θh..θ0, circleUBσ N T₀ (2 + 5 * Real.cos θ)
        = ∫ θ in θh..θ0, circleC N T₀ := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards with x hx
      rw [Set.uIoc_of_le hh0, Set.mem_Ioc] at hx
      have hx1 : 0 ≤ x := le_trans hθhnn hx.1.le
      have hx2 : x ≤ Real.pi := le_trans hx.2 hθ0pi
      have hlt : Real.cos x < Real.cos θh :=
        Real.cos_lt_cos_of_nonneg_of_le_pi hθhnn hx2 hx.1
      rw [hcosθh] at hlt
      refine circleUBσ_eq_C N T₀ (not_le.mpr (by linarith)) (not_le.mpr (by linarith)) ?_
      have hcos : Real.cos θ0 ≤ Real.cos x :=
        Real.antitoneOn_cos ⟨hx1, hx2⟩ ⟨hθ0nn, hθ0pi⟩ hx.2
      rw [hcosθ0] at hcos
      linarith
    rw [heq, intervalIntegral.integral_const, smul_eq_mul]
  have p4eq : ∫ θ in θ0..Real.pi, circleUBσ N T₀ (2 + 5 * Real.cos θ)
      = ∫ θ in θ0..Real.pi,
          ((1/2 - (2 + 5 * Real.cos θ)) * circleP N T₀ + (Real.log 2 + circleA N T₀)) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with x hx
    rw [Set.uIoc_of_le hθ0pi, Set.mem_Ioc] at hx
    have hlt : Real.cos x < Real.cos θ0 :=
      Real.cos_lt_cos_of_nonneg_of_le_pi hθ0nn hx.2 hx.1
    rw [hcosθ0] at hlt
    refine circleUBσ_eq_D N T₀ (not_le.mpr ?_) (not_le.mpr ?_) (not_le.mpr ?_) <;> linarith
  have p4val : ∫ θ in θ0..Real.pi,
        ((1/2 - (2 + 5 * Real.cos θ)) * circleP N T₀ + (Real.log 2 + circleA N T₀))
      = circleP N T₀ * (Real.sqrt 21 - (3/2) * Real.arccos (2/5))
        + (Real.log 2 + circleA N T₀) * (Real.pi - θ0) := by
    have hc1 : Continuous fun θ : ℝ => (1/2 - (2 + 5 * Real.cos θ)) * circleP N T₀ := by fun_prop
    have hc2 : Continuous fun _ : ℝ => (Real.log 2 + circleA N T₀) := continuous_const
    rw [intervalIntegral.integral_add (hc1.intervalIntegrable _ _) (hc2.intervalIntegrable _ _),
      intervalIntegral.integral_mul_const (circleP N T₀)
        (fun θ : ℝ => 1/2 - (2 + 5 * Real.cos θ)),
      intervalIntegral.integral_const]
    rw [hθ0def, integral_leftHalf]
    simp only [smul_eq_mul]
    ring
  have hsplit : ∫ θ in (0:ℝ)..Real.pi, circleUBσ N T₀ (2 + 5 * Real.cos θ)
      = (∫ θ in (0:ℝ)..θ1, circleUBσ N T₀ (2 + 5 * Real.cos θ))
        + (∫ θ in θ1..θh, circleUBσ N T₀ (2 + 5 * Real.cos θ))
        + (∫ θ in θh..θ0, circleUBσ N T₀ (2 + 5 * Real.cos θ))
        + (∫ θ in θ0..Real.pi, circleUBσ N T₀ (2 + 5 * Real.cos θ)) := by
    have a1 := intervalIntegral.integral_add_adjacent_intervals (hFint 0 θ1) (hFint θ1 Real.pi)
    have a2 := intervalIntegral.integral_add_adjacent_intervals (hFint θ1 θh) (hFint θh Real.pi)
    have a3 := intervalIntegral.integral_add_adjacent_intervals (hFint θh θ0) (hFint θ0 Real.pi)
    linarith
  have b1 : ∫ θ in (0:ℝ)..θ1, circleUBσ N T₀ (2 + 5 * Real.cos θ) ≤ (2 * Real.pi / 3) * circleA N T₀ := by
    rw [p1]
    exact mul_le_mul_of_nonneg_right hθ1_23 (circleA_nonneg N T₀)
  have b2 : ∫ θ in θ1..θh, circleUBσ N T₀ (2 + 5 * Real.cos θ) ≤ (21 / 200) * circleB N T₀ := by
    rw [p2]
    exact mul_le_mul_of_nonneg_right hδ1 (circleB_nonneg N T₀)
  have b3 : ∫ θ in θh..θ0, circleUBσ N T₀ (2 + 5 * Real.cos θ) ≤ (11 / 100) * circleC N T₀ := by
    rw [p3]
    exact mul_le_mul_of_nonneg_right hδ2 (circleC_nonneg N T₀)
  have b4 : ∫ θ in θ0..Real.pi, circleUBσ N T₀ (2 + 5 * Real.cos θ)
      ≤ (303 / 100) * circleP N T₀ + (Real.pi / 2) * (Real.log 2 + circleA N T₀) := by
    rw [p4eq, p4val]
    have hP := circleP_nonneg N T₀
    have hQ : 0 ≤ Real.log 2 + circleA N T₀ := by
      have h1 := log_two_nonneg; have h2 := circleA_nonneg N T₀; linarith
    have h1 : Real.sqrt 21 - (3/2) * Real.arccos (2/5) ≤ 303/100 := integral_leftHalf_le
    have h2 : Real.pi - θ0 ≤ Real.pi/2 := hπθ0
    have hm1 := mul_le_mul_of_nonneg_left h1 hP
    have hm2 := mul_le_mul_of_nonneg_right h2 hQ
    linarith
  rw [hsplit]
  linarith [b1, b2, b3, b4]

/-!
## Bounds for the four constants, and the final arithmetic
-/

lemma log_abs_add_seven_le (T₀ : ℝ) :
    Real.log (|T₀| + 7) ≤ Real.log (|T₀| + 4) + 1 := by
  have h4 : (0:ℝ) < |T₀| + 4 := by linarith [abs_nonneg T₀]
  have h7 : (0:ℝ) < |T₀| + 7 := by linarith [abs_nonneg T₀]
  have hratio : (|T₀| + 7)/(|T₀| + 4) ≠ 0 := div_ne_zero h7.ne' h4.ne'
  have hratio' : (|T₀| + 7)/(|T₀| + 4) ≤ 7/4 := by
    rw [div_le_iff₀ h4]; nlinarith [abs_nonneg T₀]
  have hmul : (|T₀| + 4) * ((|T₀| + 7)/(|T₀| + 4)) = |T₀| + 7 := by field_simp
  have hlog : Real.log (|T₀| + 7)
      = Real.log (|T₀| + 4) + Real.log ((|T₀| + 7)/(|T₀| + 4)) := by
    rw [← Real.log_mul h4.ne' hratio, hmul]
  have hlogr : Real.log ((|T₀| + 7)/(|T₀| + 4)) ≤ 1 := by
    rw [Real.log_le_iff_le_exp (by positivity)]
    linarith [hratio', Real.exp_one_gt_two]
  linarith

lemma log_abs_add_nine_half_le (T₀ : ℝ) :
    Real.log ((|T₀| + 9)/2) ≤ Real.log (|T₀| + 4) + 1/8 := by
  have h4 : (0:ℝ) < |T₀| + 4 := by linarith [abs_nonneg T₀]
  have hle : (|T₀| + 9)/2 ≤ (9/8) * (|T₀| + 4) := by nlinarith [abs_nonneg T₀]
  have hlog := Real.log_le_log (by positivity : (0:ℝ) < (|T₀| + 9)/2) hle
  rw [Real.log_mul (by norm_num) h4.ne'] at hlog
  have h98 : Real.log (9/8) ≤ 1/8 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    linarith [Real.add_one_le_exp (1/8)]
  linarith

lemma one_le_log_pi : 1 ≤ Real.log Real.pi := by
  have h : Real.exp 1 < Real.pi := lt_trans Real.exp_one_lt_three Real.pi_gt_three
  have hlog := Real.log_lt_log (Real.exp_pos 1) h
  rw [Real.log_exp] at hlog
  exact le_of_lt hlog

lemma circleA_le (N : ℕ) [NeZero N] (hN : 2 ≤ N) (T₀ : ℝ) :
    circleA N T₀ ≤ (1/4) * Real.log (N : ℝ) + (1/4) * Real.log (|T₀| + 4) + 7/4 := by
  have hN2 : (2:ℝ) ≤ N := by exact_mod_cast hN
  have hNnz : (N:ℝ) ≠ 0 := by positivity
  have hX : (2/3 : ℝ) ≤ Real.log (N:ℝ) := by
    have h2 : Real.log 2 ≤ Real.log (N:ℝ) := Real.log_le_log (by norm_num) hN2
    linarith [Commons.Analysis.SpecialFunctions.Log.log_two_ge_two_thirds]
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]; ring
  have hY : (4/3 : ℝ) ≤ Real.log (|T₀| + 4) := by
    have h4 : Real.log 4 ≤ Real.log (|T₀| + 4) :=
      Real.log_le_log (by norm_num) (by linarith [abs_nonneg T₀])
    linarith [Commons.Analysis.SpecialFunctions.Log.log_two_ge_two_thirds]
  have hlog7 := log_abs_add_seven_le T₀
  have hpos : 0 < Real.log (N:ℝ) + Real.log (|T₀| + 7) + 6 := by
    have h1 : 0 ≤ Real.log (N:ℝ) := by linarith
    have h2 : 0 ≤ Real.log (|T₀| + 7) := Real.log_nonneg (by linarith [abs_nonneg T₀])
    linarith
  have hW : Real.log (N:ℝ) + Real.log (|T₀| + 7) + 6
      ≤ Real.log (N:ℝ) + Real.log (|T₀| + 4) + 7 := by linarith
  have hA1 : circleA N T₀ ≤ Real.log (Real.log (N:ℝ) + Real.log (|T₀| + 4) + 7) := by
    unfold circleA
    exact Real.log_le_log hpos hW
  have hlog8 : Real.log 8 ≤ 2.08 := by
    have h8 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8:ℝ) = 2 * 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num),
        Real.log_mul (by norm_num) (by norm_num)]
      ring
    rw [h8]; linarith [Real.log_two_lt_d9]
  have hA2 : Real.log (Real.log (N:ℝ) + Real.log (|T₀| + 4) + 7)
      ≤ (1/4) * Real.log (N:ℝ) + (1/4) * Real.log (|T₀| + 4) + 7/4 := by
    have hsplitlog : Real.log (Real.log (N:ℝ) + Real.log (|T₀| + 4) + 7)
        = Real.log ((Real.log (N:ℝ) + Real.log (|T₀| + 4) + 7)/8) + Real.log 8 := by
      rw [← Real.log_mul (by positivity) (by norm_num : (8:ℝ) ≠ 0)]
      congr 1
      ring
    rw [hsplitlog]
    have h1 : Real.log ((Real.log (N:ℝ) + Real.log (|T₀| + 4) + 7)/8)
        ≤ (Real.log (N:ℝ) + Real.log (|T₀| + 4) + 7)/8 - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    linarith
  linarith

lemma circleB_le (N : ℕ) [NeZero N] (T₀ : ℝ) :
    circleB N T₀ ≤ Real.log (N : ℝ) + Real.log (|T₀| + 4) + 12/5 := by
  unfold circleB
  have hlog7 := log_abs_add_seven_le T₀
  have h2 : Real.log 2 ≤ 0.7 := by linarith [Real.log_two_lt_d9]
  linarith

lemma circleC_le (N : ℕ) [NeZero N] (T₀ : ℝ) :
    circleC N T₀ ≤ (3/2) * Real.log (N : ℝ) + 2 * Real.log (|T₀| + 4) + 67/5 := by
  unfold circleC
  have hlog7 := log_abs_add_seven_le T₀
  have h2 : Real.log 2 ≤ 0.7 := by linarith [Real.log_two_lt_d9]
  linarith

lemma circleP_le (N : ℕ) [NeZero N] (T₀ : ℝ) :
    circleP N T₀ ≤ Real.log (N : ℝ) + Real.log (|T₀| + 4) + 9/8 := by
  unfold circleP
  have hlog9 := log_abs_add_nine_half_le T₀
  have hpi := one_le_log_pi
  linarith

lemma circleQ_le (N : ℕ) [NeZero N] (hN : 2 ≤ N) (T₀ : ℝ) :
    Real.log 2 + circleA N T₀ ≤ (1/4) * Real.log (N : ℝ) + (1/4) * Real.log (|T₀| + 4) + 49/20 := by
  have hA := circleA_le N hN T₀
  have h2 : Real.log 2 ≤ 0.7 := by linarith [Real.log_two_lt_d9]
  linarith

/-- The final numerical bookkeeping. -/
lemma circleUB_arith (A B C P Q X Y : ℝ) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hBnn : 0 ≤ B) (hCnn : 0 ≤ C) (hPnn : 0 ≤ P)
    (hA : A ≤ (1/4)*X + (1/4)*Y + 7/4)
    (hB : B ≤ X + Y + 12/5) (hC : C ≤ (3/2)*X + 2*Y + 67/5)
    (hP : P ≤ X + Y + 9/8) (hQ : Q ≤ (1/4)*X + (1/4)*Y + 49/20) :
    (1/Real.pi) * ((2*Real.pi/3)*A + (21/200)*B + (11/100)*C + (303/100)*P + (Real.pi/2)*Q)
      + Real.log 4 ≤ (3/2)*(X + Y) + 6 := by
  have hkey : (1/Real.pi) * ((2*Real.pi/3)*A + (21/200)*B + (11/100)*C + (303/100)*P
      + (Real.pi/2)*Q)
      = (2/3)*A + (21/200)*((1/Real.pi)*B) + (11/100)*((1/Real.pi)*C)
        + (303/100)*((1/Real.pi)*P) + (1/2)*Q := by
    field_simp
    try ring
  rw [hkey]
  have hinv : 1/Real.pi ≤ 50/157 := by
    rw [div_le_iff₀ Real.pi_pos]; linarith [Real.pi_gt_d2]
  have hB' : (21/200) * ((1/Real.pi)*B) ≤ 0.04*X + 0.04*Y + 0.09 := by
    have h1 : (21/200) * ((1/Real.pi)*B) ≤ (21/200) * ((50/157) * (X + Y + 12/5)) :=
      mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_right hinv hBnn).trans
        (mul_le_mul_of_nonneg_left hB (by norm_num))) (by norm_num)
    refine h1.trans ?_
    have hc : ((21/200 : ℝ) * (50/157)) ≤ 0.04 := by norm_num
    have hd : ((21/200 : ℝ) * (50/157)) * (12/5) ≤ 0.09 := by norm_num
    nlinarith [mul_le_mul_of_nonneg_right hc (by linarith : (0:ℝ) ≤ X + Y + 12/5), hd]
  have hC' : (11/100) * ((1/Real.pi)*C) ≤ 0.06*X + 0.08*Y + 0.48 := by
    have h1 : (11/100) * ((1/Real.pi)*C) ≤ (11/100) * ((50/157) * ((3/2)*X + 2*Y + 67/5)) :=
      mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_right hinv hCnn).trans
        (mul_le_mul_of_nonneg_left hC (by norm_num))) (by norm_num)
    refine h1.trans ?_
    have hc1 : ((11/100 : ℝ) * (50/157)) * (3/2) ≤ 0.06 := by norm_num
    have hc2 : ((11/100 : ℝ) * (50/157)) * 2 ≤ 0.08 := by norm_num
    have hd : ((11/100 : ℝ) * (50/157)) * (67/5) ≤ 0.48 := by norm_num
    nlinarith [mul_le_mul_of_nonneg_right hc1 hX, mul_le_mul_of_nonneg_right hc2 hY, hd]
  have hP' : (303/100) * ((1/Real.pi)*P) ≤ 0.97*X + 0.97*Y + 1.09 := by
    have h1 : (303/100) * ((1/Real.pi)*P) ≤ (303/100) * ((50/157) * (X + Y + 9/8)) :=
      mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_right hinv hPnn).trans
        (mul_le_mul_of_nonneg_left hP (by norm_num))) (by norm_num)
    refine h1.trans ?_
    have hc : ((303/100 : ℝ) * (50/157)) ≤ 0.97 := by norm_num
    have hd : ((303/100 : ℝ) * (50/157)) * (9/8) ≤ 1.09 := by norm_num
    nlinarith [mul_le_mul_of_nonneg_right hc (by linarith : (0:ℝ) ≤ X + Y + 9/8), hd]
  have hA' : (2/3)*A ≤ (1/6)*X + (1/6)*Y + (7/6) := by
    nlinarith [mul_le_mul_of_nonneg_left hA (by norm_num : (0:ℝ) ≤ 2/3)]
  have hQ' : (1/2)*Q ≤ (1/8)*X + (1/8)*Y + 1.23 := by
    nlinarith [mul_le_mul_of_nonneg_left hQ (by norm_num : (0:ℝ) ≤ 1/2)]
  have hlog4 : Real.log 4 ≤ 1.4 := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]; ring
    rw [h4]; linarith [Real.log_two_lt_d9]
  linarith [hA', hB', hC', hP', hQ', hlog4]

/-!
## The target theorem
-/

theorem completedL_circleExcess_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) (T₀ : ℝ) :
    Real.circleAverage (fun z : ℂ => Real.log ‖DirichletCharacter.completedLFunction χ z‖)
        ((2 : ℂ) + Complex.I * (T₀ : ℂ)) 5 -
      Real.log ‖DirichletCharacter.completedLFunction χ ((2 : ℂ) + Complex.I * (T₀ : ℂ))‖ ≤
      (3 / 2) * (Real.log (N : ℝ) + Real.log (2 + |T₀| + 2)) + 6 := by
  have hN2 : 2 ≤ N := by
    have h0 : N ≠ 0 := NeZero.ne N
    have h1 : N ≠ 1 := ne_one_of_char_ne_one hχ
    omega
  set X := Real.log (N : ℝ) with hXdef
  set Y := Real.log (|T₀| + 4) with hYdef
  have hX : 0 ≤ X := by
    rw [hXdef]
    exact Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N))
  have hY : 0 ≤ Y := by rw [hYdef]; exact Real.log_nonneg (by linarith [abs_nonneg T₀])
  have hAb := circleA_le N hN2 T₀
  rw [← hXdef, ← hYdef] at hAb
  have hBb := circleB_le N T₀
  rw [← hXdef, ← hYdef] at hBb
  have hCb := circleC_le N T₀
  rw [← hXdef, ← hYdef] at hCb
  have hPb := circleP_le N T₀
  rw [← hXdef, ← hYdef] at hPb
  have hQb := circleQ_le N hN2 T₀
  rw [← hXdef, ← hYdef] at hQb
  have harith := circleUB_arith (circleA N T₀) (circleB N T₀) (circleC N T₀) (circleP N T₀)
    (Real.log 2 + circleA N T₀) X Y hX hY (circleB_nonneg N T₀) (circleC_nonneg N T₀)
    (circleP_nonneg N T₀) hAb hBb hCb hPb hQb
  have hlog4 : Real.log 4 ≤ 1.4 := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]; ring
    rw [h4]; linarith [Real.log_two_lt_d9]
  set a : ℂ := (2 : ℂ) + Complex.I * (T₀ : ℂ) with ha
  have hare : a.re = 2 := by rw [ha]; simp
  have haim : a.im = T₀ := by rw [ha]; simp
  have hLlow : (1:ℝ)/4 ≤ ‖LFunction χ a‖ := by
    have h := L_lower_re_two_explicit χ hχ T₀
    rw [← ha] at h
    exact h
  have hlogL : -Real.log ‖LFunction χ a‖ ≤ Real.log 4 := by
    have hpos : 0 < ‖LFunction χ a‖ := lt_of_lt_of_le (by norm_num) hLlow
    have h := Real.log_le_log (by norm_num : (0:ℝ) < 1/4) hLlow
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one, zero_sub] at h
    linarith
  have hstep : Real.circleAverage (fun z : ℂ => Real.log ‖LFunction χ z‖) a 5
      - Real.log ‖LFunction χ a‖ ≤ (3/2)*(X + Y) + 6 := by
    by_cases hInt : CircleIntegrable (fun z : ℂ => Real.log ‖LFunction χ z‖) a 5
    · have hpoint : ∀ z ∈ Metric.sphere a |(5:ℝ)|,
          Real.log ‖LFunction χ z‖ ≤ circleUBσ N T₀ z.re := by
        intro z hz
        have hdist : dist z a = 5 := by
          rw [Metric.mem_sphere] at hz
          rw [hz]; norm_num
        have hnorm5 : ‖z - a‖ = 5 := by
          rw [dist_eq_norm] at hdist
          exact hdist
        refine LFunction_log_le_circleUBσ χ hχ hχprim T₀ ?_ ?_
        · have h1 : |(z - a).re| ≤ ‖z - a‖ := Complex.abs_re_le_norm _
          rw [Complex.sub_re, hnorm5] at h1
          have h2 := (abs_le.mp h1).1
          rw [hare] at h2
          linarith
        · have h1 : |(z - a).im| ≤ ‖z - a‖ := Complex.abs_im_le_norm _
          rw [Complex.sub_im, hnorm5] at h1
          have h2 := abs_le.mp h1
          rw [haim] at h2
          rw [abs_le]
          constructor
          · linarith [h2.1, neg_le_abs T₀]
          · linarith [h2.2, le_abs_self T₀]
      have hmono := Real.circleAverage_mono hInt (circleIntegrable_circleUB N T₀ a hare) hpoint
      have hca := circleAverage_circleUB N T₀ a hare
      have hint := integral_circleUB_le N T₀
      have hfin : Real.circleAverage (fun z : ℂ => circleUBσ N T₀ z.re) a 5 + Real.log 4
          ≤ (3/2)*(X + Y) + 6 := by
        rw [hca]
        have h2 := mul_le_mul_of_nonneg_left hint (by positivity : (0:ℝ) ≤ 1/Real.pi)
        linarith [harith, h2]
      linarith [hmono, hlogL]
    · have hzero : Real.circleAverage (fun z : ℂ => Real.log ‖LFunction χ z‖) a 5 = 0 := by
        rw [Real.circleAverage_def, intervalIntegral.integral_undef hInt]
        simp
      rw [hzero]
      linarith [hlogL, hX, hY, hlog4]
  have hmain := circleExcess_le_L_excess χ hχ hχprim T₀
  rw [← ha] at hmain
  have htot : Real.circleAverage (fun z : ℂ => Real.log ‖completedLFunction χ z‖) a 5
      - Real.log ‖completedLFunction χ a‖ ≤ (3/2)*(X + Y) + 6 := by
    linarith [hmain, hstep]
  have hYeq : Y = Real.log (2 + |T₀| + 2) := by
    rw [hYdef]; congr 1; ring
  rw [hXdef, hYeq] at htot
  exact htot


end Commons.NumberTheory.DirichletCharacter

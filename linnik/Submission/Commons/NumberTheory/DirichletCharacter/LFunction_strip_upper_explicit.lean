import Mathlib
import Submission.Commons.Analysis.SpecialFunctions.Gamma.gamma_vertical_exp_decay_explicit
import Submission.Commons.Analysis.SpecialFunctions.Gamma.gammaR_real_growth
import Submission.Commons.Analysis.SpecialFunctions.Gamma.norm_Gamma_lower_strip
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_critical_poly
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_norm_half_plane
import Submission.Commons.NumberTheory.DirichletCharacter.rootNumber_norm_eq_one

open Complex DirichletCharacter Filter
open scoped Real Topology

set_option maxHeartbeats 0


namespace Commons.NumberTheory.DirichletCharacter

private noncomputable def Cg : ℝ := (32/5) * Real.exp 1 * (Real.pi / 2)

private lemma Cg_pos : 0 < Cg := by rw [Cg]; positivity

private lemma sinh_abs_im_le_norm_sin (z : ℂ) : Real.sinh |z.im| ≤ ‖Complex.sin z‖ := by
  have hform : Complex.sin z = (Complex.exp (-(z * Complex.I)) - Complex.exp (z * Complex.I)) * Complex.I / 2 := by
    simp [Complex.sin]
  have hE1 : ‖Complex.exp (-(z * Complex.I))‖ = Real.exp z.im := by
    rw [Complex.norm_exp]; simp [Complex.mul_re]
  have hE2 : ‖Complex.exp (z * Complex.I)‖ = Real.exp (-z.im) := by
    rw [Complex.norm_exp]; simp [Complex.mul_re]
  have htri : |‖Complex.exp (-(z * Complex.I))‖ - ‖Complex.exp (z * Complex.I)‖|
      ≤ ‖Complex.exp (-(z * Complex.I)) - Complex.exp (z * Complex.I)‖ :=
    abs_norm_sub_norm_le _ _
  rw [hE1, hE2] at htri
  have habs : |Real.exp z.im - Real.exp (-z.im)| = 2 * Real.sinh |z.im| := by
    have h1 : Real.exp z.im - Real.exp (-z.im) = 2 * Real.sinh z.im := by
      rw [Real.sinh_eq]; ring
    rw [h1, abs_mul, Real.abs_sinh]; norm_num
  have key : 2 * Real.sinh |z.im| ≤ ‖Complex.exp (-(z * Complex.I)) - Complex.exp (z * Complex.I)‖ :=
    calc 2 * Real.sinh |z.im| = |Real.exp z.im - Real.exp (-z.im)| := habs.symm
      _ ≤ _ := htri
  rw [hform, norm_div, norm_mul, norm_I, mul_one, Complex.norm_ofNat]
  linarith

private lemma sinh_abs_im_le_norm_cos (z : ℂ) : Real.sinh |z.im| ≤ ‖Complex.cos z‖ := by
  have hform : Complex.cos z = (Complex.exp (z * Complex.I) + Complex.exp (-(z * Complex.I))) / 2 := by
    simp [Complex.cos]
  have hE1 : ‖Complex.exp (-(z * Complex.I))‖ = Real.exp z.im := by
    rw [Complex.norm_exp]; simp [Complex.mul_re]
  have hE2 : ‖Complex.exp (z * Complex.I)‖ = Real.exp (-z.im) := by
    rw [Complex.norm_exp]; simp [Complex.mul_re]
  have htri : |‖Complex.exp (-(z * Complex.I))‖ - ‖Complex.exp (z * Complex.I)‖|
      ≤ ‖Complex.exp (z * Complex.I) + Complex.exp (-(z * Complex.I))‖ := by
    have h := abs_norm_sub_norm_le (-(Complex.exp (z * Complex.I))) (Complex.exp (-(z * Complex.I)))
    have h' : |‖Complex.exp (-(z * Complex.I))‖ - ‖Complex.exp (z * Complex.I)‖| ≤
        ‖-(Complex.exp (z * Complex.I)) - Complex.exp (-(z * Complex.I))‖ := by
      simpa [abs_sub_comm] using h
    have h'' : ‖-(Complex.exp (z * Complex.I)) - Complex.exp (-(z * Complex.I))‖ =
        ‖Complex.exp (z * Complex.I) + Complex.exp (-(z * Complex.I))‖ := by
      rw [← norm_neg]; congr 1; ring
    rwa [h''] at h'
  rw [hE1, hE2] at htri
  have habs : |Real.exp z.im - Real.exp (-z.im)| = 2 * Real.sinh |z.im| := by
    have h1 : Real.exp z.im - Real.exp (-z.im) = 2 * Real.sinh z.im := by
      rw [Real.sinh_eq]; ring
    rw [h1, abs_mul, Real.abs_sinh]; norm_num
  have key : 2 * Real.sinh |z.im| ≤ ‖Complex.exp (z * Complex.I) + Complex.exp (-(z * Complex.I))‖ :=
    calc 2 * Real.sinh |z.im| = |Real.exp z.im - Real.exp (-z.im)| := habs.symm
      _ ≤ _ := htri
  rw [hform, norm_div, Complex.norm_ofNat]
  linarith

private lemma quarter_exp_le_sinh {s : ℝ} (hs : 1 ≤ s) : (1/4) * Real.exp s ≤ Real.sinh s := by
  have h4 : (4:ℝ) ≤ Real.exp (2 * s) := by
    have h2 : Real.exp (2:ℝ) = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    have h1 : (2:ℝ) < Real.exp 1 := Real.exp_one_gt_two
    have hes : Real.exp (2:ℝ) ≤ Real.exp (2 * s) := Real.exp_le_exp.mpr (by linarith)
    nlinarith [Real.exp_pos 1]
  rw [Real.sinh_eq]
  have hexp : Real.exp (2*s) = Real.exp s * Real.exp s := by
    have hss : (2:ℝ) * s = s + s := by ring
    rw [hss, Real.exp_add]
  have key : (2:ℝ) ≤ Real.exp s * Real.exp s := by rw [← hexp]; linarith
  have hdiv : 2 / Real.exp s ≤ Real.exp s := by
    rw [div_le_iff₀ (Real.exp_pos s)]; exact key
  have hdiv' : 2 * (Real.exp s)⁻¹ ≤ Real.exp s := by simpa [div_eq_mul_inv] using hdiv
  have hgoal : (1/4) * Real.exp s ≤ (Real.exp s - Real.exp (-s)) / 2 := by
    rw [Real.exp_neg]
    have h2 : (Real.exp s)⁻¹ ≤ Real.exp s / 2 := by linarith
    linarith
  linarith [hgoal]

private lemma norm_sin_pi_le (u t : ℝ) :
    ‖Complex.sin ((Real.pi : ℂ) * ((u : ℂ) + Complex.I * (t : ℂ)))‖ ≤ Real.exp (Real.pi * |t|) := by
  have harg : (Real.pi : ℂ) * ((u : ℂ) + Complex.I * (t : ℂ)) =
      ((Real.pi * u : ℝ) : ℂ) + Complex.I * ((Real.pi * t : ℝ) : ℂ) := by
    rw [Complex.ofReal_mul, Complex.ofReal_mul]; ring
  rw [harg]
  have h := Commons.Analysis.SpecialFunctions.Gamma.norm_sin_le_exp_abs_im
    (((Real.pi * u : ℝ) : ℂ) + Complex.I * ((Real.pi * t : ℝ) : ℂ))
  have him : (((Real.pi * u : ℝ) : ℂ) + Complex.I * ((Real.pi * t : ℝ) : ℂ)).im = Real.pi * t := by
    simp [Complex.add_im, Complex.mul_im]
  rw [him, abs_mul, abs_of_nonneg (le_of_lt Real.pi_pos)] at h
  exact h

private lemma gamma_uniform_upper (u t : ℝ) (hu1 : (7/8 : ℝ) ≤ u) (hu2 : u ≤ 1) :
    ‖Complex.Gamma ((u : ℂ) + Complex.I * (t : ℂ))‖ ≤
      Cg * (1 + |t|) * Real.exp (-(Real.pi / 2) * |t|) := by
  have hσ : 0 < u := by linarith
  have hexp := Commons.Analysis.SpecialFunctions.Gamma.gamma_vertical_exp_decay_explicit u hσ t
  have hΓu : Real.Gamma u ≤ 32/5 :=
    Commons.Analysis.SpecialFunctions.Gamma.real_gamma_le_thirtytwo_fifths (by linarith) hu2
  have hpi1 : (1:ℝ) ≤ Real.pi / 2 := by linarith [Real.two_le_pi]
  have hpipow : (Real.pi / 2) ^ u ≤ Real.pi / 2 := by
    have := Real.rpow_le_rpow_of_exponent_le hpi1 hu2; simpa using this
  have ht1 : (1:ℝ) ≤ 1 + |t| := by linarith [abs_nonneg t]
  have htpow : (1 + |t|) ^ u ≤ (1 + |t|) := by
    have := Real.rpow_le_rpow_of_exponent_le ht1 hu2; simpa using this
  have hpipos : 0 < (Real.pi / 2) ^ u := Real.rpow_pos_of_pos (by linarith) u
  have htpos : 0 < (1 + |t|) ^ u := Real.rpow_pos_of_pos (by linarith) u
  have hg0 : 0 ≤ Real.Gamma u := le_of_lt (Real.Gamma_pos_of_pos hσ)
  have hE : 0 < Real.exp (-(Real.pi / 2) * |t|) := Real.exp_pos _
  have hmid : Real.Gamma u * (Real.pi / 2) ^ u * (1 + |t|) ^ u ≤ (32/5) * (Real.pi / 2) * (1 + |t|) := by
    have h1 : Real.Gamma u * (Real.pi / 2) ^ u ≤ (32/5) * (Real.pi / 2) :=
      mul_le_mul hΓu hpipow (le_of_lt hpipos) (by positivity)
    exact mul_le_mul h1 htpow (le_of_lt htpos) (by positivity)
  calc ‖Complex.Gamma ((u : ℂ) + Complex.I * (t : ℂ))‖
      ≤ Real.Gamma u * Real.exp 1 * (Real.pi / 2) ^ u * (1 + |t|) ^ u *
          Real.exp (-(Real.pi / 2) * |t|) := hexp
    _ = Real.exp 1 * (Real.Gamma u * (Real.pi / 2) ^ u * (1 + |t|) ^ u) *
          Real.exp (-(Real.pi / 2) * |t|) := by ring
    _ ≤ Real.exp 1 * ((32/5) * (Real.pi / 2) * (1 + |t|)) *
          Real.exp (-(Real.pi / 2) * |t|) := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmid (le_of_lt (Real.exp_pos 1))) (le_of_lt hE)
    _ = Cg * (1 + |t|) * Real.exp (-(Real.pi / 2) * |t|) := by
        rw [Cg]; ring

private lemma gamma_band_lower (u t : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1/8) (ht : 1 ≤ |t|) :
    (Real.pi / Cg) * (1 + |t|) ^ (-1 : ℝ) * Real.exp (-(Real.pi / 2) * |t|) ≤
      ‖Complex.Gamma ((u : ℂ) + Complex.I * (t : ℂ))‖ := by
  have ht0 : t ≠ 0 := by intro h; rw [h] at ht; norm_num at ht
  have him_ne : (Real.pi * ((u : ℂ) + Complex.I * (t : ℂ))).im ≠ 0 := by
    have : (Real.pi * ((u : ℂ) + Complex.I * (t : ℂ))).im = Real.pi * t := by
      simp [Complex.mul_im]
    rw [this]; exact mul_ne_zero (ne_of_gt Real.pi_pos) ht0
  have hsin_ne : Complex.sin (Real.pi * ((u : ℂ) + Complex.I * (t : ℂ))) ≠ 0 :=
    Commons.Analysis.SpecialFunctions.Gamma.sin_ne_zero_of_im_ne_zero him_ne
  have hΓw : Complex.Gamma ((u : ℂ) + Complex.I * (t : ℂ)) ≠ 0 := by
    refine Complex.Gamma_ne_zero (fun m hm => ?_)
    have him := congrArg Complex.im hm
    simp at him
    exact ht0 him
  have hΓ1w : Complex.Gamma ((1 : ℂ) - ((u : ℂ) + Complex.I * (t : ℂ))) ≠ 0 := by
    refine Complex.Gamma_ne_zero (fun m hm => ?_)
    have him := congrArg Complex.im hm
    simp at him
    exact ht0 (by linarith [him])
  have hrefl := Complex.Gamma_mul_Gamma_one_sub ((u : ℂ) + Complex.I * (t : ℂ))
  have hprod : ‖Complex.Gamma ((u : ℂ) + Complex.I * (t : ℂ))‖ *
      ‖Complex.Gamma ((1 : ℂ) - ((u : ℂ) + Complex.I * (t : ℂ)))‖ =
      Real.pi / ‖Complex.sin (Real.pi * ((u : ℂ) + Complex.I * (t : ℂ)))‖ := by
    have := congrArg norm hrefl
    rw [norm_mul, norm_div] at this
    rw [Complex.norm_of_nonneg (le_of_lt Real.pi_pos)] at this
    exact this
  have hΓ1 : ‖Complex.Gamma ((1 : ℂ) - ((u : ℂ) + Complex.I * (t : ℂ)))‖ ≤
      Cg * (1 + |t|) * Real.exp (-(Real.pi / 2) * |t|) := by
    have harg : (1 : ℂ) - ((u : ℂ) + Complex.I * (t : ℂ)) =
        (((1 - u : ℝ)) : ℂ) + Complex.I * ((-t : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    rw [harg]
    have := gamma_uniform_upper (1-u) (-t) (by linarith) (by linarith)
    rwa [abs_neg] at this
  have hsin : ‖Complex.sin (Real.pi * ((u : ℂ) + Complex.I * (t : ℂ)))‖ ≤ Real.exp (Real.pi * |t|) :=
    norm_sin_pi_le u t
  have hsinpos : 0 < ‖Complex.sin (Real.pi * ((u : ℂ) + Complex.I * (t : ℂ)))‖ :=
    norm_pos_iff.mpr hsin_ne
  have hpi : Real.pi = ‖Complex.Gamma ((u : ℂ) + Complex.I * (t : ℂ))‖ *
      ‖Complex.Gamma ((1 : ℂ) - ((u : ℂ) + Complex.I * (t : ℂ)))‖ *
      ‖Complex.sin (Real.pi * ((u : ℂ) + Complex.I * (t : ℂ)))‖ := by
    rw [hprod, div_mul_cancel₀ Real.pi (ne_of_gt hsinpos)]
  have hexp2 : Real.exp (-(Real.pi / 2) * |t|) * Real.exp (Real.pi * |t|) ≤
      Real.exp (Real.pi * |t| / 2) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    nlinarith [abs_nonneg t]
  have hstep1 : ‖Complex.Gamma ((u : ℂ) + Complex.I * (t : ℂ))‖ *
      ‖Complex.Gamma ((1 : ℂ) - ((u : ℂ) + Complex.I * (t : ℂ)))‖ ≤
      ‖Complex.Gamma ((u : ℂ) + Complex.I * (t : ℂ))‖ *
        (Cg * (1 + |t|) * Real.exp (-(Real.pi / 2) * |t|)) :=
    mul_le_mul_of_nonneg_left hΓ1 (norm_nonneg _)
  have h1 : Real.pi ≤ ‖Complex.Gamma ((u : ℂ) + Complex.I * (t : ℂ))‖ *
      (Cg * (1 + |t|) * Real.exp (-(Real.pi / 2) * |t|)) * Real.exp (Real.pi * |t|) := by
    have hb : 0 ≤ ‖Complex.Gamma ((u : ℂ) + Complex.I * (t : ℂ))‖ *
        (Cg * (1 + |t|) * Real.exp (-(Real.pi / 2) * |t|)) :=
      mul_nonneg (norm_nonneg _) (mul_nonneg (mul_nonneg (le_of_lt Cg_pos)
        (by linarith [abs_nonneg t])) (le_of_lt (Real.exp_pos _)))
    calc Real.pi = ‖Complex.Gamma ((u : ℂ) + Complex.I * (t : ℂ))‖ *
          ‖Complex.Gamma ((1 : ℂ) - ((u : ℂ) + Complex.I * (t : ℂ)))‖ *
          ‖Complex.sin (Real.pi * ((u : ℂ) + Complex.I * (t : ℂ)))‖ := hpi
      _ ≤ ‖Complex.Gamma ((u : ℂ) + Complex.I * (t : ℂ))‖ *
          (Cg * (1 + |t|) * Real.exp (-(Real.pi / 2) * |t|)) * Real.exp (Real.pi * |t|) :=
          mul_le_mul hstep1 hsin (norm_nonneg _) hb
  have h2 : ‖Complex.Gamma ((u : ℂ) + Complex.I * (t : ℂ))‖ *
      (Cg * (1 + |t|) * Real.exp (-(Real.pi / 2) * |t|)) * Real.exp (Real.pi * |t|) =
      ‖Complex.Gamma ((u : ℂ) + Complex.I * (t : ℂ))‖ *
        (Cg * (1 + |t|) * (Real.exp (-(Real.pi / 2) * |t|) * Real.exp (Real.pi * |t|))) := by ring
  have hmid : Real.pi ≤ ‖Complex.Gamma ((u : ℂ) + Complex.I * (t : ℂ))‖ *
      (Cg * (1 + |t|) * Real.exp (Real.pi * |t| / 2)) := by
    rw [h2] at h1
    have hb : 0 ≤ ‖Complex.Gamma ((u : ℂ) + Complex.I * (t : ℂ))‖ := norm_nonneg _
    have hbnd : Cg * (1 + |t|) * (Real.exp (-(Real.pi / 2) * |t|) * Real.exp (Real.pi * |t|)) ≤
        Cg * (1 + |t|) * Real.exp (Real.pi * |t| / 2) :=
      mul_le_mul_of_nonneg_left hexp2
        (mul_nonneg (le_of_lt Cg_pos) (by linarith [abs_nonneg t]))
    exact le_trans h1 (mul_le_mul_of_nonneg_left hbnd hb)
  have hD : 0 < Cg * (1 + |t|) * Real.exp (Real.pi * |t| / 2) :=
    mul_pos (mul_pos Cg_pos (by linarith [abs_nonneg t])) (Real.exp_pos _)
  have hfin : Real.pi / (Cg * (1 + |t|) * Real.exp (Real.pi * |t| / 2)) ≤
      ‖Complex.Gamma ((u : ℂ) + Complex.I * (t : ℂ))‖ :=
    (div_le_iff₀ hD).mpr hmid
  have heq : (Real.pi / Cg) * (1 + |t|) ^ (-1 : ℝ) * Real.exp (-(Real.pi / 2) * |t|) =
      Real.pi / (Cg * (1 + |t|) * Real.exp (Real.pi * |t| / 2)) := by
    rw [Real.rpow_neg_one]
    have hEp : Real.exp (-(Real.pi / 2) * |t|) = (Real.exp (Real.pi * |t| / 2))⁻¹ := by
      rw [← Real.exp_neg]; congr 1; ring
    rw [hEp]
    have h10 : (1 + |t|) ≠ 0 := by positivity
    have hCgne : Cg ≠ 0 := ne_of_gt Cg_pos
    have hEne : Real.exp (Real.pi * |t| / 2) ≠ 0 := (Real.exp_pos _).ne'
    field_simp
  rw [heq]
  exact hfin

end Commons.NumberTheory.DirichletCharacter

namespace Commons.NumberTheory.DirichletCharacter

private lemma norm_two_cpow (w : ℂ) : ‖(2:ℂ) ^ w‖ = (2:ℝ) ^ w.re := by
  rw [show (2:ℂ) = ((2:ℝ):ℂ) from rfl, Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0:ℝ) < 2)]

/-- Duplication lower bound: `‖Γ(2z)‖ ≤ ‖Γ z‖·‖Γ(1/2+z)‖` when `Re z ≤ 1/2`. -/
private lemma gamma_dup_lower (z : ℂ) (hz : z.re ≤ 1/2) :
    ‖Complex.Gamma (2*z)‖ ≤ ‖Complex.Gamma z‖ * ‖Complex.Gamma (1/2 + z)‖ := by
  have h := congrArg (fun w : ℂ => ‖w‖) (Complex.Gamma_mul_Gamma_add_half z)
  have heq : z + 1/2 = 1/2 + z := by ring
  rw [heq] at h
  simp only [norm_mul] at h
  rw [Complex.norm_of_nonneg (Real.sqrt_nonneg _)] at h
  rw [norm_two_cpow] at h
  have h1 : (1:ℝ) ≤ Real.sqrt Real.pi := by rw [Real.one_le_sqrt]; linarith [Real.two_le_pi]
  have hrez : (1 - 2*z).re = 1 - 2*z.re := by
    rw [Complex.sub_re, Complex.mul_re, Complex.one_re]; simp
  have h2 : (1:ℝ) ≤ (2:ℝ) ^ (1 - 2*z).re := by
    have h0 : (0:ℝ) ≤ (1 - 2*z).re := by rw [hrez]; linarith
    calc (1:ℝ) = (2:ℝ) ^ (0:ℝ) := by rw [Real.rpow_zero]
      _ ≤ (2:ℝ) ^ (1 - 2*z).re := Real.rpow_le_rpow_of_exponent_le (by norm_num) h0
  have hprod : (1:ℝ) ≤ Real.sqrt Real.pi * (2:ℝ) ^ (1 - 2*z).re := by
    simpa using mul_le_mul h1 h2 (by norm_num) (by linarith)
  rw [h]
  calc ‖Complex.Gamma (2*z)‖ = ‖Complex.Gamma (2*z)‖ * 1 := (mul_one _).symm
    _ ≤ ‖Complex.Gamma (2*z)‖ * (Real.sqrt Real.pi * (2:ℝ) ^ (1 - 2*z).re) :=
        mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ = ‖Complex.Gamma (2*z)‖ * (2:ℝ) ^ (1 - 2*z).re * Real.sqrt Real.pi := by ring

/-- Reflection at `1/2 + z` (even case). -/
private lemma gamma_refl_even (z : ℂ) :
    ‖Complex.Gamma (1/2 + z)‖ * ‖Complex.Gamma (1/2 - z)‖ = Real.pi / ‖Complex.cos (Real.pi * z)‖ := by
  have hh := Complex.Gamma_mul_Gamma_one_sub (1/2 + z)
  have heq1 : (1:ℂ) - (1/2 + z) = 1/2 - z := by ring
  have heq2 : Complex.sin (Real.pi * (1/2 + z)) = Complex.cos (Real.pi * z) := by
    have harg : Real.pi * (1/2 + z) = Real.pi/2 + Real.pi*z := by ring
    rw [harg, Complex.sin_add, Complex.sin_pi_div_two, Complex.cos_pi_div_two]
    ring
  rw [heq1, heq2] at hh
  have := congrArg norm hh
  rw [norm_mul, norm_div, Complex.norm_of_nonneg (le_of_lt Real.pi_pos)] at this
  exact this

/-- Reflection at `z` (odd case). -/
private lemma gamma_refl_odd {z : ℂ} :
    ‖Complex.Gamma z‖ * ‖Complex.Gamma (1 - z)‖ = Real.pi / ‖Complex.sin (Real.pi * z)‖ := by
  have hh := Complex.Gamma_mul_Gamma_one_sub z
  have := congrArg norm hh
  rw [norm_mul, norm_div, Complex.norm_of_nonneg (le_of_lt Real.pi_pos)] at this
  exact this

end Commons.NumberTheory.DirichletCharacter

namespace Commons.NumberTheory.DirichletCharacter

private lemma gammaR_even_ratio (σ T : ℝ) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1 / 8) (hT : 1 ≤ |T|) :
    ‖Complex.Gammaℝ (1 - ((σ : ℂ) + Complex.I * (T : ℂ))) /
        Complex.Gammaℝ ((σ : ℂ) + Complex.I * (T : ℂ))‖ ≤ 4 * Cg * (1 + |T|) := by
  set s : ℂ := (σ : ℂ) + Complex.I * (T : ℂ) with hs
  have hsre : s.re = σ := by rw [hs]; simp
  have hsim : s.im = T := by rw [hs]; simp
  have hT0 : T ≠ 0 := by intro h; rw [h] at hT; norm_num at hT
  set z : ℂ := s / 2 with hz
  have hzre : z.re = σ / 2 := by rw [hz, Complex.div_re, hsre, hsim]; simp; ring
  have hzim : z.im = T / 2 := by rw [hz, Complex.div_im, hsre, hsim]; simp; ring
  have hzre_le : z.re ≤ 1/2 := by rw [hzre]; linarith
  have h2zs : 2 * z = s := by rw [hz]; ring
  have h2zs' : (2:ℂ) * z = s := by rw [hz]; ring
  have hΓz : Complex.Gamma z ≠ 0 := by
    refine Complex.Gamma_ne_zero (fun m hm => ?_)
    have h := congrArg Complex.im hm; simp at h
    have hz0 : z.im = 0 := h
    rw [hzim] at hz0; exact (div_ne_zero hT0 two_ne_zero) hz0
  have hzim0 : z.im ≠ 0 := by rw [hzim]; exact div_ne_zero hT0 two_ne_zero
  have hΓhz : Complex.Gamma (1/2 + z) ≠ 0 := by
    refine Complex.Gamma_ne_zero (fun m hm => ?_)
    have h := congrArg Complex.im hm; simp at h
    exact hzim0 h
  have hΓs : Complex.Gamma s ≠ 0 := by
    refine Complex.Gamma_ne_zero (fun m hm => ?_)
    have h := congrArg Complex.im hm; simp [hsim] at h; exact hT0 h
  -- cos lower bound
  have hcos : (1/4) * Real.exp (Real.pi * |T| / 2) ≤ ‖Complex.cos (Real.pi * z)‖ := by
    have h1 := sinh_abs_im_le_norm_cos (Real.pi * z)
    have him : (Real.pi * z).im = Real.pi * (T/2) := by
      rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hzim]; ring
    have habs : |(Real.pi * z).im| = Real.pi * |T| / 2 := by
      rw [him, abs_mul, abs_of_nonneg (le_of_lt Real.pi_pos), abs_div]; norm_num; ring
    rw [habs] at h1
    have h2 : (1/4) * Real.exp (Real.pi * |T| / 2) ≤ Real.sinh (Real.pi * |T| / 2) := by
      apply quarter_exp_le_sinh
      rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2)]
      nlinarith [hT, Real.two_le_pi]
    linarith [h1, h2]
  have hcospos : 0 < ‖Complex.cos (Real.pi * z)‖ := lt_of_lt_of_le (by positivity) hcos
  -- gamma_band_lower at s
  have hg : (Real.pi / Cg) * (1 + |T|) ^ (-1 : ℝ) * Real.exp (-(Real.pi / 2) * |T|) ≤
      ‖Complex.Gamma s‖ := by
    have h := gamma_band_lower σ T hσ0 hσ1 hT
    rw [← hs] at h; exact h
  have hΓ2z : ‖Complex.Gamma s‖ = ‖Complex.Gamma (2*z)‖ := by rw [h2zs]
  -- numeric inequality
  have hnum : Real.pi / ‖Complex.cos (Real.pi * z)‖ ≤ (4 * Cg * (1 + |T|)) * ‖Complex.Gamma (2*z)‖ := by
    have hA : Real.pi / ‖Complex.cos (Real.pi * z)‖ ≤ 4 * Real.pi * Real.exp (-(Real.pi / 2) * |T|) := by
      rw [div_le_iff₀ hcospos]
      have h1 : (4 * Real.pi * Real.exp (-(Real.pi / 2) * |T|)) * ((1/4) * Real.exp (Real.pi * |T| / 2))
          ≤ (4 * Real.pi * Real.exp (-(Real.pi / 2) * |T|)) * ‖Complex.cos (Real.pi * z)‖ :=
        mul_le_mul_of_nonneg_left hcos (by positivity)
      have he : (4 * Real.pi * Real.exp (-(Real.pi / 2) * |T|)) * ((1/4) * Real.exp (Real.pi * |T| / 2))
          = Real.pi := by
        have hExp : Real.exp (-(Real.pi / 2) * |T|) * Real.exp (Real.pi * |T| / 2) = 1 := by
          rw [← Real.exp_add, show -(Real.pi / 2) * |T| + Real.pi * |T| / 2 = 0 by ring, Real.exp_zero]
        rw [show (4 * Real.pi * Real.exp (-(Real.pi / 2) * |T|)) * ((1/4) * Real.exp (Real.pi * |T| / 2))
            = Real.pi * (Real.exp (-(Real.pi / 2) * |T|) * Real.exp (Real.pi * |T| / 2)) by ring]
        rw [hExp]; ring
      rw [he] at h1; exact h1
    have hB : 4 * Real.pi * Real.exp (-(Real.pi / 2) * |T|) ≤
        (4 * Cg * (1 + |T|)) * ‖Complex.Gamma (2*z)‖ := by
      have hge : (Real.pi / Cg) * (1 + |T|) ^ (-1 : ℝ) * Real.exp (-(Real.pi / 2) * |T|) ≤
          ‖Complex.Gamma (2*z)‖ := by rw [← hΓ2z]; exact hg
      have hstep : (4 * Cg * (1 + |T|)) * ((Real.pi / Cg) * (1 + |T|) ^ (-1 : ℝ) *
            Real.exp (-(Real.pi / 2) * |T|)) ≤
          (4 * Cg * (1 + |T|)) * ‖Complex.Gamma (2*z)‖ :=
        mul_le_mul_of_nonneg_left hge (by
          have : (0:ℝ) ≤ 1 + |T| := by linarith [abs_nonneg T]
          have : (0:ℝ) < Cg := Cg_pos
          positivity)
      have heq : (4 * Cg * (1 + |T|)) * ((Real.pi / Cg) * (1 + |T|) ^ (-1 : ℝ) *
            Real.exp (-(Real.pi / 2) * |T|)) = 4 * Real.pi * Real.exp (-(Real.pi / 2) * |T|) := by
        rw [Real.rpow_neg_one]
        have hCgne : Cg ≠ 0 := ne_of_gt Cg_pos
        have hT1 : (1 + |T|) ≠ 0 := by positivity
        field_simp
      rw [heq] at hstep; exact hstep
    exact le_trans hA hB
  -- inner bound
  have hinner : ‖Complex.Gamma (1/2 - z)‖ ≤ (4 * Cg * (1 + |T|)) * ‖Complex.Gamma z‖ := by
    have hΓhzpos : 0 < ‖Complex.Gamma (1/2 + z)‖ := norm_pos_iff.mpr hΓhz
    refine (mul_le_mul_iff_of_pos_right hΓhzpos).mp ?_
    rw [mul_comm (‖Complex.Gamma (1/2 - z)‖) (‖Complex.Gamma (1/2 + z)‖), gamma_refl_even z]
    have hdup := gamma_dup_lower z hzre_le
    have hstep1 : (4 * Cg * (1 + |T|)) * ‖Complex.Gamma (2*z)‖ ≤
        (4 * Cg * (1 + |T|)) * (‖Complex.Gamma z‖ * ‖Complex.Gamma (1/2 + z)‖) :=
      mul_le_mul_of_nonneg_left hdup (by
        have : (0:ℝ) ≤ 1 + |T| := by linarith [abs_nonneg T]
        have : (0:ℝ) < Cg := Cg_pos
        positivity)
    have hstep2 : (4 * Cg * (1 + |T|)) * (‖Complex.Gamma z‖ * ‖Complex.Gamma (1/2 + z)‖) =
        (4 * Cg * (1 + |T|) * ‖Complex.Gamma z‖) * ‖Complex.Gamma (1/2 + z)‖ := by ring
    exact le_trans hnum (le_trans hstep1 (le_of_eq hstep2))
  -- Gammaℝ conversion
  have hgnum : ‖Complex.Gammaℝ (1 - s)‖ = Real.pi ^ (-(1-σ)/2) * ‖Complex.Gamma (1/2 - z)‖ := by
    rw [Complex.Gammaℝ_def, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    have hre : (-(1 - s) / 2).re = -(1-σ)/2 := by
      rw [Complex.div_re, Complex.neg_re, Complex.sub_re, Complex.one_re, hsre]; simp; ring
    have harg : (1 - s) / 2 = 1/2 - z := by rw [hz]; ring
    rw [harg, hre]
  have hgden : ‖Complex.Gammaℝ s‖ = Real.pi ^ (-σ/2) * ‖Complex.Gamma z‖ := by
    rw [Complex.Gammaℝ_def, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    have hre : (-s / 2).re = -σ/2 := by
      rw [Complex.div_re, Complex.neg_re, hsre]; simp; ring
    have harg : s / 2 = z := by rw [hz]
    rw [harg, hre]
  rw [Complex.norm_div, hgnum, hgden]
  have hbpos : 0 < Real.pi ^ (-σ/2) * ‖Complex.Gamma z‖ :=
    mul_pos (Real.rpow_pos_of_pos Real.pi_pos _) (norm_pos_iff.mpr hΓz)
  rw [div_le_iff₀ hbpos]
  have hpi1 : (1:ℝ) ≤ Real.pi := by linarith [Real.two_le_pi]
  have h1 : Real.pi ^ (-(1-σ)/2) ≤ Real.pi ^ (-σ/2) :=
    Real.rpow_le_rpow_of_exponent_le hpi1 (by linarith)
  calc Real.pi ^ (-(1-σ)/2) * ‖Complex.Gamma (1/2 - z)‖
      ≤ Real.pi ^ (-σ/2) * ‖Complex.Gamma (1/2 - z)‖ :=
        mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ ≤ Real.pi ^ (-σ/2) * ((4 * Cg * (1 + |T|)) * ‖Complex.Gamma z‖) :=
        mul_le_mul_of_nonneg_left hinner (Real.rpow_nonneg (le_of_lt Real.pi_pos) _)
    _ = (4 * Cg * (1 + |T|)) * (Real.pi ^ (-σ/2) * ‖Complex.Gamma z‖) := by ring

end Commons.NumberTheory.DirichletCharacter

namespace Commons.NumberTheory.DirichletCharacter

private lemma gammaR_odd_ratio (σ T : ℝ) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1 / 8) (hT : 1 ≤ |T|) :
    ‖Complex.Gammaℝ (2 - ((σ : ℂ) + Complex.I * (T : ℂ))) /
        Complex.Gammaℝ (((σ : ℂ) + Complex.I * (T : ℂ)) + 1)‖ ≤ 4 * Cg * (1 + |T|) := by
  set s : ℂ := (σ : ℂ) + Complex.I * (T : ℂ) with hs
  have hsre : s.re = σ := by rw [hs]; simp
  have hsim : s.im = T := by rw [hs]; simp
  have hT0 : T ≠ 0 := by intro h; rw [h] at hT; norm_num at hT
  set z : ℂ := s / 2 with hz
  have hzre : z.re = σ / 2 := by rw [hz, Complex.div_re, hsre, hsim]; simp; ring
  have hzim : z.im = T / 2 := by rw [hz, Complex.div_im, hsre, hsim]; simp; ring
  have hzre_le : z.re ≤ 1/2 := by rw [hzre]; linarith
  have h2zs : 2 * z = s := by rw [hz]; ring
  have hzim0 : z.im ≠ 0 := by rw [hzim]; exact div_ne_zero hT0 two_ne_zero
  have hΓz : Complex.Gamma z ≠ 0 := by
    refine Complex.Gamma_ne_zero (fun m hm => ?_)
    have h := congrArg Complex.im hm; simp at h
    exact hzim0 h
  have hΓhz : Complex.Gamma (1/2 + z) ≠ 0 := by
    refine Complex.Gamma_ne_zero (fun m hm => ?_)
    have h := congrArg Complex.im hm; simp at h
    exact hzim0 h
  have hΓs : Complex.Gamma s ≠ 0 := by
    refine Complex.Gamma_ne_zero (fun m hm => ?_)
    have h := congrArg Complex.im hm; simp [hsim] at h; exact hT0 h
  -- sin lower bound
  have hsin : (1/4) * Real.exp (Real.pi * |T| / 2) ≤ ‖Complex.sin (Real.pi * z)‖ := by
    have h1 := sinh_abs_im_le_norm_sin (Real.pi * z)
    have him : (Real.pi * z).im = Real.pi * (T/2) := by
      rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hzim]; ring
    have habs : |(Real.pi * z).im| = Real.pi * |T| / 2 := by
      rw [him, abs_mul, abs_of_nonneg (le_of_lt Real.pi_pos), abs_div]; norm_num; ring
    rw [habs] at h1
    have h2 : (1/4) * Real.exp (Real.pi * |T| / 2) ≤ Real.sinh (Real.pi * |T| / 2) := by
      apply quarter_exp_le_sinh
      rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2)]
      nlinarith [hT, Real.two_le_pi]
    linarith [h1, h2]
  have hsinpos : 0 < ‖Complex.sin (Real.pi * z)‖ := lt_of_lt_of_le (by positivity) hsin
  have hg : (Real.pi / Cg) * (1 + |T|) ^ (-1 : ℝ) * Real.exp (-(Real.pi / 2) * |T|) ≤
      ‖Complex.Gamma s‖ := by
    have h := gamma_band_lower σ T hσ0 hσ1 hT
    rw [← hs] at h; exact h
  have hΓ2z : ‖Complex.Gamma s‖ = ‖Complex.Gamma (2*z)‖ := by rw [h2zs]
  have hnum : Real.pi / ‖Complex.sin (Real.pi * z)‖ ≤ (4 * Cg * (1 + |T|)) * ‖Complex.Gamma (2*z)‖ := by
    have hA : Real.pi / ‖Complex.sin (Real.pi * z)‖ ≤ 4 * Real.pi * Real.exp (-(Real.pi / 2) * |T|) := by
      rw [div_le_iff₀ hsinpos]
      have h1 : (4 * Real.pi * Real.exp (-(Real.pi / 2) * |T|)) * ((1/4) * Real.exp (Real.pi * |T| / 2))
          ≤ (4 * Real.pi * Real.exp (-(Real.pi / 2) * |T|)) * ‖Complex.sin (Real.pi * z)‖ :=
        mul_le_mul_of_nonneg_left hsin (by positivity)
      have he : (4 * Real.pi * Real.exp (-(Real.pi / 2) * |T|)) * ((1/4) * Real.exp (Real.pi * |T| / 2))
          = Real.pi := by
        have hExp : Real.exp (-(Real.pi / 2) * |T|) * Real.exp (Real.pi * |T| / 2) = 1 := by
          rw [← Real.exp_add, show -(Real.pi / 2) * |T| + Real.pi * |T| / 2 = 0 by ring, Real.exp_zero]
        rw [show (4 * Real.pi * Real.exp (-(Real.pi / 2) * |T|)) * ((1/4) * Real.exp (Real.pi * |T| / 2))
            = Real.pi * (Real.exp (-(Real.pi / 2) * |T|) * Real.exp (Real.pi * |T| / 2)) by ring]
        rw [hExp]; ring
      rw [he] at h1; exact h1
    have hB : 4 * Real.pi * Real.exp (-(Real.pi / 2) * |T|) ≤
        (4 * Cg * (1 + |T|)) * ‖Complex.Gamma (2*z)‖ := by
      have hge : (Real.pi / Cg) * (1 + |T|) ^ (-1 : ℝ) * Real.exp (-(Real.pi / 2) * |T|) ≤
          ‖Complex.Gamma (2*z)‖ := by rw [← hΓ2z]; exact hg
      have hstep : (4 * Cg * (1 + |T|)) * ((Real.pi / Cg) * (1 + |T|) ^ (-1 : ℝ) *
            Real.exp (-(Real.pi / 2) * |T|)) ≤
          (4 * Cg * (1 + |T|)) * ‖Complex.Gamma (2*z)‖ :=
        mul_le_mul_of_nonneg_left hge (by
          have : (0:ℝ) ≤ 1 + |T| := by linarith [abs_nonneg T]
          have : (0:ℝ) < Cg := Cg_pos
          positivity)
      have heq : (4 * Cg * (1 + |T|)) * ((Real.pi / Cg) * (1 + |T|) ^ (-1 : ℝ) *
            Real.exp (-(Real.pi / 2) * |T|)) = 4 * Real.pi * Real.exp (-(Real.pi / 2) * |T|) := by
        rw [Real.rpow_neg_one]
        have hCgne : Cg ≠ 0 := ne_of_gt Cg_pos
        have hT1 : (1 + |T|) ≠ 0 := by positivity
        field_simp
      rw [heq] at hstep; exact hstep
    exact le_trans hA hB
  -- inner bound
  have hinner : ‖Complex.Gamma (1 - z)‖ ≤ (4 * Cg * (1 + |T|)) * ‖Complex.Gamma (1/2 + z)‖ := by
    have hΓzpos : 0 < ‖Complex.Gamma z‖ := norm_pos_iff.mpr hΓz
    refine (mul_le_mul_iff_of_pos_right hΓzpos).mp ?_
    rw [mul_comm (‖Complex.Gamma (1 - z)‖) (‖Complex.Gamma z‖), gamma_refl_odd (z := z)]
    have hdup := gamma_dup_lower z hzre_le
    have hstep1 : (4 * Cg * (1 + |T|)) * ‖Complex.Gamma (2*z)‖ ≤
        (4 * Cg * (1 + |T|)) * (‖Complex.Gamma z‖ * ‖Complex.Gamma (1/2 + z)‖) :=
      mul_le_mul_of_nonneg_left hdup (by
        have : (0:ℝ) ≤ 1 + |T| := by linarith [abs_nonneg T]
        have : (0:ℝ) < Cg := Cg_pos
        positivity)
    have hstep2 : (4 * Cg * (1 + |T|)) * (‖Complex.Gamma z‖ * ‖Complex.Gamma (1/2 + z)‖) =
        (4 * Cg * (1 + |T|) * ‖Complex.Gamma (1/2 + z)‖) * ‖Complex.Gamma z‖ := by ring
    exact le_trans hnum (le_trans hstep1 (le_of_eq hstep2))
  -- Gammaℝ conversion
  have hgnum : ‖Complex.Gammaℝ (2 - s)‖ = Real.pi ^ (-(2-σ)/2) * ‖Complex.Gamma (1 - z)‖ := by
    rw [Complex.Gammaℝ_def, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    have hre : (-(2 - s) / 2).re = -(2-σ)/2 := by
      rw [Complex.div_re, Complex.neg_re, Complex.sub_re, hsre]; simp; ring
    have harg : (2 - s) / 2 = 1 - z := by rw [hz]; ring
    rw [harg, hre]
  have hgden : ‖Complex.Gammaℝ (s + 1)‖ = Real.pi ^ (-(σ+1)/2) * ‖Complex.Gamma (1/2 + z)‖ := by
    rw [Complex.Gammaℝ_def, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    have hre : (-(s+1) / 2).re = -(σ+1)/2 := by
      rw [Complex.div_re, Complex.neg_re, Complex.add_re, hsre]; simp; ring
    have harg : (s + 1) / 2 = 1/2 + z := by rw [hz]; ring
    rw [harg, hre]
  rw [Complex.norm_div, hgnum, hgden]
  have hbpos : 0 < Real.pi ^ (-(σ+1)/2) * ‖Complex.Gamma (1/2 + z)‖ :=
    mul_pos (Real.rpow_pos_of_pos Real.pi_pos _) (norm_pos_iff.mpr hΓhz)
  rw [div_le_iff₀ hbpos]
  have hpi1 : (1:ℝ) ≤ Real.pi := by linarith [Real.two_le_pi]
  have h1 : Real.pi ^ (-(2-σ)/2) ≤ Real.pi ^ (-(σ+1)/2) :=
    Real.rpow_le_rpow_of_exponent_le hpi1 (by linarith)
  calc Real.pi ^ (-(2-σ)/2) * ‖Complex.Gamma (1 - z)‖
      ≤ Real.pi ^ (-(σ+1)/2) * ‖Complex.Gamma (1 - z)‖ :=
        mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ ≤ Real.pi ^ (-(σ+1)/2) * ((4 * Cg * (1 + |T|)) * ‖Complex.Gamma (1/2 + z)‖) :=
        mul_le_mul_of_nonneg_left hinner (Real.rpow_nonneg (le_of_lt Real.pi_pos) _)
    _ = (4 * Cg * (1 + |T|)) * (Real.pi ^ (-(σ+1)/2) * ‖Complex.Gamma (1/2 + z)‖) := by ring

end Commons.NumberTheory.DirichletCharacter

namespace Commons.NumberTheory.DirichletCharacter


private lemma inv_ne_one_of_ne_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    χ⁻¹ ≠ 1 := by
  intro h
  apply hχ
  have hh := congrArg (fun ψ : DirichletCharacter ℂ N => ψ⁻¹) h
  simpa using hh

/-- Ratio bound for the archimedean gamma factor of any character on the band
`0 ≤ σ ≤ 1/8`, `|t| ≥ 1`, with the exponent `1` in `(1+|t|)`. -/
private lemma gammaFactor_ratio_band_left {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ T : ℝ), 0 ≤ σ → σ ≤ 1/8 → 1 ≤ |T| →
      ‖χ.gammaFactor (1 - ((σ : ℂ) + Complex.I * (T : ℂ))) /
          χ.gammaFactor ((σ : ℂ) + Complex.I * (T : ℂ))‖ ≤ C * (1 + |T|) := by
  refine ⟨4 * Cg, mul_pos (by norm_num) Cg_pos, ?_⟩
  intro σ T h0 h1 hT
  rcases χ.even_or_odd with hE | hO
  · rw [Even.gammaFactor_def hE (1 - ((σ : ℂ) + Complex.I * (T : ℂ))),
        Even.gammaFactor_def hE ((σ : ℂ) + Complex.I * (T : ℂ))]
    exact gammaR_even_ratio σ T h0 h1 hT
  · rw [Odd.gammaFactor_def hO (1 - ((σ : ℂ) + Complex.I * (T : ℂ))),
        Odd.gammaFactor_def hO ((σ : ℂ) + Complex.I * (T : ℂ))]
    have harg : 1 - ((σ : ℂ) + Complex.I * (T : ℂ)) + 1 = 2 - ((σ : ℂ) + Complex.I * (T : ℂ)) := by
      ring
    rw [harg]
    exact gammaR_odd_ratio σ T h0 h1 hT

/-- The functional-equation based bound on the left band `0 < σ ≤ 1/8`, `|T| ≥ 1`. -/
private lemma LFunction_left_band {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hχprim : χ.IsPrimitive) {Cγ : ℝ} (hCγ0 : 0 ≤ Cγ)
    (hCγ : ∀ (σ T : ℝ), 0 ≤ σ → σ ≤ 1/8 → 1 ≤ |T| →
      ‖χ.gammaFactor (1 - ((σ : ℂ) + Complex.I * (T : ℂ))) /
          χ.gammaFactor ((σ : ℂ) + Complex.I * (T : ℂ))‖ ≤ Cγ * (1 + |T|))
    (σ T : ℝ) (hσ0 : 0 < σ) (hσ1 : σ ≤ 1/8) (hT : 1 ≤ |T|) :
    ‖DirichletCharacter.LFunction χ ((σ : ℂ) + Complex.I * (T : ℂ))‖ ≤
      (16/7) * Cγ * (N : ℝ)^2 * (1 + |T|)^2 := by
  set s : ℂ := (σ : ℂ) + Complex.I * (T : ℂ) with hs
  have hsre : s.re = σ := by rw [hs]; simp
  have hsim : s.im = T := by rw [hs]; simp
  have hs0 : 0 < s.re := by rw [hsre]; exact hσ0
  have hs1 : s.re < 1 := by rw [hsre]; linarith
  have hFE := PL.AfeAssembly.LFunction_eq χ hχprim hχ hs0 hs1
  have hrinv : χ⁻¹ ≠ 1 := inv_ne_one_of_ne_one χ hχ
  have hroot : ‖χ.rootNumber‖ = 1 :=
    Commons.NumberTheory.DirichletCharacter.rootNumber_norm_eq_one χ hχprim
  have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hNnorm : ‖(N : ℂ) ^ (1/2 - s)‖ = (N : ℝ) ^ (1/2 - σ) := by
    rw [Complex.norm_natCast_cpow_of_pos hNpos]
    congr 1
    rw [Complex.sub_re, hsre]; simp
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hNpos)
  have hNle : (N : ℝ) ^ (1/2 - σ) ≤ (N : ℝ) := by
    calc (N : ℝ) ^ (1/2 - σ) ≤ (N : ℝ) ^ (1:ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
      _ = (N : ℝ) := Real.rpow_one _
  have hr : ‖χ.gammaFactor (1 - s) / χ.gammaFactor s‖ ≤ Cγ * (1 + |T|) := by
    have hrw : (1 - s) = 1 - ((σ : ℂ) + Complex.I * (T : ℂ)) := by rw [hs]
    rw [hrw, hs]
    exact hCγ σ T (le_of_lt hσ0) hσ1 hT
  have h1s_re : 0 < (1 - s).re := by rw [Complex.sub_re, Complex.one_re, hsre]; linarith
  have hnorm1s : ‖(1:ℂ) - s‖ ≤ 1 + |T| := by
    have h := Complex.norm_le_abs_re_add_abs_im ((1:ℂ) - s)
    have hre : ((1:ℂ) - s).re = 1 - σ := by rw [Complex.sub_re, Complex.one_re, hsre]
    have him : ((1:ℂ) - s).im = -T := by rw [Complex.sub_im, Complex.one_im, hsim]; ring
    rw [hre, him, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - σ), abs_neg] at h
    linarith
  have hL1s : ‖DirichletCharacter.LFunction (χ⁻¹) ((1:ℂ) - s)‖ ≤
      (16/7) * (N : ℝ) * (1 + |T|) := by
    have h := Commons.NumberTheory.DirichletCharacter.LFunction_norm_half_plane (χ := χ⁻¹) hrinv (s := (1:ℂ) - s) h1s_re
    have hre : ((1:ℂ) - s).re = 1 - σ := by rw [Complex.sub_re, Complex.one_re, hsre]
    rw [hre] at h
    have hdiv : 2 * (N:ℝ) * ‖(1:ℂ) - s‖ / (1 - σ) ≤ (16/7) * (N:ℝ) * (1 + |T|) := by
      rw [div_le_iff₀ (by linarith : (0:ℝ) < 1 - σ)]
      have hN0 : 0 ≤ (N:ℝ) := by positivity
      have hT0 : 0 ≤ 1 + |T| := by linarith [abs_nonneg T]
      have h7 : (7/8 : ℝ) ≤ 1 - σ := by linarith
      have hstep1 : 2 * (N:ℝ) * ‖(1:ℂ) - s‖ ≤ 2 * (N:ℝ) * (1 + |T|) := by
        have := mul_le_mul_of_nonneg_left hnorm1s (by positivity : (0:ℝ) ≤ 2 * (N:ℝ))
        linarith [this]
      have hstep2 : 2 * (N:ℝ) * (1 + |T|) ≤ (16/7) * (N:ℝ) * (1 + |T|) * (1 - σ) := by
        have h0 : (0:ℝ) ≤ (16/7) * (N:ℝ) * (1 + |T|) := by positivity
        have := mul_le_mul_of_nonneg_left h7 h0
        linarith [this]
      linarith [hstep1, hstep2]
    exact le_trans h (by simpa using hdiv)
  calc ‖DirichletCharacter.LFunction χ ((σ : ℂ) + Complex.I * (T : ℂ))‖
      = ‖DirichletCharacter.LFunction χ s‖ := by rw [hs]
    _ = ‖χ.rootNumber * (N : ℂ) ^ (1/2 - s) *
          (χ.gammaFactor (1 - s) / χ.gammaFactor s) *
          DirichletCharacter.LFunction (χ⁻¹) ((1:ℂ) - s)‖ := by rw [hFE]
    _ = ‖χ.rootNumber‖ * ‖(N : ℂ) ^ (1/2 - s)‖ *
          ‖χ.gammaFactor (1 - s) / χ.gammaFactor s‖ *
          ‖DirichletCharacter.LFunction (χ⁻¹) ((1:ℂ) - s)‖ := by
        rw [norm_mul, norm_mul, norm_mul]
    _ ≤ 1 * (N : ℝ) * (Cγ * (1 + |T|)) * ((16/7) * (N : ℝ) * (1 + |T|)) := by
        rw [hroot, hNnorm]
        have hCγ1 : (0:ℝ) ≤ Cγ * (1 + |T|) := by
          have : (0:ℝ) ≤ 1 + |T| := by linarith [abs_nonneg T]
          positivity
        have h161 : (0:ℝ) ≤ (16/7) * (N:ℝ) * (1 + |T|) := by positivity
        gcongr
    _ = (16/7) * Cγ * (N : ℝ)^2 * (1 + |T|)^2 := by ring

end Commons.NumberTheory.DirichletCharacter

namespace Commons.NumberTheory.DirichletCharacter


theorem LFunction_strip_upper_explicit {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, (0 : ℝ) ≤ σ → σ ≤ 2 →
      ‖DirichletCharacter.LFunction χ ((σ : ℂ) + Complex.I * (T : ℂ))‖ ≤
        C * ((N : ℝ) + |T| + 1) ^ 2 := by
  obtain ⟨Cγ, hCγpos, hCγ⟩ := gammaFactor_ratio_band_left χ
  have hCγ0 : 0 ≤ Cγ := le_of_lt hCγpos
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne N)))
  -- compactness bound
  obtain ⟨M, hM0, hM⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ s : ℂ, ‖s‖ ≤ 2 →
      ‖DirichletCharacter.LFunction χ s‖ ≤ M := by
    let K : Set ℂ := Metric.closedBall (0:ℂ) 2
    have hcont : Continuous fun z : ℂ => ‖DirichletCharacter.LFunction χ z‖ :=
      (DirichletCharacter.differentiable_LFunction hχ).continuous.norm
    have hK : IsCompact K := ProperSpace.isCompact_closedBall (0:ℂ) 2
    obtain ⟨M0, hM0⟩ := IsCompact.exists_bound_of_continuousOn hK hcont.continuousOn
    refine ⟨max M0 0, le_max_right _ _, fun s hs => ?_⟩
    have hmem : s ∈ K := by simpa [K, Metric.mem_closedBall, dist_eq_norm, sub_zero] using hs
    have hb := hM0 s hmem
    simp only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at hb
    exact le_trans hb (le_max_left _ _)
  let C₀ : ℝ := (16/7)*Cγ*(N:ℝ)^2 + 16 + M + 1
  have hC₀pos : 0 < C₀ := by
    have h1 : 0 < (16/7)*Cγ*(N:ℝ)^2 := by
      have : 0 < Cγ * (N:ℝ)^2 := mul_pos hCγpos (pow_pos (by linarith : (0:ℝ) < N) 2)
      nlinarith
    dsimp [C₀]; linarith
  refine ⟨C₀, hC₀pos, ?_⟩
  intro σ T hσ0 hσ2
  set A : ℝ := (N:ℝ) + |T| + 1 with hA
  have hA1 : (1:ℝ) ≤ A := by rw [hA]; linarith [abs_nonneg T, hN1]
  have hA2 : (0:ℝ) ≤ A := le_trans zero_le_one hA1
  have hle1T : (1:ℝ) ≤ 1 + |T| := by linarith [abs_nonneg T]
  have hA_ge1T : 1 + |T| ≤ A := by rw [hA]; linarith [abs_nonneg T, hN1]
  have hCleft_bound : ∀ (σ T : ℝ), 0 < σ → σ ≤ 1/8 → 1 ≤ |T| →
      ‖DirichletCharacter.LFunction χ ((σ:ℂ) + Complex.I*(T:ℂ))‖ ≤
        ((16/7)*Cγ*(N:ℝ)^2)*(1+|T|)^2 :=
    fun σ T h0 h1 hT => LFunction_left_band χ hχ hχprim hCγ0 hCγ σ T h0 h1 hT
  have hCleft_le : (16/7)*Cγ*(N:ℝ)^2 ≤ C₀ := by dsimp [C₀]; linarith [hM0]
  by_cases hσ : (1/8:ℝ) ≤ σ
  · -- right region
    have hσpos : 0 < σ := lt_of_lt_of_le (by norm_num) hσ
    have hL := Commons.NumberTheory.DirichletCharacter.LFunction_norm_half_plane χ hχ
      (s := ((σ:ℂ) + Complex.I*(T:ℂ))) (by simpa using hσpos)
    have hLre : ((σ:ℂ) + Complex.I*(T:ℂ)).re = σ := by simp
    rw [hLre] at hL
    have hnorm : ‖((σ:ℂ) + Complex.I*(T:ℂ))‖ ≤ σ + |T| := by
      have h := Complex.norm_le_abs_re_add_abs_im ((σ:ℂ) + Complex.I*(T:ℂ))
      rw [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
          Complex.I_im, Complex.ofReal_re] at h
      simp at h
      linarith [h, abs_of_nonneg hσ0]
    have hsinv : 1/σ ≤ 8 := by
      have h := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 1/8) hσ
      norm_num at h; simpa [one_div] using h
    have hdiv : ‖((σ:ℂ) + Complex.I*(T:ℂ))‖ / σ ≤ 8 * (1 + |T|) := by
      calc ‖((σ:ℂ) + Complex.I*(T:ℂ))‖ / σ ≤ (σ + |T|)/σ :=
            div_le_div_of_nonneg_right hnorm (le_of_lt hσpos)
        _ = 1 + |T| * (1/σ) := by field_simp
        _ ≤ 1 + |T| * 8 := by
            have := mul_le_mul_of_nonneg_left hsinv (abs_nonneg T)
            linarith
        _ ≤ 8 * (1 + |T|) := by linarith [abs_nonneg T]
    have hright : ‖DirichletCharacter.LFunction χ ((σ:ℂ) + Complex.I*(T:ℂ))‖ ≤
        16*(N:ℝ)*(1+|T|) := by
      calc ‖DirichletCharacter.LFunction χ ((σ:ℂ) + Complex.I*(T:ℂ))‖
          ≤ 2*(N:ℝ)*‖((σ:ℂ) + Complex.I*(T:ℂ))‖/σ := hL
        _ = 2*(N:ℝ)*(‖((σ:ℂ) + Complex.I*(T:ℂ))‖/σ) := by ring
        _ ≤ 2*(N:ℝ)*(8*(1+|T|)) := mul_le_mul_of_nonneg_left hdiv (by positivity)
        _ = 16*(N:ℝ)*(1+|T|) := by ring
    have h16 : (16:ℝ) ≤ C₀ := by
      have h1 : 0 ≤ (16/7)*Cγ*(N:ℝ)^2 := by
        have h2 : 0 < Cγ * (N:ℝ)^2 := mul_pos hCγpos (pow_pos (by linarith : (0:ℝ) < N) 2)
        nlinarith
      dsimp [C₀]; linarith [hM0]
    calc ‖DirichletCharacter.LFunction χ ((σ:ℂ) + Complex.I*(T:ℂ))‖ ≤ 16*(N:ℝ)*(1+|T|) := hright
      _ ≤ 16 * A^2 := by
          have hNA : (N:ℝ) ≤ A := by rw [hA]; linarith [abs_nonneg T]
          have h1TA : 1 + |T| ≤ A := hA_ge1T
          have : (N:ℝ)*(1+|T|) ≤ A^2 := by
            calc (N:ℝ)*(1+|T|) ≤ A * A := mul_le_mul hNA h1TA (by linarith [abs_nonneg T]) hA2
              _ = A^2 := by ring
          linarith [this]
      _ ≤ C₀ * A^2 := mul_le_mul_of_nonneg_right h16 (sq_nonneg A)
      _ = C₀ * ((N:ℝ) + |T| + 1)^2 := by rw [hA]
  · have hσ_lt : σ < 1/8 := lt_of_not_ge hσ
    by_cases hT1 : (1:ℝ) ≤ |T|
    · -- left band, large |T|
      rcases eq_or_lt_of_le hσ0 with hσ_eq | hσ_pos
      · -- σ = 0 by continuity
        have hcont : ContinuousAt (fun σ : ℝ =>
            ‖DirichletCharacter.LFunction χ (((σ:ℂ)) + Complex.I*(T:ℂ))‖) 0 := by
          have h1 : Continuous fun σ : ℝ => (((σ:ℂ)) + Complex.I*(T:ℂ)) := by fun_prop
          exact ((DirichletCharacter.differentiable_LFunction hχ).continuous.comp h1).continuousAt.norm
        have hg : Filter.Tendsto (fun n : ℕ => (1/((n:ℝ)+1) : ℝ)) Filter.atTop (𝓝 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        have htend : Filter.Tendsto
            ((fun σ : ℝ => ‖DirichletCharacter.LFunction χ (((σ:ℂ)) + Complex.I*(T:ℂ))‖) ∘
              (fun n : ℕ => (1/((n:ℝ)+1) : ℝ))) Filter.atTop
            (𝓝 ((fun σ : ℝ => ‖DirichletCharacter.LFunction χ (((σ:ℂ)) + Complex.I*(T:ℂ))‖) 0)) :=
          hcont.tendsto.comp hg
        have hev : ∀ᶠ n in Filter.atTop,
            ((fun σ : ℝ => ‖DirichletCharacter.LFunction χ (((σ:ℂ)) + Complex.I*(T:ℂ))‖) ∘
              (fun n : ℕ => (1/((n:ℝ)+1) : ℝ))) n ≤
              ((16/7)*Cγ*(N:ℝ)^2)*(1+|T|)^2 := by
          filter_upwards [Filter.eventually_ge_atTop (7:ℕ)] with n hn
          have hn1 : (0:ℝ) < 1/((n:ℝ)+1) := by positivity
          have hn2 : 1/((n:ℝ)+1) ≤ 1/8 := by
            rw [div_le_iff₀ (by positivity : (0:ℝ) < (n:ℝ)+1)]
            have hnR : (7:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
            linarith
          show ‖DirichletCharacter.LFunction χ ((((1/((n:ℝ)+1) : ℝ)) : ℂ) + Complex.I*(T:ℂ))‖ ≤
              ((16/7)*Cγ*(N:ℝ)^2)*(1+|T|)^2
          exact hCleft_bound (1/((n:ℝ)+1)) T hn1 hn2 hT1
        have hlim_le : ‖DirichletCharacter.LFunction χ (((0:ℝ):ℂ) + Complex.I*(T:ℂ))‖ ≤
            ((16/7)*Cγ*(N:ℝ)^2)*(1+|T|)^2 := by
          have h := le_of_tendsto htend hev
          simpa using h
        have hzero : (((0:ℝ):ℂ) + Complex.I*(T:ℂ)) = ((σ:ℂ) + Complex.I*(T:ℂ)) := by rw [← hσ_eq]
        rw [hzero] at hlim_le
        have hCleft0 : 0 ≤ (16/7)*Cγ*(N:ℝ)^2 := by
          have h1 : 0 < Cγ * (N:ℝ)^2 := mul_pos hCγpos (pow_pos (by linarith : (0:ℝ) < N) 2)
          nlinarith
        calc ‖DirichletCharacter.LFunction χ (((σ:ℂ) + Complex.I*(T:ℂ)))‖ ≤ ((16/7)*Cγ*(N:ℝ)^2)*(1+|T|)^2 := hlim_le
          _ ≤ ((16/7)*Cγ*(N:ℝ)^2) * A^2 :=
              mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith [abs_nonneg T]) hA_ge1T 2) hCleft0
          _ ≤ C₀ * A^2 := mul_le_mul_of_nonneg_right hCleft_le (sq_nonneg A)
          _ = C₀ * ((N:ℝ) + |T| + 1)^2 := by rw [hA]
      · -- 0 < σ < 1/8
        have hleft := hCleft_bound σ T hσ_pos (le_of_lt hσ_lt) hT1
        calc ‖DirichletCharacter.LFunction χ (((σ:ℂ) + Complex.I*(T:ℂ)))‖ ≤ ((16/7)*Cγ*(N:ℝ)^2)*(1+|T|)^2 := hleft
          _ ≤ ((16/7)*Cγ*(N:ℝ)^2) * A^2 := by
              have : (1+|T|)^2 ≤ A^2 :=
                pow_le_pow_left₀ (by linarith [abs_nonneg T]) hA_ge1T 2
              have hCleft0 : 0 ≤ (16/7)*Cγ*(N:ℝ)^2 := by
                have h1 : 0 < Cγ * (N:ℝ)^2 := mul_pos hCγpos (pow_pos (by linarith : (0:ℝ) < N) 2)
                nlinarith
              nlinarith [this, hCleft0]
          _ ≤ C₀ * A^2 := mul_le_mul_of_nonneg_right hCleft_le (sq_nonneg A)
          _ = C₀ * ((N:ℝ) + |T| + 1)^2 := by rw [hA]
    · -- small |T|
      have hTle : |T| < 1 := lt_of_not_ge hT1
      have hnorm : ‖((σ:ℂ) + Complex.I*(T:ℂ))‖ ≤ 2 := by
        have h := Complex.norm_le_abs_re_add_abs_im ((σ:ℂ) + Complex.I*(T:ℂ))
        have hre : ((σ:ℂ) + Complex.I*(T:ℂ)).re = σ := by simp
        have him : ((σ:ℂ) + Complex.I*(T:ℂ)).im = T := by simp
        rw [hre, him, abs_of_nonneg hσ0] at h
        have : σ + |T| < 2 := by linarith [hσ_lt, hTle]
        linarith
      have hMbound := hM ((σ:ℂ) + Complex.I*(T:ℂ)) hnorm
      have hMC : M ≤ C₀ := by
        have h1 : 0 ≤ (16/7)*Cγ*(N:ℝ)^2 := by
          have h2 : 0 < Cγ * (N:ℝ)^2 := mul_pos hCγpos (pow_pos (by linarith : (0:ℝ) < N) 2)
          nlinarith
        dsimp [C₀]; linarith [hM0]
      calc ‖DirichletCharacter.LFunction χ (((σ:ℂ) + Complex.I*(T:ℂ)))‖ ≤ M := hMbound
        _ ≤ C₀ := hMC
        _ ≤ C₀ * A^2 := by
            have hA2' : (1:ℝ) ≤ A^2 := by nlinarith [hA1]
            have := mul_le_mul_of_nonneg_left hA2' (le_of_lt hC₀pos)
            simpa using this
        _ = C₀ * ((N:ℝ) + |T| + 1)^2 := by rw [hA]

end Commons.NumberTheory.DirichletCharacter

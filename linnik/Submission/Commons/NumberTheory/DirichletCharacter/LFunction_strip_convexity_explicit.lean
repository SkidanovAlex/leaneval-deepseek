import Mathlib
import Submission.Commons.Analysis.SpecialFunctions.Gamma.gamma_abs_sq_half
import Submission.Commons.Analysis.SpecialFunctions.Gamma.Gamma_vertical_upper_uniform_sharp
import Submission.Commons.NumberTheory.DirichletCharacter.Even_inv
import Submission.Commons.NumberTheory.DirichletCharacter.Odd_inv
import Submission.Commons.NumberTheory.DirichletCharacter.rootNumber_norm_eq_one
import Submission.Commons.NumberTheory.DirichletCharacter.completedLFunction_eq
import Submission.Commons.NumberTheory.DirichletCharacter.norm_LFunction_le_re_ge_one
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_strip_upper_explicit
open Complex DirichletCharacter
open scoped Real
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace Commons.NumberTheory.DirichletCharacter
private lemma Gamma_star (w : ℂ) : Complex.Gamma (star w) = star (Complex.Gamma w) := by
  simpa using Complex.Gamma_conj w
private lemma norm_Gamma_star (w : ℂ) : ‖Complex.Gamma (star w)‖ = ‖Complex.Gamma w‖ := by
  rw [Gamma_star, norm_star]

private lemma gamma_abs_sq_half' (v : ℝ) :
    ‖Complex.Gamma ((1/2:ℂ) + ((v:ℝ):ℂ)*I)‖^2 = Real.pi / Real.cosh (Real.pi * v) := by
  have h := Commons.Analysis.SpecialFunctions.Gamma.gamma_abs_sq_half v
  rwa [mul_comm I _] at h

private lemma cosh_pi_abs (v : ℝ) : Real.cosh (Real.pi * v) = Real.cosh (Real.pi * |v|) := by
  rcases le_total 0 v with hv | hv
  · rw [abs_of_nonneg hv]
  · rw [abs_of_nonpos hv, mul_neg, Real.cosh_neg]

private lemma Gamma_half_norm_upper (v : ℝ) :
    ‖Complex.Gamma ((1/2:ℂ) + ((v:ℝ):ℂ)*I)‖ ≤
      Real.sqrt (2*Real.pi) * Real.exp (-(Real.pi/2)*|v|) := by
  have hcosh : (1/2)*Real.exp (Real.pi*|v|) ≤ Real.cosh (Real.pi*v) := by
    rw [cosh_pi_abs, Real.cosh_eq]
    linarith [Real.exp_pos (-(Real.pi*|v|))]
  have h2 : ‖Complex.Gamma ((1/2:ℂ) + ((v:ℝ):ℂ)*I)‖^2 ≤ 2*Real.pi*Real.exp (-(Real.pi)*|v|) := by
    rw [gamma_abs_sq_half', div_le_iff₀ (Real.cosh_pos _)]
    have h2e : Real.exp (-(Real.pi)*|v|) * Real.exp (Real.pi*|v|) = 1 := by
      rw [← Real.exp_add, show -(Real.pi)*|v| + Real.pi*|v| = 0 by ring, Real.exp_zero]
    have hstep : (2*Real.pi*Real.exp (-(Real.pi)*|v|)) * ((1/2)*Real.exp (Real.pi*|v|)) = Real.pi := by
      rw [show (2*Real.pi*Real.exp (-(Real.pi)*|v|)) * ((1/2)*Real.exp (Real.pi*|v|))
          = Real.pi * (Real.exp (-(Real.pi)*|v|) * Real.exp (Real.pi*|v|)) by ring, h2e]; ring
    have := mul_le_mul_of_nonneg_left hcosh (by positivity : (0:ℝ) ≤ 2*Real.pi*Real.exp (-(Real.pi)*|v|))
    linarith [this, hstep]
  calc ‖Complex.Gamma ((1/2:ℂ) + ((v:ℝ):ℂ)*I)‖
      = Real.sqrt (‖Complex.Gamma ((1/2:ℂ) + ((v:ℝ):ℂ)*I)‖^2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (2*Real.pi*Real.exp (-(Real.pi)*|v|)) := Real.sqrt_le_sqrt h2
    _ = Real.sqrt (2*Real.pi) * Real.exp (-(Real.pi/2)*|v|) := by
        rw [Real.sqrt_mul (by positivity : (0:ℝ) ≤ 2*Real.pi)]
        have hsq : Real.sqrt (Real.exp (-(Real.pi)*|v|)) = Real.exp (-(Real.pi/2)*|v|) := by
          rw [show -(Real.pi)*|v| = (-(Real.pi/2)*|v|) + (-(Real.pi/2)*|v|) by ring, Real.exp_add,
              ← sq, Real.sqrt_sq (Real.exp_pos _).le]
        rw [hsq]

private lemma sin_I_norm (y : ℝ) : ‖Complex.sin (((y:ℝ):ℂ) * I)‖ = Real.sinh |y| := by
  rw [Complex.sin_mul_I, norm_mul, Complex.norm_I, mul_one]
  have hcast : Complex.sinh ((y:ℝ):ℂ) = ((Real.sinh y:ℝ):ℂ) := (Complex.ofReal_sinh y).symm
  rw [hcast, show ‖Complex.ofReal (Real.sinh y)‖ = |Real.sinh y| from RCLike.norm_ofReal _,
      Real.abs_sinh]

private lemma Gamma_it_half_mul (v : ℝ) :
    ‖Complex.Gamma (((v:ℝ):ℂ) * I)‖ * ‖Complex.Gamma (1 + ((v:ℝ):ℂ) * I)‖ =
      Real.pi / Real.sinh (Real.pi * |v|) := by
  have hstar : 1 - ((v:ℝ):ℂ)*I = star (1 + ((v:ℝ):ℂ)*I) := by
    apply Complex.ext <;> simp
  have hgn : ‖Complex.Gamma (1 - ((v:ℝ):ℂ)*I)‖ = ‖Complex.Gamma (1 + ((v:ℝ):ℂ)*I)‖ := by
    rw [hstar, Gamma_star, norm_star]
  have hrefl := Complex.Gamma_mul_Gamma_one_sub (((v:ℝ):ℂ) * I)
  have hnorm := congrArg norm hrefl
  rw [norm_mul, norm_div, Complex.norm_of_nonneg (le_of_lt Real.pi_pos)] at hnorm
  have hsin : ‖Complex.sin ((Real.pi:ℂ) * (((v:ℝ):ℂ) * I))‖ = Real.sinh (Real.pi * |v|) := by
    have harg : (Real.pi:ℂ) * (((v:ℝ):ℂ) * I) = (((Real.pi*v:ℝ)):ℂ) * I := by
      apply Complex.ext <;> simp <;> ring
    rw [harg, sin_I_norm, show |Real.pi*v| = Real.pi*|v| from by
      rw [abs_mul, abs_of_nonneg (le_of_lt Real.pi_pos)]]
  rw [hgn, hsin] at hnorm
  simpa [mul_comm] using hnorm

private lemma Gamma_half_norm_upper' (t : ℝ) :
    ‖Complex.Gamma ((1/2:ℂ) + (((t/2:ℝ)):ℂ)*I)‖ ≤
      Real.sqrt (2*Real.pi) * Real.exp (-(Real.pi/4)*|t|) := by
  have h := Gamma_half_norm_upper (t/2)
  rw [show |t/2| = |t|/2 from by rw [abs_div]; norm_num] at h
  rw [show -(Real.pi/2)*(|t|/2) = -(Real.pi/4)*|t| from by ring] at h
  exact h

private lemma Gamma_it_half_lower {Csh : ℝ} (hCshpos : 0 < Csh)
    (hCsh : ∀ (u v : ℝ), (1:ℝ)/2 ≤ u → u ≤ 2 →
      ‖Complex.Gamma ((u:ℂ)+((v:ℝ):ℂ)*I)‖ ≤ Csh*(1+|v|)^(u-1/2)*Real.exp (-(Real.pi/2)*|v|))
    (t : ℝ) (ht : t ≠ 0) :
    2*Real.pi*Real.exp (-(Real.pi/4)*|t|)/(Csh*(2+|t|)^((1:ℝ)/2)) ≤
      ‖Complex.Gamma ((((t/2:ℝ)):ℂ) * I)‖ := by
  have hab : |t/2| = |t|/2 := by rw [abs_div]; norm_num
  have hG : ‖Complex.Gamma (1 + (((t/2:ℝ)):ℂ)*I)‖ ≤
      Csh * (1+|t/2|)^((1:ℝ)/2) * Real.exp (-(Real.pi/2)*|t/2|) := by
    have h0 := hCsh 1 (t/2) (by norm_num) (by norm_num)
    rw [show (1:ℝ)-1/2 = 1/2 by norm_num] at h0
    exact h0
  rw [show -(Real.pi/2)*|t/2| = -(Real.pi/4)*|t| from by rw [hab]; ring] at hG
  have hsinh : Real.sinh (Real.pi * |t/2|) ≤ (1/2)*Real.exp (Real.pi*|t|/2) := by
    rw [Real.sinh_eq, hab, show Real.pi*(|t|/2) = Real.pi*|t|/2 by ring, sub_div]
    have := Real.exp_pos (-(Real.pi*|t|/2)); linarith
  have hsinhpos : 0 < Real.sinh (Real.pi * |t/2|) := by rw [Real.sinh_pos_iff]; positivity
  have hG1pos : 0 < ‖Complex.Gamma (1 + (((t/2:ℝ)):ℂ)*I)‖ := by
    apply norm_pos_iff.mpr; apply Complex.Gamma_ne_zero; intro m hm
    have := congrArg Complex.re hm; simp at this; linarith
  have hprod := Gamma_it_half_mul (t/2)
  have hEq : ‖Complex.Gamma ((((t/2:ℝ)):ℂ) * I)‖ =
      Real.pi / (Real.sinh (Real.pi*|t/2|) * ‖Complex.Gamma (1 + (((t/2:ℝ)):ℂ)*I)‖) := by
    rw [eq_div_iff (ne_of_gt (mul_pos hsinhpos hG1pos))]
    rw [show ‖Complex.Gamma ((((t/2:ℝ)):ℂ) * I)‖ * (Real.sinh (Real.pi*|t/2|) * ‖Complex.Gamma (1 + (((t/2:ℝ)):ℂ)*I)‖)
        = Real.sinh (Real.pi*|t/2|) * (‖Complex.Gamma ((((t/2:ℝ)):ℂ) * I)‖ * ‖Complex.Gamma (1 + (((t/2:ℝ)):ℂ)*I)‖) by ring]
    rw [hprod]
    field_simp
  rw [hEq, le_div_iff₀ (mul_pos hsinhpos hG1pos)]
  have he : Real.exp (-(Real.pi/4)*|t|) * Real.exp (Real.pi*|t|/4) = 1 := by
    rw [← Real.exp_add, show -(Real.pi/4)*|t| + Real.pi*|t|/4 = 0 by ring, Real.exp_zero]
  have hb : Real.sinh (Real.pi*|t/2|) * ‖Complex.Gamma (1 + (((t/2:ℝ)):ℂ)*I)‖ ≤
      Csh*(1+|t/2|)^((1:ℝ)/2)/2*Real.exp (Real.pi*|t|/4) := by
    calc Real.sinh (Real.pi*|t/2|) * ‖Complex.Gamma (1 + (((t/2:ℝ)):ℂ)*I)‖
        ≤ ((1/2)*Real.exp (Real.pi*|t|/2)) *
            (Csh * (1+|t/2|)^((1:ℝ)/2) * Real.exp (-(Real.pi/4)*|t|)) :=
          mul_le_mul hsinh hG (norm_nonneg _) (by positivity)
      _ = Csh*(1+|t/2|)^((1:ℝ)/2)/2*Real.exp (Real.pi*|t|/4) := by
          have he2 : Real.exp (Real.pi*|t|/2) * Real.exp (-(Real.pi/4)*|t|) = Real.exp (Real.pi*|t|/4) := by
            rw [← Real.exp_add]; congr 1; ring
          rw [← he2]; ring
  have hSle : (1+|t/2|)^((1:ℝ)/2) ≤ (2+|t|)^((1:ℝ)/2) := by
    apply Real.rpow_le_rpow (by positivity)
    · rw [hab]; linarith [abs_nonneg t]
    · norm_num
  have hcoef : 0 ≤ 2*Real.pi*Real.exp (-(Real.pi/4)*|t|)/(Csh*(2+|t|)^((1:ℝ)/2)) := by
    apply div_nonneg
    · exact mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) (Real.exp_pos _).le
    · exact (mul_pos hCshpos (Real.rpow_pos_of_pos (by linarith [abs_nonneg t]) _)).le
  calc (2*Real.pi*Real.exp (-(Real.pi/4)*|t|)/(Csh*(2+|t|)^((1:ℝ)/2))) *
        (Real.sinh (Real.pi*|t/2|) * ‖Complex.Gamma (1 + (((t/2:ℝ)):ℂ)*I)‖)
      ≤ (2*Real.pi*Real.exp (-(Real.pi/4)*|t|)/(Csh*(2+|t|)^((1:ℝ)/2))) *
        (Csh*(1+|t/2|)^((1:ℝ)/2)/2*Real.exp (Real.pi*|t|/4)) :=
        mul_le_mul_of_nonneg_left hb hcoef
    _ ≤ (2*Real.pi*Real.exp (-(Real.pi/4)*|t|)/(Csh*(2+|t|)^((1:ℝ)/2))) *
        (Csh*(2+|t|)^((1:ℝ)/2)/2*Real.exp (Real.pi*|t|/4)) := by
        apply mul_le_mul_of_nonneg_left _ hcoef
        have h1 : Csh*(1+|t/2|)^((1:ℝ)/2)/2 ≤ Csh*(2+|t|)^((1:ℝ)/2)/2 :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hSle hCshpos.le) (show (0:ℝ) ≤ 2 by norm_num)
        exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = Real.pi := by
        rw [show (2*Real.pi*Real.exp (-(Real.pi/4)*|t|)/(Csh*(2+|t|)^((1:ℝ)/2))) *
            (Csh*(2+|t|)^((1:ℝ)/2)/2*Real.exp (Real.pi*|t|/4))
            = Real.pi * (Real.exp (-(Real.pi/4)*|t|)*Real.exp (Real.pi*|t|/4)) *
              ((Csh*(2+|t|)^((1:ℝ)/2))/(Csh*(2+|t|)^((1:ℝ)/2))) by ring]
        rw [he, div_self (ne_of_gt (mul_pos hCshpos (Real.rpow_pos_of_pos (by linarith [abs_nonneg t]) _)))]; ring

private lemma norm_Gamma_sub_mul_I (a v : ℝ) :
    ‖Complex.Gamma ((a:ℂ) - (v:ℂ)*I)‖ = ‖Complex.Gamma ((a:ℂ) + (v:ℂ)*I)‖ := by
  have h : (a:ℂ) - (v:ℂ)*I = star ((a:ℂ) + (v:ℂ)*I) := by
    apply Complex.ext <;> simp
  rw [h, Gamma_star, norm_star]

private lemma gammaR_ratio_zero_even :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, t ≠ 0 →
      ‖Complex.Gammaℝ (1 - (t:ℂ)*I) / Complex.Gammaℝ ((t:ℂ)*I)‖ ≤
        C * (2 + |t|)^((1:ℝ)/2) := by
  obtain ⟨Csh, hCshpos, hCsh⟩ :=
    Commons.Analysis.SpecialFunctions.Gamma.Gamma_vertical_upper_uniform_sharp
  refine ⟨Real.sqrt (2*Real.pi)*Csh/(2*Real.pi*Real.sqrt Real.pi),
    div_pos (mul_pos (Real.sqrt_pos.mpr (by positivity)) hCshpos)
      (mul_pos (by positivity) (Real.sqrt_pos.mpr Real.pi_pos)), ?_⟩
  intro t ht
  have hnum : ‖Complex.Gammaℝ (1 - (t:ℂ)*I)‖ =
      Real.pi^(-(1/2):ℝ) * ‖Complex.Gamma ((1/2:ℂ) + (((t/2:ℝ)):ℂ)*I)‖ := by
    rw [Complex.Gammaℝ_def, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    congr 1
    · rw [show (-(1 - (t:ℂ)*I)/2).re = -(1/2) from by simp; norm_num]
    · rw [show (1 - (t:ℂ)*I)/2 = (((1/2:ℝ)):ℂ) - (((t/2:ℝ)):ℂ)*I from by push_cast; ring]
      simpa using norm_Gamma_sub_mul_I (1/2) (t/2)
  have hden : ‖Complex.Gammaℝ ((t:ℂ)*I)‖ = ‖Complex.Gamma ((((t/2:ℝ)):ℂ)*I)‖ := by
    rw [Complex.Gammaℝ_def, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos,
        show (-((t:ℂ)*I)/2).re = 0 from by simp, Real.rpow_zero, one_mul]
    congr 1
    rw [show ((t:ℂ)*I)/2 = (((t/2:ℝ)):ℂ)*I from by push_cast; ring]
  have hratio : ‖Complex.Gammaℝ (1 - (t:ℂ)*I) / Complex.Gammaℝ ((t:ℂ)*I)‖ =
      Real.pi^(-(1/2):ℝ) * (‖Complex.Gamma ((1/2:ℂ) + (((t/2:ℝ)):ℂ)*I)‖ /
        ‖Complex.Gamma ((((t/2:ℝ)):ℂ)*I)‖) := by
    rw [norm_div, hnum, hden]; ring
  rw [hratio]
  have hup := Gamma_half_norm_upper' t
  have hlow := Gamma_it_half_lower hCshpos hCsh t ht
  have hitpos : 0 < ‖Complex.Gamma ((((t/2:ℝ)):ℂ)*I)‖ := by
    apply norm_pos_iff.mpr; apply Complex.Gamma_ne_zero; intro m hm
    have him := congrArg Complex.im hm
    simp at him
    exact ht (by linarith [him])
  have hlowpos : 0 < 2*Real.pi*Real.exp (-(Real.pi/4)*|t|)/(Csh*(2+|t|)^((1:ℝ)/2)) := by positivity
  have hdiv : ‖Complex.Gamma ((1/2:ℂ) + (((t/2:ℝ)):ℂ)*I)‖ / ‖Complex.Gamma ((((t/2:ℝ)):ℂ)*I)‖ ≤
      (Real.sqrt (2*Real.pi)*Real.exp (-(Real.pi/4)*|t|)) /
        (2*Real.pi*Real.exp (-(Real.pi/4)*|t|)/(Csh*(2+|t|)^((1:ℝ)/2))) := by
    apply div_le_div₀ (by positivity) hup hlowpos hlow
  calc Real.pi^(-(1/2):ℝ) * (‖Complex.Gamma ((1/2:ℂ) + (((t/2:ℝ)):ℂ)*I)‖ / ‖Complex.Gamma ((((t/2:ℝ)):ℂ)*I)‖)
      ≤ Real.pi^(-(1/2):ℝ) * ((Real.sqrt (2*Real.pi)*Real.exp (-(Real.pi/4)*|t|)) /
          (2*Real.pi*Real.exp (-(Real.pi/4)*|t|)/(Csh*(2+|t|)^((1:ℝ)/2)))) :=
        mul_le_mul_of_nonneg_left hdiv (by positivity)
    _ = Real.sqrt (2*Real.pi)*Csh/(2*Real.pi*Real.sqrt Real.pi) * (2 + |t|)^((1:ℝ)/2) := by
        rw [show Real.pi^((-(1/2)):ℝ) = 1/Real.sqrt Real.pi from by
          rw [Real.rpow_neg (le_of_lt Real.pi_pos), Real.sqrt_eq_rpow, inv_eq_one_div]]
        have hSpos : 0 < (2+|t|)^((1:ℝ)/2) := Real.rpow_pos_of_pos (by linarith [abs_nonneg t]) _
        field_simp


private lemma gammaR_ratio_zero_odd :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, t ≠ 0 →
      ‖Complex.Gammaℝ (2 - (t:ℂ)*I) / Complex.Gammaℝ (1 + (t:ℂ)*I)‖ ≤
        C * (2 + |t|)^((1:ℝ)/2) := by
  obtain ⟨Csh, hCshpos, hCsh⟩ :=
    Commons.Analysis.SpecialFunctions.Gamma.Gamma_vertical_upper_uniform_sharp
  refine ⟨Csh/Real.pi, div_pos hCshpos Real.pi_pos, ?_⟩
  intro t ht
  have hnum : ‖Complex.Gammaℝ (2 - (t:ℂ)*I)‖ =
      Real.pi^(-(1:ℝ)) * ‖Complex.Gamma (1 + (((t/2:ℝ)):ℂ)*I)‖ := by
    rw [Complex.Gammaℝ_def, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    congr 1
    · rw [show (-(2 - (t:ℂ)*I)/2).re = (-(1:ℝ)) from by simp]
    · rw [show (2 - (t:ℂ)*I)/2 = (1:ℂ) - (((t/2:ℝ)):ℂ)*I from by push_cast; ring]
      simpa using norm_Gamma_sub_mul_I 1 (t/2)
  have hden : ‖Complex.Gammaℝ (1 + (t:ℂ)*I)‖ =
      Real.pi^(-(1/2):ℝ) * ‖Complex.Gamma ((1/2:ℂ) + (((t/2:ℝ)):ℂ)*I)‖ := by
    rw [Complex.Gammaℝ_def, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    congr 1
    · rw [show (-(1 + (t:ℂ)*I)/2).re = (-(1/2):ℝ) from by simp; norm_num]
    · rw [show (1 + (t:ℂ)*I)/2 = (1/2:ℂ) + (((t/2:ℝ)):ℂ)*I from by push_cast; ring]
  have hratio : ‖Complex.Gammaℝ (2 - (t:ℂ)*I) / Complex.Gammaℝ (1 + (t:ℂ)*I)‖ =
      Real.pi^(-(1:ℝ)) * ‖Complex.Gamma (1 + (((t/2:ℝ)):ℂ)*I)‖ /
        (Real.pi^(-(1/2):ℝ) * ‖Complex.Gamma ((1/2:ℂ) + (((t/2:ℝ)):ℂ)*I)‖) := by
    rw [norm_div, hnum, hden]
  rw [hratio]
  have hGup : ‖Complex.Gamma (1 + (((t/2:ℝ)):ℂ)*I)‖ ≤
      Csh*(1+|t/2|)^((1:ℝ)/2)*Real.exp (-(Real.pi/4)*|t|) := by
    have h0 := hCsh 1 (t/2) (by norm_num) (by norm_num)
    rw [show (1:ℝ)-1/2 = 1/2 by norm_num] at h0
    rw [show -(Real.pi/2)*|t/2| = -(Real.pi/4)*|t| from by rw [abs_div]; norm_num; ring] at h0
    exact h0
  have hGdlow : Real.sqrt Real.pi * Real.exp (-(Real.pi/4)*|t|) ≤
      ‖Complex.Gamma ((1/2:ℂ) + (((t/2:ℝ)):ℂ)*I)‖ := by
    have h2 : ‖Complex.Gamma ((1/2:ℂ) + (((t/2:ℝ)):ℂ)*I)‖^2 =
        Real.pi / Real.cosh (Real.pi * (t/2)) := by
      rw [gamma_abs_sq_half']
    have hcosh : Real.cosh (Real.pi*(t/2)) ≤ Real.exp (Real.pi*|t|/2) := by
      have hcase : Real.pi*(t/2) = Real.pi*|t|/2 ∨ Real.pi*(t/2) = -(Real.pi*|t|/2) := by
        rcases le_total 0 t with h | h
        · left; rw [abs_of_nonneg h]; ring
        · right; rw [abs_of_nonpos h]; ring
      rw [Real.cosh_eq]
      rcases hcase with h | h
      · rw [h]
        have hx : Real.exp (-(Real.pi*|t|/2)) ≤ Real.exp (Real.pi*|t|/2) :=
          Real.exp_le_exp.mpr (by nlinarith [abs_nonneg t, Real.pi_pos])
        linarith
      · rw [h]; simp only [neg_neg]
        have hx : Real.exp (-(Real.pi*|t|/2)) ≤ Real.exp (Real.pi*|t|/2) :=
          Real.exp_le_exp.mpr (by nlinarith [abs_nonneg t, Real.pi_pos])
        linarith
    have h2' : Real.pi / Real.exp (Real.pi*|t|/2) ≤
        ‖Complex.Gamma ((1/2:ℂ) + (((t/2:ℝ)):ℂ)*I)‖^2 := by
      rw [h2]
      exact div_le_div_of_nonneg_left Real.pi_pos.le (Real.cosh_pos _) hcosh
    have h3 : (Real.sqrt Real.pi * Real.exp (-(Real.pi/4)*|t|))^2 =
        Real.pi / Real.exp (Real.pi*|t|/2) := by
      rw [mul_pow, Real.sq_sqrt Real.pi_pos.le, sq, ← Real.exp_add]
      rw [show -(Real.pi/4)*|t| + -(Real.pi/4)*|t| = -(Real.pi*|t|/2) from by ring, Real.exp_neg]
      field_simp
    rw [← h3] at h2'
    have h5 := Real.sqrt_le_sqrt h2'
    rwa [Real.sqrt_sq (by positivity : (0:ℝ) ≤ Real.sqrt Real.pi * Real.exp (-(Real.pi/4)*|t|)),
        Real.sqrt_sq (norm_nonneg _)] at h5
  have hnumpos : 0 < Real.pi^(-(1:ℝ)) := Real.rpow_pos_of_pos Real.pi_pos _
  have hdenpos : 0 < Real.pi^(-(1/2):ℝ) * ‖Complex.Gamma ((1/2:ℂ) + (((t/2:ℝ)):ℂ)*I)‖ := by
    apply mul_pos (Real.rpow_pos_of_pos Real.pi_pos _)
    apply norm_pos_iff.mpr; apply Complex.Gamma_ne_zero; intro m hm
    have := congrArg Complex.re hm; simp at this; linarith
  have hupper : Real.pi^(-(1:ℝ)) * ‖Complex.Gamma (1 + (((t/2:ℝ)):ℂ)*I)‖ ≤
      Real.pi^(-(1:ℝ)) * (Csh*(1+|t/2|)^((1:ℝ)/2)*Real.exp (-(Real.pi/4)*|t|)) :=
    mul_le_mul_of_nonneg_left hGup hnumpos.le
  have hlower : Real.pi^(-(1/2):ℝ) * (Real.sqrt Real.pi * Real.exp (-(Real.pi/4)*|t|)) ≤
      Real.pi^(-(1/2):ℝ) * ‖Complex.Gamma ((1/2:ℂ) + (((t/2:ℝ)):ℂ)*I)‖ :=
    mul_le_mul_of_nonneg_left hGdlow (Real.rpow_pos_of_pos Real.pi_pos _).le
  calc Real.pi^(-(1:ℝ)) * ‖Complex.Gamma (1 + (((t/2:ℝ)):ℂ)*I)‖ /
        (Real.pi^(-(1/2):ℝ) * ‖Complex.Gamma ((1/2:ℂ) + (((t/2:ℝ)):ℂ)*I)‖)
      ≤ (Real.pi^(-(1:ℝ)) * (Csh*(1+|t/2|)^((1:ℝ)/2)*Real.exp (-(Real.pi/4)*|t|))) /
        (Real.pi^(-(1/2):ℝ) * (Real.sqrt Real.pi * Real.exp (-(Real.pi/4)*|t|))) :=
        div_le_div₀ (by positivity) hupper
          (mul_pos (Real.rpow_pos_of_pos Real.pi_pos _)
            (mul_pos (Real.sqrt_pos.mpr Real.pi_pos) (Real.exp_pos _))) hlower
    _ = Csh/Real.pi * (1+|t/2|)^((1:ℝ)/2) := by
        rw [show Real.pi^(-(1:ℝ)) = 1/Real.pi from by rw [Real.rpow_neg_one, inv_eq_one_div]]
        rw [show Real.pi^(-(1/2):ℝ) = 1/Real.sqrt Real.pi from by
          rw [Real.rpow_neg (le_of_lt Real.pi_pos), Real.sqrt_eq_rpow, inv_eq_one_div]]
        field_simp
    _ ≤ Csh/Real.pi * (2 + |t|)^((1:ℝ)/2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.rpow_le_rpow (by positivity)
        · linarith [abs_nonneg t, abs_div t 2, abs_of_nonneg (show (0:ℝ) ≤ |t| by positivity)]
        · norm_num

private lemma gammaFactor_ratio_zero {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, t ≠ 0 →
      ‖(χ⁻¹).gammaFactor (1 - (t:ℂ)*I) / χ.gammaFactor ((t:ℂ)*I)‖ ≤
        K * (2 + |t|)^((1:ℝ)/2) := by
  obtain ⟨Ce, hCe, he⟩ := gammaR_ratio_zero_even
  obtain ⟨Co, hCo, ho⟩ := gammaR_ratio_zero_odd
  refine ⟨max Ce Co, lt_max_of_lt_left hCe, ?_⟩
  intro t ht
  rcases χ.even_or_odd with hχe | hχo
  · rw [DirichletCharacter.Even.gammaFactor_def hχe,
        DirichletCharacter.Even.gammaFactor_def
          (Commons.NumberTheory.DirichletCharacter.Even_inv hχe)]
    exact (he t ht).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · rw [DirichletCharacter.Odd.gammaFactor_def hχo,
        DirichletCharacter.Odd.gammaFactor_def
          (Commons.NumberTheory.DirichletCharacter.Odd_inv hχo)]
    rw [show (1:ℂ) - (t:ℂ)*I + 1 = 2 - (t:ℂ)*I from by ring,
        show (t:ℂ)*I + 1 = 1 + (t:ℂ)*I from by ring]
    exact (ho t ht).trans (mul_le_mul_of_nonneg_right (le_max_right Ce Co) (by positivity))

private lemma gammaFactor_ne_zero_of_im_ne_zero {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : s.im ≠ 0) : χ.gammaFactor s ≠ 0 := by
  rcases χ.even_or_odd with h | h
  · rw [DirichletCharacter.Even.gammaFactor_def h, Complex.Gammaℝ_def]
    refine mul_ne_zero ?_ ?_
    · rw [Complex.cpow_ne_zero_iff]
      exact Or.inl (by exact_mod_cast (ne_of_gt Real.pi_pos) : (Real.pi : ℂ) ≠ 0)
    · apply Complex.Gamma_ne_zero; intro m hm
      apply hs
      have := congrArg (fun z => z * 2) hm
      simp at this
      have := congrArg Complex.im this
      simpa using this
  · rw [DirichletCharacter.Odd.gammaFactor_def h, Complex.Gammaℝ_def]
    refine mul_ne_zero ?_ ?_
    · rw [Complex.cpow_ne_zero_iff]
      exact Or.inl (by exact_mod_cast (ne_of_gt Real.pi_pos) : (Real.pi : ℂ) ≠ 0)
    · apply Complex.Gamma_ne_zero; intro m hm
      apply hs
      have := congrArg (fun z => z * 2) hm
      simp at this
      have := congrArg Complex.im this
      simp at this; linarith

private lemma LFunction_norm_zero_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hχprim : χ.IsPrimitive) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, t ≠ 0 →
      ‖LFunction χ ((t:ℂ)*I)‖ ≤ C * (N:ℝ)^((1:ℝ)/2) * (2+|t|)^((1:ℝ)/2) *
        (Real.log N + Real.log (2+|t|) + 6) := by
  obtain ⟨K, hKpos, hKb⟩ := gammaFactor_ratio_zero χ
  refine ⟨K, hKpos, ?_⟩
  intro t ht
  set s : ℂ := (t:ℂ)*I with hs
  have hsim : s.im = t := by rw [hs]; simp
  have hsre : s.re = 0 := by rw [hs]; simp
  have hsim' : s.im ≠ 0 := by rw [hsim]; exact ht
  have hs0 : s ≠ 0 := by
    intro h; apply hsim'; rw [h]; simp
  have h1s : 1 - s ≠ 0 := by
    intro h; apply hsim'; have := congrArg Complex.im h; simpa using this
  have hγχ : χ.gammaFactor s ≠ 0 := gammaFactor_ne_zero_of_im_ne_zero χ hsim'
  have hγχi : (χ⁻¹).gammaFactor (1 - s) ≠ 0 :=
    gammaFactor_ne_zero_of_im_ne_zero (χ⁻¹)
      (by rw [Complex.sub_im, Complex.one_im, hsim]; simp [ht])
  have hχine : χ⁻¹ ≠ 1 := by
    intro h; apply hχ
    have := congrArg (fun ψ : DirichletCharacter ℂ N => ψ⁻¹) h
    simpa using this
  have hL1 : LFunction χ s = completedLFunction χ s / χ.gammaFactor s :=
    LFunction_eq_completed_div_gammaFactor χ s (Or.inl hs0)
  have hL2 : LFunction (χ⁻¹) (1 - s) =
      completedLFunction (χ⁻¹) (1 - s) / (χ⁻¹).gammaFactor (1 - s) :=
    LFunction_eq_completed_div_gammaFactor (χ⁻¹) (1 - s) (Or.inl h1s)
  have hcomp : completedLFunction (χ⁻¹) (1 - s) =
      LFunction (χ⁻¹) (1 - s) * (χ⁻¹).gammaFactor (1 - s) := by
    rw [hL2]; exact (div_mul_cancel₀ _ hγχi).symm
  have hFE := completedLFunction_eq χ hχprim s
  have hmain : LFunction χ s = (N:ℂ)^((1:ℂ)/2 - s) * χ.rootNumber *
      (LFunction (χ⁻¹) (1 - s) * (χ⁻¹).gammaFactor (1 - s)) / χ.gammaFactor s := by
    rw [hL1, hFE, hcomp]
  have hNpow : ‖(N:ℂ)^((1:ℂ)/2 - s)‖ = (N:ℝ)^((1:ℝ)/2) := by
    rw [← Complex.ofReal_natCast,
        Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N))]
    congr 1
    rw [Complex.sub_re, Complex.div_re]; simp [hs]
  have hroot := rootNumber_norm_eq_one χ hχprim
  have hnorm_eq : ‖LFunction χ s‖ = (N:ℝ)^((1:ℝ)/2) * ‖χ.rootNumber‖ *
      ‖LFunction (χ⁻¹) (1 - s)‖ * ‖(χ⁻¹).gammaFactor (1 - s)‖ / ‖χ.gammaFactor s‖ := by
    rw [hmain]
    simp only [norm_div, norm_mul]
    rw [hNpow]
    ring_nf
  have hL2b : ‖LFunction (χ⁻¹) (1 - s)‖ ≤ Real.log N + Real.log (2+|t|) + 6 := by
    have h := norm_LFunction_le_re_ge_one (χ⁻¹) hχine (1 - s) (by rw [Complex.sub_re, Complex.one_re, hsre]; norm_num)
    rwa [show (1 - s).im = -t from by rw [Complex.sub_im, Complex.one_im, hsim]; ring, abs_neg] at h
  have hγb : ‖(χ⁻¹).gammaFactor (1 - s)‖ / ‖χ.gammaFactor s‖ ≤ K*(2+|t|)^((1:ℝ)/2) := by
    rw [← norm_div]
    have := hKb t ht
    rwa [show (1 - (t:ℂ)*I) = 1 - s from by rw [hs]] at this
  rw [hnorm_eq]
  simp only [hroot, mul_one, one_mul]
  have hγpos : 0 < ‖χ.gammaFactor s‖ := norm_pos_iff.mpr hγχ
  rw [div_le_iff₀ hγpos]
  have hγb' : ‖(χ⁻¹).gammaFactor (1 - s)‖ ≤ K*(2+|t|)^((1:ℝ)/2) * ‖χ.gammaFactor s‖ := by
    rw [← div_le_iff₀ hγpos]; exact hγb
  calc (N:ℝ)^((1:ℝ)/2) * ‖LFunction (χ⁻¹) (1 - s)‖ * ‖(χ⁻¹).gammaFactor (1 - s)‖
      ≤ (N:ℝ)^((1:ℝ)/2) * (Real.log N + Real.log (2+|t|) + 6) *
          (K*(2+|t|)^((1:ℝ)/2) * ‖χ.gammaFactor s‖) := by
        gcongr
        · apply mul_nonneg (Real.rpow_nonneg (by positivity) _)
          exact add_nonneg (add_nonneg (Real.log_nonneg (by exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne N))))
            (Real.log_nonneg (by linarith [abs_nonneg t]))) (by norm_num)
    _ = (K * (N:ℝ)^((1:ℝ)/2) * (2+|t|)^((1:ℝ)/2) *
          (Real.log N + Real.log (2+|t|) + 6)) * ‖χ.gammaFactor s‖ := by ring

private lemma four_add_sq_ge (t : ℝ) : 2 + |t| ≤ 4 + t^2 := by
  nlinarith [sq_abs t, abs_nonneg t, sq_nonneg (|t| - 1/2)]

private lemma clog_bounds {s : ℂ} (hre0 : 0 ≤ s.re) (hre1 : s.re ≤ 1) :
    Real.log (2 + |s.im|) / 2 ≤ ‖Complex.log (s + 2)‖ ∧
    ‖Complex.log (s + 2)‖ ≤ Real.log (2 + |s.im|) + 5 := by
  set w : ℂ := s + 2 with hw
  have hwre : w.re = s.re + 2 := by rw [hw]; simp
  have hwim : w.im = s.im := by rw [hw]; simp
  have hnorm_sq : ‖w‖^2 = w.re^2 + w.im^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hnorm_ge2 : 2 ≤ ‖w‖ := by
    have : 4 ≤ ‖w‖^2 := by rw [hnorm_sq, hwre, hwim]; nlinarith [hre0, sq_nonneg s.im]
    nlinarith [norm_nonneg w]
  have hlogre : (Complex.log w).re = Real.log ‖w‖ := Complex.log_re w
  have hlogpos : 0 ≤ Real.log ‖w‖ := Real.log_nonneg (by linarith)
  have hlow : Real.log (2 + |s.im|) / 2 ≤ ‖Complex.log w‖ := by
    have h1 : Real.log (2 + |s.im|) ≤ Real.log (‖w‖^2) := by
      apply Real.log_le_log (by positivity)
      rw [hnorm_sq, hwre, hwim]
      nlinarith [hre0, four_add_sq_ge s.im]
    rw [Real.log_pow] at h1
    push_cast at h1
    have h2 : (Complex.log w).re ≤ ‖Complex.log w‖ :=
      (le_abs_self _).trans (abs_re_le_norm _)
    rw [hlogre] at h2
    linarith
  have hup : ‖Complex.log w‖ ≤ Real.log (2 + |s.im|) + 5 := by
    have h1 : ‖Complex.log w‖ ≤ |(Complex.log w).re| + |(Complex.log w).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    have h2 : |(Complex.log w).re| = Real.log ‖w‖ := by rw [hlogre, abs_of_nonneg hlogpos]
    have h3 : |(Complex.log w).im| ≤ Real.pi := by rw [Complex.log_im]; exact Complex.abs_arg_le_pi w
    have h4 : Real.log ‖w‖ ≤ 1 + Real.log (2 + |s.im|) := by
      have h5 : ‖w‖ ≤ 2 * (2 + |s.im|) := by
        have h6 : ‖w‖^2 ≤ (2 * (2 + |s.im|))^2 := by
          rw [hnorm_sq, hwre, hwim]
          nlinarith [hre0, hre1, sq_abs s.im, abs_nonneg s.im, sq_nonneg s.im]
        nlinarith [norm_nonneg w, abs_nonneg s.im]
      have h6 := Real.log_le_log (by linarith [norm_nonneg w] : (0:ℝ) < ‖w‖) h5
      have h7 : Real.log (2 * (2 + |s.im|)) = Real.log 2 + Real.log (2 + |s.im|) :=
        Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (by linarith [abs_nonneg s.im] : (2:ℝ) + |s.im| ≠ 0)
      have h8 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
      linarith [h6, h7, h8]
    calc ‖Complex.log w‖ ≤ |(Complex.log w).re| + |(Complex.log w).im| := h1
      _ ≤ Real.log ‖w‖ + Real.pi := by rw [h2]; linarith [h3]
      _ ≤ 1 + Real.log (2 + |s.im|) + Real.pi := by linarith
      _ ≤ Real.log (2 + |s.im|) + 5 := by linarith [Real.pi_lt_four]
  exact ⟨by rwa [hw] at hlow, by rwa [hw] at hup⟩

private lemma sinh_le_mul_cosh (y : ℝ) (hy : 0 ≤ y) : Real.sinh y ≤ y * Real.cosh y := by
  have hmono : MonotoneOn (fun y => y * Real.cosh y - Real.sinh y) (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact ((continuous_id.mul Real.continuous_cosh).sub Real.continuous_sinh).continuousOn
    · intro y hy
      exact (((hasDerivAt_id y).mul (Real.hasDerivAt_cosh y)).sub
        (Real.hasDerivAt_sinh y)).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      have hd : deriv (fun y => y * Real.cosh y - Real.sinh y) y = y * Real.sinh y := by
        have h : deriv (fun y => y * Real.cosh y - Real.sinh y) y =
            Real.cosh y + y * Real.sinh y - Real.cosh y := by
          simpa using (((hasDerivAt_id y).mul (Real.hasDerivAt_cosh y)).sub
            (Real.hasDerivAt_sinh y)).deriv
        rw [h]; ring
      rw [hd]
      exact mul_nonneg hy.le (Real.sinh_nonneg_iff.mpr hy.le)
  have h0 : (0:ℝ) ∈ Set.Ici 0 := Set.mem_Ici.mpr (le_refl 0)
  have hy' : y ∈ Set.Ici 0 := Set.mem_Ici.mpr hy
  have := hmono h0 hy' hy
  simp only [mul_zero, Real.cosh_zero, Real.sinh_zero, sub_zero] at this
  linarith [this]

private lemma tanh_le_self (x : ℝ) (hx : 0 ≤ x) : Real.tanh x ≤ x := by
  rw [Real.tanh_eq_sinh_div_cosh, div_le_iff₀ (Real.cosh_pos x)]
  exact sinh_le_mul_cosh x hx

private lemma tanh_pos_of_pos {x : ℝ} (hx : 0 < x) : 0 < Real.tanh x := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_pos (Real.sinh_pos_iff.mpr hx) (Real.cosh_pos x)

private lemma Gamma_ratio_decay (s : ℂ) (hs0 : 0 ≤ s.re) (hs1 : s.re ≤ 1) :
    ‖Complex.Gamma (1 - s/4) / Complex.Gamma (1/2 + s/4)‖ ≤
      Real.exp ((1/2 - s.re/2) * (Real.log (2 + |s.im|) + 2)) := by
  set u₂ : ℝ := 1 - s.re/4 with hu₂
  set u₁ : ℝ := 1/2 + s.re/4 with hu₁
  set τ : ℝ := s.im/4 with hτ
  have hu1 : (1:ℝ)/2 ≤ u₁ := by rw [hu₁]; linarith
  have h12 : u₁ ≤ u₂ := by rw [hu₁, hu₂]; linarith
  have h2 : u₂ ≤ 8 := by rw [hu₂]; linarith
  have hu2m1 : u₂ - u₁ = 1/2 - s.re/2 := by rw [hu₂, hu₁]; ring
  have hnum : (1 - s/4) = star (((u₂ : ℝ) : ℂ) + ((τ : ℝ) : ℂ) * I) := by
    rw [hu₂, hτ]; apply Complex.ext <;> simp [Complex.div_re, Complex.div_im, Complex.sub_re,
      Complex.sub_im, Complex.mul_re, Complex.mul_im] <;> ring
  have hden : (1/2 + s/4) = ((u₁ : ℝ) : ℂ) + ((τ : ℝ) : ℂ) * I := by
    rw [hu₁, hτ]; apply Complex.ext <;> simp [Complex.div_re, Complex.div_im, Complex.add_re,
      Complex.add_im, Complex.mul_re, Complex.mul_im] <;> ring
  have hA : Complex.Gamma (((u₂ : ℝ) : ℂ) + ((τ : ℝ) : ℂ) * I) ≠ 0 := by
    apply Complex.Gamma_ne_zero; intro m hm
    have := congrArg Complex.re hm; simp at this; linarith [hu1]
  have hB : Complex.Gamma (((u₁ : ℝ) : ℂ) + ((τ : ℝ) : ℂ) * I) ≠ 0 := by
    apply Complex.Gamma_ne_zero; intro m hm
    have := congrArg Complex.re hm; simp at this; linarith [hu1]
  have hApos : 0 < ‖Complex.Gamma (((u₂ : ℝ) : ℂ) + ((τ : ℝ) : ℂ) * I)‖ := norm_pos_iff.mpr hA
  have hBpos : 0 < ‖Complex.Gamma (((u₁ : ℝ) : ℂ) + ((τ : ℝ) : ℂ) * I)‖ := norm_pos_iff.mpr hB
  have hinc := Commons.Analysis.SpecialFunctions.Gamma.log_norm_Gamma_sub_le u₁ u₂ τ hu1 h12 h2
  have hτabs : |τ| = |s.im|/4 := by rw [hτ, abs_div]; norm_num
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
  rw [hnum, hden, norm_div, norm_Gamma_star]
  refine hratio.trans (le_of_eq ?_)
  rw [hu2m1]


private lemma Gamma_one_norm_sq (v : ℝ) (hv : v ≠ 0) :
    ‖Complex.Gamma ((1:ℂ) + ((v:ℝ):ℂ)*I)‖^2 = Real.pi * |v| / Real.sinh (Real.pi * |v|) := by
  have hvne : ((v:ℝ):ℂ) ≠ 0 := by exact_mod_cast hv
  have hvn : (|v|:ℝ) ≠ 0 := abs_ne_zero.mpr hv
  have hsinhpos : 0 < Real.sinh (Real.pi * |v|) := by rw [Real.sinh_pos_iff]; positivity
  have hsinhne : Real.sinh (Real.pi * |v|) ≠ 0 := ne_of_gt hsinhpos
  set w : ℂ := (1:ℂ) + ((v:ℝ):ℂ)*I with hw
  have hwne : w ≠ 0 := by
    rw [hw]; intro h; apply hv; have := congrArg Complex.im h; simpa using this
  have hrefl := Complex.Gamma_mul_Gamma_one_sub w
  have h1w : 1 - w = -(((v:ℝ):ℂ)*I) := by rw [hw]; ring
  rw [h1w] at hrefl
  have hnegne : -(((v:ℝ):ℂ)*I) ≠ 0 := by
    intro h; apply hvne; have := congrArg Complex.im h; simpa using this
  have hadd := Complex.Gamma_add_one (-(((v:ℝ):ℂ)*I)) hnegne
  have hEq1 : -(((v:ℝ):ℂ)*I) + 1 = 1 - ((v:ℝ):ℂ)*I := by ring
  rw [hEq1] at hadd
  have hGneg : Complex.Gamma (-(((v:ℝ):ℂ)*I)) =
      Complex.Gamma (1 - ((v:ℝ):ℂ)*I) / (-(((v:ℝ):ℂ)*I)) := by
    rw [hadd]; field_simp
  have hstarw : star w = 1 - ((v:ℝ):ℂ)*I := by
    rw [hw]; apply Complex.ext <;> simp
  have hsinw : Complex.sin ((Real.pi:ℂ) * w) = -(Complex.sinh ((Real.pi:ℂ)*((v:ℝ):ℂ)) * I) := by
    rw [hw]
    have harg : (Real.pi:ℂ) * ((1:ℂ) + ((v:ℝ):ℂ)*I) = (Real.pi:ℂ) + I*((Real.pi:ℂ)*((v:ℝ):ℂ)) := by ring
    rw [harg, Complex.sin_add, Complex.sin_pi, Complex.cos_pi, zero_mul, neg_one_mul, zero_add,
        ← Complex.sin_mul_I]
    ring
  have hnormsin : ‖Complex.sin ((Real.pi:ℂ) * w)‖ = Real.sinh (Real.pi * |v|) := by
    rw [hsinw, norm_neg, norm_mul, Complex.norm_I, mul_one]
    have hcast : Complex.sinh ((Real.pi:ℂ)*((v:ℝ):ℂ)) = ((Real.sinh (Real.pi*v):ℝ):ℂ) := by
      rw [← Complex.ofReal_mul, Complex.ofReal_sinh]
    rw [hcast]
    rw [show ‖Complex.ofReal (Real.sinh (Real.pi*v))‖ = |Real.sinh (Real.pi*v)| from RCLike.norm_ofReal _]
    rw [Real.abs_sinh, abs_mul, abs_of_nonneg (le_of_lt Real.pi_pos)]
  have hnorm := congrArg norm hrefl
  rw [norm_mul, norm_div, Complex.norm_of_nonneg (le_of_lt Real.pi_pos)] at hnorm
  have hnegv : ‖(-(((v:ℝ):ℂ)*I))‖ = |v| := by
    rw [norm_neg, norm_mul, Complex.norm_I, mul_one]
    exact RCLike.norm_ofReal v
  have hG1 : ‖Complex.Gamma (-(((v:ℝ):ℂ)*I))‖ = ‖Complex.Gamma w‖ / |v| := by
    rw [hGneg, norm_div, hnegv]
    have h1 : ‖Complex.Gamma (1 - ((v:ℝ):ℂ)*I)‖ = ‖Complex.Gamma w‖ := by
      have := norm_Gamma_star w
      rwa [hstarw] at this
    rw [h1]
  rw [hG1, hnormsin] at hnorm
  have hL : ‖Complex.Gamma w‖ * (‖Complex.Gamma w‖ / |v|) = ‖Complex.Gamma w‖^2 / |v| := by ring
  rw [hL] at hnorm
  rw [div_eq_iff hvn] at hnorm
  rw [hnorm, div_mul_eq_mul_div]

private lemma Gamma_ratio_zero_lower (v : ℝ) (hv : v ≠ 0) :
    Real.sqrt (max (1/Real.pi) |v|) ≤
      ‖Complex.Gamma (1 + (v:ℂ)*I) / Complex.Gamma (1/2 + (v:ℂ)*I)‖ := by
  have ha : 0 < |v| := abs_pos.mpr hv
  have htpos : 0 < Real.tanh (Real.pi * |v|) := tanh_pos_of_pos (by positivity)
  have hr : ‖Complex.Gamma (1 + (v:ℂ)*I) / Complex.Gamma (1/2 + (v:ℂ)*I)‖^2 =
      |v| / Real.tanh (Real.pi * |v|) := by
    rw [norm_div, div_pow, Gamma_one_norm_sq v hv, gamma_abs_sq_half']
    rw [Real.tanh_eq_sinh_div_cosh]
    have hc : (0:ℝ) < Real.cosh (Real.pi * v) := Real.cosh_pos _
    have hcn : Real.cosh (Real.pi*|v|) ≠ 0 := ne_of_gt (Real.cosh_pos _)
    have hs : Real.sinh (Real.pi*|v|) ≠ 0 := ne_of_gt (Real.sinh_pos_iff.mpr (by positivity))
    rw [cosh_pi_abs v]
    field_simp
  have hle : max (1/Real.pi) |v| ≤ |v| / Real.tanh (Real.pi * |v|) := by
    apply max_le
    · rw [le_div_iff₀ htpos]
      have h1 : Real.tanh (Real.pi*|v|) ≤ Real.pi*|v| := tanh_le_self _ (by positivity)
      have h2 : (1/Real.pi) * Real.tanh (Real.pi*|v|) ≤ (1/Real.pi)*(Real.pi*|v|) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      have h3 : (1/Real.pi)*(Real.pi*|v|) = |v| := by field_simp
      linarith [h2, h3]
    · rw [le_div_iff₀ htpos]
      have h4 := Real.tanh_lt_one (Real.pi*|v|)
      nlinarith [h4, ha]
  rw [← Real.sqrt_sq (norm_nonneg _), hr]
  apply Real.sqrt_le_sqrt
  exact hle


private noncomputable def Wf (N : ℕ) (s : ℂ) : ℂ :=
  (N : ℂ) ^ ((1 - s) / 2) * (Complex.Gamma (1 - s / 4) / Complex.Gamma (1 / 2 + s / 4)) *
    Complex.log (s + 2)

private lemma Wf_norm_upper {N : ℕ} [NeZero N] (s : ℂ) (hre0 : 0 ≤ s.re) (hre1 : s.re ≤ 1) :
    ‖Wf N s‖ ≤ 5 * Real.exp 1 * ((N:ℝ) * (2 + |s.im|)) ^ ((1 - s.re)/2) *
      (Real.log ((N:ℝ) * (2 + |s.im|)) + 2) := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne N))
  have hcpow : ‖(N:ℂ) ^ ((1-s)/2)‖ = (N:ℝ)^((1-s.re)/2) := by
    rw [← Complex.ofReal_natCast]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hNpos]
    congr 1
    simp [Complex.div_re, Complex.sub_re]
  set b : ℝ := 2 + |s.im| with hb
  have hbpos : 0 < b := by rw [hb]; positivity
  have hb1 : 1 ≤ b := by rw [hb]; linarith [abs_nonneg s.im]
  set a : ℝ := 1/2 - s.re/2 with ha
  have hratio : ‖Complex.Gamma (1 - s/4) / Complex.Gamma (1/2 + s/4)‖ ≤ Real.exp (a * (Real.log b + 2)) := by
    rw [ha, hb]; exact Gamma_ratio_decay s hre0 hre1
  have hlogb' : ‖Complex.log (s + 2)‖ ≤ Real.log b + 5 := by rw [hb]; exact (clog_bounds hre0 hre1).2
  have hexp : Real.exp (a * (Real.log b + 2)) = b ^ a * Real.exp (2*a) := by
    rw [mul_add, Real.exp_add, Real.rpow_def_of_pos hbpos]; ring_nf
  have hexp2 : Real.exp (2*a) ≤ Real.exp 1 := by
    apply Real.exp_le_exp.mpr; rw [ha]; linarith
  have hab : a = (1 - s.re)/2 := by rw [ha]; ring
  have stepA : ‖Wf N s‖ = (N:ℝ)^((1-s.re)/2) *
      (‖Complex.Gamma (1 - s/4) / Complex.Gamma (1/2 + s/4)‖ * ‖Complex.log (s + 2)‖) := by
    rw [Wf, norm_mul, norm_mul, hcpow]; ring
  have stepB : (N:ℝ)^((1-s.re)/2) *
      (‖Complex.Gamma (1 - s/4) / Complex.Gamma (1/2 + s/4)‖ * ‖Complex.log (s + 2)‖)
      ≤ (N:ℝ)^((1-s.re)/2) * (Real.exp (a * (Real.log b + 2)) * (Real.log b + 5)) := by
    gcongr
  have stepC : (N:ℝ)^((1-s.re)/2) * (Real.exp (a * (Real.log b + 2)) * (Real.log b + 5))
      ≤ (N:ℝ)^((1-s.re)/2) * (b^a * Real.exp 1) * (Real.log b + 5) := by
    rw [hexp]
    have h1 : Real.exp (2*a) ≤ Real.exp 1 := hexp2
    have h2 : 0 ≤ b^a := Real.rpow_nonneg hbpos.le a
    have h3 : 0 ≤ (N:ℝ)^((1-s.re)/2) := Real.rpow_nonneg hNpos.le _
    have he1 : 0 < Real.exp 1 := Real.exp_pos 1
    have hL : 0 ≤ Real.log b + 5 := by linarith [Real.log_nonneg hb1]
    nlinarith [h1, h2, h3, he1, hL, mul_nonneg (mul_nonneg h3 h2) he1.le,
      mul_le_mul_of_nonneg_left h1 (mul_nonneg h3 h2)]
  have stepD : (N:ℝ)^((1-s.re)/2) * (b^a * Real.exp 1) * (Real.log b + 5)
      = Real.exp 1 * ((N:ℝ) * b)^((1-s.re)/2) * (Real.log b + 5) := by
    rw [Real.mul_rpow hNpos.le hbpos.le, hab]; ring
  have hkey : Real.log b + 5 ≤ 5 * (Real.log ((N:ℝ)*b) + 2) := by
    have hNb1 : (1:ℝ) ≤ (N:ℝ)*b := by nlinarith [hN1, hb1]
    have hlogNb : Real.log b ≤ Real.log ((N:ℝ)*b) := by
      apply Real.log_le_log hbpos; nlinarith [hN1]
    have hlogNb0 : 0 ≤ Real.log ((N:ℝ)*b) := Real.log_nonneg hNb1
    linarith
  have stepE : Real.exp 1 * ((N:ℝ) * b)^((1-s.re)/2) * (Real.log b + 5)
      ≤ 5 * Real.exp 1 * ((N:ℝ) * b)^((1-s.re)/2) * (Real.log ((N:ℝ)*b) + 2) := by
    have hpow0 : 0 ≤ Real.exp 1 * ((N:ℝ)*b)^((1-s.re)/2) := by
      exact mul_nonneg (Real.exp_pos 1).le (Real.rpow_nonneg (by positivity) _)
    calc Real.exp 1 * ((N:ℝ) * b)^((1-s.re)/2) * (Real.log b + 5)
        ≤ Real.exp 1 * ((N:ℝ) * b)^((1-s.re)/2) * (5 * (Real.log ((N:ℝ)*b) + 2)) := by
          exact mul_le_mul_of_nonneg_left hkey hpow0
      _ = 5 * Real.exp 1 * ((N:ℝ) * b)^((1-s.re)/2) * (Real.log ((N:ℝ)*b) + 2) := by ring
  calc ‖Wf N s‖ = (N:ℝ)^((1-s.re)/2) *
        (‖Complex.Gamma (1 - s/4) / Complex.Gamma (1/2 + s/4)‖ * ‖Complex.log (s + 2)‖) := stepA
    _ ≤ (N:ℝ)^((1-s.re)/2) * (Real.exp (a * (Real.log b + 2)) * (Real.log b + 5)) := stepB
    _ ≤ (N:ℝ)^((1-s.re)/2) * (b^a * Real.exp 1) * (Real.log b + 5) := stepC
    _ = Real.exp 1 * ((N:ℝ) * b)^((1-s.re)/2) * (Real.log b + 5) := stepD
    _ ≤ 5 * Real.exp 1 * ((N:ℝ) * b)^((1-s.re)/2) * (Real.log ((N:ℝ)*b) + 2) := stepE
    _ = 5 * Real.exp 1 * ((N:ℝ) * (2 + |s.im|)) ^ ((1 - s.re)/2) *
          (Real.log ((N:ℝ) * (2 + |s.im|)) + 2) := by rw [hb]



private lemma Gamma_ne_zero_of_re_pos' {z : ℂ} (hz : 0 < z.re) : Complex.Gamma z ≠ 0 := by
  apply Complex.Gamma_ne_zero; intro m hm
  have hre := congrArg Complex.re hm
  simp at hre
  have : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
  linarith

private lemma Wf_differentiableAt {N : ℕ} [NeZero N] (s : ℂ) (hlo : -2 < s.re) (hhi : s.re < 4) :
    DifferentiableAt ℂ (Wf N) s := by
  have hNnz : (N:ℂ) ≠ 0 := by
    have h := NeZero.ne N; exact_mod_cast h
  unfold Wf
  refine DifferentiableAt.mul (DifferentiableAt.mul ?_ ?_) ?_
  · exact DifferentiableAt.const_cpow (f := fun s : ℂ => (1 - s)/2) (by fun_prop) (Or.inl hNnz)
  · refine DifferentiableAt.div ?_ ?_ ?_
    · have hcomp : DifferentiableAt ℂ (fun s : ℂ => 1 - s/4) s := by fun_prop
      refine (Complex.differentiableAt_Gamma (1 - s/4) ?_).comp s hcomp
      intro m hm
      have hre := congrArg Complex.re hm
      rw [Complex.sub_re, Complex.div_re] at hre
      simp at hre
      have : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
      linarith
    · have hcomp : DifferentiableAt ℂ (fun s : ℂ => 1/2 + s/4) s := by fun_prop
      refine (Complex.differentiableAt_Gamma (1/2 + s/4) ?_).comp s hcomp
      intro m hm
      have hre := congrArg Complex.re hm
      rw [Complex.add_re, Complex.div_re] at hre
      simp at hre
      have : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
      linarith
    · apply Gamma_ne_zero_of_re_pos'
      rw [Complex.add_re, Complex.div_re]; simp; linarith
  · have hmem : s + 2 ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]; left
      rw [Complex.add_re]; simp; linarith
    exact (differentiableAt_log hmem).comp s (by fun_prop : DifferentiableAt ℂ (fun t : ℂ => t + 2) s)

private lemma Wf_ne_zero_strip {N : ℕ} [NeZero N] (s : ℂ) (hlo : 0 ≤ s.re) (hhi : s.re ≤ 1) :
    Wf N s ≠ 0 := by
  have hNnz : (N:ℂ) ≠ 0 := by
    have h := NeZero.ne N; exact_mod_cast h
  have hcpow : (N:ℂ)^((1-s)/2) ≠ 0 := by
    rw [Complex.cpow_ne_zero_iff]; exact Or.inl hNnz
  have hG1 : Complex.Gamma (1 - s/4) ≠ 0 := by
    apply Gamma_ne_zero_of_re_pos'
    rw [Complex.sub_re, Complex.div_re]; simp; linarith
  have hG2 : Complex.Gamma (1/2 + s/4) ≠ 0 := by
    apply Gamma_ne_zero_of_re_pos'
    rw [Complex.add_re, Complex.div_re]; simp; linarith
  have hlog : Complex.log (s+2) ≠ 0 := by
    intro h
    have hne : s + 2 ≠ 0 := by
      intro h0
      have hre := congrArg Complex.re h0
      rw [Complex.add_re] at hre; simp at hre; linarith
    have := congrArg Complex.exp h
    rw [Complex.exp_log hne, Complex.exp_zero] at this
    have hre := congrArg Complex.re this
    rw [Complex.add_re] at hre; simp at hre; linarith
  rw [Wf]
  exact mul_ne_zero (mul_ne_zero hcpow (div_ne_zero hG1 hG2)) hlog

private lemma F_differentiableOn {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    DifferentiableOn ℂ (fun s : ℂ => LFunction χ s / Wf N s) (re ⁻¹' Set.Ioo 0 1) := by
  intro s hs
  rw [Set.mem_preimage, Set.mem_Ioo] at hs
  exact ((differentiable_LFunction hχ s).differentiableWithinAt).div
    ((Wf_differentiableAt s (by linarith [hs.1]) (by linarith [hs.2])).differentiableWithinAt)
    (Wf_ne_zero_strip s (le_of_lt hs.1) (le_of_lt hs.2))

private lemma F_continuousOn {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    ContinuousOn (fun s : ℂ => LFunction χ s / Wf N s) (re ⁻¹' Set.Icc 0 1) := by
  intro s hs
  rw [Set.mem_preimage, Set.mem_Icc] at hs
  exact (ContinuousAt.continuousWithinAt (((differentiable_LFunction hχ s).continuousAt).div
    ((Wf_differentiableAt s (by linarith [hs.1]) (by linarith [hs.2])).continuousAt)
    (Wf_ne_zero_strip s hs.1 hs.2)))

private lemma Gamma_ratio_zero_lower' (t : ℝ) (ht : t ≠ 0) :
    Real.sqrt (max (1/Real.pi) (|t|/4)) ≤
      ‖Complex.Gamma (1 + (t:ℂ)/4*I) / Complex.Gamma ((1/2:ℂ) + (t:ℂ)/4*I)‖ := by
  have h := Gamma_ratio_zero_lower (t/4) (by positivity)
  rw [show |t/4| = |t|/4 from by rw [abs_div]; norm_num] at h
  have e : (t:ℂ)/4 = (((t/4:ℝ)):ℂ) := by push_cast; ring
  rw [e]
  exact h

private lemma Wf_norm_lower_zero {N : ℕ} [NeZero N] (t : ℝ) (ht : t ≠ 0) :
    (1/4) * (N:ℝ)^((1:ℝ)/2) * Real.sqrt (max 1 |t|) * (Real.log (2+|t|)) ≤
      ‖Wf N ((t:ℂ)*I)‖ := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hnum : ‖(N:ℂ)^((1-(t:ℂ)*I)/2)‖ = (N:ℝ)^((1:ℝ)/2) := by
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hNpos]
    congr 1
    rw [Complex.div_re, Complex.sub_re]; simp
  have hratio_eq : ‖Complex.Gamma (1 - ((t:ℂ)*I)/4) / Complex.Gamma (1/2 + ((t:ℂ)*I)/4)‖ =
      ‖Complex.Gamma (1 + (t:ℂ)/4*I) / Complex.Gamma (1/2 + (t:ℂ)/4*I)‖ := by
    have e1 : 1 - ((t:ℂ)*I)/4 = star (1 + (t:ℂ)/4*I) := by apply Complex.ext <;> simp
    have e2 : (1/2:ℂ) + ((t:ℂ)*I)/4 = (1/2:ℂ) + (t:ℂ)/4*I := by ring
    rw [e1, e2]
    simp only [norm_div, Gamma_star, norm_star]
  have hratio : Real.sqrt (max (1/Real.pi) (|t|/4)) ≤
      ‖Complex.Gamma (1 - ((t:ℂ)*I)/4) / Complex.Gamma (1/2 + ((t:ℂ)*I)/4)‖ := by
    rw [hratio_eq]; exact Gamma_ratio_zero_lower' t ht
  have hlog : Real.log (2+|t|)/2 ≤ ‖Complex.log ((t:ℂ)*I + 2)‖ := by
    have h := (clog_bounds (s := (t:ℂ)*I) (by simp) (by simp)).1
    rwa [show ((t:ℂ)*I).im = t from by simp] at h
  have hWf : ‖Wf N ((t:ℂ)*I)‖ = (N:ℝ)^((1:ℝ)/2) *
      (‖Complex.Gamma (1 - ((t:ℂ)*I)/4) / Complex.Gamma (1/2 + ((t:ℂ)*I)/4)‖ *
        ‖Complex.log ((t:ℂ)*I + 2)‖) := by
    rw [Wf, norm_mul, norm_mul, hnum]; ring
  rw [hWf]
  have hmax : Real.sqrt (max 1 |t|) ≤ 2 * Real.sqrt (max (1/Real.pi) (|t|/4)) := by
    have hp4 : (1:ℝ) ≤ 4/Real.pi := by rw [le_div_iff₀ Real.pi_pos]; linarith [Real.pi_lt_four]
    rcases lt_or_ge |t| (4/Real.pi) with h | h
    · have hmax1 : max 1 |t| ≤ 4/Real.pi := by
        rcases lt_or_ge |t| 1 with h1 | h1
        · rw [max_eq_left (le_of_lt h1)]; exact hp4
        · rw [max_eq_right h1]; exact le_of_lt h
      have hm : max (1/Real.pi) (|t|/4) = 1/Real.pi := by
        apply max_eq_left
        rw [div_le_div_iff₀ (by norm_num : (0:ℝ) < 4) Real.pi_pos]
        have := (lt_div_iff₀ Real.pi_pos).mp h
        linarith
      rw [hm, show (2:ℝ)*Real.sqrt (1/Real.pi) = Real.sqrt (4*(1/Real.pi)) from by
        rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4),
            show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]]
      apply Real.sqrt_le_sqrt
      rwa [mul_one_div]
    · have hm : max (1/Real.pi) (|t|/4) = |t|/4 := by
        apply max_eq_right
        rw [div_le_div_iff₀ Real.pi_pos (by norm_num : (0:ℝ) < 4)]
        have := (div_le_iff₀ Real.pi_pos).mp h
        linarith
      rw [hm, show (2:ℝ)*Real.sqrt (|t|/4) = Real.sqrt (4*(|t|/4)) from by
        rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4),
            show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)],
        show 4*(|t|/4) = |t| by ring,
        max_eq_right (by linarith [h, hp4] : (1:ℝ) ≤ |t|)]
  have hspos : 0 < Real.sqrt (max (1/Real.pi) (|t|/4)) := Real.sqrt_pos.mpr (by positivity)
  have hlogpos := Real.log_nonneg (by linarith [abs_nonneg t] : (1:ℝ) ≤ 2+|t|)
  have hN12 : 0 ≤ (N:ℝ)^((1:ℝ)/2) := Real.rpow_nonneg hNpos.le _
  calc (1/4) * (N:ℝ)^((1:ℝ)/2) * Real.sqrt (max 1 |t|) * (Real.log (2+|t|))
      ≤ (1/4) * (N:ℝ)^((1:ℝ)/2) * (2 * Real.sqrt (max (1/Real.pi) (|t|/4))) * (Real.log (2+|t|)) := by
        gcongr
    _ ≤ (N:ℝ)^((1:ℝ)/2) * (Real.sqrt (max (1/Real.pi) (|t|/4)) * ‖Complex.log ((t:ℂ)*I + 2)‖) := by
        have hs1 : 0 < Real.sqrt (max (1/Real.pi) (|t|/4)) := hspos
        have := mul_le_mul_of_nonneg_left hlog (le_of_lt (mul_pos hspos hNpos))
        nlinarith [this, hspos, hlogpos, hN12]
    _ ≤ (N:ℝ)^((1:ℝ)/2) * (‖Complex.Gamma (1 - ((t:ℂ)*I)/4) / Complex.Gamma (1/2 + ((t:ℂ)*I)/4)‖ *
          ‖Complex.log ((t:ℂ)*I + 2)‖) := by
        gcongr

private lemma Wf_norm_lower_one {N : ℕ} [NeZero N] (t : ℝ) :
    Real.log (2+|t|)/2 ≤ ‖Wf N ((1:ℂ) + (t:ℂ)*I)‖ := by
  set s : ℂ := (1:ℂ) + (t:ℂ)*I with hs
  have hsre : s.re = 1 := by rw [hs]; simp
  have hnum : ‖(N:ℂ)^((1-s)/2)‖ = 1 := by
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N))]
    congr 1
    rw [Complex.div_re, Complex.sub_re, hsre]; simp
  have hratio : ‖Complex.Gamma (1 - s/4) / Complex.Gamma (1/2 + s/4)‖ = 1 := by
    have e1 : 1 - s/4 = star (1/2 + s/4) := by
      rw [hs]; apply Complex.ext <;> simp <;> ring
    rw [e1, norm_div, Gamma_star, norm_star]
    rw [div_self]
    apply norm_ne_zero_iff.mpr
    apply Complex.Gamma_ne_zero; intro m hm
    have hre : ((1/2:ℂ) + s/4).re = 3/4 := by rw [hs]; simp; ring
    have := congrArg Complex.re hm
    rw [hre] at this
    simp at this
    have hm0 : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
    linarith
  have hlog : Real.log (2+|t|)/2 ≤ ‖Complex.log (s + 2)‖ := by
    rw [hs]
    have h := (clog_bounds (s := (1:ℂ) + (t:ℂ)*I) (by simp) (by simp)).1
    simpa using h
  have hWf : ‖Wf N s‖ = 1 * (1 * ‖Complex.log (s+2)‖) := by
    rw [Wf, norm_mul, norm_mul, hnum, hratio]
    ring
  rw [hWf, one_mul, one_mul]
  exact hlog


private lemma sqrt_max_le (t : ℝ) : (2+|t|)^((1:ℝ)/2) ≤ 4 * Real.sqrt (max (1/Real.pi) (|t|/4)) := by
  have h1 : (2+|t|)^((1:ℝ)/2) ≤ Real.sqrt 3 * Real.sqrt (max 1 |t|) := by
    rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 3), ← Real.sqrt_eq_rpow]
    apply Real.sqrt_le_sqrt
    rcases lt_or_ge |t| 1 with h | h
    · rw [max_eq_left (le_of_lt h)]; nlinarith
    · rw [max_eq_right h]; nlinarith [abs_nonneg t]
  have h2 : Real.sqrt (max 1 |t|) ≤ 2 * Real.sqrt (max (1/Real.pi) (|t|/4)) := by
    have hp4 : (1:ℝ) ≤ 4/Real.pi := by rw [le_div_iff₀ Real.pi_pos]; linarith [Real.pi_lt_four]
    rcases lt_or_ge |t| (4/Real.pi) with h | h
    · have hmax1 : max 1 |t| ≤ 4/Real.pi := by
        rcases lt_or_ge |t| 1 with h1 | h1
        · rw [max_eq_left (le_of_lt h1)]; exact hp4
        · rw [max_eq_right h1]; exact le_of_lt h
      have hm : max (1/Real.pi) (|t|/4) = 1/Real.pi := by
        apply max_eq_left
        rw [div_le_div_iff₀ (by norm_num : (0:ℝ) < 4) Real.pi_pos]
        have := (lt_div_iff₀ Real.pi_pos).mp h
        linarith
      rw [hm, show (2:ℝ)*Real.sqrt (1/Real.pi) = Real.sqrt (4*(1/Real.pi)) from by
        rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4),
            show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]]
      apply Real.sqrt_le_sqrt
      rwa [mul_one_div]
    · have hm : max (1/Real.pi) (|t|/4) = |t|/4 := by
        apply max_eq_right
        rw [div_le_div_iff₀ Real.pi_pos (by norm_num : (0:ℝ) < 4)]
        have := (div_le_iff₀ Real.pi_pos).mp h
        linarith
      rw [hm, show (2:ℝ)*Real.sqrt (|t|/4) = Real.sqrt (4*(|t|/4)) from by
        rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4),
            show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)],
        show 4*(|t|/4) = |t| by ring,
        max_eq_right (by linarith [h, hp4] : (1:ℝ) ≤ |t|)]
  have h3 : Real.sqrt 3 ≤ 2 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  calc (2+|t|)^((1:ℝ)/2) ≤ Real.sqrt 3 * Real.sqrt (max 1 |t|) := h1
    _ ≤ 2 * (2 * Real.sqrt (max (1/Real.pi) (|t|/4))) := by
        apply mul_le_mul h3 h2 (Real.sqrt_nonneg _) (by norm_num)
    _ = 4 * Real.sqrt (max (1/Real.pi) (|t|/4)) := by ring

private lemma log_bound_div (N : ℕ) [NeZero N] (t : ℝ) :
    (Real.log N + Real.log (2+|t|) + 6) ≤ (Real.log N + 8) * (Real.log (2+|t|) + 1) := by
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne N))
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hlogt : 0 ≤ Real.log (2+|t|) := Real.log_nonneg (by linarith [abs_nonneg t])
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  nlinarith [hlogN, hlogt, hlog2, Real.log_two_lt_d9]
private lemma Wf_norm_lower_global {N : ℕ} [NeZero N] (z : ℂ) (hlo : 0 ≤ z.re) (hhi : z.re ≤ 1) :
    (1/2) * Real.exp (-1) * (2+|z.im|)^((-(1:ℝ)/2)) * Real.log (2+|z.im|) ≤ ‖Wf N z‖ := by
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne N))
  have hzpos : 0 < 2 + |z.im| := by linarith [abs_nonneg z.im]
  have hnum : 1 ≤ ‖(N:ℂ)^((1-z)/2)‖ := by
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    apply Real.one_le_rpow hN1
    rw [Complex.div_re, Complex.sub_re]; simp; linarith
  set u₂ : ℝ := 1 - z.re/4 with hu₂
  set u₁ : ℝ := 1/2 + z.re/4 with hu₁
  set τ : ℝ := z.im/4 with hτ
  have hu1 : (1:ℝ)/2 ≤ u₁ := by rw [hu₁]; linarith
  have h12 : u₁ ≤ u₂ := by rw [hu₁, hu₂]; linarith
  have h2 : u₂ ≤ 8 := by rw [hu₂]; linarith
  have hnum2 : (1 - z/4) = star (((u₂:ℝ):ℂ) + ((τ:ℝ):ℂ)*I) := by
    rw [hu₂, hτ]; apply Complex.ext <;> simp
  have hden2 : (1/2 + z/4) = ((u₁:ℝ):ℂ) + ((τ:ℝ):ℂ)*I := by
    rw [hu₁, hτ]; apply Complex.ext <;> simp
  have hA : Complex.Gamma (((u₂:ℝ):ℂ) + ((τ:ℝ):ℂ)*I) ≠ 0 := by
    apply Complex.Gamma_ne_zero; intro m hm
    have := congrArg Complex.re hm; simp at this; linarith [hu1]
  have hB : Complex.Gamma (((u₁:ℝ):ℂ) + ((τ:ℝ):ℂ)*I) ≠ 0 := by
    apply Complex.Gamma_ne_zero; intro m hm
    have := congrArg Complex.re hm; simp at this; linarith [hu1]
  have hApos : 0 < ‖Complex.Gamma (((u₂:ℝ):ℂ) + ((τ:ℝ):ℂ)*I)‖ := norm_pos_iff.mpr hA
  have hBpos : 0 < ‖Complex.Gamma (((u₁:ℝ):ℂ) + ((τ:ℝ):ℂ)*I)‖ := norm_pos_iff.mpr hB
  have hinc := Commons.Analysis.SpecialFunctions.Gamma.abs_log_norm_Gamma_sub_le u₁ u₂ τ hu1 h12 h2
  have hτle : |τ| ≤ |z.im| := by rw [hτ, abs_div]; linarith [abs_nonneg z.im]
  have hratio' : Real.exp (-((u₂-u₁)*(Real.log (2+|τ|)+2))) ≤
      ‖Complex.Gamma (((u₂:ℝ):ℂ) + ((τ:ℝ):ℂ)*I)‖ / ‖Complex.Gamma (((u₁:ℝ):ℂ) + ((τ:ℝ):ℂ)*I)‖ := by
    rw [abs_le] at hinc
    obtain ⟨hlo2, _⟩ := hinc
    have hexp : Real.exp (Real.log ‖Complex.Gamma (((u₂:ℝ):ℂ) + ((τ:ℝ):ℂ)*I)‖ -
        Real.log ‖Complex.Gamma (((u₁:ℝ):ℂ) + ((τ:ℝ):ℂ)*I)‖) =
        ‖Complex.Gamma (((u₂:ℝ):ℂ) + ((τ:ℝ):ℂ)*I)‖ / ‖Complex.Gamma (((u₁:ℝ):ℂ) + ((τ:ℝ):ℂ)*I)‖ := by
      rw [Real.exp_sub, Real.exp_log hApos, Real.exp_log hBpos]
    rw [← hexp]
    exact Real.exp_le_exp.mpr hlo2
  have hu21 : u₂ - u₁ = 1/2 - z.re/2 := by rw [hu₂, hu₁]; ring
  have hC : (u₂-u₁)*(Real.log (2+|τ|)+2) ≤ 1 + (1/2)*Real.log (2+|z.im|) := by
    have hlog2 : Real.log (2+|τ|) ≤ Real.log (2+|z.im|) :=
      Real.log_le_log (by linarith [abs_nonneg τ]) (by linarith [hτle])
    have hle : (u₂-u₁) ≤ 1/2 := by rw [hu21]; linarith
    have h0 : 0 ≤ u₂-u₁ := by rw [hu21]; linarith
    have h3 : 0 ≤ Real.log (2+|τ|) + 2 := by linarith [Real.log_nonneg (by linarith [abs_nonneg τ] : (1:ℝ) ≤ 2+|τ|)]
    nlinarith [hle, hlog2, h0, h3]
  have hgoal : Real.exp (-1) * (2+|z.im|)^((-(1:ℝ)/2)) =
      Real.exp (-(1 + (1/2)*Real.log (2+|z.im|))) := by
    rw [Real.rpow_def_of_pos hzpos, ← Real.exp_add]
    congr 1; ring
  have hratio : Real.exp (-1) * (2+|z.im|)^((-(1:ℝ)/2)) ≤
      ‖Complex.Gamma (1 - z/4) / Complex.Gamma (1/2 + z/4)‖ := by
    rw [hgoal, hnum2, hden2, norm_div, norm_Gamma_star]
    exact (Real.exp_le_exp.mpr (by rw [neg_le_neg_iff]; exact hC)).trans hratio'
  have hlog : Real.log (2+|z.im|)/2 ≤ ‖Complex.log (z+2)‖ := (clog_bounds hlo hhi).1
  have hWf : ‖Wf N z‖ = ‖(N:ℂ)^((1-z)/2)‖ *
      (‖Complex.Gamma (1 - z/4) / Complex.Gamma (1/2 + z/4)‖ * ‖Complex.log (z+2)‖) := by
    rw [Wf, norm_mul, norm_mul]; ring
  rw [hWf]
  have hel : 0 < Real.exp (-1) := Real.exp_pos _
  have hlg : 0 ≤ Real.log (2+|z.im|) := Real.log_nonneg (by linarith [abs_nonneg z.im])
  have hpp : 0 < (2+|z.im|)^((-(1:ℝ)/2)) := Real.rpow_pos_of_pos hzpos _
  calc (1/2) * Real.exp (-1) * (2+|z.im|)^((-(1:ℝ)/2)) * Real.log (2+|z.im|)
      ≤ 1 * ((Real.exp (-1) * (2+|z.im|)^((-(1:ℝ)/2))) * ‖Complex.log (z+2)‖) := by
        nlinarith [hlog, hel, hlg, hpp, mul_pos hel hpp]
    _ ≤ ‖(N:ℂ)^((1-z)/2)‖ * (‖Complex.Gamma (1 - z/4) / Complex.Gamma (1/2 + z/4)‖ * ‖Complex.log (z+2)‖) := by
        gcongr

private lemma F_bound_strip {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hχprim : χ.IsPrimitive) :
    ∃ Cg : ℝ, 0 < Cg ∧ ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 → 1 ≤ |z.im| →
      ‖LFunction χ z / Wf N z‖ ≤ Cg * (2 + |z.im|)^3 := by
  obtain ⟨D, hDpos, hD⟩ := LFunction_strip_upper_explicit (N := N) χ hχ hχprim
  refine ⟨64 * (D + 1) * ((N:ℝ) + 1)^2, by positivity, ?_⟩
  intro z hlo hhi hbig
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne N))
  have hDz : ‖LFunction χ z‖ ≤ D * ((N:ℝ) + |z.im| + 1)^2 := by
    have h := hD z.re z.im hlo (by linarith [hhi])
    rwa [show (z.re:ℂ) + I*(z.im:ℂ) = z from by apply Complex.ext <;> simp] at h
  have hW := Wf_norm_lower_global (N := N) z hlo hhi
  have hzpos : 0 < 2 + |z.im| := by linarith [abs_nonneg z.im]
  have hWpos : 0 < (1/2) * Real.exp (-1) * (2+|z.im|)^((-(1:ℝ)/2)) * Real.log (2+|z.im|) := by
    have h3 : 0 < Real.log (2+|z.im|) := Real.log_pos (by linarith [abs_nonneg z.im])
    positivity
  have hlog1 : 1 ≤ Real.log (2+|z.im|) := by
    have h1 : Real.log (Real.exp 1) ≤ Real.log (2+|z.im|) :=
      Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_three, abs_nonneg z.im])
    rwa [Real.log_exp] at h1
  have he1 : (1:ℝ)/4 ≤ Real.exp (-1) := by
    rw [Real.exp_neg, one_div]
    exact (inv_le_inv₀ (by norm_num : (0:ℝ) < 4) (Real.exp_pos 1)).mpr
      (by linarith [Real.exp_one_lt_three])
  have hb : 0 < (2+|z.im|)^((-(1:ℝ)/2)) := Real.rpow_pos_of_pos hzpos _
  have hrp : (2+|z.im|)^3 * (2+|z.im|)^((-(1:ℝ)/2)) = (2+|z.im|)^((5:ℝ)/2) := by
    rw [← Real.rpow_natCast (2+|z.im|) 3, ← Real.rpow_add hzpos]
    congr 1
    push_cast
    ring
  have h2z : (2+|z.im|)^((2:ℝ)) ≤ (2+|z.im|)^((5:ℝ)/2) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg z.im]) (by norm_num)
  have hNle2 : ((N:ℝ)+|z.im|+1)^2 ≤ ((N:ℝ)+1)^2 * (2+|z.im|)^((2:ℝ)) := by
    have h1 : (N:ℝ)+|z.im|+1 ≤ ((N:ℝ)+1)*(2+|z.im|) := by nlinarith [hN1, abs_nonneg z.im]
    have h3 : (2+|z.im|)^2 = (2+|z.im|)^((2:ℝ)) := (Real.rpow_natCast _ 2).symm
    rw [← h3]
    nlinarith [h1, hN1, abs_nonneg z.im]
  rw [norm_div]
  refine (div_le_div_of_nonneg_left (norm_nonneg _) hWpos hW).trans ?_
  rw [div_le_iff₀ hWpos]
  have h5pos : 0 < (2+|z.im|)^((5:ℝ)/2) := Real.rpow_pos_of_pos hzpos _
  have hchain : D * ((N:ℝ)+|z.im|+1)^2 ≤
      (64 * (D + 1) * ((N:ℝ) + 1)^2 * (2 + |z.im|)^3) *
        ((1/2) * Real.exp (-1) * (2+|z.im|)^((-(1:ℝ)/2)) * Real.log (2+|z.im|)) := by
    rw [show (64 * (D + 1) * ((N:ℝ) + 1)^2 * (2 + |z.im|)^3) *
        ((1/2) * Real.exp (-1) * (2+|z.im|)^((-(1:ℝ)/2)) * Real.log (2+|z.im|))
        = 64 * (D+1) * ((N:ℝ)+1)^2 * ((1/2) * Real.exp (-1)) *
          ((2+|z.im|)^3 * (2+|z.im|)^((-(1:ℝ)/2))) * Real.log (2+|z.im|) by ring, hrp]
    have hNn : (0:ℝ) ≤ ((N:ℝ)+1)^2 := by positivity
    have h1 : D * ((N:ℝ)+|z.im|+1)^2 ≤ D * (((N:ℝ)+1)^2 * (2+|z.im|)^((2:ℝ))) :=
      mul_le_mul_of_nonneg_left hNle2 hDpos.le
    have h2 : D * (((N:ℝ)+1)^2 * (2+|z.im|)^((2:ℝ))) ≤ D * (((N:ℝ)+1)^2 * (2+|z.im|)^((5:ℝ)/2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2z hNn) hDpos.le
    have h3 : D * (((N:ℝ)+1)^2 * (2+|z.im|)^((5:ℝ)/2)) ≤
        64 * (D+1) * ((N:ℝ)+1)^2 * ((1/2) * Real.exp (-1)) *
          (2+|z.im|)^((5:ℝ)/2) * Real.log (2+|z.im|) := by
      have hD1 : D ≤ 64*(D+1) := by linarith
      have h5n : 0 ≤ (2+|z.im|)^((5:ℝ)/2) := le_of_lt h5pos
      have hmul : (1:ℝ)/4 ≤ Real.exp (-1) * Real.log (2+|z.im|) := by
        nlinarith [he1, hlog1, (Real.exp_pos (-1)).le]
      have hNn2 : 0 ≤ ((N:ℝ)+1)^2 * (2+|z.im|)^((5:ℝ)/2) := by positivity
      have hD8 : D ≤ 8*(D+1) := by linarith
      have hmul4 : (1:ℝ) ≤ 4 * (Real.exp (-1) * Real.log (2+|z.im|)) := by linarith [hmul]
      have hstep : 8*(D+1) ≤ 32*(D+1)*(Real.exp (-1) * Real.log (2+|z.im|)) := by
        rw [show 32*(D+1)*(Real.exp (-1)*Real.log (2+|z.im|))
            = 8*(D+1) * (4*(Real.exp (-1)*Real.log (2+|z.im|))) by ring]
        simpa using mul_le_mul_of_nonneg_left hmul4 (show (0:ℝ) ≤ 8*(D+1) by linarith)
      calc D * (((N:ℝ)+1)^2 * (2+|z.im|)^((5:ℝ)/2))
          ≤ 8*(D+1) * (((N:ℝ)+1)^2 * (2+|z.im|)^((5:ℝ)/2)) :=
            mul_le_mul_of_nonneg_right hD8 (by positivity)
        _ ≤ 32*(D+1)*(Real.exp (-1)*Real.log (2+|z.im|)) * (((N:ℝ)+1)^2 * (2+|z.im|)^((5:ℝ)/2)) :=
            mul_le_mul_of_nonneg_right hstep (by positivity)
        _ = 64 * (D+1) * ((N:ℝ)+1)^2 * ((1/2) * Real.exp (-1)) * (2+|z.im|)^((5:ℝ)/2) * Real.log (2+|z.im|) := by ring
    exact h1.trans (h2.trans h3)

  linarith [hDz, hchain]


private lemma sqrt_pair_le (t : ℝ) : (2+|t|)^((1:ℝ)/2) ≤ 2 * Real.sqrt (max 1 |t|) := by
  rw [← Real.sqrt_eq_rpow]
  rcases lt_or_ge |t| 1 with h | h
  · rw [max_eq_left (le_of_lt h), Real.sqrt_one, mul_one]
    have hs : Real.sqrt (2+|t|) ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by linarith)
    rwa [show Real.sqrt 4 = 2 by
      rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]] at hs
  · rw [max_eq_right h]
    calc Real.sqrt (2+|t|) ≤ Real.sqrt (4*|t|) := Real.sqrt_le_sqrt (by linarith)
      _ = 2 * Real.sqrt |t| := by
          rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4),
              show Real.sqrt 4 = 2 by
                rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]]

private lemma Wf_zero_lower {N : ℕ} [NeZero N] : (1/4 : ℝ) ≤ ‖Wf N 0‖ := by
  have hN1 : (1:ℝ) ≤ N := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne N))
  have hNpos : (0:ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hWf : Wf N 0 = (N:ℂ)^((1:ℂ)/2) * (Complex.Gamma (1:ℂ) / Complex.Gamma (1/2)) *
      Complex.log 2 := by
    unfold Wf
    norm_num
  rw [hWf, norm_mul, norm_mul]
  have hnum : 1 ≤ ‖(N:ℂ)^((1:ℂ)/2)‖ := by
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hNpos]
    apply Real.one_le_rpow hN1
    simp [Complex.div_re]
  have hG2 : ‖Complex.Gamma ((1/2:ℂ))‖ ≤ 2 := by
    have h := gamma_abs_sq_half' 0
    have h' : ‖Complex.Gamma ((1/2:ℂ))‖^2 = Real.pi := by simpa using h
    have hpos : (0:ℝ) ≤ ‖Complex.Gamma (1/2:ℂ)‖ := norm_nonneg _
    nlinarith [h', hpos, Real.pi_lt_four]
  have hG2pos : 0 < ‖Complex.Gamma (1/2:ℂ)‖ := by
    apply norm_pos_iff.mpr
    apply Complex.Gamma_ne_zero
    intro m hm
    have hre := congrArg Complex.re hm
    simp at hre
    have hmm : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
    linarith
  have hG : (1:ℝ)/2 ≤ ‖Complex.Gamma (1:ℂ) / Complex.Gamma (1/2)‖ := by
    have hG1 : ‖Complex.Gamma (1:ℂ)‖ = 1 := by rw [Complex.Gamma_one, norm_one]
    rw [norm_div, hG1]
    exact one_div_le_one_div_of_le hG2pos hG2
  have hlog : (1:ℝ)/2 ≤ ‖Complex.log 2‖ := by
    have h2 : Complex.log (2:ℂ) = ((Real.log 2 : ℝ):ℂ) := by
      have := Complex.ofReal_log (show (0:ℝ) ≤ 2 by norm_num)
      simpa using this.symm
    rw [h2, show ‖((Real.log 2 : ℝ):ℂ)‖ = |Real.log 2| from RCLike.norm_ofReal _,
        abs_of_nonneg (le_of_lt (Real.log_pos (by norm_num)))]
    linarith [Real.log_two_gt_d9]
  have h23 : (1/2:ℝ) * (1/2) ≤
      ‖Complex.Gamma (1:ℂ) / Complex.Gamma (1/2)‖ * ‖Complex.log 2‖ :=
    mul_le_mul hG hlog (by norm_num) (by linarith)
  have hmain := mul_le_mul hnum h23 (by norm_num : (0:ℝ) ≤ (1/2:ℝ)*(1/2)) (by linarith)
  linarith

private lemma F_bound_boundary {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hχprim : χ.IsPrimitive) :
    ∃ Cb : ℝ, 0 < Cb ∧ (∀ z : ℂ, z.re = 0 → ‖LFunction χ z / Wf N z‖ ≤ Cb) ∧
      (∀ z : ℂ, z.re = 1 → ‖LFunction χ z / Wf N z‖ ≤ Cb) := by
  obtain ⟨K, hKpos, hKb⟩ := LFunction_norm_zero_le χ hχ hχprim
  obtain ⟨D, hDpos, hD⟩ := LFunction_strip_upper_explicit (N := N) χ hχ hχprim
  have hlogN : 0 ≤ Real.log N :=
    Real.log_nonneg (by exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne N)))
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hNpos : (0:ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hN12 : 0 < (N:ℝ)^((1:ℝ)/2) := Real.rpow_pos_of_pos hNpos _
  refine ⟨1000 * (K + 1) * (Real.log N + 8) + 1000 + 4 * D * ((N:ℝ)+1)^2, by positivity, ?_, ?_⟩
  · intro z hz
    have hzeq : z = ((z.im:ℝ):ℂ)*I := by apply Complex.ext <;> simp [hz]
    rw [hzeq]
    rcases eq_or_ne z.im 0 with h0 | h0
    · rw [h0]
      simp only [Complex.ofReal_zero, zero_mul]
      have hL0 : ‖LFunction χ 0‖ ≤ D * ((N:ℝ)+1)^2 := by
        have h := hD 0 0 (by norm_num) (by norm_num)
        simpa using h
      have hW0 := Wf_zero_lower (N := N)
      rw [norm_div]
      have hWpos : 0 < ‖Wf N 0‖ := by linarith
      refine le_trans (div_le_div₀ (by positivity) hL0 (by norm_num : (0:ℝ) < 1/4) hW0) ?_
      rw [show D * ((N:ℝ)+1)^2 / (1/4) = 4 * D * ((N:ℝ)+1)^2 by ring]
      have h1000 : (0:ℝ) ≤ 1000 * (K + 1) * (Real.log N + 8) := by positivity
      linarith
    · have hL := hKb z.im h0
      have hW := Wf_norm_lower_zero (N := N) z.im h0
      have hsp := sqrt_pair_le z.im
      rw [norm_div]
      have hlogt : 0 < Real.log (2+|z.im|) := Real.log_pos (by linarith [abs_nonneg z.im])
      have hspos : 0 < Real.sqrt (max 1 |z.im|) :=
        Real.sqrt_pos.mpr (lt_of_lt_of_le (by norm_num) (le_max_left 1 |z.im|))
      have hDl : 0 < (1/4) * (N:ℝ)^((1:ℝ)/2) * Real.sqrt (max 1 |z.im|) * Real.log (2+|z.im|) :=
        mul_pos (mul_pos (mul_pos (by norm_num) hN12) hspos) hlogt
      have hC0 : 0 ≤ K * (N:ℝ)^((1:ℝ)/2) * (2+|z.im|)^((1:ℝ)/2) *
          (Real.log N + Real.log (2+|z.im|) + 6) := by
        have h1 : 0 ≤ (2+|z.im|)^((1:ℝ)/2) := Real.rpow_nonneg (by linarith [abs_nonneg z.im]) _
        have h2 : 0 ≤ Real.log N + Real.log (2+|z.im|) + 6 := by
          have := Real.log_nonneg (by linarith [abs_nonneg z.im] : (1:ℝ) ≤ 2+|z.im|)
          linarith
        exact mul_nonneg (mul_nonneg (mul_nonneg hKpos.le hN12.le) h1) h2
      have hstep : ‖LFunction χ (((z.im:ℝ):ℂ)*I)‖ / ‖Wf N (((z.im:ℝ):ℂ)*I)‖ ≤
          K * (N:ℝ)^((1:ℝ)/2) * (2+|z.im|)^((1:ℝ)/2) * (Real.log N + Real.log (2+|z.im|) + 6) /
            ((1/4) * (N:ℝ)^((1:ℝ)/2) * Real.sqrt (max 1 |z.im|) * Real.log (2+|z.im|)) :=
        div_le_div₀ hC0 hL hDl hW
      refine hstep.trans ?_
      rw [div_le_iff₀ hDl]
      have h1 : K * (N:ℝ)^((1:ℝ)/2) * (2+|z.im|)^((1:ℝ)/2) *
            (Real.log N + Real.log (2+|z.im|) + 6) ≤
          K * (N:ℝ)^((1:ℝ)/2) * Real.sqrt (max 1 |z.im|) * 2 *
            (Real.log N + Real.log (2+|z.im|) + 6) := by
        have hL0 : 0 ≤ Real.log N + Real.log (2+|z.im|) + 6 := by
          have := Real.log_nonneg (by linarith [abs_nonneg z.im] : (1:ℝ) ≤ 2+|z.im|)
          linarith
        have hK' : 0 ≤ K * (N:ℝ)^((1:ℝ)/2) * (Real.log N + Real.log (2+|z.im|) + 6) :=
          mul_nonneg (mul_nonneg hKpos.le hN12.le) hL0
        calc K * (N:ℝ)^((1:ℝ)/2) * (2+|z.im|)^((1:ℝ)/2) *
              (Real.log N + Real.log (2+|z.im|) + 6)
            = (K * (N:ℝ)^((1:ℝ)/2) * (Real.log N + Real.log (2+|z.im|) + 6)) *
                ((2+|z.im|)^((1:ℝ)/2)) := by ring
          _ ≤ (K * (N:ℝ)^((1:ℝ)/2) * (Real.log N + Real.log (2+|z.im|) + 6)) *
                (2 * Real.sqrt (max 1 |z.im|)) :=
              mul_le_mul_of_nonneg_left hsp hK'
          _ = K * (N:ℝ)^((1:ℝ)/2) * Real.sqrt (max 1 |z.im|) * 2 *
                (Real.log N + Real.log (2+|z.im|) + 6) := by ring
      have hLM : Real.log N + Real.log (2+|z.im|) + 6 ≤
          3 * (Real.log N + 8) * Real.log (2+|z.im|) := by
        have h1 := log_bound_div N z.im
        have hLN : 0 ≤ Real.log N + 8 := by linarith
        have hMt : (1:ℝ)/2 ≤ Real.log (2+|z.im|) := by
          have h2 : Real.log 2 ≤ Real.log (2+|z.im|) :=
            Real.log_le_log (by norm_num) (by linarith [abs_nonneg z.im])
          linarith [h2, Real.log_two_gt_d9]
        have h2 : Real.log (2+|z.im|) + 1 ≤ 3 * Real.log (2+|z.im|) := by linarith
        have h3 : (Real.log N + 8) * (Real.log (2+|z.im|) + 1) ≤
            (Real.log N + 8) * (3 * Real.log (2+|z.im|)) := mul_le_mul_of_nonneg_left h2 hLN
        have h4 : (Real.log N + 8) * (3 * Real.log (2+|z.im|)) =
            3 * (Real.log N + 8) * Real.log (2+|z.im|) := by ring
        linarith [h1, h3, h4]
      have h2 : K * (N:ℝ)^((1:ℝ)/2) * Real.sqrt (max 1 |z.im|) * 2 *
            (Real.log N + Real.log (2+|z.im|) + 6) ≤
          1000 * (K + 1) * (Real.log N + 8) *
            ((1/4) * (N:ℝ)^((1:ℝ)/2) * Real.sqrt (max 1 |z.im|) * Real.log (2+|z.im|)) := by
        have hpos : 0 < (N:ℝ)^((1:ℝ)/2) * Real.sqrt (max 1 |z.im|) := mul_pos hN12 hspos
        have hB0 : 0 ≤ (Real.log N + 8) * Real.log (2+|z.im|) :=
          mul_nonneg (by linarith) hlogt.le
        have hkey : 2 * K * (Real.log N + Real.log (2+|z.im|) + 6) ≤
            250 * (K + 1) * (Real.log N + 8) * Real.log (2+|z.im|) := by
          have hA : 2 * K * (Real.log N + Real.log (2+|z.im|) + 6) ≤
              2 * K * (3 * (Real.log N + 8) * Real.log (2+|z.im|)) :=
            mul_le_mul_of_nonneg_left hLM (by linarith [hKpos])
          have hB : 2 * K * (3 * (Real.log N + 8) * Real.log (2+|z.im|)) =
              6 * K * ((Real.log N + 8) * Real.log (2+|z.im|)) := by ring
          have hC : 6 * K * ((Real.log N + 8) * Real.log (2+|z.im|)) ≤
              250 * (K + 1) * ((Real.log N + 8) * Real.log (2+|z.im|)) :=
            mul_le_mul_of_nonneg_right (by linarith [hKpos]) hB0
          have hD : 250 * (K + 1) * ((Real.log N + 8) * Real.log (2+|z.im|)) =
              250 * (K + 1) * (Real.log N + 8) * Real.log (2+|z.im|) := by ring
          linarith [hA, hB, hC, hD]
        calc K * (N:ℝ)^((1:ℝ)/2) * Real.sqrt (max 1 |z.im|) * 2 *
              (Real.log N + Real.log (2+|z.im|) + 6)
            = (N:ℝ)^((1:ℝ)/2) * Real.sqrt (max 1 |z.im|) *
                (2 * K * (Real.log N + Real.log (2+|z.im|) + 6)) := by ring
          _ ≤ (N:ℝ)^((1:ℝ)/2) * Real.sqrt (max 1 |z.im|) *
                (250 * (K + 1) * (Real.log N + 8) * Real.log (2+|z.im|)) :=
              mul_le_mul_of_nonneg_left hkey hpos.le
          _ = 1000 * (K + 1) * (Real.log N + 8) *
                ((1/4) * (N:ℝ)^((1:ℝ)/2) * Real.sqrt (max 1 |z.im|) * Real.log (2+|z.im|)) := by ring
      have hcoef : 1000 * (K + 1) * (Real.log N + 8) ≤
          1000 * (K + 1) * (Real.log N + 8) + 1000 + 4 * D * ((N:ℝ) + 1)^2 := by
        have h1 : 0 ≤ 1000 + 4 * D * ((N:ℝ) + 1)^2 := by positivity
        linarith
      have h3 : 1000 * (K + 1) * (Real.log N + 8) *
            ((1/4) * (N:ℝ)^((1:ℝ)/2) * Real.sqrt (max 1 |z.im|) * Real.log (2+|z.im|)) ≤
          (1000 * (K + 1) * (Real.log N + 8) + 1000 + 4 * D * ((N:ℝ) + 1)^2) *
            ((1/4) * (N:ℝ)^((1:ℝ)/2) * Real.sqrt (max 1 |z.im|) * Real.log (2+|z.im|)) :=
        mul_le_mul_of_nonneg_right hcoef hDl.le
      linarith [h1, h2, h3]
  · intro z hz
    have hzeq : z = (1:ℂ) + ((z.im:ℝ):ℂ)*I := by apply Complex.ext <;> simp [hz]
    rw [hzeq, norm_div]
    have hL1 : ‖LFunction χ ((1:ℂ) + ((z.im:ℝ):ℂ)*I)‖ ≤
        Real.log N + Real.log (2+|z.im|) + 6 := by
      have h := norm_LFunction_le_re_ge_one χ hχ ((1:ℂ) + ((z.im:ℝ):ℂ)*I) (by simp)
      have him : ((1:ℂ) + ((z.im:ℝ):ℂ)*I).im = z.im := by simp
      rwa [him] at h
    have hW1 := Wf_norm_lower_one (N := N) z.im
    have hlogt : 0 < Real.log (2+|z.im|) := Real.log_pos (by linarith [abs_nonneg z.im])
    have hlogt2 : Real.log 2 ≤ Real.log (2+|z.im|) :=
      Real.log_le_log (by norm_num) (by linarith [abs_nonneg z.im])
    have hWpos : 0 < Real.log (2+|z.im|)/2 := by linarith
    have hstep : ‖LFunction χ ((1:ℂ) + ((z.im:ℝ):ℂ)*I)‖ / ‖Wf N ((1:ℂ) + ((z.im:ℝ):ℂ)*I)‖ ≤
        (Real.log N + Real.log (2+|z.im|) + 6) / (Real.log (2+|z.im|)/2) :=
      div_le_div₀ (by
          have := Real.log_nonneg (by linarith [abs_nonneg z.im] : (1:ℝ) ≤ 2+|z.im|)
          linarith) hL1 hWpos hW1
    refine hstep.trans ?_
    have heq : (Real.log N + Real.log (2+|z.im|) + 6) / (Real.log (2+|z.im|)/2) =
        2 * (Real.log N + Real.log (2+|z.im|) + 6) / Real.log (2+|z.im|) := by ring
    rw [heq]
    have hratio : (Real.log N + Real.log (2+|z.im|) + 6) / Real.log (2+|z.im|) ≤
        3 * (Real.log N + 8) := by
      rw [div_le_iff₀ hlogt]
      have h1 := log_bound_div N z.im
      have hLN : 0 ≤ Real.log N + 8 := by linarith
      have hMt : (1:ℝ)/2 ≤ Real.log (2+|z.im|) := by nlinarith [hlogt2, Real.log_two_gt_d9]
      have h2 : Real.log (2+|z.im|) + 1 ≤ 3 * Real.log (2+|z.im|) := by linarith
      have h3 : (Real.log N + 8) * (Real.log (2+|z.im|) + 1) ≤
          (Real.log N + 8) * (3 * Real.log (2+|z.im|)) := mul_le_mul_of_nonneg_left h2 hLN
      have h4 : (Real.log N + 8) * (3 * Real.log (2+|z.im|)) =
          3 * (Real.log N + 8) * Real.log (2+|z.im|) := by ring
      linarith [h1, h3, h4]
    have h6 : 6 * (Real.log N + 8) ≤
        1000 * (K + 1) * (Real.log N + 8) + 1000 + 4 * D * ((N:ℝ) + 1)^2 := by
      have hA : 6 * (Real.log N + 8) ≤ 1000 * (K + 1) * (Real.log N + 8) :=
        mul_le_mul_of_nonneg_right (by linarith : (6:ℝ) ≤ 1000 * (K + 1))
          (by linarith : (0:ℝ) ≤ Real.log N + 8)
      have hB : 0 ≤ 1000 + 4 * D * ((N:ℝ) + 1)^2 := by positivity
      linarith
    have h7 : 2 * (Real.log N + Real.log (2+|z.im|) + 6) / Real.log (2+|z.im|) ≤
        6 * (Real.log N + 8) := by
      rw [div_le_iff₀ hlogt]
      have h := (div_le_iff₀ hlogt).mp hratio
      linarith
    linarith [h7, h6]



private lemma F_growth {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hχprim : χ.IsPrimitive) :
    ∃ B : ℝ, (fun z : ℂ => LFunction χ z / Wf N z) =O[
      Filter.comap (abs ∘ Complex.im) Filter.atTop ⊓ Filter.principal (Complex.re ⁻¹' Set.Ioo 0 1)]
      (fun z : ℂ => Real.exp (B * Real.exp (1 * |z.im|))) := by
  obtain ⟨Cg, hCgpos, hCg⟩ := F_bound_strip χ hχ hχprim
  refine ⟨40 + |Real.log Cg| + 1, ?_⟩
  rw [Asymptotics.isBigO_iff]
  refine ⟨1, ?_⟩
  rw [Filter.eventually_inf_principal, Filter.eventually_comap]
  filter_upwards [Filter.eventually_ge_atTop (1:ℝ)] with b hb
  intro z hzim hz
  have h1 : (1:ℝ) ≤ |z.im| := by
    have h := hb
    simp only [Function.comp_apply] at hzim
    rw [← hzim] at h
    exact h
  have hzre : 0 ≤ z.re ∧ z.re ≤ 1 := by
    simp only [Set.mem_preimage, Set.mem_Ioo] at hz
    exact ⟨le_of_lt hz.1, le_of_lt hz.2⟩
  have hone : (1:ℝ) * |z.im| = |z.im| := one_mul _
  have hcube : (2 + |z.im|)^3 ≤ Real.exp (3 * |z.im| + 5) := by
    have hx0 : (0:ℝ) ≤ |z.im| := by linarith
    have h3 : (2 + |z.im|)^3 ≤ (3 * |z.im|)^3 :=
      pow_le_pow_left₀ (by linarith : (0:ℝ) ≤ 2 + |z.im|) (by linarith) 3
    have hx3 : |z.im|^3 ≤ Real.exp (3 * |z.im|) := by
      have hle : |z.im| ≤ Real.exp |z.im| := by linarith [Real.add_one_le_exp |z.im|]
      have h := pow_le_pow_left₀ hx0 hle 3
      have e : Real.exp |z.im| ^ 3 = Real.exp (3 * |z.im|) := by
        rw [show Real.exp (3 * |z.im|) = Real.exp |z.im| ^ 3 from by
          rw [show (3:ℝ) * |z.im| = ((3:ℕ):ℝ) * |z.im| by norm_num, Real.exp_nat_mul]]
      exact h.trans (le_of_eq e)
    have hexp5 : (27:ℝ) ≤ Real.exp 5 := by
      have he1 : (2:ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
      have h2 : Real.exp 5 = Real.exp 1 ^ 5 := by
        rw [show (5:ℝ) = ((5:ℕ):ℝ) * 1 by norm_num, Real.exp_nat_mul]
      rw [h2]
      have h3 := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) he1 5
      norm_num at h3
      linarith
    have h4 : (3 * |z.im|)^3 = 27 * |z.im|^3 := by ring
    have h5 : 27 * |z.im|^3 ≤ 27 * Real.exp (3 * |z.im|) :=
      mul_le_mul_of_nonneg_left hx3 (by norm_num)
    have h6 : 27 * Real.exp (3 * |z.im|) ≤ Real.exp 5 * Real.exp (3 * |z.im|) :=
      mul_le_mul_of_nonneg_right hexp5 (Real.exp_pos _).le
    have h7 : Real.exp 5 * Real.exp (3 * |z.im|) = Real.exp (3 * |z.im| + 5) := by
      rw [Real.exp_add]
      ring
    linarith [h3, h4, h5, h6, h7]
  have hBbound : 3 * |z.im| + 5 + Real.log Cg ≤
      (40 + |Real.log Cg| + 1) * Real.exp |z.im| := by
    have hx0 : (0:ℝ) ≤ |z.im| := by linarith
    have hex : 1 ≤ Real.exp |z.im| := Real.one_le_exp hx0
    have hB0 : 0 ≤ |Real.log Cg| + 1 := by positivity
    have hlogabs : Real.log Cg ≤ |Real.log Cg| := le_abs_self _
    have hsplit : (40 + |Real.log Cg| + 1) * Real.exp |z.im| =
        40 * Real.exp |z.im| + (|Real.log Cg| + 1) * Real.exp |z.im| := by ring
    have hA : 40 * (|z.im| + 1) ≤ 40 * Real.exp |z.im| :=
      mul_le_mul_of_nonneg_left (Real.add_one_le_exp |z.im|) (by norm_num)
    have hC : (|Real.log Cg| + 1) ≤ (|Real.log Cg| + 1) * Real.exp |z.im| := by
      nlinarith [hB0, hex]
    linarith [hsplit, hA, hC, hlogabs, hx0]
  have hexp_ge : Real.exp (3 * |z.im| + 5) * Cg ≤
      Real.exp ((40 + |Real.log Cg| + 1) * Real.exp |z.im|) := by
    have h : Real.exp (3 * |z.im| + 5 + Real.log Cg) = Real.exp (3 * |z.im| + 5) * Cg := by
      rw [Real.exp_add, Real.exp_log hCgpos]
    rw [← h]
    exact Real.exp_le_exp.mpr hBbound
  have hmain : Cg * (2 + |z.im|)^3 ≤
      Real.exp ((40 + |Real.log Cg| + 1) * Real.exp (1 * |z.im|)) := by
    rw [hone]
    calc Cg * (2 + |z.im|)^3 ≤ Cg * Real.exp (3 * |z.im| + 5) :=
          mul_le_mul_of_nonneg_left hcube hCgpos.le
      _ = Real.exp (3 * |z.im| + 5) * Cg := by ring
      _ ≤ Real.exp ((40 + |Real.log Cg| + 1) * Real.exp |z.im|) := hexp_ge
  calc ‖LFunction χ z / Wf N z‖ ≤ Cg * (2 + |z.im|)^3 := hCg z hzre.1 hzre.2 h1
    _ ≤ Real.exp ((40 + |Real.log Cg| + 1) * Real.exp (1 * |z.im|)) := hmain
    _ = 1 * ‖Real.exp ((40 + |Real.log Cg| + 1) * Real.exp (1 * |z.im|))‖ := by
        rw [Real.norm_of_nonneg (Real.exp_pos _).le]
        simp

theorem LFunction_strip_convexity_explicit {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ T : ℝ), 0 ≤ σ → σ ≤ 1 →
      ‖DirichletCharacter.LFunction χ ((σ : ℂ) + Complex.I * (T : ℂ))‖ ≤
        C * ((N : ℝ) * (2 + |T|)) ^ ((1 - σ) / 2) *
          (Real.log ((N : ℝ) * (2 + |T|)) + 2) := by
  obtain ⟨Cb, hCbpos, hb0, hb1⟩ := F_bound_boundary χ hχ hχprim
  obtain ⟨B, hB⟩ := F_growth χ hχ hχprim
  refine ⟨Cb * (5 * Real.exp 1), by positivity, ?_⟩
  intro σ T hσ0 hσ1
  set z : ℂ := (σ : ℂ) + Complex.I * (T : ℂ) with hz
  have hzre : z.re = σ := by rw [hz]; simp
  have hzim : |z.im| = |T| := by rw [hz]; simp
  have hclos : closure (Complex.re ⁻¹' Set.Ioo (0:ℝ) 1) ⊆ Complex.re ⁻¹' Set.Icc (0:ℝ) 1 := by
    apply closure_minimal _ (isClosed_Icc.preimage continuous_re)
    intro w hw
    simp only [Set.mem_preimage, Set.mem_Icc] at hw ⊢
    exact ⟨le_of_lt hw.1, le_of_lt hw.2⟩
  have hdco : DiffContOnCl ℂ (fun s : ℂ => LFunction χ s / Wf N s)
      (Complex.re ⁻¹' Set.Ioo (0:ℝ) 1) :=
    ⟨F_differentiableOn χ hχ, (F_continuousOn χ hχ).mono hclos⟩
  have hWfne : Wf N z ≠ 0 :=
    Wf_ne_zero_strip z (by rw [hzre]; exact hσ0) (by rw [hzre]; exact hσ1)
  have hnormpos : 0 < ‖Wf N z‖ := norm_pos_iff.mpr hWfne
  have hPL : ‖LFunction χ z / Wf N z‖ ≤ Cb :=
    PhragmenLindelof.vertical_strip (a := 0) (b := 1) (C := Cb)
      (f := fun s : ℂ => LFunction χ s / Wf N s) (z := z) hdco
      ⟨1, by rw [sub_zero, div_one]; linarith [Real.pi_gt_three], B, hB⟩ hb0 hb1
      (by rw [hzre]; exact hσ0) (by rw [hzre]; exact hσ1)
  have hLle : ‖LFunction χ z‖ ≤ Cb * ‖Wf N z‖ := by
    rw [norm_div] at hPL
    exact (div_le_iff₀ hnormpos).mp hPL
  have hW := Wf_norm_upper (N := N) z (by rw [hzre]; exact hσ0) (by rw [hzre]; exact hσ1)
  calc ‖LFunction χ z‖ ≤ Cb * ‖Wf N z‖ := hLle
    _ ≤ Cb * (5 * Real.exp 1 * ((N:ℝ) * (2 + |z.im|)) ^ ((1 - z.re)/2) *
          (Real.log ((N:ℝ) * (2 + |z.im|)) + 2)) :=
        mul_le_mul_of_nonneg_left hW hCbpos.le
    _ = Cb * (5 * Real.exp 1) * ((N:ℝ) * (2 + |T|)) ^ ((1 - σ)/2) *
          (Real.log ((N:ℝ) * (2 + |T|)) + 2) := by
        rw [hzre, hzim]; ring

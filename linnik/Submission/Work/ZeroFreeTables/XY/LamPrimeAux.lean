
/-
# ZeroFreeTables/XY/LamPrimeAux

Integral identities for the order-2 supremum estimates.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.XY.LamPrimeData
import Submission.Work.ZeroFreeTables.XY.XYEngineDefs

open DirichletCharacter Complex MeasureTheory
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables.XY

open Work.ZeroFreeTables

lemma xyG_supp' (x : ℝ) (hx : x ∉ Set.Icc (-(3/4)) (3/4)) : xyG x = 0 := by
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
  refine xyG_supp x ?_
  rcases hx with h | h
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

lemma integral_re_eq_of_continuous {F : ℝ → ℂ} (hF : Continuous F) (a b : ℝ) :
    (∫ x in a..b, F x).re = ∫ x in a..b, (F x).re := by
  rw [← Complex.reCLM_apply,
    ← ContinuousLinearMap.intervalIntegral_comp_comm Complex.reCLM
      (hF.intervalIntegrable a b)]
  simp only [Complex.reCLM_apply]

lemma integral_im_eq_of_continuous {F : ℝ → ℂ} (hF : Continuous F) (a b : ℝ) :
    (∫ x in a..b, F x).im = ∫ x in a..b, (F x).im := by
  rw [← Complex.imCLM_apply,
    ← ContinuousLinearMap.intervalIntegral_comp_comm Complex.imCLM
      (hF.intervalIntegrable a b)]
  simp only [Complex.imCLM_apply]

lemma integral_add_eq_of_continuous {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (a b : ℝ) :
    (∫ x in a..b, f x) + (∫ x in a..b, g x) = ∫ x in a..b, (f x + g x) := by
  rw [← intervalIntegral.integral_add (hf.intervalIntegrable a b) (hg.intervalIntegrable a b)]

/-- Real and imaginary parts of `exp` at the two exponents of `(it-λ)·x`. -/
lemma exp_neg_it_sub_re (lam t x : ℝ) :
    (Complex.exp (-(((t : ℂ) * Complex.I - (lam : ℂ)) * (x : ℂ)))).re
      = Real.exp (lam*x) * Real.cos (t*x) := by
  have ha : (-(((t : ℂ) * Complex.I - (lam : ℂ)) * (x : ℂ))).re = lam*x := by
    simp only [Complex.neg_re, Complex.mul_re, Complex.sub_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_I_re, Complex.mul_I_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_zero]
    ring
  have hb : (-(((t : ℂ) * Complex.I - (lam : ℂ)) * (x : ℂ))).im = -(t*x) := by
    simp only [Complex.neg_im, Complex.mul_im, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_I_re, Complex.mul_I_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_zero]
    ring
  rw [Complex.exp_re, ha, hb, Real.cos_neg]

lemma exp_it_sub_re (lam t x : ℝ) :
    (Complex.exp (((t : ℂ) * Complex.I - (lam : ℂ)) * (x : ℂ))).re
      = Real.exp (-(lam*x)) * Real.cos (t*x) := by
  have hc : (((t : ℂ) * Complex.I - (lam : ℂ)) * (x : ℂ)).re = -(lam*x) := by
    simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_I_re, Complex.mul_I_im, Complex.I_re, Complex.I_im, Complex.ofReal_zero]
    ring
  have hd : (((t : ℂ) * Complex.I - (lam : ℂ)) * (x : ℂ)).im = t*x := by
    simp only [Complex.mul_im, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_I_re, Complex.mul_I_im, Complex.I_re, Complex.I_im, Complex.ofReal_zero]
    ring
  rw [Complex.exp_re, hc, hd]

lemma exp_neg_it_sub_im (lam t x : ℝ) :
    (Complex.exp (-(((t : ℂ) * Complex.I - (lam : ℂ)) * (x : ℂ)))).im
      = -(Real.exp (lam*x) * Real.sin (t*x)) := by
  have ha : (-(((t : ℂ) * Complex.I - (lam : ℂ)) * (x : ℂ))).re = lam*x := by
    simp only [Complex.neg_re, Complex.mul_re, Complex.sub_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_I_re, Complex.mul_I_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_zero]
    ring
  have hb : (-(((t : ℂ) * Complex.I - (lam : ℂ)) * (x : ℂ))).im = -(t*x) := by
    simp only [Complex.neg_im, Complex.mul_im, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_I_re, Complex.mul_I_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_zero]
    ring
  rw [Complex.exp_im, ha, hb, Real.sin_neg]
  ring

lemma exp_it_sub_im (lam t x : ℝ) :
    (Complex.exp (((t : ℂ) * Complex.I - (lam : ℂ)) * (x : ℂ))).im
      = Real.exp (-(lam*x)) * Real.sin (t*x) := by
  have hc : (((t : ℂ) * Complex.I - (lam : ℂ)) * (x : ℂ)).re = -(lam*x) := by
    simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_I_re, Complex.mul_I_im, Complex.I_re, Complex.I_im, Complex.ofReal_zero]
    ring
  have hd : (((t : ℂ) * Complex.I - (lam : ℂ)) * (x : ℂ)).im = t*x := by
    simp only [Complex.mul_im, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_I_re, Complex.mul_I_im, Complex.I_re, Complex.I_im, Complex.ofReal_zero]
    ring
  rw [Complex.exp_im, hc, hd]

/-- The Laplace transform of `g` as an integral over `[0,3/4]` of the two exponentials. -/
theorem Ac_eq_exp (z : ℂ) :
    Ac z = ∫ x in (0:ℝ)..(3/4), ((xyG x : ℝ) : ℂ) *
      (Complex.exp (-(z * (x : ℂ))) + Complex.exp (z * (x : ℂ))) := by
  have hcont : Continuous (fun x : ℝ => ((xyG x : ℝ) : ℂ) * Complex.exp (-(z * (x : ℂ)))) :=
    (Complex.continuous_ofReal.comp xyG_cont).mul
      (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal).neg)
  have hcont2 : Continuous (fun x : ℝ => ((xyG x : ℝ) : ℂ) * Complex.exp (z * (x : ℂ))) :=
    (Complex.continuous_ofReal.comp xyG_cont).mul
      (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))
  have hzero : ∀ x : ℝ, x ∉ Set.Icc (-(3/4)) (3/4) →
      ((xyG x : ℝ) : ℂ) * Complex.exp (-(z * (x : ℂ))) = 0 := by
    intro x hx
    have h1 := xyG_supp' x hx
    rw [h1]
    simp
  have h2 : (∫ x in Set.Icc (-(3/4)) (3/4),
        ((xyG x : ℝ) : ℂ) * Complex.exp (-(z * (x : ℂ))))
      = ∫ x in (-(3/4))..(3/4), ((xyG x : ℝ) : ℂ) * Complex.exp (-(z * (x : ℂ))) := by
    have hle : (-(3/4) : ℝ) ≤ 3/4 := by norm_num
    have h3' : (∫ x in (-(3/4))..(3/4), ((xyG x : ℝ) : ℂ) * Complex.exp (-(z * (x : ℂ))))
        = ∫ x in Set.Ioc (-(3/4)) (3/4), ((xyG x : ℝ) : ℂ) * Complex.exp (-(z * (x : ℂ))) :=
      intervalIntegral.integral_of_le (μ := volume) hle
    rw [h3', MeasureTheory.integral_Icc_eq_integral_Ioc]
  have h3 : (∫ x in (-(3/4))..(3/4), ((xyG x : ℝ) : ℂ) * Complex.exp (-(z * (x : ℂ))))
      = (∫ x in (-(3/4))..0, ((xyG x : ℝ) : ℂ) * Complex.exp (-(z * (x : ℂ))))
        + ∫ x in (0:ℝ)..(3/4), ((xyG x : ℝ) : ℂ) * Complex.exp (-(z * (x : ℂ))) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
  have h4 : (∫ x in (-(3/4))..0, ((xyG x : ℝ) : ℂ) * Complex.exp (-(z * (x : ℂ))))
      = ∫ x in (0:ℝ)..(3/4), ((xyG x : ℝ) : ℂ) * Complex.exp (z * (x : ℂ)) := by
    have h4a : (∫ x in (-(3/4))..0, ((xyG x : ℝ) : ℂ) * Complex.exp (-(z * (x : ℂ))))
        = ∫ x in (0:ℝ)..(3/4),
            ((xyG (-x) : ℝ) : ℂ) * Complex.exp (-(z * ((-x : ℝ) : ℂ))) := by
      have hci := intervalIntegral.integral_comp_neg (a := (0:ℝ)) (b := (3/4))
        (f := fun x : ℝ => ((xyG x : ℝ) : ℂ) * Complex.exp (-(z * (x : ℂ))))
      simpa using hci.symm
    rw [h4a]
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [xyG_even x, show -(z * ((-x : ℝ) : ℂ)) = z * (x : ℂ) from by push_cast; ring]
  have h5 : (∫ x in (0:ℝ)..(3/4), ((xyG x : ℝ) : ℂ) * Complex.exp (z * (x : ℂ)))
        + ∫ x in (0:ℝ)..(3/4), ((xyG x : ℝ) : ℂ) * Complex.exp (-(z * (x : ℂ)))
      = ∫ x in (0:ℝ)..(3/4), ((xyG x : ℝ) : ℂ) *
          (Complex.exp (-(z * (x : ℂ))) + Complex.exp (z * (x : ℂ))) := by
    rw [← intervalIntegral.integral_add
      (hcont2.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _)]
    refine intervalIntegral.integral_congr fun x _ => ?_
    ring
  have hkey : (∫ x : ℝ, ((xyG x : ℝ) : ℂ) * Complex.exp (-(z * (x : ℂ))))
      = (∫ x in (-(3/4))..0, ((xyG x : ℝ) : ℂ) * Complex.exp (-(z * (x : ℂ))))
        + ∫ x in (0:ℝ)..(3/4), ((xyG x : ℝ) : ℂ) * Complex.exp (-(z * (x : ℂ))) := by
    rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := Set.Icc (-(3/4)) (3/4)) hzero, h2, h3]
  rw [Ac, hkey, h4, h5]

/-- `C + E` is the `g`-integral of `cosh(λ·)cos(t·)`. -/
theorem Cc_add_Ec (lam t : ℝ) :
    Cc t + Ec lam t
      = ∫ x in (0:ℝ)..(3/4), xyG x * Real.cosh (lam*x) * Real.cos (t*x) := by
  have hc : Continuous (fun x : ℝ => xyG x * (Real.cosh (lam*x) - 1) * Real.cos (t*x)) :=
    (xyG_cont.mul ((Real.continuous_cosh.comp (continuous_const.mul continuous_id)).sub
      continuous_const)).mul (Real.continuous_cos.comp (continuous_const.mul continuous_id))
  have hc2 : Continuous (fun x : ℝ => xyG x * Real.cos (t*x)) :=
    xyG_cont.mul (Real.continuous_cos.comp (continuous_const.mul continuous_id))
  have hsum := integral_add_eq_of_continuous hc2 hc (0:ℝ) (3/4)
  rw [Cc, Ec, hsum]
  refine intervalIntegral.integral_congr fun x _ => ?_
  rw [Real.cosh_eq]; ring

/-- Real part of `Ac (it - λ)`. -/
theorem Ac_it_sub_re (lam t : ℝ) :
    (Ac ((t : ℂ) * Complex.I - (lam : ℂ))).re = 2 * (Cc t + Ec lam t) := by
  have hcont : Continuous (fun x : ℝ => ((xyG x : ℝ) : ℂ) *
      (Complex.exp (-(((t : ℂ) * Complex.I - (lam : ℂ)) * (x : ℂ)))
        + Complex.exp (((t : ℂ) * Complex.I - (lam : ℂ)) * (x : ℂ)))) :=
    (Complex.continuous_ofReal.comp xyG_cont).mul
      ((Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal).neg).add
        (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)))
  have hpt : ∀ x : ℝ, (((xyG x : ℝ) : ℂ) *
      (Complex.exp (-(((t : ℂ) * Complex.I - (lam : ℂ)) * (x : ℂ)))
        + Complex.exp (((t : ℂ) * Complex.I - (lam : ℂ)) * (x : ℂ)))).re
      = 2 * (xyG x * Real.cosh (lam*x) * Real.cos (t*x)) := by
    intro x
    simp only [Complex.mul_re, Complex.add_re, exp_neg_it_sub_re lam t x, exp_it_sub_re lam t x,
      Complex.ofReal_im, Complex.ofReal_re, zero_mul, mul_zero, sub_zero]
    rw [Real.cosh_eq]; ring
  rw [Ac_eq_exp, integral_re_eq_of_continuous hcont 0 (3/4)]
  rw [show (∫ x in (0:ℝ)..(3/4), (((xyG x : ℝ) : ℂ) *
        (Complex.exp (-(((t : ℂ) * Complex.I - (lam : ℂ)) * (x : ℂ)))
          + Complex.exp (((t : ℂ) * Complex.I - (lam : ℂ)) * (x : ℂ)))).re)
      = ∫ x in (0:ℝ)..(3/4), 2 * (xyG x * Real.cosh (lam*x) * Real.cos (t*x)) from
    intervalIntegral.integral_congr fun x _ => hpt x]
  rw [intervalIntegral.integral_const_mul, ← Cc_add_Ec]
  try ring

/-- Imaginary part of `Ac (it - λ)`. -/
theorem Ac_it_sub_im (lam t : ℝ) :
    (Ac ((t : ℂ) * Complex.I - (lam : ℂ))).im = -(2 * Bc lam t) := by
  have hcont : Continuous (fun x : ℝ => ((xyG x : ℝ) : ℂ) *
      (Complex.exp (-(((t : ℂ) * Complex.I - (lam : ℂ)) * (x : ℂ)))
        + Complex.exp (((t : ℂ) * Complex.I - (lam : ℂ)) * (x : ℂ)))) :=
    (Complex.continuous_ofReal.comp xyG_cont).mul
      ((Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal).neg).add
        (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)))
  have hpt : ∀ x : ℝ, (((xyG x : ℝ) : ℂ) *
      (Complex.exp (-(((t : ℂ) * Complex.I - (lam : ℂ)) * (x : ℂ)))
        + Complex.exp (((t : ℂ) * Complex.I - (lam : ℂ)) * (x : ℂ)))).im
      = -(2 * (xyG x * Real.sinh (lam*x) * Real.sin (t*x))) := by
    intro x
    simp only [Complex.mul_im, Complex.add_im, exp_neg_it_sub_im lam t x, exp_it_sub_im lam t x,
      Complex.ofReal_im, Complex.ofReal_re, zero_mul, mul_zero, zero_add]
    rw [Real.sinh_eq]; ring
  rw [Ac_eq_exp, integral_im_eq_of_continuous hcont 0 (3/4), Bc]
  rw [show (∫ x in (0:ℝ)..(3/4), (((xyG x : ℝ) : ℂ) *
        (Complex.exp (-(((t : ℂ) * Complex.I - (lam : ℂ)) * (x : ℂ)))
          + Complex.exp (((t : ℂ) * Complex.I - (lam : ℂ)) * (x : ℂ)))).im)
      = ∫ x in (0:ℝ)..(3/4), -(2 * (xyG x * Real.sinh (lam*x) * Real.sin (t*x))) from
    intervalIntegral.integral_congr fun x _ => hpt x]
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_const_mul]
  try ring

/-- Real part of `Ac (it)`. -/
theorem Ac_it_re (t : ℝ) : (Ac ((t : ℂ) * Complex.I)).re = 2 * Cc t := by
  have h := Ac_it_sub_re 0 t
  rw [Complex.ofReal_zero, sub_zero] at h
  have hE : Ec 0 t = 0 := by simp [Ec]
  rw [h, hE, add_zero]

/-- `xyRe (-λ) t - xyRe λ t = 2·S(λ,t)`. -/
theorem xyRe_sub_lam (lam t : ℝ) :
    xyRe (-lam) t - xyRe lam t = 2 * Sc lam t := by
  have h1 : xyRe (-lam) t = ∫ u in (0:ℝ)..(3/2),
      Real.cos (t*u) * (Real.exp (-((-lam)*u)) * xyT.f u) := xyRe_eq_integral (-lam) t
  have h2 : xyRe lam t = ∫ u in (0:ℝ)..(3/2),
      Real.cos (t*u) * (Real.exp (-(lam*u)) * xyT.f u) := xyRe_eq_integral lam t
  have hf : ContinuousOn xyT.f (Set.Icc (0:ℝ) (3/2)) := xyT.f_cont.mono (fun x hx => hx.1)
  have hcos : Continuous fun u : ℝ => Real.cos (t*u) :=
    Real.continuous_cos.comp (continuous_const.mul continuous_id)
  have hexp : Continuous fun u : ℝ => Real.exp (-(lam*u)) :=
    Real.continuous_exp.comp ((continuous_const.mul continuous_id).neg)
  have hexpm : Continuous fun u : ℝ => Real.exp (-((-lam)*u)) :=
    Real.continuous_exp.comp (((continuous_const.neg).mul continuous_id).neg)
  have hA : ContinuousOn (fun u : ℝ =>
      Real.cos (t*u) * (Real.exp (-((-lam)*u)) * xyT.f u)) (Set.Icc (0:ℝ) (3/2)) :=
    hcos.continuousOn.mul (hexpm.continuousOn.mul hf)
  have hB : ContinuousOn (fun u : ℝ =>
      Real.cos (t*u) * (Real.exp (-(lam*u)) * xyT.f u)) (Set.Icc (0:ℝ) (3/2)) :=
    hcos.continuousOn.mul (hexp.continuousOn.mul hf)
  rw [h1, h2, ← intervalIntegral.integral_sub
    (ContinuousOn.intervalIntegrable_of_Icc (by norm_num) hA)
    (ContinuousOn.intervalIntegrable_of_Icc (by norm_num) hB)]
  rw [show (∫ u in (0:ℝ)..(3/2), Real.cos (t*u) * (Real.exp (-((-lam)*u)) * xyT.f u)
        - Real.cos (t*u) * (Real.exp (-(lam*u)) * xyT.f u))
      = ∫ u in (0:ℝ)..(3/2), 2 * (Real.sinh (lam*u) * Real.cos (t*u) * xyT.f u) from by
    refine intervalIntegral.integral_congr fun u _ => ?_
    rw [Real.sinh_eq]; ring]
  rw [intervalIntegral.integral_const_mul, Sc]
  congr 1

end Work.ZeroFreeTables.XY

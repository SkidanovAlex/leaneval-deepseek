import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Submission.Commons.Analysis.Fourier.neumann_lhs_eq_zeta
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.Analysis.Fourier

open scoped BigOperators

set_option maxHeartbeats 2000000


private lemma summable_nat_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) :
    Summable (fun n : ℕ => Real.exp (-(b * (n:ℝ)^2))) := by
  have h := Real.summable_exp_nat_mul_of_ge (c := -b) (by linarith) (f := fun i : ℕ => (i:ℝ)^2) ?_
  · simpa only [neg_mul] using h
  · intro i
    rcases Nat.eq_zero_or_pos i with h | h
    · subst h; simp
    · have : (1:ℝ) ≤ (i:ℝ) := by exact_mod_cast h
      nlinarith

private lemma summable_gauss_int {b : ℝ} (hb : 0 < b) :
    Summable (fun n : ℤ => Real.exp (-(b * (n:ℝ)^2))) := by
  apply Summable.of_nat_of_neg_add_one
  · exact summable_nat_exp_neg_mul_sq hb
  · refine Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) (fun n => ?_)
      (summable_nat_exp_neg_mul_sq hb)
    apply Real.exp_le_exp.mpr
    have hcast : ((-(↑n + 1) : ℤ) : ℝ) = -((n:ℝ) + 1) := by push_cast; ring
    rw [hcast]
    have hnn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    have hle : (n:ℝ)^2 ≤ ((n:ℝ)+1)^2 := by nlinarith [hnn]
    nlinarith [mul_le_mul_of_nonneg_left hle hb.le]

private lemma exp_neg_sq_shift_le {a c : ℝ} (ha : 0 < a) (y : ℝ) :
    Real.exp (-(a * (y + c)^2)) ≤ Real.exp (a * c^2) * Real.exp (-(a/2 * y^2)) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg (y + 2*c)]

private lemma summable_exp_neg_sq_shift {a c : ℝ} (ha : 0 < a) :
    Summable (fun n : ℤ => Real.exp (-(a * ((n:ℝ) + c)^2))) := by
  have hG : Summable (fun n : ℤ => Real.exp (-(a/2 * (n:ℝ)^2))) := summable_gauss_int (by linarith)
  refine Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) (fun n => exp_neg_sq_shift_le ha _) ?_
  exact hG.mul_left (Real.exp (a*c^2))

private lemma complex_arg_lhs {a ath c : ℝ} (hpi : Real.pi * ath = a) (n : ℤ) :
    (-(Real.pi : ℂ) * (ath : ℂ) * ((n : ℂ))^2 + 2 * (Real.pi : ℂ) * ((-(ath*c) : ℝ) : ℂ) * (n : ℂ))
      = (((Real.pi * ath * c^2 - a * ((n:ℝ) + c)^2) : ℝ) : ℂ) := by
  rw [← hpi]
  push_cast
  ring

private lemma complex_arg_rhs {a ath c : ℝ} (hath : ath ≠ 0) (hpi : Real.pi * ath = a) (n : ℤ) :
    (-(Real.pi:ℂ) / (ath:ℂ) * (((n:ℂ)) + Complex.I * ((-(ath*c):ℝ):ℂ))^2)
      = (((Real.pi*ath*c^2 - (Real.pi*(n:ℝ))^2/a) : ℝ) : ℂ)
        + (((2*Real.pi*(n:ℝ)*c):ℝ):ℂ) * Complex.I := by
  have hk : -(Real.pi:ℂ) / (ath:ℂ) = ((-(Real.pi/ath):ℝ):ℂ) := by
    push_cast; ring
  have hz : (((n:ℂ)) + Complex.I*((-(ath*c):ℝ):ℂ))^2
      = ((((n:ℝ)^2 - (ath*c)^2 : ℝ)):ℂ) + (((2*(n:ℝ)*(-(ath*c))):ℝ):ℂ)*Complex.I := by
    push_cast
    ring_nf
    rw [Complex.I_sq]; ring
  rw [hk, hz]
  have hA : -(Real.pi/ath) * ((n:ℝ)^2 - (ath*c)^2) = Real.pi*ath*c^2 - (Real.pi*(n:ℝ))^2/a := by
    rw [← hpi]; field_simp; ring
  have hB : -(Real.pi/ath) * (2*(n:ℝ)*(-(ath*c))) = 2*Real.pi*(n:ℝ)*c := by
    field_simp [hath]
  rw [show ((-(Real.pi/ath):ℝ):ℂ) * (((( (n:ℝ)^2 - (ath*c)^2 : ℝ)):ℂ) + (((2*(n:ℝ)*(-(ath*c))):ℝ):ℂ)*Complex.I)
        = ((( (-(Real.pi/ath) * ((n:ℝ)^2 - (ath*c)^2) : ℝ)):ℂ)) + ((((-(Real.pi/ath)*(2*(n:ℝ)*(-(ath*c)))):ℝ):ℂ)*Complex.I) by push_cast; ring]
  rw [hA, hB]


private theorem theta_shift_real_aux {a c : ℝ} (ha : 0 < a) :
    (∑' n : ℤ, Real.exp (-(a * ((n : ℝ) + c) ^ 2)))
      = Real.sqrt (Real.pi / a) *
        (∑' n : ℤ, Real.exp (-((Real.pi * (n : ℝ)) ^ 2) / a)
          * Real.cos (2 * Real.pi * (n : ℝ) * c)) := by
  set ath : ℝ := a / Real.pi with hathdef
  have hath : 0 < ath := by rw [hathdef]; positivity
  have hathne : ath ≠ 0 := ne_of_gt hath
  have hpi_ath : Real.pi * ath = a := by rw [hathdef]; field_simp
  set S : ℝ := ∑' n : ℤ, Real.exp (-(a * ((n:ℝ) + c)^2)) with hSdef
  set T : ℝ := ∑' n : ℤ, Real.exp (-((Real.pi*(n:ℝ))^2)/a) * Real.cos (2*Real.pi*(n:ℝ)*c) with hTdef
  have hcomplex := Complex.tsum_exp_neg_quadratic (a := (ath:ℂ))
      (by rw [Complex.ofReal_re]; exact hath) (b := ((-(ath*c):ℝ):ℂ))
  have hSsum : Summable (fun n : ℤ => Real.exp (-(a * ((n:ℝ) + c)^2))) := summable_exp_neg_sq_shift ha
  have hGsum : Summable (fun n : ℤ => Real.exp (-(((Real.pi*(n:ℝ))^2)/a))) := by
    have h := summable_gauss_int (b := Real.pi/ath) (by positivity)
    refine h.congr (fun n => ?_)
    congr 1
    have hpa : Real.pi/ath = Real.pi^2/a := by rw [← hpi_ath]; field_simp
    rw [hpa]; ring
  have hL_eq : ∀ n : ℤ, Complex.exp (-(Real.pi : ℂ) * (ath : ℂ) * ((n : ℂ))^2
        + 2 * (Real.pi : ℂ) * ((-(ath*c) : ℝ) : ℂ) * (n : ℂ))
      = (((Real.exp (Real.pi * ath * c^2) * Real.exp (-(a * ((n:ℝ) + c)^2))):ℝ):ℂ) := by
    intro n
    rw [complex_arg_lhs hpi_ath n, ← Complex.ofReal_exp, sub_eq_add_neg, Real.exp_add]
  have hL_tsum : (∑' n : ℤ, Complex.exp (-(Real.pi : ℂ) * (ath : ℂ) * ((n : ℂ))^2
        + 2 * (Real.pi : ℂ) * ((-(ath*c) : ℝ) : ℂ) * (n : ℂ)))
      = (((Real.exp (Real.pi * ath * c^2) * S):ℝ):ℂ) := by
    rw [tsum_congr hL_eq, ← Complex.ofReal_tsum, tsum_mul_left, hSdef]
  have hL_summ : Summable (fun n : ℤ => Complex.exp (-(Real.pi : ℂ) * (ath : ℂ) * ((n : ℂ))^2
        + 2 * (Real.pi : ℂ) * ((-(ath*c) : ℝ) : ℂ) * (n : ℂ))) := by
    rw [show (fun n : ℤ => Complex.exp (-(Real.pi : ℂ) * (ath : ℂ) * ((n : ℂ))^2
        + 2 * (Real.pi : ℂ) * ((-(ath*c) : ℝ) : ℂ) * (n : ℂ)))
        = (fun n : ℤ => (((Real.exp (Real.pi * ath * c^2) * Real.exp (-(a * ((n:ℝ) + c)^2))):ℝ):ℂ))
        from funext hL_eq]
    exact (Complex.summable_ofReal).mpr (hSsum.mul_left _)
  have hL_re : (∑' n : ℤ, Complex.exp (-(Real.pi : ℂ) * (ath : ℂ) * ((n : ℂ))^2
        + 2 * (Real.pi : ℂ) * ((-(ath*c) : ℝ) : ℂ) * (n : ℂ))).re
      = Real.exp (Real.pi * ath * c^2) * S := by
    rw [Complex.re_tsum hL_summ]
    simp only [hL_eq, Complex.ofReal_re]
    rw [tsum_mul_left, hSdef]
  have hR_arg : ∀ n : ℤ, (-(Real.pi:ℂ) / (ath:ℂ) * (((n:ℂ)) + Complex.I * ((-(ath*c):ℝ):ℂ))^2)
      = (((Real.pi*ath*c^2 - (Real.pi*(n:ℝ))^2/a) : ℝ) : ℂ)
        + (((2*Real.pi*(n:ℝ)*c):ℝ):ℂ) * Complex.I := fun n => complex_arg_rhs hathne hpi_ath n
  have hR_arg_re : ∀ n : ℤ, (-(Real.pi:ℂ) / (ath:ℂ) * (((n:ℂ)) + Complex.I * ((-(ath*c):ℝ):ℂ))^2).re
      = Real.pi*ath*c^2 - (Real.pi*(n:ℝ))^2/a := by
    intro n
    rw [hR_arg n, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hR_re : ∀ n : ℤ, (Complex.exp (-(Real.pi:ℂ) / (ath:ℂ) * (((n:ℂ)) + Complex.I * ((-(ath*c):ℝ):ℂ))^2)).re
      = Real.exp (Real.pi*ath*c^2) * (Real.exp (-((Real.pi*(n:ℝ))^2)/a) * Real.cos (2*Real.pi*(n:ℝ)*c)) := by
    intro n
    rw [hR_arg n, Complex.exp_add, ← Complex.ofReal_exp, Complex.exp_ofReal_mul_I]
    simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_I_re, Complex.mul_I_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
      sub_zero, add_zero, zero_mul]
    rw [sub_eq_add_neg (Real.pi*ath*c^2) ((Real.pi*(n:ℝ))^2/a), Real.exp_add]
    ring
  have hR_summ : Summable (fun n : ℤ => Complex.exp (-(Real.pi:ℂ) / (ath:ℂ) * (((n:ℂ)) + Complex.I * ((-(ath*c):ℝ):ℂ))^2)) := by
    refine Summable.of_norm_bounded (hGsum.mul_left (Real.exp (Real.pi*ath*c^2))) (fun n => ?_)
    rw [Complex.norm_exp, hR_arg_re n]
    have heq : Real.exp (Real.pi*ath*c^2 - (Real.pi*(n:ℝ))^2/a)
        = Real.exp (Real.pi*ath*c^2) * Real.exp (-(((Real.pi*(n:ℝ))^2)/a)) := by
      rw [sub_eq_add_neg, Real.exp_add]
    rw [heq]
  have hR_re_tsum : (∑' n : ℤ, Complex.exp (-(Real.pi:ℂ) / (ath:ℂ) * (((n:ℂ)) + Complex.I * ((-(ath*c):ℝ):ℂ))^2)).re
      = Real.exp (Real.pi*ath*c^2) * T := by
    rw [Complex.re_tsum hR_summ]
    simp only [hR_re]
    rw [tsum_mul_left, hTdef]
  have hrc : (1/(ath:ℂ)^(1/2:ℂ)) = ((Real.sqrt (Real.pi/a):ℝ):ℂ) := by
    have h12 : (1/2:ℂ) = ((1/2:ℝ):ℂ) := by norm_num
    rw [h12, ← Complex.ofReal_cpow hath.le (1/2:ℝ), ← Real.sqrt_eq_rpow ath]
    rw [one_div, ← Complex.ofReal_inv]
    congr 1
    have hinv : ath⁻¹ = Real.pi/a := by rw [hathdef]; field_simp
    rw [← Real.sqrt_inv, hinv]
  have hRHS_re : (1/(ath:ℂ)^(1/2:ℂ) * (∑' n : ℤ, Complex.exp (-(Real.pi:ℂ) / (ath:ℂ) * (((n:ℂ)) + Complex.I * ((-(ath*c):ℝ):ℂ))^2))).re
      = Real.sqrt (Real.pi/a) * (Real.exp (Real.pi*ath*c^2) * T) := by
    rw [hrc]
    rw [show (((Real.sqrt (Real.pi/a):ℝ):ℂ) * (∑' n : ℤ, Complex.exp (-(Real.pi:ℂ) / (ath:ℂ) * (((n:ℂ)) + Complex.I * ((-(ath*c):ℝ):ℂ))^2))).re
        = Real.sqrt (Real.pi/a) * (∑' n : ℤ, Complex.exp (-(Real.pi:ℂ) / (ath:ℂ) * (((n:ℂ)) + Complex.I * ((-(ath*c):ℝ):ℂ))^2)).re by
          simp [Complex.mul_re]]
    rw [hR_re_tsum]
  have hmain : Real.exp (Real.pi*ath*c^2) * S
      = Real.sqrt (Real.pi/a) * (Real.exp (Real.pi*ath*c^2) * T) := by
    calc Real.exp (Real.pi*ath*c^2) * S
        = (∑' n : ℤ, Complex.exp (-(Real.pi : ℂ) * (ath : ℂ) * ((n : ℂ))^2
              + 2 * (Real.pi : ℂ) * ((-(ath*c) : ℝ) : ℂ) * (n : ℂ))).re := hL_re.symm
      _ = (1/(ath:ℂ)^(1/2:ℂ) * (∑' n : ℤ, Complex.exp (-(Real.pi:ℂ) / (ath:ℂ) * (((n:ℂ)) + Complex.I * ((-(ath*c):ℝ):ℂ))^2))).re := by
            rw [hcomplex]
      _ = Real.sqrt (Real.pi/a) * (Real.exp (Real.pi*ath*c^2) * T) := hRHS_re
  have hfin : S = Real.sqrt (Real.pi/a) * T := by
    have h2 : Real.exp (Real.pi*ath*c^2) * S
        = Real.exp (Real.pi*ath*c^2) * (Real.sqrt (Real.pi/a) * T) := by
      rw [hmain]; ring
    exact mul_left_cancel₀ (Real.exp_ne_zero _) h2
  rw [hSdef, hTdef]
  exact hfin


private lemma summable_exp_neg_ratio {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Summable (fun n : ℤ => Real.exp (-(t*(Real.pi*(n:ℝ)/s)^2))) := by
  have h := summable_gauss_int (b := t*Real.pi^2/s^2) (by positivity)
  refine h.congr (fun n => ?_)
  congr 1
  field_simp

private lemma summable_neu_zeta {s t w : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Summable (fun n : ℤ => Real.exp (-(t*(Real.pi*(n:ℝ)/s)^2)) * Real.cos (Real.pi*(n:ℝ)*w/s)) := by
  have hg := summable_exp_neg_ratio hs ht
  refine Summable.of_norm_bounded hg (fun n => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  have hc := Real.abs_cos_le_one (Real.pi*(n:ℝ)*w/s)
  nlinarith [hc, (Real.exp_pos (-(t*(Real.pi*(n:ℝ)/s)^2))).le]

private lemma summable_gauss_image {s t w : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Summable (fun n : ℤ => Real.exp (-(w + 2*s*(n:ℝ))^2/(4*t))) := by
  have := summable_exp_neg_sq_shift (a := s^2/t) (c := w/(2*s)) (by positivity)
  refine this.congr (fun n => ?_)
  congr 1
  field_simp
  ring

private lemma gauss_image_sum {s t w : ℝ} (hs : 0 < s) (ht : 0 < t) :
    (∑' n : ℤ, Real.exp (-(w + 2*s*(n:ℝ))^2/(4*t)))
      = Real.sqrt (Real.pi*t)/s *
        (∑' n : ℤ, Real.exp (-(t*(Real.pi*(n:ℝ)/s)^2)) * Real.cos (Real.pi*(n:ℝ)*w/s)) := by
  have ha : (0:ℝ) < s^2/t := by positivity
  have h := theta_shift_real_aux (a := s^2/t) (c := w/(2*s)) ha
  rw [show (∑' n : ℤ, Real.exp (-(w + 2*s*(n:ℝ))^2/(4*t)))
        = (∑' n : ℤ, Real.exp (-((s^2/t) * ((n:ℝ) + w/(2*s))^2))) from
          tsum_congr (fun n => by congr 1; field_simp; ring), h]
  congr 1
  · rw [show Real.pi/(s^2/t) = Real.pi*t/s^2 by field_simp]
    rw [Real.sqrt_div (by positivity : (0:ℝ) ≤ Real.pi*t), Real.sqrt_sq hs.le]
  · apply tsum_congr; intro n
    rw [show Real.exp (-((Real.pi*(n:ℝ))^2)/(s^2/t)) = Real.exp (-(t*(Real.pi*(n:ℝ)/s)^2)) by
          congr 1; field_simp,
        show Real.cos (2*Real.pi*(n:ℝ)*(w/(2*s))) = Real.cos (Real.pi*(n:ℝ)*w/s) by
          congr 1; field_simp]


private lemma cos_sum_neu {s u v : ℝ} (hs : s ≠ 0) (n : ℤ) :
    Real.cos (Real.pi * (n:ℝ) * (u - v) / s) + Real.cos (Real.pi * (n:ℝ) * (u + v - s) / s)
      = 2 * (Real.cos (Real.pi*(n:ℝ)*(u+s/2)/s) * Real.cos (Real.pi*(n:ℝ)*(v+s/2)/s)) := by
  set A : ℝ := Real.pi*(n:ℝ)*(u+s/2)/s with hA
  set B : ℝ := Real.pi*(n:ℝ)*(v+s/2)/s with hB
  have h1 : Real.pi * (n:ℝ) * (u - v) / s = A - B := by rw [hA, hB]; field_simp; ring
  have h2 : Real.pi * (n:ℝ) * (u + v - s) / s = (A + B) - (n:ℤ)*(2*Real.pi) := by
    rw [hA, hB]; push_cast; field_simp; ring
  rw [h1, h2, Real.cos_sub_int_mul_two_pi, Real.cos_sub, Real.cos_add]
  ring

private theorem neumann_rhs_eq_zeta {s t u v : ℝ} (hs : 0 < s) (ht : 0 < t) :
    (∑' n : ℤ, (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) *
          (Real.exp (-((u - v + 2 * s * n) ^ 2) / (4 * t))
            + Real.exp (-((u + v - s + 2 * s * n) ^ 2) / (4 * t))))
      = s⁻¹ * ∑' n : ℤ, Real.cos (Real.pi * n * (u + s / 2) / s)
          * Real.cos (Real.pi * n * (v + s / 2) / s)
          * Real.exp (-(t * (Real.pi * n / s) ^ 2)) := by
  set z : ℤ → ℝ := fun n => Real.cos (Real.pi * (n:ℝ) * (u + s/2)/s)
      * Real.cos (Real.pi*(n:ℝ)*(v+s/2)/s) * Real.exp (-(t*(Real.pi*(n:ℝ)/s)^2)) with hzdef
  have hcoef : (4*Real.pi*t)^(-(1/2:ℝ)) * (Real.sqrt (Real.pi*t)/s) = (2*s)⁻¹ := by
    have hpos : (0:ℝ) < 4*Real.pi*t := by positivity
    have hsq : Real.sqrt (4*Real.pi*t) = 2*Real.sqrt (Real.pi*t) := by
      rw [show (4:ℝ)*Real.pi*t = (2*Real.sqrt (Real.pi*t))^2 by
            rw [mul_pow, Real.sq_sqrt (by positivity : (0:ℝ) ≤ Real.pi*t)]; ring,
          Real.sqrt_sq (by positivity)]
    rw [Real.rpow_neg (le_of_lt hpos), ← Real.sqrt_eq_rpow, hsq]
    field_simp
  rw [tsum_mul_left]
  rw [Summable.tsum_add (summable_gauss_image (w := u-v) hs ht) (summable_gauss_image (w := u+v-s) hs ht)]
  rw [gauss_image_sum (w := u-v) hs ht, gauss_image_sum (w := u+v-s) hs ht]
  set Q1 : ℝ := ∑' n : ℤ, Real.exp (-(t*(Real.pi*(n:ℝ)/s)^2)) * Real.cos (Real.pi*(n:ℝ)*(u-v)/s) with hQ1def
  set Q2 : ℝ := ∑' n : ℤ, Real.exp (-(t*(Real.pi*(n:ℝ)/s)^2)) * Real.cos (Real.pi*(n:ℝ)*(u+v-s)/s) with hQ2def
  have hQ : Q1 + Q2 = 2 * (∑' n : ℤ, z n) := by
    rw [hQ1def, hQ2def,
        ← Summable.tsum_add (summable_neu_zeta (w := u-v) hs ht) (summable_neu_zeta (w := u+v-s) hs ht)]
    rw [show (∑' n : ℤ, (Real.exp (-(t*(Real.pi*(n:ℝ)/s)^2)) * Real.cos (Real.pi*(n:ℝ)*(u-v)/s)
            + Real.exp (-(t*(Real.pi*(n:ℝ)/s)^2)) * Real.cos (Real.pi*(n:ℝ)*(u+v-s)/s)))
        = ∑' n : ℤ, 2 * z n from tsum_congr (fun n => by
            rw [hzdef]
            rw [← mul_add, cos_sum_neu (ne_of_gt hs)]
            ring)]
    rw [tsum_mul_left]
  rw [show (4*Real.pi*t)^(-(1/2:ℝ)) * ((Real.sqrt (Real.pi*t)/s) * Q1 + (Real.sqrt (Real.pi*t)/s) * Q2)
        = ((4*Real.pi*t)^(-(1/2:ℝ)) * (Real.sqrt (Real.pi*t)/s)) * (Q1 + Q2) by ring, hcoef, hQ]
  rw [show (2*s)⁻¹ * (2 * (∑' n : ℤ, z n)) = s⁻¹ * (∑' n : ℤ, z n) by field_simp]



theorem neumann_heat_one_dim_images {s t u v : ℝ} (hs : 0 < s) (ht : 0 < t) :
    (∑' k : ℕ, Real.cos (Real.pi * k * (u + s / 2) / s) * Real.cos (Real.pi * k * (v + s / 2) / s)
        * Real.exp (-(t * (Real.pi * k / s) ^ 2)) * (if k = 0 then s else s / 2)⁻¹)
      = ∑' n : ℤ, (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) *
          (Real.exp (-((u - v + 2 * s * n) ^ 2) / (4 * t))
            + Real.exp (-((u + v - s + 2 * s * n) ^ 2) / (4 * t))) := by
  rw [neumann_lhs_eq_zeta hs ht]
  exact (neumann_rhs_eq_zeta hs ht).symm

end Commons.Analysis.Fourier
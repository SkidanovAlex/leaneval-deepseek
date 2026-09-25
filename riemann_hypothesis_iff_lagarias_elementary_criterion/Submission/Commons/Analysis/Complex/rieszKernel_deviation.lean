import Mathlib
import Submission.Commons.Analysis.Fourier.perron_kernel_sigma_bound
import Submission.Commons.Analysis.Complex.exists_perron_formula_bound
import Submission.Commons.Analysis.Calculus.integral_two_mul_s_div_sq_add_sq

noncomputable section

open Complex MeasureTheory intervalIntegral Filter
open scoped Topology BigOperators

namespace Commons.Analysis.Complex

open Commons.Analysis.Fourier
open Commons.Analysis.Calculus

/-- For `y > 0`, `(y:ℂ)^{ρ+it} = y^ρ · e^{i t log y}`. -/
lemma cpow_eq_rpow_mul_exp (y : ℝ) (hy : 0 < y) (ρ t : ℝ) :
    (y : ℂ) ^ ((ρ : ℂ) + (t : ℂ) * Complex.I)
      = ((y ^ ρ : ℝ) : ℂ) * Complex.exp (Complex.I * ((Real.log y : ℂ) * (t : ℂ))) := by
  have hyc : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  rw [Complex.cpow_def_of_ne_zero hyc, ← Complex.ofReal_log hy.le]
  have harg : ((Real.log y : ℝ) : ℂ) * ((ρ : ℂ) + (t : ℂ) * Complex.I)
      = ((ρ * Real.log y : ℝ) : ℂ)
        + Complex.I * (((Real.log y : ℝ) : ℂ) * (t : ℂ)) := by
    rw [mul_add, ← Complex.ofReal_mul]
    have h2 : (((Real.log y * ρ : ℝ)) : ℂ) = (((ρ * Real.log y : ℝ)) : ℂ) := by
      rw [mul_comm]
    have h3 : (((Real.log y : ℝ) : ℂ)) * ((t : ℂ) * Complex.I)
        = Complex.I * (((Real.log y : ℝ) : ℂ) * (t : ℂ)) := by ring_nf
    rw [h2, h3]
  rw [harg, Complex.exp_add, ← Complex.ofReal_exp]
  have hpow : ((y ^ ρ : ℝ) : ℂ) = ((Real.exp (ρ * Real.log y) : ℝ) : ℂ) := by
    rw [Real.rpow_def_of_pos hy]
    congr 1
    ring
  rw [hpow]

/-- The Riesz/Perron integrand is `y^c` times a difference of two σ-kernels. -/
lemma rieszIntegrand_eq (y : ℝ) (hy : 0 < y) (c t : ℝ) (hc : 0 < c) :
    (y : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) /
        (((c : ℂ) + (t : ℂ) * Complex.I) * (((c + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I))
      = ((y ^ c : ℝ) : ℂ) * (pskKern c (Real.log y) t - pskKern (c + 1) (Real.log y) t) := by
  have hB : ((c : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    rw [show (t : ℂ) * Complex.I = Complex.I * (t : ℂ) by ring]
    exact sigma_denom_ne_zero c t hc.ne'
  have hC : (((c + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    rw [show (t : ℂ) * Complex.I = Complex.I * (t : ℂ) by ring]
    exact sigma_denom_ne_zero (c + 1) t (by linarith)
  have hCB : (((c + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I) - ((c : ℂ) + (t : ℂ) * Complex.I) = 1 := by
    push_cast
    ring
  have hsplit : (y : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) /
        (((c : ℂ) + (t : ℂ) * Complex.I) * (((c + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I))
      = (y : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) / ((c : ℂ) + (t : ℂ) * Complex.I)
        - (y : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I)
            / (((c + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I) := by
    rw [div_sub_div ((y : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I))
      ((y : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I)) hB hC]
    congr 1
    rw [show (y : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) * (((c + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I)
          - ((c : ℂ) + (t : ℂ) * Complex.I) * (y : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I)
        = (y : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I)
            * ((((c + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I) - ((c : ℂ) + (t : ℂ) * Complex.I)) by ring]
    rw [hCB, mul_one]
  have h1 : (y : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) / ((c : ℂ) + (t : ℂ) * Complex.I)
      = ((y ^ c : ℝ) : ℂ) * pskKern c (Real.log y) t := by
    rw [cpow_eq_rpow_mul_exp y hy c t, pskKern]
    rw [show ((c : ℂ) + (t : ℂ) * Complex.I) = ((c : ℂ) + Complex.I * (t : ℂ)) by ring]
    ring
  have h2 : (y : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I)
        / (((c + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I)
      = ((y ^ c : ℝ) : ℂ) * pskKern (c + 1) (Real.log y) t := by
    rw [cpow_eq_rpow_mul_exp y hy c t, pskKern]
    rw [show (((c + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I)
        = (((c + 1 : ℝ) : ℂ) + Complex.I * (t : ℂ)) by ring]
    ring
  rw [hsplit, h1, h2, mul_sub]

/-- `‖(y:ℂ)^{c+it}‖ = y^c` for `y > 0`. -/
lemma norm_cpow_rpow (y : ℝ) (hy : 0 < y) (c t : ℝ) :
    ‖(y : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I)‖ = y ^ c := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hy.ne'), ← Complex.ofReal_log hy.le,
    Complex.norm_exp]
  have hre : (((Real.log y : ℝ) : ℂ) * ((c : ℂ) + (t : ℂ) * Complex.I)).re
      = Real.log y * c := by
    simp [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im]
  rw [hre, Real.rpow_def_of_pos hy]

/-- The Riesz/Perron integrand. -/
def rieszKern (y c : ℝ) (t : ℝ) : ℂ :=
  (y : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) /
    (((c : ℂ) + (t : ℂ) * Complex.I) * (((c + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I))

/-- The σ-line is at distance at least `|t|` from the origin. -/
lemma norm_sline_ge_abs (c t : ℝ) : |t| ≤ ‖((c : ℂ) + (t : ℂ) * Complex.I)‖ := by
  have h : |t| ^ 2 ≤ ‖((c : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 := by
    rw [sq_abs, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    nlinarith [sq_nonneg c]
  simpa [abs_of_nonneg (norm_nonneg _)] using (sq_le_sq.mp h)

/-- Pointwise absolute bound on the Riesz integrand. -/
lemma norm_rieszKern_le (y c t : ℝ) (hy : 0 < y) (ht : 1 ≤ |t|) :
    ‖rieszKern y c t‖ ≤ y ^ c * (t ^ 2)⁻¹ := by
  have ht0 : 0 < |t| := lt_of_lt_of_le zero_lt_one ht
  have hA : |t| ≤ ‖((c : ℂ) + (t : ℂ) * Complex.I)‖ := norm_sline_ge_abs c t
  have hB : |t| ≤ ‖(((c + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ := norm_sline_ge_abs (c + 1) t
  have hApos : (0:ℝ) < ‖((c : ℂ) + (t : ℂ) * Complex.I)‖ := lt_of_lt_of_le ht0 hA
  have hBpos : (0:ℝ) < ‖(((c + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ := lt_of_lt_of_le ht0 hB
  have hden : t ^ 2 ≤ ‖((c : ℂ) + (t : ℂ) * Complex.I)‖
      * ‖(((c + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ := by
    rw [← sq_abs, pow_two]
    calc |t| * |t| ≤ ‖((c : ℂ) + (t : ℂ) * Complex.I)‖ * |t| :=
          mul_le_mul_of_nonneg_right hA ht0.le
      _ ≤ ‖((c : ℂ) + (t : ℂ) * Complex.I)‖
            * ‖(((c + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ :=
          mul_le_mul_of_nonneg_left hB (norm_nonneg _)
  unfold rieszKern
  rw [norm_div, norm_mul, norm_cpow_rpow y hy c t, div_eq_mul_inv]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hy.le c)
  exact (inv_le_inv₀ (mul_pos hApos hBpos) (by rw [← sq_abs]; exact pow_pos ht0 2)).mpr hden

/-- Continuity of the Riesz integrand in `t`. -/
lemma continuous_rieszKern (y c : ℝ) (hy : 0 < y) (hc : 0 < c) :
    Continuous (rieszKern y c) := by
  have hfun : rieszKern y c
      = fun t => ((y ^ c : ℝ) : ℂ)
          * (pskKern c (Real.log y) t - pskKern (c + 1) (Real.log y) t) := by
    funext t
    exact rieszIntegrand_eq y hy c t hc
  rw [hfun]
  exact continuous_const.mul
    ((psk_continuous c (Real.log y) hc.ne').sub (psk_continuous (c + 1) (Real.log y) (by linarith)))

/-- Interval-integral identity: the Riesz integral is `y^c` times the difference of two
σ-kernels. -/
lemma integral_rieszKern_eq (y c R : ℝ) (hy : 0 < y) (hc : 0 < c) :
    (∫ t in (-R)..R, rieszKern y c t)
      = ((y ^ c : ℝ) : ℂ) * (pskInt c R (Real.log y) - pskInt (c + 1) R (Real.log y)) := by
  have hpt : ∀ t : ℝ, rieszKern y c t
      = ((y ^ c : ℝ) : ℂ) * (pskKern c (Real.log y) t - pskKern (c + 1) (Real.log y) t) :=
    fun t => rieszIntegrand_eq y hy c t hc
  rw [intervalIntegral.integral_congr (fun t _ => hpt t)]
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_sub
    ((psk_continuous c (Real.log y) hc.ne').intervalIntegrable _ _)
    ((psk_continuous (c + 1) (Real.log y) (by linarith)).intervalIntegrable _ _)]
  simp only [pskInt]


/-- The limiting values of the two σ-kernels combine to the Riesz kernel `(1-1/y)_+`. -/
lemma pskValReal_rieszValue (y c : ℝ) (hy : 0 < y) :
    (y ^ c / (2 * Real.pi)) * (pskValReal c (Real.log y) - pskValReal (c + 1) (Real.log y))
      = max (1 - 1 / y) 0 := by
  by_cases hpos : 0 < Real.log y
  · have hy1 : 1 < y := (Real.log_pos_iff hy.le).mp hpos
    have hmax : max (1 - 1 / y) 0 = 1 - 1 / y := by
      apply max_eq_left
      have h := (div_lt_one hy).mpr hy1
      linarith
    rw [hmax]
    unfold pskValReal
    rw [if_pos hpos, if_pos hpos]
    have e1 : Real.exp (-(c * Real.log y)) = (y ^ c)⁻¹ := by
      rw [show -(c * Real.log y) = -((Real.log y) * c) by ring, Real.exp_neg,
        ← Real.rpow_def_of_pos hy]
    have e2 : Real.exp (-((c + 1) * Real.log y)) = (y ^ (c + 1))⁻¹ := by
      rw [show -((c + 1) * Real.log y) = -((Real.log y) * (c + 1)) by ring, Real.exp_neg,
        ← Real.rpow_def_of_pos hy]
    rw [e1, e2]
    have hcp : y ^ (c + 1) = y ^ c * y := by rw [Real.rpow_add hy c 1, Real.rpow_one]
    have hyc : y ^ c ≠ 0 := (Real.rpow_pos_of_pos hy c).ne'
    have hy0 : y ≠ 0 := hy.ne'
    have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_pos.ne'
    rw [hcp]
    field_simp
  · have hy1 : y ≤ 1 := (Real.log_nonpos_iff hy.le).mp (le_of_not_gt hpos)
    have hmax : max (1 - 1 / y) 0 = 0 := by
      apply max_eq_right
      have h : 1 ≤ 1 / y := by rw [le_div_iff₀ hy]; simpa using hy1
      linarith
    rw [hmax]
    unfold pskValReal
    rw [if_neg hpos, if_neg hpos, sub_zero, mul_zero]

/-- The truncated Riesz integral converges to the Riesz kernel as `R → ∞` (for `y ≠ 1`). -/
lemma tendsto_rieszInt (y c : ℝ) (hy : 0 < y) (hc : 0 < c) (hL : Real.log y ≠ 0) :
    Tendsto (fun R : ℝ => (1 / (2 * Real.pi)) * (∫ t in (-R)..R, rieszKern y c t))
      atTop (nhds ((max (1 - 1 / y) 0 : ℝ) : ℂ)) := by
  have hc1 : 0 < c + 1 := by linarith
  have h1 : Tendsto (fun R : ℝ => pskInt c R (Real.log y)) atTop
      (nhds (if 0 < Real.log y then 2 * ↑Real.pi
        * Complex.exp (-((c : ℂ) * ↑(Real.log y))) else 0)) := by
    simpa [pskInt, pskKern] using (perronKernelSigma_tendsto c (Real.log y) hc hL)
  have h2 : Tendsto (fun R : ℝ => pskInt (c + 1) R (Real.log y)) atTop
      (nhds (if 0 < Real.log y then 2 * ↑Real.pi
        * Complex.exp (-(((c + 1 : ℝ) : ℂ) * ↑(Real.log y))) else 0)) := by
    simpa [pskInt, pskKern] using (perronKernelSigma_tendsto (c + 1) (Real.log y) hc1 hL)
  have h3 : Tendsto (fun R : ℝ => pskInt c R (Real.log y) - pskInt (c + 1) R (Real.log y))
      atTop (nhds ((if 0 < Real.log y then 2 * ↑Real.pi
          * Complex.exp (-((c : ℂ) * ↑(Real.log y))) else 0)
        - (if 0 < Real.log y then 2 * ↑Real.pi
          * Complex.exp (-(((c + 1 : ℝ) : ℂ) * ↑(Real.log y))) else 0))) :=
    h1.sub h2
  have hlim : ((1 / (2 * Real.pi)) * ((y ^ c : ℝ) : ℂ))
      * ((if 0 < Real.log y then 2 * ↑Real.pi * Complex.exp (-((c : ℂ) * ↑(Real.log y))) else 0)
        - (if 0 < Real.log y then 2 * ↑Real.pi
            * Complex.exp (-(((c + 1 : ℝ) : ℂ) * ↑(Real.log y))) else 0))
      = ((max (1 - 1 / y) 0 : ℝ) : ℂ) := by
    rw [psk_value_eq_ofReal c (Real.log y), psk_value_eq_ofReal (c + 1) (Real.log y)]
    have hscal : (1 / (2 * Real.pi)) * ((y ^ c : ℝ) : ℂ)
        = (((y ^ c / (2 * Real.pi) : ℝ)) : ℂ) := by
      push_cast
      ring
    rw [hscal, ← Complex.ofReal_sub, ← Complex.ofReal_mul, pskValReal_rieszValue y c hy]
  have hfun : (fun R : ℝ => (1 / (2 * Real.pi)) * (∫ t in (-R)..R, rieszKern y c t))
      = fun R : ℝ => ((1 / (2 * Real.pi)) * ((y ^ c : ℝ) : ℂ))
          * (pskInt c R (Real.log y) - pskInt (c + 1) R (Real.log y)) := by
    funext R
    rw [integral_rieszKern_eq y c R hy hc]
    ring
  rw [hfun]
  have hfinal : Tendsto (fun R : ℝ => ((1 / (2 * Real.pi)) * ((y ^ c : ℝ) : ℂ))
      * (pskInt c R (Real.log y) - pskInt (c + 1) R (Real.log y))) atTop
      (nhds ((max (1 - 1 / y) 0 : ℝ) : ℂ)) := by
    have := Filter.Tendsto.const_mul (((1 / (2 * Real.pi)) * ((y ^ c : ℝ) : ℂ))) h3
    rwa [hlim] at this
  exact hfinal

/-- Positive tail bound. -/
lemma rieszKern_pos_tail (y c T R : ℝ) (hy : 0 < y) (hc : 1 ≤ c) (hT : 1 ≤ T)
    (hTR : T ≤ R) : ‖∫ t in T..R, rieszKern y c t‖ ≤ y ^ c / T := by
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hR0 : 0 < R := lt_of_lt_of_le hT0 hTR
  calc
    ‖∫ t in T..R, rieszKern y c t‖ ≤ ∫ t in T..R, ‖rieszKern y c t‖ :=
      intervalIntegral.norm_integral_le_integral_norm hTR
    _ ≤ ∫ t in T..R, y ^ c * (t ^ 2)⁻¹ := by
      refine intervalIntegral.integral_mono_on hTR ?_ ?_ ?_
      · exact ((continuous_rieszKern y c hy hc0).norm).intervalIntegrable T R
      · exact (PerronSigma.integrable_inv_sq_Icc T R hT0 hTR).const_mul (y ^ c)
      · intro t ht
        exact norm_rieszKern_le y c t hy (by
          rw [abs_of_nonneg (le_trans hT0.le ht.1)]; exact le_trans hT ht.1)
    _ = y ^ c * ∫ t in T..R, (t ^ 2)⁻¹ := intervalIntegral.integral_const_mul _ _
    _ = y ^ c * (T⁻¹ - R⁻¹) := by rw [PerronSigma.integral_inv_sq_of_pos T R hT0 hR0]
    _ ≤ y ^ c / T := by
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left (sub_le_self _ (inv_nonneg.mpr hR0.le))
        (Real.rpow_nonneg hy.le c)

/-- Negative tail bound. -/
lemma rieszKern_neg_tail (y c T R : ℝ) (hy : 0 < y) (hc : 1 ≤ c) (hT : 1 ≤ T)
    (hTR : T ≤ R) : ‖∫ t in (-R)..(-T), rieszKern y c t‖ ≤ y ^ c / T := by
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hR0 : 0 < R := lt_of_lt_of_le hT0 hTR
  rw [← intervalIntegral.integral_comp_neg (f := fun t => rieszKern y c t) (a := T) (b := R)]
  calc
    ‖∫ x in T..R, rieszKern y c (-x)‖ ≤ ∫ x in T..R, ‖rieszKern y c (-x)‖ :=
      intervalIntegral.norm_integral_le_integral_norm hTR
    _ ≤ ∫ x in T..R, y ^ c * (x ^ 2)⁻¹ := by
      refine intervalIntegral.integral_mono_on hTR ?_ ?_ ?_
      · exact (((continuous_rieszKern y c hy hc0).comp continuous_neg).norm).intervalIntegrable T R
      · exact (PerronSigma.integrable_inv_sq_Icc T R hT0 hTR).const_mul (y ^ c)
      · intro x hx
        calc ‖rieszKern y c (-x)‖ ≤ y ^ c * ((-x) ^ 2)⁻¹ := norm_rieszKern_le y c (-x) hy (by
              rw [abs_neg, abs_of_nonneg (le_trans hT0.le hx.1)]; exact le_trans hT hx.1)
          _ = y ^ c * (x ^ 2)⁻¹ := by rw [show (-x) ^ 2 = x ^ 2 by ring]
    _ = y ^ c * ∫ x in T..R, (x ^ 2)⁻¹ := intervalIntegral.integral_const_mul _ _
    _ = y ^ c * (T⁻¹ - R⁻¹) := by rw [PerronSigma.integral_inv_sq_of_pos T R hT0 hR0]
    _ ≤ y ^ c / T := by
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left (sub_le_self _ (inv_nonneg.mpr hR0.le))
        (Real.rpow_nonneg hy.le c)


/-- `∫_{-T}^{T} σ/(σ²+t²) dt = 2 arctan(T/σ)`. -/
lemma integral_sigma_div (σ T : ℝ) (hσ : 0 < σ) :
    ∫ t in (-T)..T, σ/(σ^2+t^2) = 2 * Real.arctan (T/σ) := by
  have h2σ := integral_two_mul_s_div_sq_add_sq (s := σ) hσ T
  have heq : (∫ u in (-T)..T, 2*σ/(u^2+σ^2)) = 2 * ∫ u in (-T)..T, σ/(σ^2+u^2) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u _
    ring
  rw [heq] at h2σ
  linarith

/-- The integral of an odd function over a symmetric interval vanishes. -/
lemma integral_odd_zero_real (f : ℝ → ℝ) (hf : ∀ x, f (-x) = -f x) (T : ℝ) :
    ∫ x in (-T)..T, f x = 0 := by
  have h := intervalIntegral.integral_comp_neg (f := f) (a := -T) (b := T)
  have hL : (∫ x in (-T)..T, f (-x)) = -∫ x in (-T)..T, f x := by
    rw [show (fun x => f (-x)) = (fun x => -f x) from funext fun x => hf x]
    exact intervalIntegral.integral_neg
  rw [hL] at h
  simp only [neg_neg] at h
  have h2 : (∫ x in (-T)..T, f x) + (∫ x in (-T)..T, f x) = 0 :=
    (neg_eq_iff_add_eq_zero).mp h
  linarith

/-- `pskInt σ T 0 = 2 arctan(T/σ)`. -/
lemma pskInt_zero (σ T : ℝ) (hσ : 0 < σ) :
    pskInt σ T 0 = (((2 * Real.arctan (T / σ) : ℝ)) : ℂ) := by
  have hcont : Continuous (pskKern σ 0) := psk_continuous σ 0 hσ.ne'
  have hnormSq : ∀ t : ℝ, Complex.normSq ((σ:ℂ) + Complex.I*(t:ℂ)) = σ^2 + t^2 := by
    intro t
    rw [Complex.normSq_apply]
    simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hz : ∀ t : ℝ, pskKern σ 0 t = ((σ:ℂ) + Complex.I*(t:ℂ))⁻¹ := by
    intro t; simp [pskKern]
  have hre_pt : ∀ t : ℝ, (pskKern σ 0 t).re = σ / (σ^2 + t^2) := by
    intro t
    rw [hz t, Complex.inv_re, hnormSq t]
    simp [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im]
  have him_pt : ∀ t : ℝ, (pskKern σ 0 t).im = -(t / (σ^2 + t^2)) := by
    intro t
    rw [hz t, Complex.inv_im, hnormSq t]
    simp [Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, Complex.I_re,
      Complex.I_im, neg_div]
  have hre : (pskInt σ T 0).re = 2 * Real.arctan (T/σ) := by
    have h := Complex.reCLM.intervalIntegral_comp_comm (μ := volume) (f := pskKern σ 0)
      (a := -T) (b := T) (hcont.intervalIntegrable (-T) T)
    change Complex.reCLM (∫ t in (-T)..T, pskKern σ 0 t) = 2 * Real.arctan (T/σ)
    rw [← h]
    rw [show (∫ t in (-T)..T, Complex.reCLM (pskKern σ 0 t))
        = ∫ t in (-T)..T, σ/(σ^2+t^2) by
      apply intervalIntegral.integral_congr
      intro t _
      simpa using hre_pt t]
    exact integral_sigma_div σ T hσ
  have him : (pskInt σ T 0).im = 0 := by
    have h := Complex.imCLM.intervalIntegral_comp_comm (μ := volume) (f := pskKern σ 0)
      (a := -T) (b := T) (hcont.intervalIntegrable (-T) T)
    change Complex.imCLM (∫ t in (-T)..T, pskKern σ 0 t) = 0
    rw [← h]
    rw [show (∫ t in (-T)..T, Complex.imCLM (pskKern σ 0 t))
        = ∫ t in (-T)..T, -(t/(σ^2+t^2)) by
      apply intervalIntegral.integral_congr
      intro t _
      simpa using him_pt t]
    rw [intervalIntegral.integral_neg]
    rw [integral_odd_zero_real (fun t => t/(σ^2+t^2)) (fun x => by
      rw [show σ^2 + (-x)^2 = σ^2 + x^2 by ring]
      ring) T]
    ring
  rw [Complex.ext_iff]
  exact ⟨by rw [hre, Complex.ofReal_re], by rw [him, Complex.ofReal_im]⟩

/-- `arctan b - arctan a ≤ 1/a - 1/b` for `0 < a ≤ b`. -/
lemma arctan_diff_le (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    Real.arctan b - Real.arctan a ≤ a⁻¹ - b⁻¹ := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hFTC : (∫ x in a..b, 1/(1+x^2)) = Real.arctan b - Real.arctan a := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := Real.arctan)
      (f' := fun x => 1/(1+x^2)) (fun x _ => Real.hasDerivAt_arctan x)]
    exact (continuous_const.div (by fun_prop) (fun x => by positivity)).intervalIntegrable a b
  rw [← hFTC]
  calc
    ∫ x in a..b, 1/(1+x^2) ≤ ∫ x in a..b, (x^2)⁻¹ := by
      apply intervalIntegral.integral_mono_on hab
      · exact (continuous_const.div (by fun_prop) (fun x => by positivity)).intervalIntegrable a b
      · exact PerronSigma.integrable_inv_sq_Icc a b ha hab
      · intro x hx
        have hx0 : 0 < x := lt_of_lt_of_le ha hx.1
        rw [one_div]
        exact (inv_le_inv₀ (by positivity : (0:ℝ) < 1 + x^2) (pow_pos hx0 2)).mpr (by linarith)
    _ = a⁻¹ - b⁻¹ := PerronSigma.integral_inv_sq_of_pos a b ha hb

/-- `arctan(T/c) - arctan(T/(c+1)) ≤ 1/T` for `1 ≤ c`, `0 < T`. -/
lemma arctan_div_sub_le (c T : ℝ) (hc : 1 ≤ c) (hT : 0 < T) :
    Real.arctan (T/c) - Real.arctan (T/(c+1)) ≤ 1/T := by
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have ha : 0 < T/(c+1) := div_pos hT (by linarith)
  have hab : T/(c+1) ≤ T/c := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left
      ((inv_le_inv₀ (by linarith : (0:ℝ) < c+1) hc0).mpr (by linarith)) hT.le
  have h := arctan_diff_le (T/(c+1)) (T/c) ha hab
  have h2 : (T/(c+1))⁻¹ - (T/c)⁻¹ = 1/T := by
    field_simp
    ring
  linarith [h, h2]

/-- The `y = 1` Riesz morsel. -/
lemma rieszInt_one_bound (c T : ℝ) (hc : 1 ≤ c) (hT : 1 ≤ T) :
    ‖(1 / (2 * Real.pi)) * (pskInt c T 0 - pskInt (c + 1) T 0)‖ ≤ 1 / T := by
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hc1 : 0 < c + 1 := by linarith
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
  rw [pskInt_zero c T hc0, pskInt_zero (c + 1) T hc1]
  have hsub : (((2 * Real.arctan (T/c) : ℝ)) : ℂ) - (((2 * Real.arctan (T/(c+1)) : ℝ)) : ℂ)
      = (((2 * Real.arctan (T/c) - 2 * Real.arctan (T/(c+1)) : ℝ)) : ℂ) := by
    rw [Complex.ofReal_sub]
  rw [hsub]
  have hCn : ‖(1 / (2 * Real.pi) : ℂ)‖ = 1 / (2 * Real.pi) := by
    have h1 : (1 / (2 * Real.pi) : ℂ) = (((1 / (2 * Real.pi) : ℝ)) : ℂ) := by simp
    rw [h1]
    rw [show ‖(((1 / (2 * Real.pi) : ℝ)) : ℂ)‖ = |(1 / (2 * Real.pi) : ℝ)| from
      RCLike.norm_ofReal (K := ℂ) (1 / (2 * Real.pi))]
    exact abs_of_nonneg (by positivity)
  rw [norm_mul, hCn]
  rw [show ‖((((2 * Real.arctan (T/c) - 2 * Real.arctan (T/(c+1)) : ℝ)) : ℂ))‖
      = |2 * Real.arctan (T/c) - 2 * Real.arctan (T/(c+1))| from
      RCLike.norm_ofReal (K := ℂ) (2 * Real.arctan (T/c) - 2 * Real.arctan (T/(c+1)))]
  have hb : |2 * Real.arctan (T/c) - 2 * Real.arctan (T/(c+1))| ≤ 2/T := by
    have hnon : Real.arctan (T/(c+1)) ≤ Real.arctan (T/c) := by
      apply Real.arctan_mono
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left
        ((inv_le_inv₀ (by linarith : (0:ℝ) < c+1) hc0).mpr (by linarith)) hT0.le
    rw [abs_of_nonneg (by linarith [hnon])]
    calc
      2 * Real.arctan (T/c) - 2 * Real.arctan (T/(c+1))
          = 2 * (Real.arctan (T/c) - Real.arctan (T/(c+1))) := by ring
      _ ≤ 2 * (1/T) := mul_le_mul_of_nonneg_left (arctan_div_sub_le c T hc hT0) (by norm_num)
      _ = 2/T := by ring
  calc
    (1 / (2 * Real.pi)) * |2 * Real.arctan (T/c) - 2 * Real.arctan (T/(c+1))|
        ≤ (1 / (2 * Real.pi)) * (2/T) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = 1 / (Real.pi * T) := by ring
    _ ≤ 1/T := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (inv_le_inv₀ (by positivity) hT0).mpr (by nlinarith [Real.pi_gt_three, hT0])

/-- The Riesz kernel `(1-1/y)_+` has the Mellin/Perron representation
`(1/2π)∫_{-T}^{T} y^{c+it}/((c+it)(c+1+it)) dt`, with error `O(y^c/T)`. -/
theorem rieszKernel_deviation (c T y : ℝ) (hc : 1 ≤ c) (hT : 1 ≤ T) (hy : 0 < y) :
    ‖(1 / (2 * Real.pi)) * (∫ t in (-T)..T,
        ((y : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I)) /
          ((((c : ℂ) + (t : ℂ) * Complex.I) * (((c + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I))))
      - ((max (1 - 1 / y) 0 : ℝ) : ℂ)‖ ≤ y ^ c / T := by
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
  change ‖(1 / (2 * Real.pi)) * (∫ t in (-T)..T, rieszKern y c t)
      - ((max (1 - 1 / y) 0 : ℝ) : ℂ)‖ ≤ y ^ c / T
  by_cases hy1 : y = 1
  · subst hy1
    have hmax : ((max (1 - 1 / 1) 0 : ℝ) : ℂ) = 0 := by norm_num
    rw [hmax, sub_zero]
    have hrpow : (1:ℝ) ^ c = 1 := Real.one_rpow c
    rw [hrpow]
    have hone : (∫ t in (-T)..T, rieszKern 1 c t) = pskInt c T 0 - pskInt (c + 1) T 0 := by
      have hpt : ∀ t : ℝ, rieszKern 1 c t = pskKern c 0 t - pskKern (c + 1) 0 t := by
        intro t
        rw [rieszKern, rieszIntegrand_eq 1 (by norm_num) c t hc0, Real.one_rpow, Real.log_one]
        simp
      rw [intervalIntegral.integral_congr (fun t _ => hpt t)]
      rw [intervalIntegral.integral_sub
        ((psk_continuous c 0 hc0.ne').intervalIntegrable _ _)
        ((psk_continuous (c + 1) 0 (by linarith)).intervalIntegrable _ _)]
      simp only [pskInt]
    rw [hone]
    exact rieszInt_one_bound c T hc hT
  · have hL : Real.log y ≠ 0 := by
      intro h
      apply hy1
      have hz := Real.exp_log hy
      rw [← hz, h, Real.exp_zero]
    have hconv := tendsto_rieszInt y c hy hc0 hL
    have htail : ∀ R : ℝ, T ≤ R → ‖(1 / (2 * Real.pi)) * (∫ t in (-R)..R, rieszKern y c t)
        - (1 / (2 * Real.pi)) * (∫ t in (-T)..T, rieszKern y c t)‖ ≤ y ^ c / (Real.pi * T) := by
      intro R hTR
      have hcont := continuous_rieszKern y c hy hc0
      have hsplit : (∫ t in (-R)..R, rieszKern y c t) - (∫ t in (-T)..T, rieszKern y c t)
          = (∫ t in (-R)..(-T), rieszKern y c t) + (∫ t in T..R, rieszKern y c t) := by
        have h1 := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
          (f := fun t => rieszKern y c t) (a := -R) (b := -T) (c := T)
          (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)
        have h2 := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
          (f := fun t => rieszKern y c t) (a := -R) (b := T) (c := R)
          (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)
        have hE : (∫ t in (-R)..R, rieszKern y c t)
            = (∫ t in (-R)..(-T), rieszKern y c t) + (∫ t in (-T)..T, rieszKern y c t)
              + (∫ t in T..R, rieszKern y c t) := by
          rw [← h2, ← h1]
        rw [hE]; abel
      rw [← mul_sub, hsplit]
      have hCn : ‖(1 / (2 * Real.pi) : ℂ)‖ = 1 / (2 * Real.pi) := by
        have h1 : (1 / (2 * Real.pi) : ℂ) = (((1 / (2 * Real.pi) : ℝ)) : ℂ) := by simp
        rw [h1]
        rw [show ‖(((1 / (2 * Real.pi) : ℝ)) : ℂ)‖ = |(1 / (2 * Real.pi) : ℝ)| from
          RCLike.norm_ofReal (K := ℂ) (1 / (2 * Real.pi))]
        exact abs_of_nonneg (by positivity)
      calc
        ‖(1 / (2 * Real.pi)) * ((∫ t in (-R)..(-T), rieszKern y c t)
            + (∫ t in T..R, rieszKern y c t))‖
            = ‖(1 / (2 * Real.pi) : ℂ)‖ * ‖(∫ t in (-R)..(-T), rieszKern y c t)
                + (∫ t in T..R, rieszKern y c t)‖ := norm_mul _ _
        _ ≤ (1 / (2 * Real.pi)) * (‖∫ t in (-R)..(-T), rieszKern y c t‖
              + ‖∫ t in T..R, rieszKern y c t‖) := by
            rw [hCn]
            exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
        _ ≤ (1 / (2 * Real.pi)) * (y ^ c / T + y ^ c / T) :=
            mul_le_mul_of_nonneg_left (add_le_add (rieszKern_neg_tail y c T R hy hc hT hTR)
              (rieszKern_pos_tail y c T R hy hc hT hTR)) (by positivity)
        _ = y ^ c / (Real.pi * T) := by ring
    have hmain : ‖(1 / (2 * Real.pi)) * (∫ t in (-T)..T, rieszKern y c t)
        - ((max (1 - 1 / y) 0 : ℝ) : ℂ)‖ ≤ y ^ c / (Real.pi * T) := by
      apply le_of_forall_pos_le_add
      intro ε hε
      have hconvε : ∀ᶠ R in atTop, ‖(1 / (2 * Real.pi)) * (∫ t in (-R)..R, rieszKern y c t)
          - ((max (1 - 1 / y) 0 : ℝ) : ℂ)‖ < ε := by
        have hh := (Metric.tendsto_nhds.mp hconv) ε hε
        simpa [dist_eq_norm] using hh
      rcases eventually_atTop.1 hconvε with ⟨R0, hR0⟩
      let R1 := max T R0
      have hTR1 : T ≤ R1 := le_max_left _ _
      have hR0R1 : R0 ≤ R1 := le_max_right _ _
      have hεR := (hR0 R1 hR0R1).le
      have htri : ‖(1 / (2 * Real.pi)) * (∫ t in (-T)..T, rieszKern y c t)
            - ((max (1 - 1 / y) 0 : ℝ) : ℂ)‖
          ≤ ‖(1 / (2 * Real.pi)) * (∫ t in (-T)..T, rieszKern y c t)
              - (1 / (2 * Real.pi)) * (∫ t in (-R1)..R1, rieszKern y c t)‖
            + ‖(1 / (2 * Real.pi)) * (∫ t in (-R1)..R1, rieszKern y c t)
              - ((max (1 - 1 / y) 0 : ℝ) : ℂ)‖ := by
        have := dist_triangle ((1 / (2 * Real.pi)) * (∫ t in (-T)..T, rieszKern y c t))
          ((1 / (2 * Real.pi)) * (∫ t in (-R1)..R1, rieszKern y c t))
          (((max (1 - 1 / y) 0 : ℝ) : ℂ))
        simpa [dist_eq_norm] using this
      calc
        ‖(1 / (2 * Real.pi)) * (∫ t in (-T)..T, rieszKern y c t)
            - ((max (1 - 1 / y) 0 : ℝ) : ℂ)‖ ≤ _ := htri
        _ = ‖(1 / (2 * Real.pi)) * (∫ t in (-R1)..R1, rieszKern y c t)
              - (1 / (2 * Real.pi)) * (∫ t in (-T)..T, rieszKern y c t)‖
            + ‖(1 / (2 * Real.pi)) * (∫ t in (-R1)..R1, rieszKern y c t)
              - ((max (1 - 1 / y) 0 : ℝ) : ℂ)‖ := by rw [norm_sub_rev]
        _ ≤ y ^ c / (Real.pi * T) + ε := add_le_add (htail R1 hTR1) hεR
    calc
      ‖(1 / (2 * Real.pi)) * (∫ t in (-T)..T, rieszKern y c t)
          - ((max (1 - 1 / y) 0 : ℝ) : ℂ)‖ ≤ y ^ c / (Real.pi * T) := hmain
      _ ≤ y ^ c / T := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hy.le c)
        exact (inv_le_inv₀ (by positivity) hT0).mpr (by nlinarith [Real.pi_gt_three, hT0])

end Commons.Analysis.Complex

import Mathlib
import Submission.Commons.Analysis.Perron.integral_cpow_kernel

noncomputable section
open MeasureTheory Set Complex
open scoped FourierTransform RealInnerProductSpace

namespace Commons.Analysis.Laplace

def laplaceSource (σ β : ℝ) : ℝ → ℂ :=
  fun v => if 0 < v then (v:ℂ)^((β:ℂ)-1) * Complex.exp (-(σ:ℂ)*(v:ℂ)) else 0

lemma integrable_laplaceSource (σ β : ℝ) (hσ : 0 < σ) (hβ : 0 < β) : Integrable (laplaceSource σ β) := by
  have hreal : Integrable (fun v : ℝ => if 0 < v then v ^ (β-1) * Real.exp (-(σ*v)) else 0) :=
    Commons.Analysis.Perron.integrable_rpow_mul_exp_neg_ite β σ hβ hσ
  refine (hreal.ofReal).congr (Filter.Eventually.of_forall (fun v => ?_))
  change ↑(if 0 < v then v ^ (β-1) * Real.exp (-(σ*v)) else 0) = laplaceSource σ β v
  by_cases hv : 0 < v
  · rw [if_pos hv, laplaceSource, if_pos hv]
    have h1 : ↑(v ^ (β - 1)) = (v:ℂ) ^ ((β:ℂ) - 1) := by
      rw [Complex.ofReal_cpow hv.le (β-1), Complex.ofReal_sub, Complex.ofReal_one]
    have h2 : ↑(Real.exp (-(σ*v))) = Complex.exp (-(σ:ℂ)*(v:ℂ)) := by
      rw [Complex.ofReal_exp]; congr 1; push_cast; ring
    rw [Complex.ofReal_mul, h1, h2]
  · rw [if_neg hv, laplaceSource, if_neg hv]; simp

lemma fourier_laplaceSource (σ β : ℝ) (hσ : 0 < σ) (hβ : 0 < β) (w : ℝ) :
    𝓕 (laplaceSource σ β) w
      = Complex.Gamma (β:ℂ) * (((σ:ℂ) + (2*Real.pi:ℂ)*(w:ℂ)*Complex.I) ^ (-(β:ℂ))) := by
  set z : ℂ := (σ:ℂ) + (2*Real.pi:ℂ)*(w:ℂ)*Complex.I with hzdef
  have hzre : 0 < z.re := by
    have hzw : (2*Real.pi:ℂ)*(w:ℂ) = ((2*Real.pi*w:ℝ):ℂ) := by push_cast; ring
    rw [hzdef, hzw]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_one, mul_zero, sub_zero, add_zero]
    exact hσ
  have hβre : 0 < ((β:ℂ)).re := by simpa using hβ
  rw [Real.fourier_eq']
  have hpt : ∀ v : ℝ, Complex.exp (↑(-2*Real.pi*⟪v,w⟫)*Complex.I) • laplaceSource σ β v
      = (Ioi (0:ℝ)).indicator (fun v => (v:ℂ)^((β:ℂ)-1) * Complex.exp (-(z*(v:ℂ)))) v := by
    intro v
    rw [Real.inner_apply]
    by_cases hv : 0 < v
    · rw [laplaceSource, if_pos hv, Set.indicator_of_mem (mem_Ioi.mpr hv), smul_eq_mul]
      have hexp : Complex.exp (↑(-2*Real.pi*(v*w))*Complex.I) * Complex.exp (-(σ:ℂ)*(v:ℂ))
          = Complex.exp (-(z*(v:ℂ))) := by
        rw [← Complex.exp_add]
        congr 1
        rw [hzdef]; push_cast; ring
      rw [show Complex.exp (↑(-2*Real.pi*(v*w))*Complex.I) * ((v:ℂ)^((β:ℂ)-1) * Complex.exp (-(σ:ℂ)*(v:ℂ)))
            = (v:ℂ)^((β:ℂ)-1) * (Complex.exp (↑(-2*Real.pi*(v*w))*Complex.I) * Complex.exp (-(σ:ℂ)*(v:ℂ))) from by ring,
          hexp]
    · rw [laplaceSource, if_neg hv, Set.indicator_of_notMem (by simp only [mem_Ioi]; exact hv), smul_eq_mul, mul_zero]
  rw [show (∫ v : ℝ, Complex.exp (↑(-2 * Real.pi * ⟪v, w⟫) * Complex.I) • laplaceSource σ β v)
        = ∫ v : ℝ, (Ioi (0:ℝ)).indicator (fun v => (v:ℂ)^((β:ℂ)-1) * Complex.exp (-(z*(v:ℂ)))) v
      from integral_congr_ae (Filter.Eventually.of_forall hpt)]
  rw [integral_indicator measurableSet_Ioi]
  rw [Commons.Analysis.Complex.gamma_integral_cpow hβre hzre]

lemma integrable_cpow_vertical_kernel (σ β : ℝ) (hσ : 0 < σ) (hβ : 1 < β) :
    Integrable (fun w : ℝ => ((σ:ℂ) + (2*Real.pi:ℂ)*(w:ℂ)*Complex.I) ^ (-(β:ℂ))) := by
  set m : ℝ := min (σ^2) ((2*Real.pi)^2) with hm
  have hmpos : 0 < m := by rw [hm]; exact lt_min (by positivity) (by positivity)
  have hdom : Integrable (fun w : ℝ => m ^ (-β/2) * (1 + ‖w‖^2) ^ (-β/2)) := by
    have h := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (r := β) (by simpa using hβ)
    exact h.const_mul _
  have hcont : Continuous (fun w : ℝ => ((σ:ℂ) + (2*Real.pi:ℂ)*(w:ℂ)*Complex.I) ^ (-(β:ℂ))) := by
    rw [← continuousOn_univ]
    apply ContinuousOn.cpow_const
    · fun_prop
    · intro a _
      rw [Complex.slitPlane_eq_union]; left
      change 0 < ((σ:ℂ) + (2*Real.pi:ℂ)*(a:ℂ)*Complex.I).re
      rw [show (2*Real.pi:ℂ)*(a:ℂ) = ((2*Real.pi*a:ℝ):ℂ) from by push_cast; ring]
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_one, mul_zero, sub_zero, add_zero]
      exact hσ
  refine Integrable.mono' hdom hcont.aestronglyMeasurable ?_
  filter_upwards with w
  set base : ℂ := (σ:ℂ) + (2*Real.pi:ℂ)*(w:ℂ)*Complex.I with hbase
  have hnormSq : ‖base‖^2 = σ^2 + (2*Real.pi*w)^2 := by
    rw [hbase, Complex.sq_norm, Complex.normSq_apply]
    rw [show (2*Real.pi:ℂ)*(w:ℂ) = ((2*Real.pi*w:ℝ):ℂ) from by push_cast; ring]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one, mul_zero, sub_zero, add_zero]
    ring
  have hAle : m * (1 + ‖w‖^2) ≤ σ^2 + (2*Real.pi*w)^2 := by
    rw [Real.norm_eq_abs, sq_abs]
    have hm1 : m ≤ σ^2 := by rw [hm]; exact min_le_left _ _
    have hm2 : m ≤ (2*Real.pi)^2 := by rw [hm]; exact min_le_right _ _
    nlinarith [hm1, hm2, sq_nonneg w, sq_nonneg (2*Real.pi*w)]
  rw [show (-(β:ℂ)) = ((-β:ℝ):ℂ) from by push_cast; ring, Complex.norm_cpow_real]
  have hX : ‖base‖ ^ (-β) = (σ^2 + (2*Real.pi*w)^2) ^ (-β/2) := by
    have hstep : ‖base‖ ^ (-β) = (‖base‖^2) ^ (-β/2) := by
      rw [show (‖base‖^2) = ‖base‖^(2:ℝ) by exact (Real.rpow_natCast ‖base‖ 2).symm]
      rw [← Real.rpow_mul (norm_nonneg base)]
      congr 1; ring
    rw [hstep, hnormSq]
  rw [hX]
  calc (σ^2 + (2*Real.pi*w)^2) ^ (-β/2)
      ≤ (m * (1 + ‖w‖^2)) ^ (-β/2) :=
        Real.rpow_le_rpow_of_nonpos (mul_pos hmpos (by positivity)) hAle (by linarith)
    _ = m ^ (-β/2) * (1 + ‖w‖^2) ^ (-β/2) := by rw [Real.mul_rpow hmpos.le (by positivity)]

lemma integrable_fourier_laplaceSource (σ β : ℝ) (hσ : 0 < σ) (hβ : 1 < β) :
    Integrable (𝓕 (laplaceSource σ β)) := by
  have hF : 𝓕 (laplaceSource σ β) = fun w : ℝ => Complex.Gamma (β:ℂ) *
      (((σ:ℂ) + (2*Real.pi:ℂ)*(w:ℂ)*Complex.I) ^ (-(β:ℂ))) :=
    funext (fun w => fourier_laplaceSource σ β hσ (by linarith) w)
  rw [hF]
  exact (integrable_cpow_vertical_kernel σ β hσ hβ).const_mul _

lemma continuousAt_laplaceSource (σ β T : ℝ) (_hσ : 0 < σ) (hβ : 1 < β) (hT : 0 < T) :
    ContinuousAt (laplaceSource σ β) T := by
  have hfun : ContinuousAt (fun v : ℝ => (v:ℂ)^((β:ℂ)-1) * Complex.exp (-(σ:ℂ)*(v:ℂ))) T := by
    apply ContinuousAt.mul
    · exact (Complex.continuous_ofReal_cpow_const (y := (β:ℂ)-1) (by
        rw [Complex.sub_re, Complex.ofReal_re, Complex.one_re]; linarith)).continuousAt
    · fun_prop
  refine hfun.congr ?_
  filter_upwards [isOpen_Ioi.mem_nhds hT] with v hv
  rw [laplaceSource, if_pos (mem_Ioi.mp hv)]

theorem laplace_kernel_power_gt_one (σ T β : ℝ) (hσ : 0 < σ) (hT : 0 < T) (hβ : 1 < β) :
    (1 / (2 * Real.pi)) * ∫ τ : ℝ,
        Complex.exp (((σ : ℂ) + (τ : ℂ) * Complex.I) * (T : ℂ))
          * (((σ : ℂ) + (τ : ℂ) * Complex.I) ^ (-(β : ℂ)))
      = ((T ^ (β - 1) / Real.Gamma β : ℝ) : ℂ) := by
  have hβ0 : 0 < β := by linarith
  have hΓne : Complex.Gamma (β:ℂ) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simpa using hβ0)
  set J : ℂ := ∫ v : ℝ, Complex.exp (↑(2*Real.pi*(v*T))*Complex.I) *
        (((σ:ℂ) + (2*Real.pi:ℂ)*(v:ℂ)*Complex.I) ^ (-(β:ℂ))) with hJdef
  have hsrcT : laplaceSource σ β T = (↑(T^(β-1)) : ℂ) * (↑(Real.exp (-(σ*T))) : ℂ) := by
    rw [laplaceSource, if_pos hT]
    have h1 : (T:ℂ)^((β:ℂ)-1) = ↑(T^(β-1)) := by
      rw [show (β:ℂ)-1 = ↑(β-1) from by push_cast; ring]
      exact (Complex.ofReal_cpow hT.le (β-1)).symm
    have h2 : Complex.exp (-(σ:ℂ)*(T:ℂ)) = ↑(Real.exp (-(σ*T))) := by
      rw [show -(σ:ℂ)*(T:ℂ) = ↑(-(σ*T)) from by push_cast; ring, ← Complex.ofReal_exp]
    rw [h1, h2]
  have hsrc_eq : laplaceSource σ β T = Complex.Gamma (β:ℂ) * J := by
    have hinv := (integrable_laplaceSource σ β hσ hβ0).fourierInv_fourier_eq (integrable_fourier_laplaceSource σ β hσ hβ) (continuousAt_laplaceSource σ β T hσ hβ hT)
    rw [← hinv, Real.fourierInv_eq', hJdef]
    rw [show (∫ v : ℝ, Complex.exp (↑(2*Real.pi*⟪v,T⟫)*Complex.I) • 𝓕 (laplaceSource σ β) v)
          = Complex.Gamma (β:ℂ) * ∫ v : ℝ, Complex.exp (↑(2*Real.pi*(v*T))*Complex.I) *
              (((σ:ℂ) + (2*Real.pi:ℂ)*(v:ℂ)*Complex.I) ^ (-(β:ℂ))) from by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with v
        rw [Real.inner_apply, smul_eq_mul, fourier_laplaceSource σ β hσ hβ0 v]
        ring]
  have hFval : (∫ y : ℝ, Complex.exp (↑(y*T)*Complex.I) * (((σ:ℂ) + (y:ℂ)*Complex.I) ^ (-(β:ℂ))))
      = ((2*Real.pi : ℝ) : ℂ) * J := by
    have hcomp := Measure.integral_comp_mul_left
        (fun y : ℝ => Complex.exp (↑(y*T)*Complex.I) * (((σ:ℂ) + (y:ℂ)*Complex.I) ^ (-(β:ℂ)))) (2*Real.pi)
    rw [show |(2*Real.pi)⁻¹| = (2*Real.pi)⁻¹ from abs_of_pos (by positivity)] at hcomp
    rw [real_smul] at hcomp
    have hL : (∫ x : ℝ, (fun y : ℝ => Complex.exp (↑(y*T)*Complex.I) * (((σ:ℂ)+(y:ℂ)*Complex.I)^(-(β:ℂ)))) (2*Real.pi*x)) = J := by
      rw [hJdef]
      apply integral_congr_ae
      filter_upwards with x
      rw [show (2*Real.pi*x)*T = 2*Real.pi*(x*T) from by ring,
          show ((2*Real.pi*x:ℝ):ℂ) = (2*Real.pi:ℂ)*(x:ℂ) from by push_cast; ring]
    rw [hL] at hcomp
    have hmain : ((2*Real.pi : ℝ) : ℂ) * J
        = ∫ y : ℝ, Complex.exp (↑(y*T)*Complex.I) * (((σ:ℂ) + (y:ℂ)*Complex.I) ^ (-(β:ℂ))) := by
      rw [hcomp, ← mul_assoc, ← Complex.ofReal_mul,
        mul_inv_cancel₀ (by positivity : (2*Real.pi:ℝ) ≠ 0), Complex.ofReal_one, one_mul]
    exact hmain.symm
  have htarget : (∫ τ : ℝ, Complex.exp (((σ : ℂ) + (τ : ℂ) * Complex.I) * (T : ℂ))
          * (((σ : ℂ) + (τ : ℂ) * Complex.I) ^ (-(β : ℂ))))
      = Complex.exp ((σ:ℂ)*(T:ℂ)) * ((2*Real.pi : ℝ) : ℂ) * J := by
    have hpull : (∫ τ : ℝ, Complex.exp (((σ:ℂ)+(τ:ℂ)*Complex.I)*(T:ℂ)) * (((σ:ℂ)+(τ:ℂ)*Complex.I)^(-(β:ℂ))))
        = Complex.exp ((σ:ℂ)*(T:ℂ)) * ∫ τ : ℝ, Complex.exp (↑(τ*T)*Complex.I) * (((σ:ℂ)+(τ:ℂ)*Complex.I)^(-(β:ℂ))) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with τ
      rw [show ((σ:ℂ)+(τ:ℂ)*Complex.I)*(T:ℂ) = (σ:ℂ)*(T:ℂ) + (↑(τ*T))*Complex.I from by push_cast; ring,
          Complex.exp_add]
      ring
    rw [hpull, hFval]
    ring
  have hJeq : J = (↑(T^(β-1)) : ℂ) * (↑(Real.exp (-(σ*T))) : ℂ) / Complex.Gamma (β:ℂ) := by
    have h1 : J = laplaceSource σ β T / Complex.Gamma (β:ℂ) := by rw [hsrc_eq]; field_simp
    rw [h1, hsrcT]
  rw [htarget, hJeq]
  rw [show Complex.exp ((σ:ℂ) * (T:ℂ)) = (↑(Real.exp (σ*T)) : ℂ) from by
        rw [show ((σ:ℂ)*(T:ℂ)) = (↑(σ*T) : ℂ) from by push_cast; ring, ← Complex.ofReal_exp],
      Complex.Gamma_ofReal β]
  have hreal : (1/(2*Real.pi)) * (Real.exp (σ*T) * (2*Real.pi) * (T^(β-1) * Real.exp (-(σ*T)) / Real.Gamma β)) = T^(β-1)/Real.Gamma β := by
    have hΓneR : Real.Gamma β ≠ 0 := ne_of_gt (Real.Gamma_pos_of_pos hβ0)
    have hee' : Real.exp (σ*T) * Real.exp (-(σ*T)) = 1 := by
      rw [← Real.exp_add]; ring_nf; rw [Real.exp_zero]
    field_simp
    rw [hee']
  have hcomplex : (↑((1/(2*Real.pi)) * (Real.exp (σ*T) * (2*Real.pi) * (T^(β-1) * Real.exp (-(σ*T)) / Real.Gamma β))) : ℂ) = ↑(T^(β-1)/Real.Gamma β) := by
    rw [hreal]
  rw [← hcomplex]
  push_cast
  ring

end Commons.Analysis.Laplace

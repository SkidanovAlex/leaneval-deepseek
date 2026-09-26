import Mathlib
import Submission.Work.CKFinal.LineDecay.LamDefs

noncomputable section

namespace Work.CKFinal.LineDecay

open MeasureTheory Filter
open scoped Topology

/-- Integrability on `[1,∞)` of the majorant `t ↦ t (1+t)^M e^{-bt}` for `M ≥ 0`, `b > 0`. -/
private lemma integrableOn_laplace_majorant {M b : ℝ} (hM : 0 ≤ M) (hb : 0 < b) :
    IntegrableOn (fun t : ℝ => t * (1 + t) ^ M * Real.exp (-(b * t))) (Set.Ici 1) := by
  have hbase : IntegrableOn (fun t : ℝ => t ^ (M + 1) * Real.exp (-(b * t))) (Set.Ioi 0) := by
    simpa only [Real.rpow_one, neg_mul] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := M + 1) (b := b)
        (by linarith) one_pos hb)
  have hbase1 : IntegrableOn (fun t : ℝ => t ^ (M + 1) * Real.exp (-(b * t))) (Set.Ici 1) :=
    hbase.mono_set (fun t ht => Set.mem_Ioi.mpr (lt_of_lt_of_le zero_lt_one ht))
  have hdom : Integrable (fun t : ℝ => (2 : ℝ) ^ M * (t ^ (M + 1) * Real.exp (-(b * t))))
      (volume.restrict (Set.Ici 1)) := hbase1.const_mul _
  refine hdom.mono' ?_ ?_
  · measurability
  · filter_upwards [ae_restrict_mem measurableSet_Ici] with t htu
    have ht1 : (1 : ℝ) ≤ t := htu
    have ht0 : 0 < t := lt_of_lt_of_le one_pos ht1
    have h1t : 0 ≤ 1 + t := by linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hle : (1 + t) ^ M ≤ (2 * t) ^ M := Real.rpow_le_rpow h1t (by linarith) hM
    have h2M : (2 * t) ^ M = (2 : ℝ) ^ M * t ^ M := Real.mul_rpow (by norm_num) ht0.le
    rw [h2M] at hle
    have htM : t ^ (M + 1) = t ^ M * t := by rw [Real.rpow_add ht0, Real.rpow_one]
    have key : t * (1 + t) ^ M ≤ (2 : ℝ) ^ M * t ^ (M + 1) := by
      calc t * (1 + t) ^ M ≤ t * ((2 : ℝ) ^ M * t ^ M) := mul_le_mul_of_nonneg_left hle ht0.le
        _ = (2 : ℝ) ^ M * t ^ (M + 1) := by rw [htM]; ring
    calc t * (1 + t) ^ M * Real.exp (-(b * t))
        = (t * (1 + t) ^ M) * Real.exp (-(b * t)) := by ring
      _ ≤ ((2 : ℝ) ^ M * t ^ (M + 1)) * Real.exp (-(b * t)) :=
          mul_le_mul_of_nonneg_right key (Real.exp_nonneg _)
      _ = (2 : ℝ) ^ M * (t ^ (M + 1) * Real.exp (-(b * t))) := by ring

/-- Derivative of the Laplace kernel `z ↦ f₀ e^{-zt}`. -/
private lemma hasDerivAt_laplaceKernel (f₀ : ℂ) (t : ℝ) (z : ℂ) :
    HasDerivAt (fun w : ℂ => f₀ * Complex.exp (-(w * (t : ℂ))))
      (f₀ * (-(t : ℂ) * Complex.exp (-(z * (t : ℂ))))) z := by
  have h1 : HasDerivAt (fun w : ℂ => w * (t : ℂ)) ((t : ℂ)) z := by
    simpa using (hasDerivAt_id z).mul_const (t : ℂ)
  have h2 : HasDerivAt (fun w : ℂ => -(w * (t : ℂ))) (-(t : ℂ)) z := h1.neg
  have h3 : HasDerivAt Complex.exp (Complex.exp (-(z * (t : ℂ)))) (-(z * (t : ℂ))) :=
    Complex.hasDerivAt_exp _
  have h4 : HasDerivAt (fun w : ℂ => Complex.exp (-(w * (t : ℂ))))
      (Complex.exp (-(z * (t : ℂ))) * (-(t : ℂ))) z := h3.comp z h2
  have h5 : HasDerivAt (fun w : ℂ => f₀ * Complex.exp (-(w * (t : ℂ))))
      (0 * Complex.exp (-(z * (t : ℂ)))
        + f₀ * (Complex.exp (-(z * (t : ℂ))) * (-(t : ℂ)))) z :=
    (hasDerivAt_const (x := z) f₀).mul h4
  convert h5 using 1
  ring

/-- Norm of the Laplace kernel. -/
private lemma norm_laplaceKernel (f₀ : ℂ) (t : ℝ) (z : ℂ) :
    ‖f₀ * Complex.exp (-(z * (t : ℂ)))‖ = ‖f₀‖ * Real.exp (-(z.re * t)) := by
  rw [norm_mul, Complex.norm_exp, Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]

/-- Norm of the derivative of the Laplace kernel. -/
private lemma norm_laplaceKernel_deriv (f₀ : ℂ) (t : ℝ) (z : ℂ) (ht : 0 ≤ t) :
    ‖f₀ * (-(t : ℂ) * Complex.exp (-(z * (t : ℂ))))‖ = ‖f₀‖ * t * Real.exp (-(z.re * t)) := by
  have hnormt : ‖(t : ℂ)‖ = t := by
    rw [show ‖(t : ℂ)‖ = |t| from RCLike.norm_ofReal t, abs_of_nonneg ht]
  rw [norm_mul, norm_mul, Complex.norm_exp, norm_neg, hnormt,
      Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  ring

/-- The Laplace transform `z ↦ ∫_1^∞ f t e^{-zt} dt` of a function decaying like `(1+t)^M e^{-π(t-T)}` is analytic on the half-plane `Re z > -π`.  Proof by dominated convergence: at `z₀` with `z₀.re > -π` pick `c` with `-π < c < z₀.re` and the ball `s = ball z₀ (z₀.re - c)`; for `z ∈ s` one has `|e^{-zt}| ≤ e^{-c t}`, so the derivand is dominated by `C e^{πT} t (1+t)^M e^{-(π+c)t} ∈ L¹(1,∞)`. -/
theorem laplace_analytic_Ici {f : ℝ → ℂ} {C M T : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M) (hT : 0 ≤ T)
    (hf : MeasureTheory.AEStronglyMeasurable f (MeasureTheory.volume.restrict (Set.Ici 1)))
    (hbound : ∀ t ∈ Set.Ici (1 : ℝ), ‖f t‖ ≤ C * (1 + t) ^ M * Real.exp (-(Real.pi * (t - T)))) :
    AnalyticOnNhd ℂ (fun z : ℂ => ∫ t in Set.Ici (1 : ℝ), f t * Complex.exp (-(z * t)))
      {z : ℂ | -(Real.pi) < z.re} := by
  have key : ∀ z₀ : ℂ, -(Real.pi) < z₀.re →
      DifferentiableAt ℂ (fun z : ℂ => ∫ t in Set.Ici (1 : ℝ), f t * Complex.exp (-(z * t))) z₀ := by
    intro z₀ hz₀
    obtain ⟨c, hc1, hc2⟩ := exists_between hz₀
    set r : ℝ := z₀.re - c with hr
    have hrpos : 0 < r := by rw [hr]; linarith
    set A : ℝ := C * Real.exp (Real.pi * T) with hA
    set b : ℝ := Real.pi + c with hb
    have hbpos : 0 < b := by rw [hb]; linarith [Real.pi_pos]
    have hA0 : 0 ≤ A := by rw [hA]; positivity
    have hbound_int : Integrable (fun t : ℝ => A * (t * (1 + t) ^ M * Real.exp (-(b * t))))
        (volume.restrict (Set.Ici (1 : ℝ))) := by
      have h := integrableOn_laplace_majorant (M := M) (b := b) hM hbpos
      exact h.const_mul A
    have hsre : ∀ z ∈ Metric.ball z₀ r, c < z.re := by
      intro z hz
      have hzd : dist z z₀ < r := Metric.mem_ball.mp hz
      rw [dist_eq_norm] at hzd
      have h2 : (z₀ - z).re ≤ ‖z₀ - z‖ := Complex.re_le_norm _
      rw [norm_sub_rev] at h2
      rw [Complex.sub_re] at h2
      rw [hr] at hzd
      linarith
    have hF_meas : ∀ᶠ z in 𝓝 z₀,
        AEStronglyMeasurable (fun t : ℝ => f t * Complex.exp (-(z * (t : ℂ))))
          (volume.restrict (Set.Ici (1 : ℝ))) :=
      Filter.Eventually.of_forall (fun z => hf.mul (by measurability))
    have hF_int : Integrable (fun t : ℝ => f t * Complex.exp (-(z₀ * (t : ℂ))))
        (volume.restrict (Set.Ici (1 : ℝ))) := by
      refine hbound_int.mono' (by measurability) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
      have ht1 : (1 : ℝ) ≤ t := ht
      have ht0 : 0 ≤ t := le_trans zero_le_one ht1
      rw [norm_laplaceKernel (f t) t z₀]
      have hexp := hbound t ht
      have hbz : Real.exp (-(z₀.re * t)) ≤ Real.exp (-(c * t)) :=
        Real.exp_le_exp.mpr (by nlinarith [hc2, ht0])
      have hCnn : 0 ≤ C * (1 + t) ^ M * Real.exp (-(Real.pi * (t - T))) :=
        mul_nonneg (mul_nonneg hC (Real.rpow_nonneg (by linarith) M)) (Real.exp_nonneg _)
      have hexpeq : Real.exp (-(Real.pi * (t - T))) * Real.exp (-(c * t))
          = Real.exp (Real.pi * T) * Real.exp (-(b * t)) := by
        have h1 : -(Real.pi * (t - T)) + -(c * t) = Real.pi * T + -(b * t) := by
          rw [hb]; ring
        rw [← Real.exp_add, h1, Real.exp_add]
      calc ‖f t‖ * Real.exp (-(z₀.re * t))
          ≤ (C * (1 + t) ^ M * Real.exp (-(Real.pi * (t - T)))) * Real.exp (-(c * t)) :=
            mul_le_mul hexp hbz (Real.exp_nonneg _) hCnn
        _ = C * (1 + t) ^ M * (Real.exp (-(Real.pi * (t - T))) * Real.exp (-(c * t))) := by
            ring
        _ = C * (1 + t) ^ M * (Real.exp (Real.pi * T) * Real.exp (-(b * t))) := by rw [hexpeq]
        _ = A * ((1 + t) ^ M * Real.exp (-(b * t))) := by rw [hA]; ring
        _ ≤ A * (t * (1 + t) ^ M * Real.exp (-(b * t))) := by
            refine mul_le_mul_of_nonneg_left ?_ hA0
            have hnn : 0 ≤ (1 + t) ^ M * Real.exp (-(b * t)) :=
              mul_nonneg (Real.rpow_nonneg (by linarith) M) (Real.exp_nonneg _)
            calc (1 + t) ^ M * Real.exp (-(b * t))
                = 1 * ((1 + t) ^ M * Real.exp (-(b * t))) := by ring
              _ ≤ t * ((1 + t) ^ M * Real.exp (-(b * t))) :=
                  mul_le_mul_of_nonneg_right ht1 hnn
              _ = t * (1 + t) ^ M * Real.exp (-(b * t)) := by ring
    have hF'_meas : AEStronglyMeasurable
        (fun t : ℝ => f t * (-(t : ℂ) * Complex.exp (-(z₀ * (t : ℂ)))))
        (volume.restrict (Set.Ici (1 : ℝ))) := by
      exact hf.mul (by measurability)
    have h_bnd_deriv : ∀ᵐ a ∂(volume.restrict (Set.Ici (1 : ℝ))),
        ∀ z ∈ Metric.ball z₀ r, ‖f a * (-(a : ℂ) * Complex.exp (-(z * (a : ℂ))))‖
          ≤ A * (a * (1 + a) ^ M * Real.exp (-(b * a))) := by
      filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht z hz
      have ht1 : (1 : ℝ) ≤ t := ht
      have ht0 : 0 ≤ t := le_trans zero_le_one ht1
      have hcz : c ≤ z.re := le_of_lt (hsre z hz)
      rw [norm_laplaceKernel_deriv (f t) t z ht0]
      have hexp := hbound t ht
      have hbz : Real.exp (-(z.re * t)) ≤ Real.exp (-(c * t)) :=
        Real.exp_le_exp.mpr (by nlinarith [hcz, ht0])
      have hCnn : 0 ≤ C * (1 + t) ^ M * Real.exp (-(Real.pi * (t - T))) :=
        mul_nonneg (mul_nonneg hC (Real.rpow_nonneg (by linarith) M)) (Real.exp_nonneg _)
      have hexpeq : Real.exp (-(Real.pi * (t - T))) * Real.exp (-(c * t))
          = Real.exp (Real.pi * T) * Real.exp (-(b * t)) := by
        have h1 : -(Real.pi * (t - T)) + -(c * t) = Real.pi * T + -(b * t) := by
          rw [hb]; ring
        rw [← Real.exp_add, h1, Real.exp_add]
      have hstep : ‖f t‖ * t * Real.exp (-(z.re * t))
          ≤ (C * (1 + t) ^ M * Real.exp (-(Real.pi * (t - T)))) * t * Real.exp (-(c * t)) := by
        have h2 : ‖f t‖ * t ≤ (C * (1 + t) ^ M * Real.exp (-(Real.pi * (t - T)))) * t :=
          mul_le_mul_of_nonneg_right hexp ht0
        calc ‖f t‖ * t * Real.exp (-(z.re * t))
            = (‖f t‖ * t) * Real.exp (-(z.re * t)) := by ring
          _ ≤ ((C * (1 + t) ^ M * Real.exp (-(Real.pi * (t - T)))) * t)
                * Real.exp (-(c * t)) :=
              mul_le_mul h2 hbz (Real.exp_nonneg _) (mul_nonneg hCnn ht0)
          _ = (C * (1 + t) ^ M * Real.exp (-(Real.pi * (t - T)))) * t
                * Real.exp (-(c * t)) := by ring
      calc ‖f t‖ * t * Real.exp (-(z.re * t))
          ≤ (C * (1 + t) ^ M * Real.exp (-(Real.pi * (t - T)))) * t * Real.exp (-(c * t)) := hstep
        _ = C * (1 + t) ^ M * t * (Real.exp (-(Real.pi * (t - T))) * Real.exp (-(c * t))) := by
            ring
        _ = C * (1 + t) ^ M * t * (Real.exp (Real.pi * T) * Real.exp (-(b * t))) := by
            rw [hexpeq]
        _ = A * (t * (1 + t) ^ M * Real.exp (-(b * t))) := by rw [hA]; ring
    have h_diff : ∀ᵐ a ∂(volume.restrict (Set.Ici (1 : ℝ))),
        ∀ z ∈ Metric.ball z₀ r, HasDerivAt (fun w : ℂ => f a * Complex.exp (-(w * (a : ℂ))))
          (f a * (-(a : ℂ) * Complex.exp (-(z * (a : ℂ))))) z :=
      Filter.Eventually.of_forall (fun a z _ => hasDerivAt_laplaceKernel (f a) a z)
    have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
        (𝕜 := ℂ) (E := ℂ) (α := ℝ) (μ := volume.restrict (Set.Ici (1 : ℝ)))
        (F := fun z t => f t * Complex.exp (-(z * (t : ℂ))))
        (F' := fun z t => f t * (-(t : ℂ) * Complex.exp (-(z * (t : ℂ)))))
        (x₀ := z₀) (s := Metric.ball z₀ r)
        (bound := fun t : ℝ => A * (t * (1 + t) ^ M * Real.exp (-(b * t))))
        (Metric.ball_mem_nhds z₀ hrpos) hF_meas hF_int hF'_meas h_bnd_deriv hbound_int h_diff
    exact hmain.2.differentiableAt
  refine DifferentiableOn.analyticOnNhd (fun z₀ hz₀ => (key z₀ hz₀).differentiableWithinAt) ?_
  exact isOpen_lt continuous_const Complex.continuous_re

end Work.CKFinal.LineDecay

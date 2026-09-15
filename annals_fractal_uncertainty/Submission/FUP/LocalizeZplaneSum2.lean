import Submission.FUP.LocalizeZplaneSum
import Submission.Commons.Analysis.Measure.finset_ball_lintegral_strip_le

open MeasureTheory Metric Set Complex Filter
open scoped ENNReal BigOperators Topology

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# The sum over the cells: `Σ_n S_n² ≤ C ∫_strip ‖F‖²`
-/

namespace Submission.FUP

variable {d : ℕ}

lemma continuousOn_PsiC {q ε η : ℝ} (hq : 0 < q) (hε0 : 0 < ε) (hε1 : ε < 1)
    (c : Fin d → ℝ) :
    ContinuousOn (fun z : Fin d → ℂ => PsiCLens q ε η c z) (Metric.closedBall 0 1) := by
  rw [continuousOn_pi]
  intro j
  have hmem : ∀ z ∈ Metric.closedBall (0 : Fin d → ℂ) 1,
      ((1 - ε : ℝ) : ℂ) * z j ∈ ball (0 : ℂ) 1 := by
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (by norm_num)] at hz
    rw [mem_ball, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - ε)]
    nlinarith [hz j, norm_nonneg (z j), hε0, hε1]
  have h1 : ContinuousOn (fun z : Fin d → ℂ => lensMap q ε (z j)) (Metric.closedBall 0 1) :=
    ContinuousOn.comp (g := lensMap q ε) (t := {w : ℂ | ‖((1 - ε : ℝ) : ℂ) * w‖ < 1})
      ((differentiableOn_lensMap (le_of_lt hε0) hε1).continuousOn)
      ((continuous_apply j : Continuous (fun z : Fin d → ℂ => z j)).continuousOn) ?_
  · have h2 : ContinuousOn (fun z : Fin d → ℂ =>
        ((c j : ℂ) + (η : ℂ) * lensMap q ε (z j))) (Metric.closedBall 0 1) :=
      (h1.const_mul ((η : ℝ) : ℂ)).const_add ((c j : ℝ) : ℂ)
    simpa only [PsiCLens] using h2
  · intro z hz
    simpa only [Set.mem_ofPred_eq, mem_ball, dist_zero_right] using hmem z hz

/-- **The sum over the cells.**  The sup norms of the per-cell functions are controlled by the
strip `lintegral` of the entire extension `F`. -/
theorem sup_sum_le {q ε η r : ℝ} {γ : Fin d → ℝ} (hq : 0 < q) (hε0 : 0 < ε)
    (hε1 : ε ≤ 1/2) (hη0 : 0 < η) (hr0 : 0 < r) {F : (Fin d → ℂ) → ℂ}
    (hF : Differentiable ℂ F) (s : Finset (Fin d → ℤ)) :
    ∑ n ∈ s, ENNReal.ofReal ((sSup ((fun z : Fin d → ℂ =>
        ‖F (PsiCLens q ε η (cellCentre γ n) z)‖) '' Metric.closedBall 0 1))^2)
      ≤ ENNReal.ofReal (((Real.pi * r^2)^d)⁻¹)
          * ENNReal.ofReal ((η * phiLens q ε 1 + r + 1)^d)
          * ∫⁻ z in {z : Fin d → ℂ | ∀ i, |(z i).im| ≤ η*q + r},
              ENNReal.ofReal (‖F z‖^2) := by
  classical
  have hε1' : ε < 1 := by linarith
  have hmax : ∀ n : Fin d → ℤ, ∃ w ∈ Metric.closedBall (0 : Fin d → ℂ) 1,
      sSup ((fun z : Fin d → ℂ => ‖F (PsiCLens q ε η (cellCentre γ n) z)‖)
          '' Metric.closedBall 0 1)
        = ‖F (PsiCLens q ε η (cellCentre γ n) w)‖ := by
    intro n
    have hcont : ContinuousOn (fun z : Fin d → ℂ =>
        ‖F (PsiCLens q ε η (cellCentre γ n) z)‖) (Metric.closedBall 0 1) :=
      (hF.continuous.comp_continuousOn
        (continuousOn_PsiC (d := d) hq hε0 hε1' (cellCentre γ n))).norm
    obtain ⟨w, hw, hwmax⟩ := (isCompact_closedBall (0 : Fin d → ℂ) 1).exists_isMaxOn
      ⟨0, Metric.mem_closedBall_self (by norm_num : (0:ℝ) ≤ 1)⟩ hcont
    exact ⟨w, hw, csSup_image_eq_of_isMaxOn hw (fun x hx => hwmax hx)⟩
  choose p hp using hmax
  set zz : (Fin d → ℤ) → Fin d → ℂ := fun n => PsiCLens q ε η (cellCentre γ n) (p n) with hzz
  have hple : ∀ n, ∀ i, ‖p n i‖ ≤ 1 := by
    intro n i
    have h2 := (hp n).1
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (by norm_num)] at h2
    exact h2 i
  have hzr : ∀ n, ∀ i, |(zz n i).re - (2 * (n i : ℝ) + γ i + 1)| ≤ η * phiLens q ε 1 := by
    intro n i
    have h3 := abs_re_lensMap_le hq hε0 hε1' (w := p n i) (hple n i)
    have hre : (zz n i).re = (2 * (n i : ℝ) + γ i + 1) + η * (lensMap q ε (p n i)).re := by
      simp only [hzz, PsiCLens, cellCentre, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, mul_zero, zero_add, add_zero, sub_zero]
    rw [hre]
    rw [show (2 * (n i : ℝ) + γ i + 1) + η * (lensMap q ε (p n i)).re
          - (2 * (n i : ℝ) + γ i + 1) = η * (lensMap q ε (p n i)).re from by ring,
      abs_mul, abs_of_pos hη0]
    exact mul_le_mul_of_nonneg_left h3 (le_of_lt hη0)
  have hzi : ∀ n, ∀ i, |(zz n i).im| ≤ (η*q + r) - r := by
    intro n i
    have h3 := im_lensMap_le hq hε0 hε1' (w := p n i) (hple n i)
    have him : (zz n i).im = η * (lensMap q ε (p n i)).im := by
      simp only [hzz, PsiCLens, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, mul_zero, zero_add, add_zero]
    rw [him, abs_mul, abs_of_pos hη0, show η*q + r - r = η*q from by ring]
    exact mul_le_mul_of_nonneg_left h3 (le_of_lt hη0)
  have hSle : ∀ n ∈ s, ENNReal.ofReal ((sSup ((fun z : Fin d → ℂ =>
      ‖F (PsiCLens q ε η (cellCentre γ n) z)‖) '' Metric.closedBall 0 1))^2)
      ≤ ENNReal.ofReal (((Real.pi * r^2)^d)⁻¹)
          * ∫⁻ z in Metric.closedBall (zz n) r, ENNReal.ofReal (‖F z‖^2) := by
    intro n _
    have h1 : (sSup ((fun z : Fin d → ℂ => ‖F (PsiCLens q ε η (cellCentre γ n) z)‖)
        '' Metric.closedBall 0 1))^2 = ‖F (zz n)‖^2 := by
      rw [(hp n).2]
    rw [h1]
    have h2 := Commons.Analysis.Complex.norm_sq_le_inv_polydisc_mul_integral (d := d) hF
      (z := zz n) hr0
    have hint : IntegrableOn (fun z : Fin d → ℂ => ‖F z‖^2)
        (Metric.closedBall (zz n) r) volume :=
      ContinuousOn.integrableOn_compact (isCompact_closedBall (zz n) r)
        ((hF.continuous.norm.pow 2).continuousOn)
    calc ENNReal.ofReal (‖F (zz n)‖^2)
        ≤ ENNReal.ofReal (((Real.pi * r^2)^d)⁻¹
            * ∫ z in Metric.closedBall (zz n) r, ‖F z‖^2) := ENNReal.ofReal_le_ofReal h2
      _ = ENNReal.ofReal (((Real.pi * r^2)^d)⁻¹)
            * ∫⁻ z in Metric.closedBall (zz n) r, ENNReal.ofReal (‖F z‖^2) := by
          rw [ENNReal.ofReal_mul (by positivity),
            ofReal_integral_eq_lintegral_ofReal hint
              (Filter.Eventually.of_forall (fun z => by positivity))]
  calc ∑ n ∈ s, ENNReal.ofReal ((sSup ((fun z : Fin d → ℂ =>
        ‖F (PsiCLens q ε η (cellCentre γ n) z)‖) '' Metric.closedBall 0 1))^2)
      ≤ ∑ n ∈ s, ENNReal.ofReal (((Real.pi * r^2)^d)⁻¹)
          * ∫⁻ z in Metric.closedBall (zz n) r, ENNReal.ofReal (‖F z‖^2) :=
        Finset.sum_le_sum hSle
    _ = ENNReal.ofReal (((Real.pi * r^2)^d)⁻¹)
          * ∑ n ∈ s, ∫⁻ z in Metric.closedBall (zz n) r, ENNReal.ofReal (‖F z‖^2) := by
        rw [← Finset.mul_sum]
    _ ≤ ENNReal.ofReal (((Real.pi * r^2)^d)⁻¹)
          * (ENNReal.ofReal ((η * phiLens q ε 1 + r + 1)^d)
              * ∫⁻ z in {z : Fin d → ℂ | ∀ i, |(z i).im| ≤ η*q + r},
                  ENNReal.ofReal (‖F z‖^2)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have hθ : (0:ℝ) ≤ η * phiLens q ε 1 := by
          have h := phiLens_one_pos hq hε0 hε1'
          positivity
        exact Commons.Analysis.Measure.finset_ball_lintegral_strip_le
          (fun z : Fin d → ℂ => ENNReal.ofReal (‖F z‖^2)) (le_of_lt hr0)
          hθ γ s zz (fun n _ i => hzr n i) (fun n _ i => hzi n i)
    _ = ENNReal.ofReal (((Real.pi * r^2)^d)⁻¹)
          * ENNReal.ofReal ((η * phiLens q ε 1 + r + 1)^d)
          * ∫⁻ z in {z : Fin d → ℂ | ∀ i, |(z i).im| ≤ η*q + r},
              ENNReal.ofReal (‖F z‖^2) := by
        rw [mul_assoc]

end Submission.FUP

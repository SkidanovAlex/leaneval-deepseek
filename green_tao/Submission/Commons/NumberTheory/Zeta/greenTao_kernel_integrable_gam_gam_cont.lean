import Mathlib
import Submission.Commons.NumberTheory.Zeta.zeta_region_inv_analytic_bound_ne
import Submission.Commons.NumberTheory.Zeta.gam0_Rz_div_sq_integral_le
import Submission.Commons.Analysis.Complex.curve_inv_sq_integrable
import Submission.Commons.Analysis.Integral.uScaleHalf_integrable
import Submission.Commons.NumberTheory.Zeta.zeta_one_add_add_bound_curve_sqrt_curve

namespace Commons.NumberTheory.Zeta

open MeasureTheory
open scoped Topology

noncomputable section

/-! ## Helper definitions for the `Γ₀ × Γ₀` Green–Tao kernel

This is the two-curve analogue of `greenTao_kernel_integrable_gam_sigma_cont`: both variables
range over the boundary curve `gam β`. -/

/-- The Green–Tao weight `(|t|+3)^{1/2} (log(|t|+2)+1)/(1+t²)`, dominating one of the two
`Γ₀`-factors of the `Γ₀ × Γ₀` kernel. -/
private def uScaleHalfPt (t : ℝ) : ℝ :=
  (|t| + 3) ^ ((1:ℝ)/2) * (Real.log (|t| + 2) + 1) / (1 + t ^ 2)

/-- `(|t|+|t'|+3)^{1/2} ≤ (|t|+3)^{1/2} (|t'|+3)^{1/2}`. -/
private lemma sqrt_base_le (t t' : ℝ) :
    (|t| + |t'| + 3) ^ ((1:ℝ)/2)
      ≤ (|t| + 3) ^ ((1:ℝ)/2) * (|t'| + 3) ^ ((1:ℝ)/2) := by
  have h1 : 0 ≤ |t| + 3 := by linarith [abs_nonneg t]
  have h2 : 0 ≤ |t'| + 3 := by linarith [abs_nonneg t']
  have hle : |t| + |t'| + 3 ≤ (|t| + 3) * (|t'| + 3) := by
    nlinarith [abs_nonneg t, abs_nonneg t']
  calc (|t| + |t'| + 3) ^ ((1:ℝ)/2)
      ≤ ((|t| + 3) * (|t'| + 3)) ^ ((1:ℝ)/2) :=
        Real.rpow_le_rpow (by positivity) hle (by norm_num)
    _ = (|t| + 3) ^ ((1:ℝ)/2) * (|t'| + 3) ^ ((1:ℝ)/2) := Real.mul_rpow h1 h2

/-- The `Γ₀ × Γ₀` kernel integrand, as a function on `ℝ × ℝ`. -/
private def ggIntegrand (β R : ℝ) (f : ℂ → ℂ → ℂ) : ℝ × ℝ → ℂ := fun p =>
  f (Commons.Analysis.Complex.gam β p.1) (Commons.Analysis.Complex.gam β p.2)
    * (riemannZeta (1 + Commons.Analysis.Complex.gam β p.1
          + Commons.Analysis.Complex.gam β p.2)
        / (riemannZeta (1 + Commons.Analysis.Complex.gam β p.1)
            * riemannZeta (1 + Commons.Analysis.Complex.gam β p.2)))
    * (R : ℂ) ^ (Commons.Analysis.Complex.gam β p.1 + Commons.Analysis.Complex.gam β p.2)
    / ((Commons.Analysis.Complex.gam β p.1) ^ 2 * (Commons.Analysis.Complex.gam β p.2) ^ 2)
    * Commons.Analysis.Complex.gamDot β p.1 * Commons.Analysis.Complex.gamDot β p.2

/-! ## Measurability -/

private lemma measurable_riemannZeta : Measurable riemannZeta := by
  refine measurable_of_continuousOn_compl_singleton 1 ?_
  intro z hz
  exact ((differentiableAt_riemannZeta hz).continuousAt).continuousWithinAt

private lemma measurable_gamDot (β : ℝ) : Measurable (Commons.Analysis.Complex.gamDot β) := by
  have hlog : Measurable (fun y : ℝ => Real.log (y + 2)) :=
    Real.measurable_log.comp (measurable_id.add_const 2)
  have hlog' : Measurable (fun y : ℝ => Real.log (-y + 2)) :=
    Real.measurable_log.comp ((measurable_id.neg).add_const 2)
  have hPhiPos : Measurable (Commons.Analysis.Complex.PhiPos β) := by
    unfold Commons.Analysis.Complex.PhiPos
    exact measurable_const.div ((measurable_id.add_const 2).mul (hlog.pow_const 2))
  have hPhiNeg : Measurable (Commons.Analysis.Complex.PhiNeg β) := by
    unfold Commons.Analysis.Complex.PhiNeg
    exact (measurable_const.div (((measurable_id.neg).add_const 2).mul (hlog'.pow_const 2))).neg
  have hPhi' : Measurable (Commons.Analysis.Complex.Phi' β) := by
    unfold Commons.Analysis.Complex.Phi'
    exact Measurable.ite measurableSet_Ici hPhiPos hPhiNeg
  unfold Commons.Analysis.Complex.gamDot
  exact (Complex.measurable_ofReal.comp hPhi').add measurable_const

private lemma aesm_ggIntegrand {β R : ℝ} (hRpos : 0 < R) (f : ℂ → ℂ → ℂ)
    (hcont : Continuous (Function.uncurry f)) :
    AEStronglyMeasurable (ggIntegrand β R f) (volume.prod volume) := by
  have hRne : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hRpos)
  have hgam : Continuous (fun p : ℝ × ℝ => Commons.Analysis.Complex.gam β p.1) :=
    (Commons.Analysis.Complex.gam_continuous β).comp continuous_fst
  have hgam2 : Continuous (fun p : ℝ × ℝ => Commons.Analysis.Complex.gam β p.2) :=
    (Commons.Analysis.Complex.gam_continuous β).comp continuous_snd
  have hE1 : Measurable (fun p : ℝ × ℝ =>
      f (Commons.Analysis.Complex.gam β p.1) (Commons.Analysis.Complex.gam β p.2)) :=
    (hcont.comp (hgam.prodMk hgam2)).measurable
  have hE2 : Measurable (fun p : ℝ × ℝ =>
      riemannZeta (1 + Commons.Analysis.Complex.gam β p.1
        + Commons.Analysis.Complex.gam β p.2)) :=
    measurable_riemannZeta.comp ((continuous_const.add hgam).add hgam2).measurable
  have hE3 : Measurable (fun p : ℝ × ℝ =>
      riemannZeta (1 + Commons.Analysis.Complex.gam β p.1)) :=
    measurable_riemannZeta.comp (continuous_const.add hgam).measurable
  have hE4 : Measurable (fun p : ℝ × ℝ =>
      riemannZeta (1 + Commons.Analysis.Complex.gam β p.2)) :=
    measurable_riemannZeta.comp (continuous_const.add hgam2).measurable
  have hE5 : Measurable (fun p : ℝ × ℝ =>
      (R : ℂ) ^ (Commons.Analysis.Complex.gam β p.1 + Commons.Analysis.Complex.gam β p.2)) :=
    ((hgam.add hgam2).const_cpow (b := (R : ℂ)) (Or.inl hRne)).measurable
  have hE6 : Measurable (fun p : ℝ × ℝ =>
      (Commons.Analysis.Complex.gam β p.1) ^ 2 * (Commons.Analysis.Complex.gam β p.2) ^ 2) :=
    (hgam.measurable.pow_const 2).mul (hgam2.measurable.pow_const 2)
  have hPhi : Measurable (fun p : ℝ × ℝ =>
      f (Commons.Analysis.Complex.gam β p.1) (Commons.Analysis.Complex.gam β p.2)
        * (riemannZeta (1 + Commons.Analysis.Complex.gam β p.1
            + Commons.Analysis.Complex.gam β p.2)
            / (riemannZeta (1 + Commons.Analysis.Complex.gam β p.1)
              * riemannZeta (1 + Commons.Analysis.Complex.gam β p.2)))
        * (R : ℂ) ^ (Commons.Analysis.Complex.gam β p.1 + Commons.Analysis.Complex.gam β p.2)
        / ((Commons.Analysis.Complex.gam β p.1) ^ 2 * (Commons.Analysis.Complex.gam β p.2) ^ 2)) :=
    ((hE1.mul (hE2.div (hE3.mul hE4))).mul hE5).div hE6
  have hgd1 : AEStronglyMeasurable (fun p : ℝ × ℝ => Commons.Analysis.Complex.gamDot β p.1)
      (volume.prod volume) :=
    ((measurable_gamDot β).comp measurable_fst).aestronglyMeasurable
  have hgd2 : AEStronglyMeasurable (fun p : ℝ × ℝ => Commons.Analysis.Complex.gamDot β p.2)
      (volume.prod volume) :=
    ((measurable_gamDot β).comp measurable_snd).aestronglyMeasurable
  exact ((hPhi.aestronglyMeasurable.mul hgd1).mul hgd2)

/-! ## Pointwise domination -/

private lemma norm_ggIntegrand_le {β R : ℝ} (hβ : 0 < β) (hR : 3 ≤ R)
    (f : ℂ → ℂ → ℂ) (B C₁ Cn : ℝ) (hC1 : 0 < C₁) (hCn : 0 < Cn)
    (hinvb : ∀ z : ℂ, z ≠ 0 → -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 →
        ‖(riemannZeta (1 + z))⁻¹‖ ≤ C₁ * (Real.log (|z.im| + 2) + 1))
    (hbound : ∀ z z' : ℂ, -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 →
        -(β / Real.log (|z'.im| + 2)) ≤ z'.re → z'.re ≤ 1 → ‖f z z'‖ ≤ B)
    (hnum : ∀ t t' : ℝ, ‖riemannZeta (1 + Commons.Analysis.Complex.gam β t
        + Commons.Analysis.Complex.gam β t')‖ ≤ Cn * (|t| + |t'| + 3) ^ ((1:ℝ)/2)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ p : ℝ × ℝ,
      ‖ggIntegrand β R f p‖ ≤ K * uScaleHalfPt p.1 * uScaleHalfPt p.2 := by
  have hRpos : 0 < R := by linarith
  have hB : 0 ≤ B := by
    have h := hbound (Commons.Analysis.Complex.gam β 0) (Commons.Analysis.Complex.gam β 0)
      (gam_mem_region hβ 0).1 (gam_mem_region hβ 0).2
      (gam_mem_region hβ 0).1 (gam_mem_region hβ 0).2
    exact le_trans (norm_nonneg _) h
  have hcc : 0 ≤ Commons.Analysis.Complex.curveConst β :=
    (Commons.Analysis.Complex.curveConst_pos hβ).le
  refine ⟨B * Cn * C₁ ^ 2 * Commons.Analysis.Complex.curveConst β ^ 2,
    mul_nonneg (mul_nonneg (mul_nonneg hB hCn.le) (sq_nonneg C₁)) (sq_nonneg _), ?_⟩
  intro p
  set z : ℂ := Commons.Analysis.Complex.gam β p.1 with hz
  set w : ℂ := Commons.Analysis.Complex.gam β p.2 with hw
  set Z : ℂ := riemannZeta (1 + z + w) with hZ
  set c : ℂ := riemannZeta (1 + z) with hc
  set W : ℂ := riemannZeta (1 + w) with hW
  set Rc : ℂ := (R : ℂ) ^ (z + w) with hRc
  have hzreg : -(β / Real.log (|z.im| + 2)) ≤ z.re ∧ z.re ≤ 1 := by
    rw [hz]; exact gam_mem_region hβ p.1
  have hwreg : -(β / Real.log (|w.im| + 2)) ≤ w.re ∧ w.re ≤ 1 := by
    rw [hw]; exact gam_mem_region hβ p.2
  have hz0 : z ≠ 0 := by rw [hz]; exact Commons.Analysis.Complex.gam_ne_zero hβ p.1
  have hw0 : w ≠ 0 := by rw [hw]; exact Commons.Analysis.Complex.gam_ne_zero hβ p.2
  have hF : ‖f z w‖ ≤ B := hbound z w hzreg.1 hzreg.2 hwreg.1 hwreg.2
  have hZu : ‖Z‖ ≤ Cn * (|p.1| + |p.2| + 3) ^ ((1:ℝ)/2) := by
    have := hnum p.1 p.2
    simpa only [Z, hz, hw] using this
  have hcinv : ‖c⁻¹‖ ≤ C₁ * (Real.log (|p.1| + 2) + 1) := by
    have h := hinvb z hz0 hzreg.1 hzreg.2
    rw [hc]
    simp only [hz, Commons.Analysis.Complex.gam_im] at h
    exact h
  have hWinv : ‖W⁻¹‖ ≤ C₁ * (Real.log (|p.2| + 2) + 1) := by
    have h := hinvb w hw0 hwreg.1 hwreg.2
    rw [hW]
    simp only [hw, Commons.Analysis.Complex.gam_im] at h
    exact h
  have hRcb : ‖Rc‖ ≤ 1 := by
    rw [hRc, Complex.norm_cpow_eq_rpow_re_of_pos hRpos]
    refine Real.rpow_le_one_of_one_le_of_nonpos (by linarith) ?_
    have h1 := Commons.Analysis.Complex.phi_le_zero hβ p.1
    have h2 := Commons.Analysis.Complex.phi_le_zero hβ p.2
    simp only [Commons.Analysis.Complex.phi] at h1 h2
    simp only [Complex.add_re, hz, hw, Commons.Analysis.Complex.gam_re]
    linarith
  have hQb : ‖(z ^ 2)⁻¹ * Commons.Analysis.Complex.gamDot β p.1‖
      ≤ Commons.Analysis.Complex.curveConst β * (1 + p.1 ^ 2)⁻¹ := by
    rw [hz]
    exact Commons.Analysis.Complex.inv_sq_mul_gamDot_norm_le hβ p.1
  have hQb' : ‖(w ^ 2)⁻¹ * Commons.Analysis.Complex.gamDot β p.2‖
      ≤ Commons.Analysis.Complex.curveConst β * (1 + p.2 ^ 2)⁻¹ := by
    rw [hw]
    exact Commons.Analysis.Complex.inv_sq_mul_gamDot_norm_le hβ p.2
  have hl1nn : 0 ≤ Real.log (|p.1| + 2) + 1 := by
    have := Real.log_nonneg (show (1:ℝ) ≤ |p.1| + 2 by linarith [abs_nonneg p.1]); linarith
  have hl2nn : 0 ≤ Real.log (|p.2| + 2) + 1 := by
    have := Real.log_nonneg (show (1:ℝ) ≤ |p.2| + 2 by linarith [abs_nonneg p.2]); linarith
  have hGS : ggIntegrand β R f p
      = f z w * (Z / (c * W)) * Rc / (z ^ 2 * w ^ 2)
        * Commons.Analysis.Complex.gamDot β p.1 * Commons.Analysis.Complex.gamDot β p.2 := rfl
  rw [hGS]
  have hnorm_eq : ‖f z w * (Z / (c * W)) * Rc / (z ^ 2 * w ^ 2)
        * Commons.Analysis.Complex.gamDot β p.1 * Commons.Analysis.Complex.gamDot β p.2‖
      = ‖f z w‖ * ‖Z‖ * ‖c⁻¹‖ * ‖W⁻¹‖ * ‖Rc‖
        * ‖(z ^ 2)⁻¹ * Commons.Analysis.Complex.gamDot β p.1‖
        * ‖(w ^ 2)⁻¹ * Commons.Analysis.Complex.gamDot β p.2‖ := by
    rw [show f z w * (Z / (c * W)) * Rc / (z ^ 2 * w ^ 2)
          * Commons.Analysis.Complex.gamDot β p.1 * Commons.Analysis.Complex.gamDot β p.2
        = f z w * Z * c⁻¹ * W⁻¹ * Rc
          * ((z ^ 2)⁻¹ * Commons.Analysis.Complex.gamDot β p.1)
          * ((w ^ 2)⁻¹ * Commons.Analysis.Complex.gamDot β p.2) by
      rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv, mul_inv]; ring]
    simp only [norm_mul]
  rw [hnorm_eq]
  have hA1 : 0 ≤ B * Cn := mul_nonneg hB hCn.le
  have hc1a : 0 ≤ C₁ * (Real.log (|p.1| + 2) + 1) := mul_nonneg hC1.le hl1nn
  have hc1b : 0 ≤ C₁ * (Real.log (|p.2| + 2) + 1) := mul_nonneg hC1.le hl2nn
  have h1t : 0 ≤ (1 + p.1 ^ 2)⁻¹ := by positivity
  have h1t' : 0 ≤ (1 + p.2 ^ 2)⁻¹ := by positivity
  have h1 : ‖f z w‖ * ‖Z‖
      ≤ B * (Cn * (|p.1| + |p.2| + 3) ^ ((1:ℝ)/2)) :=
    mul_le_mul hF hZu (norm_nonneg _) hB
  have hA2 : 0 ≤ B * (Cn * (|p.1| + |p.2| + 3) ^ ((1:ℝ)/2)) :=
    mul_nonneg hB (mul_nonneg hCn.le (Real.rpow_nonneg (by positivity) _))
  have h2 : ‖f z w‖ * ‖Z‖ * ‖c⁻¹‖
      ≤ B * (Cn * (|p.1| + |p.2| + 3) ^ ((1:ℝ)/2))
        * (C₁ * (Real.log (|p.1| + 2) + 1)) :=
    mul_le_mul h1 hcinv (norm_nonneg _) hA2
  have hA3 : 0 ≤ B * (Cn * (|p.1| + |p.2| + 3) ^ ((1:ℝ)/2))
      * (C₁ * (Real.log (|p.1| + 2) + 1)) := mul_nonneg hA2 hc1a
  have h3 : ‖f z w‖ * ‖Z‖ * ‖c⁻¹‖ * ‖W⁻¹‖
      ≤ B * (Cn * (|p.1| + |p.2| + 3) ^ ((1:ℝ)/2))
        * (C₁ * (Real.log (|p.1| + 2) + 1)) * (C₁ * (Real.log (|p.2| + 2) + 1)) :=
    mul_le_mul h2 hWinv (norm_nonneg _) hA3
  have hA4 : 0 ≤ B * (Cn * (|p.1| + |p.2| + 3) ^ ((1:ℝ)/2))
      * (C₁ * (Real.log (|p.1| + 2) + 1)) * (C₁ * (Real.log (|p.2| + 2) + 1)) :=
    mul_nonneg hA3 hc1b
  have h4 : ‖f z w‖ * ‖Z‖ * ‖c⁻¹‖ * ‖W⁻¹‖ * ‖Rc‖
      ≤ B * (Cn * (|p.1| + |p.2| + 3) ^ ((1:ℝ)/2))
        * (C₁ * (Real.log (|p.1| + 2) + 1)) * (C₁ * (Real.log (|p.2| + 2) + 1)) * 1 :=
    mul_le_mul h3 hRcb (norm_nonneg _) hA4
  have hA5 : 0 ≤ B * (Cn * (|p.1| + |p.2| + 3) ^ ((1:ℝ)/2))
      * (C₁ * (Real.log (|p.1| + 2) + 1)) * (C₁ * (Real.log (|p.2| + 2) + 1)) * 1 :=
    mul_nonneg hA4 zero_le_one
  have h5 : ‖f z w‖ * ‖Z‖ * ‖c⁻¹‖ * ‖W⁻¹‖ * ‖Rc‖
        * ‖(z ^ 2)⁻¹ * Commons.Analysis.Complex.gamDot β p.1‖
      ≤ B * (Cn * (|p.1| + |p.2| + 3) ^ ((1:ℝ)/2))
        * (C₁ * (Real.log (|p.1| + 2) + 1)) * (C₁ * (Real.log (|p.2| + 2) + 1)) * 1
        * (Commons.Analysis.Complex.curveConst β * (1 + p.1 ^ 2)⁻¹) :=
    mul_le_mul h4 hQb (norm_nonneg _) hA5
  have hA6 : 0 ≤ B * (Cn * (|p.1| + |p.2| + 3) ^ ((1:ℝ)/2))
      * (C₁ * (Real.log (|p.1| + 2) + 1)) * (C₁ * (Real.log (|p.2| + 2) + 1)) * 1
      * (Commons.Analysis.Complex.curveConst β * (1 + p.1 ^ 2)⁻¹) :=
    mul_nonneg hA5 (mul_nonneg hcc h1t)
  have h6 : ‖f z w‖ * ‖Z‖ * ‖c⁻¹‖ * ‖W⁻¹‖ * ‖Rc‖
        * ‖(z ^ 2)⁻¹ * Commons.Analysis.Complex.gamDot β p.1‖
        * ‖(w ^ 2)⁻¹ * Commons.Analysis.Complex.gamDot β p.2‖
      ≤ B * (Cn * (|p.1| + |p.2| + 3) ^ ((1:ℝ)/2))
        * (C₁ * (Real.log (|p.1| + 2) + 1)) * (C₁ * (Real.log (|p.2| + 2) + 1)) * 1
        * (Commons.Analysis.Complex.curveConst β * (1 + p.1 ^ 2)⁻¹)
        * (Commons.Analysis.Complex.curveConst β * (1 + p.2 ^ 2)⁻¹) :=
    mul_le_mul h5 hQb' (norm_nonneg _) hA6
  refine le_trans h6 ?_
  have hl1' : 0 ≤ (Real.log (|p.1| + 2) + 1) / (1 + p.1 ^ 2) :=
    div_nonneg hl1nn (by positivity)
  have hl2' : 0 ≤ (Real.log (|p.2| + 2) + 1) / (1 + p.2 ^ 2) :=
    div_nonneg hl2nn (by positivity)
  have hA : 0 ≤ B * Cn * C₁ ^ 2 * Commons.Analysis.Complex.curveConst β ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg hB hCn.le) (sq_nonneg C₁)) (sq_nonneg _)
  calc B * (Cn * (|p.1| + |p.2| + 3) ^ ((1:ℝ)/2))
        * (C₁ * (Real.log (|p.1| + 2) + 1)) * (C₁ * (Real.log (|p.2| + 2) + 1)) * 1
        * (Commons.Analysis.Complex.curveConst β * (1 + p.1 ^ 2)⁻¹)
        * (Commons.Analysis.Complex.curveConst β * (1 + p.2 ^ 2)⁻¹)
      = (B * Cn * C₁ ^ 2 * Commons.Analysis.Complex.curveConst β ^ 2)
        * ((|p.1| + |p.2| + 3) ^ ((1:ℝ)/2))
        * ((Real.log (|p.1| + 2) + 1) / (1 + p.1 ^ 2))
        * ((Real.log (|p.2| + 2) + 1) / (1 + p.2 ^ 2)) := by ring
    _ ≤ (B * Cn * C₁ ^ 2 * Commons.Analysis.Complex.curveConst β ^ 2)
        * ((|p.1| + 3) ^ ((1:ℝ)/2) * (|p.2| + 3) ^ ((1:ℝ)/2))
        * ((Real.log (|p.1| + 2) + 1) / (1 + p.1 ^ 2))
        * ((Real.log (|p.2| + 2) + 1) / (1 + p.2 ^ 2)) := by
        have hb := sqrt_base_le p.1 p.2
        have hstep1 : (B * Cn * C₁ ^ 2 * Commons.Analysis.Complex.curveConst β ^ 2)
              * ((|p.1| + |p.2| + 3) ^ ((1:ℝ)/2))
            ≤ (B * Cn * C₁ ^ 2 * Commons.Analysis.Complex.curveConst β ^ 2)
              * ((|p.1| + 3) ^ ((1:ℝ)/2) * (|p.2| + 3) ^ ((1:ℝ)/2)) :=
          mul_le_mul_of_nonneg_left hb hA
        have hstep2 := mul_le_mul_of_nonneg_right hstep1 hl1'
        exact mul_le_mul_of_nonneg_right hstep2 hl2'
    _ = (B * Cn * C₁ ^ 2 * Commons.Analysis.Complex.curveConst β ^ 2)
        * uScaleHalfPt p.1 * uScaleHalfPt p.2 := by
        simp only [uScaleHalfPt]; ring

/-- The Green-Tao kernel times `gamDot β t * gamDot β t'` is jointly integrable on `Γ₀ × Γ₀`.

NOTE the continuity hypothesis `hcont` is REQUIRED (otherwise a non-measurable `f` in the imaginary
part is a counterexample); with it the integrand is continuous and the pointwise domination gives
finiteness: `‖ζ(1+gam β t + gam β t')‖ ≤ Cn (|t|+|t'|+3)^(1/2)` (from
`Commons.NumberTheory.Zeta.zeta_one_add_add_bound_curve_sqrt_curve`),
`‖(ζ(1+gam β t))⁻¹‖ ≤ C₁(log(|t|+2)+1)` and similarly for `t'`,
`‖R^(gam β t + gam β t')‖ ≤ 1` (real parts `≤ 0`), and
`‖(gam β t^2)⁻¹ * gamDot β t‖ ≤ curveConst β (1+t^2)⁻¹`
(`Commons.Analysis.Complex.inv_sq_mul_gamDot_norm_le`).  Since
`(|t|+|t'|+3)^(1/2) ≤ (|t|+3)^(1/2) (|t'|+3)^(1/2)`, the integrand is dominated by a constant times
`(|t|+3)^(1/2)(log(|t|+2)+1)/(1+t^2) * (|t'|+3)^(1/2)(log(|t'|+2)+1)/(1+t'^2)`; use
`Integrable.mul_prod` and `Commons.Analysis.Integral.uScaleHalf_integrable`. -/
theorem greenTao_kernel_integrable_gam_gam_cont {β R : ℝ} (hβ : 0 < β) (hβ10 : β ≤ 1 / 10) (hR : 3 ≤ R)
    (f : ℂ → ℂ → ℂ) (B C₁ Cn : ℝ) (hC1 : 0 < C₁) (hCn : 0 < Cn)
    (hcont : Continuous (Function.uncurry f))
    (hinvb : ∀ z : ℂ, z ≠ 0 → -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 →
        ‖(riemannZeta (1 + z))⁻¹‖ ≤ C₁ * (Real.log (|z.im| + 2) + 1))
    (hbound : ∀ z z' : ℂ, -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 →
        -(β / Real.log (|z'.im| + 2)) ≤ z'.re → z'.re ≤ 1 → ‖f z z'‖ ≤ B)
    (hnum : ∀ t t' : ℝ, ‖riemannZeta (1 + Commons.Analysis.Complex.gam β t
        + Commons.Analysis.Complex.gam β t')‖ ≤ Cn * (|t| + |t'| + 3) ^ ((1:ℝ)/2)) :
    MeasureTheory.Integrable (Function.uncurry (fun t t' : ℝ =>
      f (Commons.Analysis.Complex.gam β t) (Commons.Analysis.Complex.gam β t')
        * (riemannZeta (1 + Commons.Analysis.Complex.gam β t + Commons.Analysis.Complex.gam β t')
            / (riemannZeta (1 + Commons.Analysis.Complex.gam β t)
                * riemannZeta (1 + Commons.Analysis.Complex.gam β t')))
        * (R : ℂ) ^ (Commons.Analysis.Complex.gam β t + Commons.Analysis.Complex.gam β t')
        / ((Commons.Analysis.Complex.gam β t) ^ 2 * (Commons.Analysis.Complex.gam β t') ^ 2)
        * Commons.Analysis.Complex.gamDot β t * Commons.Analysis.Complex.gamDot β t'))
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
  obtain ⟨K, hK0, hKb⟩ :=
    norm_ggIntegrand_le hβ hR f B C₁ Cn hC1 hCn hinvb hbound hnum
  obtain ⟨_, _, hu, _⟩ := Commons.Analysis.Integral.uScaleHalf_integrable
  have hu' : Integrable (fun t : ℝ => uScaleHalfPt t) volume := by
    simpa only [uScaleHalfPt] using hu
  have hD : Integrable (fun p : ℝ × ℝ => (K * uScaleHalfPt p.1) * uScaleHalfPt p.2)
      (volume.prod volume) := (hu'.const_mul K).mul_prod hu'
  have hmeas : AEStronglyMeasurable (ggIntegrand β R f) (volume.prod volume) :=
    aesm_ggIntegrand (by linarith : 0 < R) f hcont
  have hb : ∀ᵐ p ∂(volume.prod volume),
      ‖ggIntegrand β R f p‖ ≤ (K * uScaleHalfPt p.1) * uScaleHalfPt p.2 :=
    Filter.Eventually.of_forall hKb
  change Integrable (ggIntegrand β R f) (volume.prod volume)
  exact Integrable.mono' hD hmeas hb

end

end Commons.NumberTheory.Zeta

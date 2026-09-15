import Mathlib
import Submission.Commons.Analysis.Complex.contour_shift_residue
import Submission.Commons.Analysis.Complex.curve_inv_sq_integrable
import Submission.Commons.Analysis.Integral.uScaleHalf_integrable
import Submission.Commons.NumberTheory.Zeta.gam0_Rz_div_sq_integral_le
import Submission.Commons.Analysis.Complex.norm_cpow_gam_eq

namespace Commons.NumberTheory.Zeta

open MeasureTheory
open scoped Topology

noncomputable section

/-! ## Helper definitions for the `Γ₀ × Γ₂` Green–Tao kernel -/

/-- The `Γ₂` vertical coordinate `w(t) = 1 + t·i`. -/
private def sigPt (t : ℝ) : ℂ := (1 : ℂ) + (t : ℂ) * Complex.I

@[simp] private lemma sigPt_re (t : ℝ) : (sigPt t).re = 1 := by simp [sigPt]
@[simp] private lemma sigPt_im (t : ℝ) : (sigPt t).im = t := by simp [sigPt]

private lemma sigPt_ne_zero (t : ℝ) : sigPt t ≠ 0 := by
  intro h
  have : (sigPt t).re = 0 := by rw [h]; simp
  rw [sigPt_re] at this
  norm_num at this

/-- `sigPt t` lies in the region of the hypotheses. -/
private lemma sigPt_mem_region {β : ℝ} (hβ : 0 < β) (t : ℝ) :
    -(β / Real.log (|(sigPt t).im| + 2)) ≤ (sigPt t).re ∧ (sigPt t).re ≤ 1 := by
  constructor
  · rw [sigPt_im, sigPt_re]
    have : 0 < β / Real.log (|t| + 2) := div_pos hβ (Real.log_pos (by linarith [abs_nonneg t]))
    linarith
  · rw [sigPt_re]

/-- The `Γ₀ × Γ₂` kernel integrand, as a function on `ℝ × ℝ`. -/
private def gsIntegrand (β R : ℝ) (f : ℂ → ℂ → ℂ) : ℝ × ℝ → ℂ := fun p =>
  f (Commons.Analysis.Complex.gam β p.1) (sigPt p.2)
    * (riemannZeta (1 + Commons.Analysis.Complex.gam β p.1 + sigPt p.2)
        / (riemannZeta (1 + Commons.Analysis.Complex.gam β p.1)
          * riemannZeta (1 + sigPt p.2)))
    * (R : ℂ) ^ (Commons.Analysis.Complex.gam β p.1 + sigPt p.2)
    / ((Commons.Analysis.Complex.gam β p.1) ^ 2 * (sigPt p.2) ^ 2)
    * Commons.Analysis.Complex.gamDot β p.1

/-- The Green–Tao weight `(|t|+3)^{1/2} (log(|t|+2)+1)/(1+t²)`, dominating the
product of the `Γ₀` and `Γ₂` factors. -/
private def uScaleHalfPt (t : ℝ) : ℝ :=
  (|t| + 3) ^ ((1:ℝ)/2) * (Real.log (|t| + 2) + 1) / (1 + t ^ 2)

private lemma uScaleHalfPt_nonneg (t : ℝ) : 0 ≤ uScaleHalfPt t := by
  rw [uScaleHalfPt]
  refine div_nonneg (mul_nonneg (Real.rpow_nonneg (by linarith [abs_nonneg t]) _) ?_) (by positivity)
  have := Real.log_nonneg (show (1:ℝ) ≤ |t| + 2 by linarith [abs_nonneg t])
  linarith

private lemma log_weight_le_uScaleHalfPt (t : ℝ) :
    (Real.log (|t| + 2) + 1) / (1 + t ^ 2) ≤ uScaleHalfPt t := by
  rw [uScaleHalfPt]
  have hpos : 0 ≤ (Real.log (|t| + 2) + 1) / (1 + t ^ 2) := by
    refine div_nonneg ?_ (by positivity)
    have := Real.log_nonneg (show (1:ℝ) ≤ |t| + 2 by linarith [abs_nonneg t])
    linarith
  have hone : (1:ℝ) ≤ (|t| + 3) ^ ((1:ℝ)/2) :=
    Real.one_le_rpow (by linarith [abs_nonneg t]) (by norm_num)
  calc (Real.log (|t| + 2) + 1) / (1 + t ^ 2)
      = 1 * ((Real.log (|t| + 2) + 1) / (1 + t ^ 2)) := by ring
    _ ≤ (|t| + 3) ^ ((1:ℝ)/2) * ((Real.log (|t| + 2) + 1) / (1 + t ^ 2)) :=
        mul_le_mul_of_nonneg_right hone hpos
    _ = (|t| + 3) ^ ((1:ℝ)/2) * (Real.log (|t| + 2) + 1) / (1 + t ^ 2) := by ring

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

private lemma aesm_gsIntegrand {β R : ℝ} (hRpos : 0 < R) (f : ℂ → ℂ → ℂ)
    (hcont : Continuous (Function.uncurry f)) :
    AEStronglyMeasurable (gsIntegrand β R f) (volume.prod volume) := by
  have hRne : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hRpos)
  have hgam : Continuous (fun p : ℝ × ℝ => Commons.Analysis.Complex.gam β p.1) :=
    (Commons.Analysis.Complex.gam_continuous β).comp continuous_fst
  have hw : Continuous (fun p : ℝ × ℝ => sigPt p.2) := by
    unfold sigPt
    exact continuous_const.add ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)
  have hE1 : Measurable (fun p : ℝ × ℝ =>
      f (Commons.Analysis.Complex.gam β p.1) (sigPt p.2)) :=
    (hcont.comp (hgam.prodMk hw)).measurable
  have hE2 : Measurable (fun p : ℝ × ℝ =>
      riemannZeta (1 + Commons.Analysis.Complex.gam β p.1 + sigPt p.2)) :=
    measurable_riemannZeta.comp ((continuous_const.add hgam).add hw).measurable
  have hE3 : Measurable (fun p : ℝ × ℝ =>
      riemannZeta (1 + Commons.Analysis.Complex.gam β p.1)) :=
    measurable_riemannZeta.comp (continuous_const.add hgam).measurable
  have hE4 : Measurable (fun p : ℝ × ℝ => riemannZeta (1 + sigPt p.2)) :=
    measurable_riemannZeta.comp (continuous_const.add hw).measurable
  have hE5 : Measurable (fun p : ℝ × ℝ =>
      (R : ℂ) ^ (Commons.Analysis.Complex.gam β p.1 + sigPt p.2)) :=
    ((hgam.add hw).const_cpow (b := (R : ℂ)) (Or.inl hRne)).measurable
  have hE6 : Measurable (fun p : ℝ × ℝ =>
      (Commons.Analysis.Complex.gam β p.1) ^ 2 * (sigPt p.2) ^ 2) :=
    (hgam.measurable.pow_const 2).mul (hw.measurable.pow_const 2)
  have hPhi : Measurable (fun p : ℝ × ℝ =>
      f (Commons.Analysis.Complex.gam β p.1) (sigPt p.2)
        * (riemannZeta (1 + Commons.Analysis.Complex.gam β p.1 + sigPt p.2)
            / (riemannZeta (1 + Commons.Analysis.Complex.gam β p.1)
              * riemannZeta (1 + sigPt p.2)))
        * (R : ℂ) ^ (Commons.Analysis.Complex.gam β p.1 + sigPt p.2)
        / ((Commons.Analysis.Complex.gam β p.1) ^ 2 * (sigPt p.2) ^ 2)) :=
    ((hE1.mul (hE2.div (hE3.mul hE4))).mul hE5).div hE6
  have hgd : AEStronglyMeasurable (fun p : ℝ × ℝ => Commons.Analysis.Complex.gamDot β p.1)
      (volume.prod volume) :=
    ((measurable_gamDot β).comp measurable_fst).aestronglyMeasurable
  exact hPhi.aestronglyMeasurable.mul hgd

/-! ## Pointwise domination -/

private lemma norm_gsIntegrand_le {β R : ℝ} (hβ : 0 < β) (hR : 3 ≤ R)
    (f : ℂ → ℂ → ℂ) (B C₁ C₂ : ℝ) (hC1 : 0 < C₁) (hC2 : 0 < C₂)
    (hinvb : ∀ z : ℂ, z ≠ 0 → -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 →
        ‖(riemannZeta (1 + z))⁻¹‖ ≤ C₁ * (Real.log (|z.im| + 2) + 1))
    (hbound : ∀ z z' : ℂ, -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 →
        -(β / Real.log (|z'.im| + 2)) ≤ z'.re → z'.re ≤ 1 → ‖f z z'‖ ≤ B)
    (hnum : ∀ t t' : ℝ, ‖riemannZeta (1 + Commons.Analysis.Complex.gam β t
        + ((1 : ℂ) + (t' : ℂ) * Complex.I))‖ ≤ C₂) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ p : ℝ × ℝ,
      ‖gsIntegrand β R f p‖ ≤ K * uScaleHalfPt p.1 * uScaleHalfPt p.2 := by
  have hRpos : 0 < R := by linarith
  have hB : 0 ≤ B := by
    have h := hbound (Commons.Analysis.Complex.gam β 0) (Commons.Analysis.Complex.gam β 0)
      (gam_mem_region hβ 0).1 (gam_mem_region hβ 0).2
      (gam_mem_region hβ 0).1 (gam_mem_region hβ 0).2
    exact le_trans (norm_nonneg _) h
  have hcc : 0 ≤ Commons.Analysis.Complex.curveConst β :=
    (Commons.Analysis.Complex.curveConst_pos hβ).le
  refine ⟨B * C₂ * C₁ ^ 2 * R * Commons.Analysis.Complex.curveConst β,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hB hC2.le) (sq_nonneg C₁))
      (by linarith)) hcc, ?_⟩
  intro p
  set z : ℂ := Commons.Analysis.Complex.gam β p.1 with hz
  set w : ℂ := sigPt p.2 with hw
  set Z : ℂ := riemannZeta (1 + z + w) with hZ
  set c : ℂ := riemannZeta (1 + z) with hc
  set W : ℂ := riemannZeta (1 + w) with hW
  set Rc : ℂ := (R : ℂ) ^ (z + w) with hRc
  have hzreg : -(β / Real.log (|z.im| + 2)) ≤ z.re ∧ z.re ≤ 1 := gam_mem_region hβ p.1
  have hwreg : -(β / Real.log (|w.im| + 2)) ≤ w.re ∧ w.re ≤ 1 := sigPt_mem_region hβ p.2
  have hz0 : z ≠ 0 := Commons.Analysis.Complex.gam_ne_zero hβ p.1
  have hw0 : w ≠ 0 := sigPt_ne_zero p.2
  have hF : ‖f z w‖ ≤ B := hbound z w hzreg.1 hzreg.2 hwreg.1 hwreg.2
  have hZu : ‖Z‖ ≤ C₂ := by
    have := hnum p.1 p.2
    simpa only [Z, sigPt, hz, hw] using this
  have hcinv : ‖c⁻¹‖ ≤ C₁ * (Real.log (|p.1| + 2) + 1) := by
    have h := hinvb z hz0 hzreg.1 hzreg.2
    rw [hc]
    simp only [hz, Commons.Analysis.Complex.gam_im] at h
    exact h
  have hWinv : ‖W⁻¹‖ ≤ C₁ * (Real.log (|p.2| + 2) + 1) := by
    have h := hinvb w hw0 hwreg.1 hwreg.2
    rw [hW]
    simp only [hw, sigPt_im] at h
    exact h
  have hRcb : ‖Rc‖ ≤ R := by
    rw [hRc, Complex.norm_cpow_eq_rpow_re_of_pos hRpos]
    have hre : (z + w).re ≤ 1 := by
      rw [Complex.add_re, hz, hw, sigPt_re, Commons.Analysis.Complex.gam_re]
      have h := Commons.Analysis.Complex.phi_le_zero hβ p.1
      simp only [Commons.Analysis.Complex.phi] at h
      linarith
    calc R ^ (z + w).re ≤ R ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) hre
      _ = R := Real.rpow_one R
  have hQb : ‖(z ^ 2)⁻¹ * Commons.Analysis.Complex.gamDot β p.1‖
      ≤ Commons.Analysis.Complex.curveConst β * (1 + p.1 ^ 2)⁻¹ := by
    rw [hz]
    exact Commons.Analysis.Complex.inv_sq_mul_gamDot_norm_le hβ p.1
  have hw2inv : ‖(w ^ 2)⁻¹‖ = (1 + p.2 ^ 2)⁻¹ := by
    rw [norm_inv, norm_pow]
    have hw2 : ‖w‖ ^ 2 = 1 + p.2 ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, hw]
      simp only [sigPt_re, sigPt_im]
      ring
    rw [hw2]
  have hl1nn : 0 ≤ Real.log (|p.1| + 2) + 1 := by
    have := Real.log_nonneg (show (1:ℝ) ≤ |p.1| + 2 by linarith [abs_nonneg p.1]); linarith
  have hl2nn : 0 ≤ Real.log (|p.2| + 2) + 1 := by
    have := Real.log_nonneg (show (1:ℝ) ≤ |p.2| + 2 by linarith [abs_nonneg p.2]); linarith
  have hGS : gsIntegrand β R f p
      = f z w * (Z / (c * W)) * Rc / (z ^ 2 * w ^ 2) * Commons.Analysis.Complex.gamDot β p.1 := rfl
  rw [hGS]
  have hnorm_eq : ‖f z w * (Z / (c * W)) * Rc / (z ^ 2 * w ^ 2)
        * Commons.Analysis.Complex.gamDot β p.1‖
      = ‖f z w‖ * ‖Z‖ * ‖c⁻¹‖ * ‖W⁻¹‖ * ‖Rc‖
        * ‖(z ^ 2)⁻¹ * Commons.Analysis.Complex.gamDot β p.1‖ * ‖(w ^ 2)⁻¹‖ := by
    rw [show f z w * (Z / (c * W)) * Rc / (z ^ 2 * w ^ 2)
          * Commons.Analysis.Complex.gamDot β p.1
        = f z w * Z * c⁻¹ * W⁻¹ * Rc
          * ((z ^ 2)⁻¹ * Commons.Analysis.Complex.gamDot β p.1) * (w ^ 2)⁻¹ by
      rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv, mul_inv]; ring]
    simp only [norm_mul]
  rw [hnorm_eq]
  have hA1 : 0 ≤ B * C₂ := mul_nonneg hB hC2.le
  have hc1a : 0 ≤ C₁ * (Real.log (|p.1| + 2) + 1) := mul_nonneg hC1.le hl1nn
  have hc1b : 0 ≤ C₁ * (Real.log (|p.2| + 2) + 1) := mul_nonneg hC1.le hl2nn
  have h1t : 0 ≤ (1 + p.1 ^ 2)⁻¹ := by positivity
  have h1t' : 0 ≤ (1 + p.2 ^ 2)⁻¹ := by positivity
  have h1 : ‖f z w‖ * ‖Z‖ ≤ B * C₂ := mul_le_mul hF hZu (norm_nonneg _) hB
  have hA2 : 0 ≤ B * C₂ * (C₁ * (Real.log (|p.1| + 2) + 1)) := mul_nonneg hA1 hc1a
  have h2 : ‖f z w‖ * ‖Z‖ * ‖c⁻¹‖ ≤ B * C₂ * (C₁ * (Real.log (|p.1| + 2) + 1)) :=
    mul_le_mul h1 hcinv (norm_nonneg _) hA1
  have hA3 : 0 ≤ B * C₂ * (C₁ * (Real.log (|p.1| + 2) + 1))
      * (C₁ * (Real.log (|p.2| + 2) + 1)) := mul_nonneg hA2 hc1b
  have h3 : ‖f z w‖ * ‖Z‖ * ‖c⁻¹‖ * ‖W⁻¹‖
      ≤ B * C₂ * (C₁ * (Real.log (|p.1| + 2) + 1)) * (C₁ * (Real.log (|p.2| + 2) + 1)) :=
    mul_le_mul h2 hWinv (norm_nonneg _) hA2
  have hA4 : 0 ≤ B * C₂ * (C₁ * (Real.log (|p.1| + 2) + 1))
      * (C₁ * (Real.log (|p.2| + 2) + 1)) * R := mul_nonneg hA3 (by linarith)
  have h4 : ‖f z w‖ * ‖Z‖ * ‖c⁻¹‖ * ‖W⁻¹‖ * ‖Rc‖
      ≤ B * C₂ * (C₁ * (Real.log (|p.1| + 2) + 1))
        * (C₁ * (Real.log (|p.2| + 2) + 1)) * R := mul_le_mul h3 hRcb (norm_nonneg _) hA3
  have hA5 : 0 ≤ B * C₂ * (C₁ * (Real.log (|p.1| + 2) + 1))
      * (C₁ * (Real.log (|p.2| + 2) + 1)) * R
      * (Commons.Analysis.Complex.curveConst β * (1 + p.1 ^ 2)⁻¹) :=
    mul_nonneg hA4 (mul_nonneg hcc h1t)
  have h5 : ‖f z w‖ * ‖Z‖ * ‖c⁻¹‖ * ‖W⁻¹‖ * ‖Rc‖
        * ‖(z ^ 2)⁻¹ * Commons.Analysis.Complex.gamDot β p.1‖
      ≤ B * C₂ * (C₁ * (Real.log (|p.1| + 2) + 1))
        * (C₁ * (Real.log (|p.2| + 2) + 1)) * R
        * (Commons.Analysis.Complex.curveConst β * (1 + p.1 ^ 2)⁻¹) :=
    mul_le_mul h4 hQb (norm_nonneg _) hA4
  have h6 : ‖f z w‖ * ‖Z‖ * ‖c⁻¹‖ * ‖W⁻¹‖ * ‖Rc‖
        * ‖(z ^ 2)⁻¹ * Commons.Analysis.Complex.gamDot β p.1‖ * ‖(w ^ 2)⁻¹‖
      ≤ B * C₂ * (C₁ * (Real.log (|p.1| + 2) + 1))
        * (C₁ * (Real.log (|p.2| + 2) + 1)) * R
        * (Commons.Analysis.Complex.curveConst β * (1 + p.1 ^ 2)⁻¹) * (1 + p.2 ^ 2)⁻¹ :=
    mul_le_mul h5 hw2inv.le (norm_nonneg _) hA5
  refine le_trans h6 ?_
  calc B * C₂ * (C₁ * (Real.log (|p.1| + 2) + 1))
        * (C₁ * (Real.log (|p.2| + 2) + 1)) * R
        * (Commons.Analysis.Complex.curveConst β * (1 + p.1 ^ 2)⁻¹) * (1 + p.2 ^ 2)⁻¹
      = (B * C₂ * C₁ ^ 2 * R * Commons.Analysis.Complex.curveConst β)
        * ((Real.log (|p.1| + 2) + 1) / (1 + p.1 ^ 2))
        * ((Real.log (|p.2| + 2) + 1) / (1 + p.2 ^ 2)) := by ring
    _ ≤ (B * C₂ * C₁ ^ 2 * R * Commons.Analysis.Complex.curveConst β)
        * uScaleHalfPt p.1 * uScaleHalfPt p.2 := by
        have hg1 := log_weight_le_uScaleHalfPt p.1
        have hg2 := log_weight_le_uScaleHalfPt p.2
        have hg1nn : 0 ≤ (Real.log (|p.1| + 2) + 1) / (1 + p.1 ^ 2) :=
          div_nonneg hl1nn (by positivity)
        have hg2nn : 0 ≤ (Real.log (|p.2| + 2) + 1) / (1 + p.2 ^ 2) :=
          div_nonneg hl2nn (by positivity)
        have hAnn : 0 ≤ B * C₂ * C₁ ^ 2 * R * Commons.Analysis.Complex.curveConst β :=
          mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hB hC2.le) (sq_nonneg C₁))
            (by linarith)) hcc
        calc (B * C₂ * C₁ ^ 2 * R * Commons.Analysis.Complex.curveConst β)
              * ((Real.log (|p.1| + 2) + 1) / (1 + p.1 ^ 2))
              * ((Real.log (|p.2| + 2) + 1) / (1 + p.2 ^ 2))
            = (B * C₂ * C₁ ^ 2 * R * Commons.Analysis.Complex.curveConst β)
              * (((Real.log (|p.1| + 2) + 1) / (1 + p.1 ^ 2))
                * ((Real.log (|p.2| + 2) + 1) / (1 + p.2 ^ 2))) := by ring
          _ ≤ (B * C₂ * C₁ ^ 2 * R * Commons.Analysis.Complex.curveConst β)
              * (uScaleHalfPt p.1 * uScaleHalfPt p.2) :=
              mul_le_mul_of_nonneg_left (mul_le_mul hg1 hg2 hg2nn (uScaleHalfPt_nonneg p.1)) hAnn
          _ = (B * C₂ * C₁ ^ 2 * R * Commons.Analysis.Complex.curveConst β)
              * uScaleHalfPt p.1 * uScaleHalfPt p.2 := by ring

/-- Green-Tao kernel times `gamDot` is jointly integrable on `Γ₀ × Γ₂`:
`(t,t') ↦ K R f (gam β t) (1 + t' i) * gamDot β t`, where `gam β t = (-(β/log(|t|+2)) : ℝ) + t i`.

This is the same statement as the requested `greenTao_kernel_integrable_gam_sigma`, but with the
measurability hypothesis on `f` that the original statement is missing (without it the original is
false: `Integrable` requires `AEStronglyMeasurable`, and a function that is merely bounded on the
region need not be measurable).

Proof route: pointwise domination. For `z = gam β t` and `w = 1 + t'i` (both in the region of
`hbound`/`hinvb`):
* `‖f (gam β t) w‖ ≤ B` (`hbound`);
* `‖ζ(1+gam β t+w)‖ ≤ C₂` (`hnum`), `‖(ζ(1+gam β t))⁻¹‖ ≤ C₁ (log(|t|+2)+1)`,
  `‖(ζ(1+w))⁻¹‖ ≤ C₁ (log(|t'|+2)+1)` (`hinvb` at `gam β t` resp. `1+t'i`, both nonzero and in the
  region);
* `‖R^(gam β t+w)‖ ≤ R` since `Re(gam β t+w) = 1 - β/log(|t|+2) ≤ 1` and `1 ≤ R`
  (`Complex.norm_cpow_eq_rpow_re_of_pos`, `Real.rpow_le_rpow_of_exponent_le`);
* `‖((gam β t)^2)⁻¹ * gamDot β t‖ ≤ curveConst β * (1+t²)⁻¹`
  (`Commons.Analysis.Complex.inv_sq_mul_gamDot_norm_le`) and `‖((1+t'i)^2)⁻¹‖ = (1+t'²)⁻¹`.
Hence `‖integrand‖ ≤ B*C₂*C₁²*R*curveConst β * (log(|t|+2)+1)/(1+t²) * (log(|t'|+2)+1)/(1+t'²)`.
The one-variable factor `g t = (log(|t|+2)+1)/(1+t²)` is integrable: it is dominated by
`(|t|+3)^(1/2) * (log(|t|+2)+1)/(1+t²)`, which is integrable by
`Commons.Analysis.Integral.uScaleHalf_integrable` (`(|t|+3)^(1/2) ≥ 1`). Combine with
`Integrable.mul_prod`. For `AEStronglyMeasurable` of the integrand: `hcont` gives it for the
`f`-factor, `gamDot` is measurable (piecewise formula with `Real.measurable_log`), and all the
zeta/`cpow`/inverse factors are measurable (zeta via its continuity off `1`); put them together and
apply `Integrable.mono'`. (Alternatively use `Integrable.mul_prod`-style domination plus
`Integrable.mono'`, and `aestronglyMeasurable_deriv` + `Integrable.mono'`.) -/
theorem greenTao_kernel_integrable_gam_sigma_cont {β R : ℝ} (hβ : 0 < β) (hβ10 : β ≤ 1 / 10) (hR : 3 ≤ R)
    (f : ℂ → ℂ → ℂ) (B C₁ C₂ : ℝ) (hC1 : 0 < C₁) (hC2 : 0 < C₂)
    (hcont : Continuous (Function.uncurry f))
    (hinvb : ∀ z : ℂ, z ≠ 0 → -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 →
        ‖(riemannZeta (1 + z))⁻¹‖ ≤ C₁ * (Real.log (|z.im| + 2) + 1))
    (hbound : ∀ z z' : ℂ, -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 →
        -(β / Real.log (|z'.im| + 2)) ≤ z'.re → z'.re ≤ 1 → ‖f z z'‖ ≤ B)
    (hnum : ∀ t t' : ℝ, ‖riemannZeta (1 + Commons.Analysis.Complex.gam β t
        + ((1 : ℂ) + (t' : ℂ) * Complex.I))‖ ≤ C₂) :
    MeasureTheory.Integrable (Function.uncurry (fun t t' : ℝ =>
      f (Commons.Analysis.Complex.gam β t) ((1 : ℂ) + (t' : ℂ) * Complex.I)
        * (riemannZeta (1 + Commons.Analysis.Complex.gam β t + ((1 : ℂ) + (t' : ℂ) * Complex.I))
            / (riemannZeta (1 + Commons.Analysis.Complex.gam β t)
                * riemannZeta (1 + ((1 : ℂ) + (t' : ℂ) * Complex.I))))
        * (R : ℂ) ^ (Commons.Analysis.Complex.gam β t + ((1 : ℂ) + (t' : ℂ) * Complex.I))
        / ((Commons.Analysis.Complex.gam β t) ^ 2 * ((1 : ℂ) + (t' : ℂ) * Complex.I) ^ 2)
        * Commons.Analysis.Complex.gamDot β t))
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
  obtain ⟨K, hK0, hKb⟩ := norm_gsIntegrand_le hβ hR f B C₁ C₂ hC1 hC2 hinvb hbound hnum
  obtain ⟨_, _, hu, _⟩ := Commons.Analysis.Integral.uScaleHalf_integrable
  have hu' : Integrable uScaleHalfPt volume := hu
  have hD : Integrable (fun p : ℝ × ℝ => (K * uScaleHalfPt p.1) * uScaleHalfPt p.2)
      (volume.prod volume) := (hu'.const_mul K).mul_prod hu'
  have hmeas : AEStronglyMeasurable (gsIntegrand β R f) (volume.prod volume) :=
    aesm_gsIntegrand (by linarith : 0 < R) f hcont
  have hb : ∀ᵐ p ∂(volume.prod volume),
      ‖gsIntegrand β R f p‖ ≤ (K * uScaleHalfPt p.1) * uScaleHalfPt p.2 :=
    Filter.Eventually.of_forall hKb
  change Integrable (gsIntegrand β R f) (volume.prod volume)
  exact Integrable.mono' hD hmeas hb

end

end Commons.NumberTheory.Zeta

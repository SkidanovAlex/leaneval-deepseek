import Mathlib
import Submission.Commons.NumberTheory.Zeta.zeta_bound_m1
import Submission.Commons.Analysis.Measure.Fubini.integral_fin_cons_split_swap
import Submission.Commons.NumberTheory.Zeta.zetaM1Kernel_eta_bound
import Submission.Commons.NumberTheory.Zeta.zeta_region_inv_analytic_bound_ne
import Submission.Commons.NumberTheory.Zeta.norm_riemannZeta_le_const_of_one_lt_re
import Submission.Commons.NumberTheory.Zeta.zeta_one_add_add_bound_curve_sqrt_curve
import Submission.Commons.Analysis.Integral.uScaleHalf_integrable
import Submission.Commons.NumberTheory.Zeta.gam0_Rz_div_sq_integral_le
import Submission.Commons.NumberTheory.Zeta.gam0_sq_GTG_integral_le
import Submission.Commons.NumberTheory.Zeta.gam0_zeta_quartic_integral_le
import Submission.Commons.NumberTheory.Zeta.gam0_zeta_quartic_integrable
import Submission.Commons.NumberTheory.Zeta.measurable_riemannZeta
import Submission.Commons.NumberTheory.Zeta.measurable_zetaM1Kernel_eta
import Submission.Commons.Analysis.Complex.measurable_gamDot
import Submission.Commons.Analysis.Measure.integrable_weight_prod_fin
import Submission.Commons.Analysis.Measure.integral_fin_one
import Submission.Commons.Analysis.Measure.integral_fin_fin_real_swap
import Submission.Commons.Analysis.Measure.integral_fin_fin_real_real_swap
import Submission.Commons.Analysis.Complex.aemeasurable_deriv_parametric

open Complex MeasureTheory intervalIntegral Filter Set
open scoped Topology Interval

namespace Commons.NumberTheory.Zeta

open MeasureTheory

noncomputable section

open Commons.Analysis.Complex

set_option maxHeartbeats 4000000



/-- The `Γ₀`-contour term `W₁` of the exact `m = 1` contour-shift identity:
`∫_{Γ₀} f(0,ζ) R^ζ / ζ² dζ`. -/
noncomputable def zetaM0W1 (R β : ℝ) (f : ℂ → ℂ → ℂ) : ℂ :=
  ∫ t : ℝ, (f 0 (gam β t) * (R : ℂ) ^ (gam β t)) / (gam β t) ^ 2 * gamDot β t

/-- The `Γ₀ × Γ₀`-contour term `W₂` of the exact `m = 1` contour-shift identity. -/
noncomputable def zetaM0W2 (R β : ℝ) (f : ℂ → ℂ → ℂ) : ℂ :=
  ∫ t : ℝ, (∫ t' : ℝ, zetaM1Kernel R f (gam β t) (gam β t') * gamDot β t') * gamDot β t

/-- The `Γ₀`-contour term `W₃` of the exact `m = 1` contour-shift identity:
`∫_{Γ₀} f(ζ,0) R^ζ / ζ² dζ`. -/
noncomputable def zetaM0W3 (R β : ℝ) (f : ℂ → ℂ → ℂ) : ℂ :=
  ∫ t : ℝ, (f (gam β t) 0 * (R : ℂ) ^ (gam β t)) / (gam β t) ^ 2 * gamDot β t

/-- The `Γ₀`-contour term `W₄` of the exact `m = 1` contour-shift identity:
`∫_{Γ₀} f(ζ,-ζ) / (ζ(1+ζ) ζ(1-ζ) ζ⁴) dζ`. -/
noncomputable def zetaM0W4 (R β : ℝ) (f : ℂ → ℂ → ℂ) : ℂ :=
  ∫ t : ℝ, (f (gam β t) (-(gam β t))
      / (riemannZeta (1 + gam β t) * riemannZeta (1 - gam β t) * (gam β t) ^ 4))
      * gamDot β t


theorem zetaM1Kernel_exact {β R : ℝ} (hβpos : 0 < β) (hβ10 : β ≤ 1 / 10) (hR : 3 ≤ R)
    (f : ℂ → ℂ → ℂ) (B C₁ Cs Cn : ℝ)
    (hC₁pos : 0 < C₁) (hCspos : 0 < Cs) (hCnpos : 0 < Cn)
    (hreg : ∀ z : ℂ, z ≠ 0 → -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 →
        riemannZeta (1 + z) ≠ 0 ∧
        DifferentiableAt ℂ (fun u : ℂ => (riemannZeta (1 + u))⁻¹) z ∧
        ‖(riemannZeta (1 + z))⁻¹‖ ≤ C₁ * (Real.log (|z.im| + 2) + 1))
    (hCs : ∀ z : ℂ, 3 / 2 ≤ z.re → ‖riemannZeta z‖ ≤ Cs)
    (hCn : ∀ z z' : ℂ, -(β / Real.log 2) ≤ z.re → z.re ≤ -(β / Real.log (|z.im| + 2)) →
        -(β / Real.log 2) ≤ z'.re → z'.re ≤ -(β / Real.log (|z'.im| + 2)) →
        ‖riemannZeta (1 + z + z')‖ ≤ Cn * (|z.im| + |z'.im| + 3) ^ ((1:ℝ)/2))
    (hd1 : ∀ z z' : ℂ, -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 →
        -(β / Real.log (|z'.im| + 2)) ≤ z'.re → z'.re ≤ 1 →
        DifferentiableAt ℂ (fun u : ℂ => f u z') z)
    (hd2 : ∀ z z' : ℂ, -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 →
        -(β / Real.log (|z'.im| + 2)) ≤ z'.re → z'.re ≤ 1 →
        DifferentiableAt ℂ (fun u : ℂ => f z u) z')
    (hcont : Continuous (Function.uncurry f))
    (hbound : ∀ z z' : ℂ, -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 →
        -(β / Real.log (|z'.im| + 2)) ≤ z'.re → z'.re ≤ 1 → ‖f z z'‖ ≤ B) :
    (∫ t : ℝ, ∫ t' : ℝ, f (zetaM1Eta R t) (zetaM1Eta R t')
        * (riemannZeta (1 + zetaM1Eta R t + zetaM1Eta R t')
            / (riemannZeta (1 + zetaM1Eta R t) * riemannZeta (1 + zetaM1Eta R t')))
        * (R : ℂ) ^ (zetaM1Eta R t + zetaM1Eta R t')
        / ((zetaM1Eta R t) ^ 2 * (zetaM1Eta R t') ^ 2) * Complex.I * Complex.I)
      = (2 * (Real.pi : ℂ) * Complex.I) ^ 2
          * (f 0 0 * Real.log R + deriv (fun w : ℂ => f 0 w) 0)
        + (2 * (Real.pi : ℂ) * Complex.I) * zetaM0W1 R β f
        + zetaM0W2 R β f
        + (2 * (Real.pi : ℂ) * Complex.I) * (zetaM0W3 R β f + zetaM0W4 R β f) := by
  simp only [zetaM0W1, zetaM0W2, zetaM0W3, zetaM0W4]
  have hinv : ∀ z : ℂ, z ≠ 0 → -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 →
      DifferentiableAt ℂ (fun u : ℂ => (riemannZeta (1 + u))⁻¹) z :=
    fun z hz h1 h2 => (hreg z hz h1 h2).2.1
  have hinvb : ∀ z : ℂ, z ≠ 0 → -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 →
      ‖(riemannZeta (1 + z))⁻¹‖ ≤ C₁ * (Real.log (|z.im| + 2) + 1) :=
    fun z hz h1 h2 => (hreg z hz h1 h2).2.2
  obtain ⟨Ku, hKupos, hUint, hUle⟩ := Commons.Analysis.Integral.uScaleHalf_integrable
  obtain ⟨Cq, hCqpos, hQle⟩ := gam0_zeta_quartic_integral_le (β := β) hβpos hβ10 C₁ hC₁pos hinvb
  have hcc : 0 < Commons.Analysis.Complex.curveConst β :=
    Commons.Analysis.Complex.curveConst_pos hβpos
  set K1 : ℝ := Commons.Analysis.Complex.curveConst β * (∫ t : ℝ, (1 + t ^ 2)⁻¹) with hK1def
  set K2 : ℝ := Cn * C₁ * C₁ * Commons.Analysis.Complex.curveConst β ^ 2 * Ku ^ 2 with hK2def
  set Cbig : ℝ := max 1 ((2 * Real.pi)⁻¹
    * (K1 + K1 + Cq) + (4 * Real.pi ^ 2)⁻¹ * K2) with hCbigdef
  have hCbigpos : 0 < Cbig := by
    rw [hCbigdef]; exact lt_of_lt_of_le one_pos (le_max_left _ _)
  set M : ℂ := (2 * (Real.pi : ℂ) * Complex.I)⁻¹ with hMdef
  have hRpos : 0 < R := by linarith
  have hRone : (1:ℝ) ≤ R := by linarith
  have hlogRpos : 0 < Real.log R := Real.log_pos (by linarith)
  have hpiI : 2 * (Real.pi : ℂ) * Complex.I ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (by norm_num) ?_) Complex.I_ne_zero
    exact_mod_cast Real.pi_ne_zero
  have hMM : M * (2 * (Real.pi : ℂ) * Complex.I) = 1 := by
    rw [hMdef]; exact inv_mul_cancel₀ hpiI
  have hM2 : M ^ 2 * (2 * (Real.pi : ℂ) * Complex.I) ^ 2 = 1 := by
    rw [← mul_pow, hMM]; simp
  have hM21 : M ^ 2 * (2 * (Real.pi : ℂ) * Complex.I) = M := by
    rw [sq, mul_assoc, hMM, mul_one]
  have hnormM : ‖M‖ = (2 * Real.pi)⁻¹ := by
    have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    have hp : ‖(Real.pi : ℂ)‖ = Real.pi := by
      have hsq : ‖(Real.pi : ℂ)‖ ^ 2 = Real.pi ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_ofReal]; ring
      nlinarith [norm_nonneg (Real.pi : ℂ), Real.pi_pos]
    rw [hMdef, norm_inv, norm_mul, norm_mul, h2, hp, Complex.norm_I, mul_one]
  have hnormM2 : ‖M ^ 2‖ = (4 * Real.pi ^ 2)⁻¹ := by
    rw [norm_pow, hnormM, inv_pow]
    congr 1
    ring
  -- region membership of 0
  have hzero_reg : -(β / Real.log (|(0:ℂ).im| + 2)) ≤ (0:ℂ).re := by
    simp only [Complex.zero_im, abs_zero, Complex.zero_re, zero_add]
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have : 0 ≤ β / Real.log 2 := div_nonneg hβpos.le hlog2.le
    linarith
  have hzero_le : (0:ℂ).re ≤ 1 := by simp
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hbound 0 0 hzero_reg hzero_le hzero_reg hzero_le)
  -- basic region facts for `gam`
  have hgam_re : ∀ s : ℝ, (Commons.Analysis.Complex.gam β s).re
      = -(β / Real.log (|s| + 2)) := by
    intro s; simp [Commons.Analysis.Complex.gam, Commons.Analysis.Complex.phi]
  have hgam_im : ∀ s : ℝ, (Commons.Analysis.Complex.gam β s).im = s := by
    intro s; simp [Commons.Analysis.Complex.gam]
  have hbeta_div_le : ∀ s : ℝ, β / Real.log (|s| + 2) ≤ 1 / 2 := by
    intro s
    have hpos : 0 < Real.log (|s| + 2) := Real.log_pos (by linarith [abs_nonneg s])
    rw [div_le_iff₀ hpos]
    have hlog2' : (0.69:ℝ) < Real.log (|s| + 2) := by
      have h1 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
      have h2 : Real.log 2 ≤ Real.log (|s| + 2) :=
        Real.log_le_log (by norm_num) (by linarith [abs_nonneg s])
      linarith
    nlinarith [hβ10, hlog2']
  have hgam_reg : ∀ t : ℝ, -(β / Real.log (|(Commons.Analysis.Complex.gam β t).im| + 2))
      ≤ (Commons.Analysis.Complex.gam β t).re := by
    intro t; rw [hgam_re, hgam_im]
  have hgam_reg' : ∀ t : ℝ, (Commons.Analysis.Complex.gam β t).re
      ≤ -(β / Real.log (|(Commons.Analysis.Complex.gam β t).im| + 2)) := by
    intro t; rw [hgam_re, hgam_im]
  have hgam_le : ∀ t : ℝ, (Commons.Analysis.Complex.gam β t).re ≤ 1 := by
    intro t
    rw [hgam_re, neg_le]
    exact le_trans (by norm_num : (-1:ℝ) ≤ 0)
      (div_nonneg hβpos.le (Real.log_pos (by linarith [abs_nonneg t])).le)
  have hgam_le_neg_one : ∀ t : ℝ, -1 ≤ (Commons.Analysis.Complex.gam β t).re := by
    intro t
    rw [hgam_re]
    exact neg_le_neg (le_trans (hbeta_div_le t) (by norm_num))
  -- numerator bounds
  have hnum_eta_sigma : ∀ t t' : ℝ,
      ‖riemannZeta (1 + zetaM1Eta R t + zetaM1Sigma t')‖ ≤ Cs := by
    intro t t'
    refine hCs _ ?_
    simp only [Complex.add_re, Complex.one_re, zetaM1Eta_re, zetaM1Sigma_re]
    have h := one_div_log_pos hR
    linarith
  have hnum_gam_sigma : ∀ t t' : ℝ,
      ‖riemannZeta (1 + Commons.Analysis.Complex.gam β t + zetaM1Sigma t')‖ ≤ Cs := by
    intro t t'
    refine hCs _ ?_
    rw [show (1 + Commons.Analysis.Complex.gam β t + zetaM1Sigma t').re
        = 2 - β / Real.log (|t| + 2) by
      simp only [Complex.add_re, Complex.one_re, zetaM1Sigma_re, hgam_re]; ring]
    linarith [hbeta_div_le t]
  have hgam_lo : ∀ s : ℝ, -(β / Real.log 2) ≤ (Commons.Analysis.Complex.gam β s).re := by
    intro s
    rw [hgam_re]
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hle : β / Real.log (|s| + 2) ≤ β / Real.log 2 :=
      div_le_div_of_nonneg_left hβpos.le hlog2
        (Real.log_le_log (by norm_num) (by linarith [abs_nonneg s]))
    linarith
  have hnum_gam_gam : ∀ t t' : ℝ,
      ‖riemannZeta (1 + Commons.Analysis.Complex.gam β t + Commons.Analysis.Complex.gam β t')‖
        ≤ Cn * (|t| + |t'| + 3) ^ ((1:ℝ)/2) := by
    intro t t'
    have h := hCn (Commons.Analysis.Complex.gam β t) (Commons.Analysis.Complex.gam β t')
      (hgam_lo t) (hgam_reg' t) (hgam_lo t') (hgam_reg' t')
    simpa [hgam_im] using h
  have hd0 : ∀ z' : ℂ, -(β / Real.log (|z'.im| + 2)) ≤ z'.re → z'.re ≤ 1 →
      DifferentiableAt ℂ (fun u : ℂ => f 0 u) z' :=
    fun z' h1 h2 => hd2 0 z' hzero_reg hzero_le h1 h2
  have hb0 : ∀ z' : ℂ, -(β / Real.log (|z'.im| + 2)) ≤ z'.re → z'.re ≤ 1 → ‖f 0 z'‖ ≤ B :=
    fun z' h1 h2 => hbound 0 z' hzero_reg hzero_le h1 h2
  -- the initial unfolding
  have hE : (fun g1 : ℝ → ℂ =>
          (2 * (Real.pi : ℂ) * Complex.I)⁻¹ ^ 2 *
            ∫ t : ℝ, ∫ t' : ℝ,
              f (g1 t) (g1 t') *
                (riemannZeta (1 + g1 t + g1 t') / (riemannZeta (1 + g1 t) * riemannZeta (1 + g1 t'))) *
                (R : ℂ) ^ (g1 t + g1 t') / ((g1 t) ^ 2 * (g1 t') ^ 2) * Complex.I * Complex.I)
        (fun t => ((1 / Real.log R : ℝ) : ℂ) + (t : ℂ) * Complex.I)
      = M ^ 2 * ∫ t : ℝ,
          (∫ t' : ℝ, zetaM1Kernel R f (zetaM1Eta R t) (zetaM1Eta R t') * Complex.I) * Complex.I := by
    simp only [zetaM1Kernel, zetaM1Eta, hMdef]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards with t
    simp only [MeasureTheory.integral_mul_const]
  -- STEP 1: shift the second variable from Γ₁ to Γ₂ (pointwise in t)
  have hstep1 : M ^ 2 * ∫ t : ℝ,
        (∫ t' : ℝ, zetaM1Kernel R f (zetaM1Eta R t) (zetaM1Eta R t') * Complex.I) * Complex.I
      = M ^ 2 * ∫ t : ℝ,
        (∫ t' : ℝ, zetaM1Kernel R f (zetaM1Eta R t) (zetaM1Sigma t') * Complex.I) * Complex.I := by
    congr 1
    refine integral_congr_ae ?_
    filter_upwards with t
    congr 1
    refine greenTao_shift_Gamma1_to_Gamma2 (β := β) hβpos hβ10 hR f B C₁ hC₁pos hinv hinvb
      hd2 hcont hbound (z := zetaM1Eta R t) (by simp) ?_
    rw [zetaM1Eta_re, zetaM1Eta_im, neg_le]
    exact le_trans (neg_nonpos.mpr (le_of_lt (one_div_log_pos hR)))
      (div_nonneg hβpos.le (Real.log_nonneg (by linarith [abs_nonneg t])))
  -- FUBINI 1
  have hInt1 : MeasureTheory.Integrable (Function.uncurry (fun t t' : ℝ =>
      zetaM1Kernel R f (zetaM1Eta R t) (zetaM1Sigma t')))
      (MeasureTheory.volume.prod MeasureTheory.volume) :=
    greenTao_kernel_integrable_eta_sigma_cont hβpos hβ10 hR f B C₁ Cs hC₁pos hCspos hcont hinvb hbound hnum_eta_sigma
  have hInt1b : MeasureTheory.Integrable (Function.uncurry (fun t t' : ℝ =>
      (zetaM1Kernel R f (zetaM1Eta R t) (zetaM1Sigma t') * Complex.I) * Complex.I))
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
    refine hInt1.neg.congr ?_
    filter_upwards with p
    obtain ⟨a, b⟩ := p
    simp only [Function.uncurry_apply_pair, Pi.neg_apply]
    rw [show (zetaM1Kernel R f (zetaM1Eta R a) (zetaM1Sigma b) * Complex.I) * Complex.I
        = -(zetaM1Kernel R f (zetaM1Eta R a) (zetaM1Sigma b)) by
          rw [mul_assoc, Complex.I_mul_I]; ring]
  have hstep2 : M ^ 2 * ∫ t : ℝ,
        (∫ t' : ℝ, zetaM1Kernel R f (zetaM1Eta R t) (zetaM1Sigma t') * Complex.I) * Complex.I
      = M ^ 2 * ∫ t' : ℝ,
        (∫ t : ℝ, zetaM1Kernel R f (zetaM1Eta R t) (zetaM1Sigma t') * Complex.I) * Complex.I := by
    have hL : (∫ t : ℝ,
          (∫ t' : ℝ, zetaM1Kernel R f (zetaM1Eta R t) (zetaM1Sigma t') * Complex.I) * Complex.I)
        = ∫ t : ℝ, ∫ t' : ℝ,
            (zetaM1Kernel R f (zetaM1Eta R t) (zetaM1Sigma t') * Complex.I) * Complex.I := by
      refine integral_congr_ae ?_
      filter_upwards with t
      simp only [MeasureTheory.integral_mul_const]
    have hR' : (∫ t' : ℝ,
          (∫ t : ℝ, zetaM1Kernel R f (zetaM1Eta R t) (zetaM1Sigma t') * Complex.I) * Complex.I)
        = ∫ t' : ℝ, ∫ t : ℝ,
            (zetaM1Kernel R f (zetaM1Eta R t) (zetaM1Sigma t') * Complex.I) * Complex.I := by
      refine integral_congr_ae ?_
      filter_upwards with t'
      simp only [MeasureTheory.integral_mul_const]
    rw [hL, hR', MeasureTheory.integral_integral_swap hInt1b]
  -- STEP 2: shift the first variable from Γ₁ to Γ₀ (pointwise in t')
  have hstep3 : M ^ 2 * ∫ t' : ℝ,
        (∫ t : ℝ, zetaM1Kernel R f (zetaM1Eta R t) (zetaM1Sigma t') * Complex.I) * Complex.I
      = M ^ 2 * ∫ t' : ℝ, ((∫ t : ℝ,
            zetaM1Kernel R f (Commons.Analysis.Complex.gam β t) (zetaM1Sigma t')
              * Commons.Analysis.Complex.gamDot β t)
          + 2 * (Real.pi : ℂ) * Complex.I *
            (f 0 (zetaM1Sigma t') * (R : ℂ) ^ (zetaM1Sigma t') / (zetaM1Sigma t') ^ 2))
          * Complex.I := by
    congr 1
    refine integral_congr_ae ?_
    filter_upwards with t'
    congr 1
    exact greenTao_single_pole_shift_Gamma2 (β := β) hβpos hβ10 hR f B C₁ hC₁pos hinv hinvb
      hd1 hcont hbound t'
  -- integrability of the two pieces of the split
  have hIntA : MeasureTheory.Integrable (fun t' : ℝ =>
      (∫ t : ℝ, zetaM1Kernel R f (Commons.Analysis.Complex.gam β t) (zetaM1Sigma t')
        * Commons.Analysis.Complex.gamDot β t) * Complex.I) MeasureTheory.volume := by
    have hjoin : MeasureTheory.Integrable (Function.uncurry (fun t t' : ℝ =>
        zetaM1Kernel R f (Commons.Analysis.Complex.gam β t) (zetaM1Sigma t')
          * Commons.Analysis.Complex.gamDot β t)) (MeasureTheory.volume.prod MeasureTheory.volume) :=
      greenTao_kernel_integrable_gam_sigma_cont hβpos hβ10 hR f B C₁ Cs hC₁pos hCspos hcont hinvb hbound hnum_gam_sigma
    exact (hjoin.integral_prod_right).mul_const Complex.I
  have hRne : (R : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hRpos)
  have hIntB : MeasureTheory.Integrable (fun t' : ℝ =>
      (2 * (Real.pi : ℂ) * Complex.I *
        (f 0 (zetaM1Sigma t') * (R : ℂ) ^ (zetaM1Sigma t') / (zetaM1Sigma t') ^ 2))
        * Complex.I) MeasureTheory.volume := by
    have hcont1 : Continuous (fun t' : ℝ =>
        2 * (Real.pi : ℂ) * Complex.I *
          (f 0 (zetaM1Sigma t') * (R : ℂ) ^ (zetaM1Sigma t') / (zetaM1Sigma t') ^ 2)
          * Complex.I) := by
      refine Continuous.mul (Continuous.mul continuous_const ?_) continuous_const
      refine Continuous.div (Continuous.mul ?_ ?_) (zetaM1Sigma_continuous.pow 2) ?_
      · exact hcont.comp (Continuous.prodMk continuous_const zetaM1Sigma_continuous)
      · exact zetaM1Sigma_continuous.const_cpow (Or.inl hRne)
      · intro t' h
        have hz : zetaM1Sigma t' ≠ 0 := by
          intro hz
          have h1 := congrArg Complex.re hz
          simpa [zetaM1Sigma] using h1
        exact pow_ne_zero 2 hz h
    refine Integrable.mono' ((show MeasureTheory.Integrable (fun x : ℝ => (1 + x ^ 2)⁻¹)
        MeasureTheory.volume from integrable_inv_one_add_sq).const_mul (2 * Real.pi * B * R))
      hcont1.aestronglyMeasurable ?_
    filter_upwards with t'
    have hre : -(β / Real.log (|(zetaM1Sigma t').im| + 2)) ≤ (zetaM1Sigma t').re := by
      rw [zetaM1Sigma_re, zetaM1Sigma_im, neg_le]
      exact le_trans (neg_nonpos.mpr zero_le_one)
        (div_nonneg hβpos.le (Real.log_nonneg (by linarith [abs_nonneg t'])))
    have hle : (zetaM1Sigma t').re ≤ 1 := by rw [zetaM1Sigma_re]
    have hb : ‖f 0 (zetaM1Sigma t')‖ ≤ B := hb0 (zetaM1Sigma t') hre hle
    have hR2 : ‖(R : ℂ) ^ (zetaM1Sigma t')‖ ≤ R := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hRpos, zetaM1Sigma_re]
      exact le_of_eq (Real.rpow_one R)
    have hprod : ‖f 0 (zetaM1Sigma t') * (R : ℂ) ^ (zetaM1Sigma t')‖ ≤ B * R := by
      rw [norm_mul]; exact mul_le_mul hb hR2 (norm_nonneg _) hB0
    have hden : ‖(zetaM1Sigma t') ^ 2‖ = 1 + t' ^ 2 := by
      rw [norm_pow, normSq_zetaM1Sigma]
    have hsplit : ‖2 * (Real.pi : ℂ) * Complex.I *
          (f 0 (zetaM1Sigma t') * (R : ℂ) ^ (zetaM1Sigma t') / (zetaM1Sigma t') ^ 2)
          * Complex.I‖
        = ‖(2 : ℂ) * (Real.pi : ℂ)‖ * ‖f 0 (zetaM1Sigma t') * (R : ℂ) ^ (zetaM1Sigma t')‖
            / ‖(zetaM1Sigma t') ^ 2‖ := by
      rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_div, Complex.norm_I, mul_one, mul_one]
      ring
    have hstep : ‖(2 : ℂ) * (Real.pi : ℂ)‖ * ‖f 0 (zetaM1Sigma t') * (R : ℂ) ^ (zetaM1Sigma t')‖
          / ‖(zetaM1Sigma t') ^ 2‖ ≤ (2 * Real.pi * B * R) * (1 + t' ^ 2)⁻¹ := by
      rw [norm_two_pi_complex, hden, div_eq_mul_inv]
      have h2 : (0:ℝ) ≤ (1 + t' ^ 2)⁻¹ := by positivity
      have h3 : (0:ℝ) ≤ 2 * Real.pi := by positivity
      have h4 : (0:ℝ) ≤ B * R := mul_nonneg hB0 (by linarith)
      calc (2 * Real.pi) * ‖f 0 (zetaM1Sigma t') * (R : ℂ) ^ (zetaM1Sigma t')‖ * (1 + t' ^ 2)⁻¹
          ≤ (2 * Real.pi) * (B * R) * (1 + t' ^ 2)⁻¹ := by
            apply mul_le_mul_of_nonneg_right _ h2
            exact mul_le_mul_of_nonneg_left hprod h3
        _ = (2 * Real.pi * B * R) * (1 + t' ^ 2)⁻¹ := by ring
    exact le_trans (le_of_eq hsplit) hstep
  have hstep4 : M ^ 2 * ∫ t' : ℝ, ((∫ t : ℝ,
            zetaM1Kernel R f (Commons.Analysis.Complex.gam β t) (zetaM1Sigma t')
              * Commons.Analysis.Complex.gamDot β t)
          + 2 * (Real.pi : ℂ) * Complex.I *
            (f 0 (zetaM1Sigma t') * (R : ℂ) ^ (zetaM1Sigma t') / (zetaM1Sigma t') ^ 2))
          * Complex.I
      = M ^ 2 * ((∫ t' : ℝ, (∫ t : ℝ,
            zetaM1Kernel R f (Commons.Analysis.Complex.gam β t) (zetaM1Sigma t')
              * Commons.Analysis.Complex.gamDot β t) * Complex.I)
          + ∫ t' : ℝ, (2 * (Real.pi : ℂ) * Complex.I *
              (f 0 (zetaM1Sigma t') * (R : ℂ) ^ (zetaM1Sigma t') / (zetaM1Sigma t') ^ 2))
              * Complex.I) := by
    congr 1
    rw [show (∫ t' : ℝ, ((∫ t : ℝ,
              zetaM1Kernel R f (Commons.Analysis.Complex.gam β t) (zetaM1Sigma t')
                * Commons.Analysis.Complex.gamDot β t)
            + 2 * (Real.pi : ℂ) * Complex.I *
              (f 0 (zetaM1Sigma t') * (R : ℂ) ^ (zetaM1Sigma t') / (zetaM1Sigma t') ^ 2))
            * Complex.I)
        = ∫ t' : ℝ, ((∫ t : ℝ, zetaM1Kernel R f (Commons.Analysis.Complex.gam β t)
              (zetaM1Sigma t') * Commons.Analysis.Complex.gamDot β t) * Complex.I
            + (2 * (Real.pi : ℂ) * Complex.I *
              (f 0 (zetaM1Sigma t') * (R : ℂ) ^ (zetaM1Sigma t') / (zetaM1Sigma t') ^ 2))
              * Complex.I) from by
          refine integral_congr_ae ?_
          filter_upwards with t'
          ring]
    rw [MeasureTheory.integral_add hIntA hIntB]
  -- the double pole at z' = 0
  have hpart2 : (∫ t' : ℝ, (2 * (Real.pi : ℂ) * Complex.I *
        (f 0 (zetaM1Sigma t') * (R : ℂ) ^ (zetaM1Sigma t') / (zetaM1Sigma t') ^ 2)) * Complex.I)
      = 2 * (Real.pi : ℂ) * Complex.I *
        (2 * (Real.pi : ℂ) * Complex.I *
            deriv (fun w : ℂ => f 0 w * (R : ℂ) ^ w) 0
          + (∫ t : ℝ, (f 0 (Commons.Analysis.Complex.gam β t)
              * (R : ℂ) ^ (Commons.Analysis.Complex.gam β t))
              / (Commons.Analysis.Complex.gam β t) ^ 2
              * Commons.Analysis.Complex.gamDot β t)) := by
    rw [show (∫ t' : ℝ, (2 * (Real.pi : ℂ) * Complex.I *
          (f 0 (zetaM1Sigma t') * (R : ℂ) ^ (zetaM1Sigma t') / (zetaM1Sigma t') ^ 2)) * Complex.I)
        = ∫ t' : ℝ, 2 * (Real.pi : ℂ) * Complex.I *
            ((f 0 (zetaM1Sigma t') * (R : ℂ) ^ (zetaM1Sigma t') / (zetaM1Sigma t') ^ 2)
              * Complex.I) from by
          refine integral_congr_ae ?_
          filter_upwards with t'
          ring]
    rw [MeasureTheory.integral_const_mul]
    simp only [zetaM1Sigma]
    rw [greenTao_Gamma2_double_pole (β := β) hβpos hR f B hd0 hb0]
  -- integrability on the Γ₀ side
  have hdot : AEStronglyMeasurable (fun t : ℝ => Commons.Analysis.Complex.gamDot β t)
      MeasureTheory.volume :=
    (aestronglyMeasurable_deriv (Commons.Analysis.Complex.gam β) MeasureTheory.volume).congr
      (by filter_upwards [Commons.Analysis.Complex.ae_ne_zero] with t ht
          rw [(Commons.Analysis.Complex.hasDerivAt_gam (β := β) ht).deriv])
  have hgam_cont : Continuous (fun t : ℝ => (Commons.Analysis.Complex.gam β t) ^ 2) :=
    (Commons.Analysis.Complex.gam_continuous β).pow 2
  have hIntC : MeasureTheory.Integrable (fun t : ℝ =>
      (f (Commons.Analysis.Complex.gam β t) 0 * (R : ℂ) ^ (Commons.Analysis.Complex.gam β t)
        / (Commons.Analysis.Complex.gam β t) ^ 2) * Commons.Analysis.Complex.gamDot β t)
      MeasureTheory.volume := by
    have hcont1 : Continuous (fun t : ℝ =>
        f (Commons.Analysis.Complex.gam β t) 0 * (R : ℂ) ^ (Commons.Analysis.Complex.gam β t)
          / (Commons.Analysis.Complex.gam β t) ^ 2) := by
      refine Continuous.div (Continuous.mul ?_ ?_) hgam_cont ?_
      · exact hcont.comp (Continuous.prodMk (Commons.Analysis.Complex.gam_continuous β) continuous_const)
      · exact (Commons.Analysis.Complex.gam_continuous β).const_cpow (Or.inl hRne)
      · intro t; exact pow_ne_zero 2 (Commons.Analysis.Complex.gam_ne_zero hβpos t)
    refine Integrable.mono' ((show MeasureTheory.Integrable (fun x : ℝ => (1 + x ^ 2)⁻¹)
        MeasureTheory.volume from integrable_inv_one_add_sq).const_mul
        (B * Commons.Analysis.Complex.curveConst β))
      (hcont1.aestronglyMeasurable.mul hdot) ?_
    filter_upwards with t
    have hb : ‖f (Commons.Analysis.Complex.gam β t) 0‖ ≤ B :=
      hbound _ _ (hgam_reg t) (hgam_le t) hzero_reg hzero_le
    have hR2 : ‖(R : ℂ) ^ (Commons.Analysis.Complex.gam β t)‖ ≤ 1 := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hRpos, hgam_re]
      exact Real.rpow_le_one_of_one_le_of_nonpos hRone
        (neg_nonpos.mpr (div_nonneg hβpos.le (Real.log_nonneg (by linarith [abs_nonneg t]))))
    have hmu := Commons.Analysis.Complex.inv_sq_mul_gamDot_norm_le hβpos t
    rw [show (f (Commons.Analysis.Complex.gam β t) 0
            * (R : ℂ) ^ (Commons.Analysis.Complex.gam β t) / (Commons.Analysis.Complex.gam β t) ^ 2)
            * Commons.Analysis.Complex.gamDot β t
        = (f (Commons.Analysis.Complex.gam β t) 0 * (R : ℂ) ^ (Commons.Analysis.Complex.gam β t))
            * (((Commons.Analysis.Complex.gam β t) ^ 2)⁻¹ * Commons.Analysis.Complex.gamDot β t) by ring,
      norm_mul, norm_mul]
    calc ‖f (Commons.Analysis.Complex.gam β t) 0‖
          * ‖(R : ℂ) ^ (Commons.Analysis.Complex.gam β t)‖
          * ‖((Commons.Analysis.Complex.gam β t) ^ 2)⁻¹ * Commons.Analysis.Complex.gamDot β t‖
        ≤ (B * 1) * (Commons.Analysis.Complex.curveConst β * (1 + t ^ 2)⁻¹) :=
          mul_le_mul (mul_le_mul hb hR2 (norm_nonneg _) hB0) hmu (norm_nonneg _) (by positivity)
      _ = (B * Commons.Analysis.Complex.curveConst β) * (1 + t ^ 2)⁻¹ := by ring
  have hneggam : Continuous (fun t : ℝ => -(Commons.Analysis.Complex.gam β t)) :=
    (Commons.Analysis.Complex.gam_continuous β).neg
  have hgam_ne1 : ∀ t : ℝ, 1 + Commons.Analysis.Complex.gam β t ≠ 1 := by
    intro t h
    have h0 : Commons.Analysis.Complex.gam β t = 0 := by
      have := congrArg (fun w : ℂ => w - 1) h; simpa using this
    exact Commons.Analysis.Complex.gam_ne_zero hβpos t h0
  have hgam_ne1' : ∀ t : ℝ, 1 - Commons.Analysis.Complex.gam β t ≠ 1 := by
    intro t h
    have h0 : Commons.Analysis.Complex.gam β t = 0 := by
      have := congrArg (fun w : ℂ => 1 - w) h; simpa using this
    exact Commons.Analysis.Complex.gam_ne_zero hβpos t h0
  have hcontζ1 : Continuous (fun t : ℝ => riemannZeta (1 + Commons.Analysis.Complex.gam β t)) := by
    rw [continuous_iff_continuousAt]
    intro t
    exact ContinuousAt.comp (x := t)
      ((differentiableAt_riemannZeta (hgam_ne1 t)).continuousAt)
      (((continuous_const : Continuous fun _ : ℝ => (1:ℂ)).add
        (Commons.Analysis.Complex.gam_continuous β)).continuousAt)
  have hcontζ2 : Continuous (fun t : ℝ => riemannZeta (1 - Commons.Analysis.Complex.gam β t)) := by
    rw [continuous_iff_continuousAt]
    intro t
    exact ContinuousAt.comp (x := t)
      ((differentiableAt_riemannZeta (hgam_ne1' t)).continuousAt)
      (((continuous_const : Continuous fun _ : ℝ => (1:ℂ)).sub
        (Commons.Analysis.Complex.gam_continuous β)).continuousAt)
  have hzene1 : ∀ t : ℝ, riemannZeta (1 + Commons.Analysis.Complex.gam β t) ≠ 0 :=
    fun t => (hreg (Commons.Analysis.Complex.gam β t)
      (Commons.Analysis.Complex.gam_ne_zero hβpos t) (hgam_reg t) (hgam_le t)).1
  have hreg_neg : ∀ t : ℝ, -(β / Real.log (|(-(Commons.Analysis.Complex.gam β t)).im| + 2))
      ≤ (-(Commons.Analysis.Complex.gam β t)).re := by
    intro t
    have him : (-(Commons.Analysis.Complex.gam β t)).im = -t := by rw [Complex.neg_im, hgam_im]
    have hre : (-(Commons.Analysis.Complex.gam β t)).re = β / Real.log (|t| + 2) := by
      rw [Complex.neg_re, hgam_re]; ring
    rw [him, abs_neg, hre]
    exact neg_le_self (div_nonneg hβpos.le (Real.log_nonneg (by linarith [abs_nonneg t])))
  have hneg_le : ∀ t : ℝ, (-(Commons.Analysis.Complex.gam β t)).re ≤ 1 := by
    intro t
    rw [Complex.neg_re, hgam_re, neg_neg]
    exact le_trans (hbeta_div_le t) (by norm_num)
  have hzene2 : ∀ t : ℝ, riemannZeta (1 - Commons.Analysis.Complex.gam β t) ≠ 0 := by
    intro t
    have := hreg (-(Commons.Analysis.Complex.gam β t))
      (by intro h; exact Commons.Analysis.Complex.gam_ne_zero hβpos t (neg_eq_zero.mp h))
      (hreg_neg t) (hneg_le t)
    simpa [sub_eq_add_neg] using this.1
  have hIntD : MeasureTheory.Integrable (fun t : ℝ =>
      (f (Commons.Analysis.Complex.gam β t) (-(Commons.Analysis.Complex.gam β t))
        / (riemannZeta (1 + Commons.Analysis.Complex.gam β t)
            * riemannZeta (1 - Commons.Analysis.Complex.gam β t)
            * (Commons.Analysis.Complex.gam β t) ^ 4))
        * Commons.Analysis.Complex.gamDot β t) MeasureTheory.volume := by
    have hQint := gam0_zeta_quartic_integrable (β := β) hβpos hβ10 C₁ hC₁pos hinvb
    have hcont1 : Continuous (fun t : ℝ =>
        f (Commons.Analysis.Complex.gam β t) (-(Commons.Analysis.Complex.gam β t))
          / (riemannZeta (1 + Commons.Analysis.Complex.gam β t)
              * riemannZeta (1 - Commons.Analysis.Complex.gam β t)
              * (Commons.Analysis.Complex.gam β t) ^ 4)) := by
      refine Continuous.div ?_ ?_ ?_
      · exact hcont.comp (Continuous.prodMk (Commons.Analysis.Complex.gam_continuous β) hneggam)
      · exact Continuous.mul (Continuous.mul hcontζ1 hcontζ2)
          ((Commons.Analysis.Complex.gam_continuous β).pow 4)
      · intro t
        exact mul_ne_zero (mul_ne_zero (hzene1 t) (hzene2 t))
          (pow_ne_zero 4 (Commons.Analysis.Complex.gam_ne_zero hβpos t))
    refine Integrable.mono' (hQint.const_mul B) (hcont1.aestronglyMeasurable.mul hdot) ?_
    filter_upwards with t
    have hb : ‖f (Commons.Analysis.Complex.gam β t) (-(Commons.Analysis.Complex.gam β t))‖ ≤ B :=
      hbound _ _ (hgam_reg t) (hgam_le t) (hreg_neg t) (hneg_le t)
    have hden : ‖riemannZeta (1 + Commons.Analysis.Complex.gam β t)
          * riemannZeta (1 - Commons.Analysis.Complex.gam β t)
          * (Commons.Analysis.Complex.gam β t) ^ 4‖
        = ‖riemannZeta (1 + Commons.Analysis.Complex.gam β t)‖
          * ‖riemannZeta (1 - Commons.Analysis.Complex.gam β t)‖
          * ‖Commons.Analysis.Complex.gam β t‖ ^ 4 := by
      rw [norm_mul, norm_mul, norm_pow]
    rw [show (f (Commons.Analysis.Complex.gam β t) (-(Commons.Analysis.Complex.gam β t))
            / (riemannZeta (1 + Commons.Analysis.Complex.gam β t)
                * riemannZeta (1 - Commons.Analysis.Complex.gam β t)
                * (Commons.Analysis.Complex.gam β t) ^ 4))
            * Commons.Analysis.Complex.gamDot β t
        = (f (Commons.Analysis.Complex.gam β t) (-(Commons.Analysis.Complex.gam β t)))
            * (Commons.Analysis.Complex.gamDot β t
              / (riemannZeta (1 + Commons.Analysis.Complex.gam β t)
                  * riemannZeta (1 - Commons.Analysis.Complex.gam β t)
                  * (Commons.Analysis.Complex.gam β t) ^ 4)) by ring,
      norm_mul, norm_div, hden]
    exact mul_le_mul hb le_rfl (by positivity) hB0
  have hIntA2 : MeasureTheory.Integrable (fun t : ℝ =>
      (∫ t' : ℝ, zetaM1Kernel R f (Commons.Analysis.Complex.gam β t)
          (Commons.Analysis.Complex.gam β t') * Commons.Analysis.Complex.gamDot β t')
        * Commons.Analysis.Complex.gamDot β t) MeasureTheory.volume := by
    have hjoin : MeasureTheory.Integrable (Function.uncurry (fun t t' : ℝ =>
        zetaM1Kernel R f (Commons.Analysis.Complex.gam β t) (Commons.Analysis.Complex.gam β t')
          * Commons.Analysis.Complex.gamDot β t' * Commons.Analysis.Complex.gamDot β t))
        (MeasureTheory.volume.prod MeasureTheory.volume) := by
      refine (greenTao_kernel_integrable_gam_gam_cont hβpos hβ10 hR f B C₁ Cn hC₁pos hCnpos hcont hinvb hbound
        hnum_gam_gam).congr ?_
      filter_upwards with p
      obtain ⟨a, b⟩ := p
      simp only [Function.uncurry_apply_pair, zetaM1Kernel_eq]
      ring
    refine (hjoin.integral_prod_left).congr ?_
    filter_upwards with t
    simp only [Function.uncurry_apply_pair]
    exact (MeasureTheory.integral_mul_const (Commons.Analysis.Complex.gamDot β t)
      (fun t' : ℝ => zetaM1Kernel R f (Commons.Analysis.Complex.gam β t)
        (Commons.Analysis.Complex.gam β t') * Commons.Analysis.Complex.gamDot β t'))
  have hIntB2 : MeasureTheory.Integrable (fun t : ℝ =>
      (2 * (Real.pi : ℂ) * Complex.I *
        (f (Commons.Analysis.Complex.gam β t) 0 * (R : ℂ) ^ (Commons.Analysis.Complex.gam β t)
          / (Commons.Analysis.Complex.gam β t) ^ 2
          + f (Commons.Analysis.Complex.gam β t) (-(Commons.Analysis.Complex.gam β t))
            / (riemannZeta (1 + Commons.Analysis.Complex.gam β t)
                * riemannZeta (1 - Commons.Analysis.Complex.gam β t)
                * (Commons.Analysis.Complex.gam β t) ^ 4)))
        * Commons.Analysis.Complex.gamDot β t) MeasureTheory.volume := by
    refine ((hIntC.add hIntD).const_mul (2 * (Real.pi : ℂ) * Complex.I)).congr ?_
    filter_upwards with t
    simp only [Pi.add_apply]
    ring
  -- FUBINI 2 and STEP 3 (two poles)
  have hIntGamSigma := greenTao_kernel_integrable_gam_sigma_cont hβpos hβ10 hR f B C₁ Cs hC₁pos hCspos hcont hinvb hbound
    hnum_gam_sigma
  have hIntD3 : MeasureTheory.Integrable (Function.uncurry (fun x y : ℝ =>
      zetaM1Kernel R f (Commons.Analysis.Complex.gam β y) (zetaM1Sigma x)
        * Commons.Analysis.Complex.gamDot β y))
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
    refine (hIntGamSigma.swap).congr ?_
    filter_upwards with p
    obtain ⟨a, b⟩ := p
    simp only [Function.comp_apply, Prod.swap_prod_mk, Function.uncurry_apply_pair, zetaM1Kernel,
      zetaM1Sigma]
  have hpart1 : (∫ t' : ℝ, (∫ t : ℝ, zetaM1Kernel R f (Commons.Analysis.Complex.gam β t)
          (zetaM1Sigma t') * Commons.Analysis.Complex.gamDot β t) * Complex.I)
      = (∫ t : ℝ, (∫ t' : ℝ, zetaM1Kernel R f (Commons.Analysis.Complex.gam β t)
            (Commons.Analysis.Complex.gam β t') * Commons.Analysis.Complex.gamDot β t')
          * Commons.Analysis.Complex.gamDot β t)
        + 2 * (Real.pi : ℂ) * Complex.I *
          ((∫ t : ℝ, (f (Commons.Analysis.Complex.gam β t) 0
              * (R : ℂ) ^ (Commons.Analysis.Complex.gam β t)
              / (Commons.Analysis.Complex.gam β t) ^ 2)
              * Commons.Analysis.Complex.gamDot β t)
            + (∫ t : ℝ, (f (Commons.Analysis.Complex.gam β t)
                (-(Commons.Analysis.Complex.gam β t))
              / (riemannZeta (1 + Commons.Analysis.Complex.gam β t)
                  * riemannZeta (1 - Commons.Analysis.Complex.gam β t)
                  * (Commons.Analysis.Complex.gam β t) ^ 4))
              * Commons.Analysis.Complex.gamDot β t)) := by
    rw [MeasureTheory.integral_mul_const]
    have hswap := MeasureTheory.integral_integral_swap (μ := MeasureTheory.volume)
      (ν := MeasureTheory.volume)
      (f := fun x y : ℝ => zetaM1Kernel R f (Commons.Analysis.Complex.gam β y)
        (zetaM1Sigma x) * Commons.Analysis.Complex.gamDot β y) hIntD3
    rw [hswap]
    rw [← MeasureTheory.integral_mul_const]
    rw [show (∫ t : ℝ, (∫ t' : ℝ, zetaM1Kernel R f (Commons.Analysis.Complex.gam β t)
            (zetaM1Sigma t') * Commons.Analysis.Complex.gamDot β t) * Complex.I)
        = ∫ t : ℝ, (∫ t' : ℝ, zetaM1Kernel R f (Commons.Analysis.Complex.gam β t)
            (zetaM1Sigma t') * Complex.I) * Commons.Analysis.Complex.gamDot β t from by
          refine integral_congr_ae ?_
          filter_upwards with t
          rw [MeasureTheory.integral_mul_const, MeasureTheory.integral_mul_const]
          ring]
    have h2 : (∫ t : ℝ, (∫ t' : ℝ, zetaM1Kernel R f (Commons.Analysis.Complex.gam β t)
            (zetaM1Sigma t') * Complex.I) * Commons.Analysis.Complex.gamDot β t)
        = ∫ t : ℝ, ((∫ t' : ℝ, zetaM1Kernel R f (Commons.Analysis.Complex.gam β t)
              (Commons.Analysis.Complex.gam β t') * Commons.Analysis.Complex.gamDot β t')
            + 2 * (Real.pi : ℂ) * Complex.I *
              (f (Commons.Analysis.Complex.gam β t) 0
                  * (R : ℂ) ^ (Commons.Analysis.Complex.gam β t)
                  / (Commons.Analysis.Complex.gam β t) ^ 2
                + f (Commons.Analysis.Complex.gam β t) (-(Commons.Analysis.Complex.gam β t))
                  / (riemannZeta (1 + Commons.Analysis.Complex.gam β t)
                      * riemannZeta (1 - Commons.Analysis.Complex.gam β t)
                      * (Commons.Analysis.Complex.gam β t) ^ 4)))
            * Commons.Analysis.Complex.gamDot β t := by
      refine integral_congr_ae ?_
      filter_upwards with t
      congr 1
      exact greenTao_two_pole_shift_v4 (β := β) hβpos hβ10 hR f B C₁ Cs Cn hC₁pos hCspos hCnpos
        hinv hinvb hd2 hcont hbound t
        (fun t' => le_trans (hnum_gam_sigma t t') (le_mul_of_one_le_right hCspos.le
          (Real.one_le_rpow (by linarith [abs_nonneg t, abs_nonneg t']) (by norm_num))))
        (fun t' => hnum_gam_gam t t')
    rw [h2]
    rw [show (∫ t : ℝ, ((∫ t' : ℝ, zetaM1Kernel R f (Commons.Analysis.Complex.gam β t)
              (Commons.Analysis.Complex.gam β t') * Commons.Analysis.Complex.gamDot β t')
            + 2 * (Real.pi : ℂ) * Complex.I *
              (f (Commons.Analysis.Complex.gam β t) 0
                  * (R : ℂ) ^ (Commons.Analysis.Complex.gam β t)
                  / (Commons.Analysis.Complex.gam β t) ^ 2
                + f (Commons.Analysis.Complex.gam β t) (-(Commons.Analysis.Complex.gam β t))
                  / (riemannZeta (1 + Commons.Analysis.Complex.gam β t)
                      * riemannZeta (1 - Commons.Analysis.Complex.gam β t)
                      * (Commons.Analysis.Complex.gam β t) ^ 4)))
            * Commons.Analysis.Complex.gamDot β t)
        = ∫ t : ℝ, ((∫ t' : ℝ, zetaM1Kernel R f (Commons.Analysis.Complex.gam β t)
              (Commons.Analysis.Complex.gam β t') * Commons.Analysis.Complex.gamDot β t')
              * Commons.Analysis.Complex.gamDot β t
            + (2 * (Real.pi : ℂ) * Complex.I *
              (f (Commons.Analysis.Complex.gam β t) 0
                  * (R : ℂ) ^ (Commons.Analysis.Complex.gam β t)
                  / (Commons.Analysis.Complex.gam β t) ^ 2
                + f (Commons.Analysis.Complex.gam β t) (-(Commons.Analysis.Complex.gam β t))
                  / (riemannZeta (1 + Commons.Analysis.Complex.gam β t)
                      * riemannZeta (1 - Commons.Analysis.Complex.gam β t)
                      * (Commons.Analysis.Complex.gam β t) ^ 4)))
              * Commons.Analysis.Complex.gamDot β t) from by
          refine integral_congr_ae ?_
          filter_upwards with t
          ring]
    rw [MeasureTheory.integral_add hIntA2 hIntB2]
    rw [show (∫ t : ℝ, (2 * (Real.pi : ℂ) * Complex.I *
              (f (Commons.Analysis.Complex.gam β t) 0
                  * (R : ℂ) ^ (Commons.Analysis.Complex.gam β t)
                  / (Commons.Analysis.Complex.gam β t) ^ 2
                + f (Commons.Analysis.Complex.gam β t) (-(Commons.Analysis.Complex.gam β t))
                  / (riemannZeta (1 + Commons.Analysis.Complex.gam β t)
                      * riemannZeta (1 - Commons.Analysis.Complex.gam β t)
                      * (Commons.Analysis.Complex.gam β t) ^ 4)))
              * Commons.Analysis.Complex.gamDot β t)
        = ∫ t : ℝ, 2 * (Real.pi : ℂ) * Complex.I *
            ((f (Commons.Analysis.Complex.gam β t) 0
                * (R : ℂ) ^ (Commons.Analysis.Complex.gam β t)
                / (Commons.Analysis.Complex.gam β t) ^ 2
              + f (Commons.Analysis.Complex.gam β t) (-(Commons.Analysis.Complex.gam β t))
                / (riemannZeta (1 + Commons.Analysis.Complex.gam β t)
                    * riemannZeta (1 - Commons.Analysis.Complex.gam β t)
                    * (Commons.Analysis.Complex.gam β t) ^ 4))
              * Commons.Analysis.Complex.gamDot β t) from by
          refine integral_congr_ae ?_
          filter_upwards with t
          ring]
    rw [MeasureTheory.integral_const_mul]
    congr 1
    rw [show (∫ t : ℝ, (f (Commons.Analysis.Complex.gam β t) 0
            * (R : ℂ) ^ (Commons.Analysis.Complex.gam β t)
            / (Commons.Analysis.Complex.gam β t) ^ 2
          + f (Commons.Analysis.Complex.gam β t) (-(Commons.Analysis.Complex.gam β t))
            / (riemannZeta (1 + Commons.Analysis.Complex.gam β t)
                * riemannZeta (1 - Commons.Analysis.Complex.gam β t)
                * (Commons.Analysis.Complex.gam β t) ^ 4))
          * Commons.Analysis.Complex.gamDot β t)
        = ∫ t : ℝ, ((f (Commons.Analysis.Complex.gam β t) 0
            * (R : ℂ) ^ (Commons.Analysis.Complex.gam β t)
            / (Commons.Analysis.Complex.gam β t) ^ 2)
            * Commons.Analysis.Complex.gamDot β t
          + (f (Commons.Analysis.Complex.gam β t) (-(Commons.Analysis.Complex.gam β t))
            / (riemannZeta (1 + Commons.Analysis.Complex.gam β t)
                * riemannZeta (1 - Commons.Analysis.Complex.gam β t)
                * (Commons.Analysis.Complex.gam β t) ^ 4))
            * Commons.Analysis.Complex.gamDot β t) from by
          refine integral_congr_ae ?_
          filter_upwards with t
          ring]
    rw [MeasureTheory.integral_add hIntC hIntD]
  -- the four Γ₀ error terms
  set W1 : ℂ := ∫ t : ℝ, (f 0 (Commons.Analysis.Complex.gam β t)
      * (R : ℂ) ^ (Commons.Analysis.Complex.gam β t))
      / (Commons.Analysis.Complex.gam β t) ^ 2
      * Commons.Analysis.Complex.gamDot β t with hW1
  set W2 : ℂ := ∫ t : ℝ, (∫ t' : ℝ, zetaM1Kernel R f (Commons.Analysis.Complex.gam β t)
      (Commons.Analysis.Complex.gam β t') * Commons.Analysis.Complex.gamDot β t')
      * Commons.Analysis.Complex.gamDot β t with hW2
  set W3 : ℂ := ∫ t : ℝ, (f (Commons.Analysis.Complex.gam β t) 0
      * (R : ℂ) ^ (Commons.Analysis.Complex.gam β t)
      / (Commons.Analysis.Complex.gam β t) ^ 2)
      * Commons.Analysis.Complex.gamDot β t with hW3
  set W4 : ℂ := ∫ t : ℝ, (f (Commons.Analysis.Complex.gam β t)
      (-(Commons.Analysis.Complex.gam β t))
      / (riemannZeta (1 + Commons.Analysis.Complex.gam β t)
          * riemannZeta (1 - Commons.Analysis.Complex.gam β t)
          * (Commons.Analysis.Complex.gam β t) ^ 4))
      * Commons.Analysis.Complex.gamDot β t with hW4
  have hW1b : ‖W1‖ ≤ K1 * B := by
    rw [hW1]
    refine le_trans (MeasureTheory.norm_integral_le_integral_norm _) ?_
    have hg : MeasureTheory.Integrable (fun t : ℝ =>
        B * (Commons.Analysis.Complex.curveConst β * (1 + t ^ 2)⁻¹)) MeasureTheory.volume :=
      ((show MeasureTheory.Integrable (fun x : ℝ => (1 + x ^ 2)⁻¹) MeasureTheory.volume
        from integrable_inv_one_add_sq).const_mul
        (Commons.Analysis.Complex.curveConst β)).const_mul B
    refine le_trans (MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun t => norm_nonneg _)) hg
      (Filter.Eventually.of_forall (fun t => ?_))) ?_
    · exact norm_integrand_le hβpos hRone hB0 (fun z => f 0 z) (fun z h1 h2 => hb0 z h1 h2) t
    · have hI1 : (∫ t : ℝ, B * (Commons.Analysis.Complex.curveConst β * (1 + t ^ 2)⁻¹))
          = B * (∫ t : ℝ, Commons.Analysis.Complex.curveConst β * (1 + t ^ 2)⁻¹) :=
        MeasureTheory.integral_const_mul _ _
      have hI2 : (∫ t : ℝ, Commons.Analysis.Complex.curveConst β * (1 + t ^ 2)⁻¹)
          = Commons.Analysis.Complex.curveConst β * (∫ t : ℝ, (1 + t ^ 2)⁻¹) :=
        MeasureTheory.integral_const_mul _ _
      rw [hI1, hI2, hK1def]
      exact le_of_eq (by ring)
  have hW3b : ‖W3‖ ≤ K1 * B := by
    rw [hW3]
    refine le_trans (MeasureTheory.norm_integral_le_integral_norm _) ?_
    have hg : MeasureTheory.Integrable (fun t : ℝ =>
        B * (Commons.Analysis.Complex.curveConst β * (1 + t ^ 2)⁻¹)) MeasureTheory.volume :=
      ((show MeasureTheory.Integrable (fun x : ℝ => (1 + x ^ 2)⁻¹) MeasureTheory.volume
        from integrable_inv_one_add_sq).const_mul
        (Commons.Analysis.Complex.curveConst β)).const_mul B
    refine le_trans (MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun t => norm_nonneg _)) hg
      (Filter.Eventually.of_forall (fun t => ?_))) ?_
    · exact norm_integrand_le hβpos hRone hB0 (fun z => f z 0)
        (fun z h1 h2 => hbound z 0 h1 h2 hzero_reg hzero_le) t
    · have hI1 : (∫ t : ℝ, B * (Commons.Analysis.Complex.curveConst β * (1 + t ^ 2)⁻¹))
          = B * (∫ t : ℝ, Commons.Analysis.Complex.curveConst β * (1 + t ^ 2)⁻¹) :=
        MeasureTheory.integral_const_mul _ _
      have hI2 : (∫ t : ℝ, Commons.Analysis.Complex.curveConst β * (1 + t ^ 2)⁻¹)
          = Commons.Analysis.Complex.curveConst β * (∫ t : ℝ, (1 + t ^ 2)⁻¹) :=
        MeasureTheory.integral_const_mul _ _
      rw [hI1, hI2, hK1def]
      exact le_of_eq (by ring)
  have hW4b : ‖W4‖ ≤ Cq * B := by
    rw [hW4]
    refine le_trans (MeasureTheory.norm_integral_le_integral_norm _) ?_
    have hQint := gam0_zeta_quartic_integrable (β := β) hβpos hβ10 C₁ hC₁pos hinvb
    have hpt : ∀ t : ℝ, ‖(f (Commons.Analysis.Complex.gam β t)
          (-(Commons.Analysis.Complex.gam β t))
          / (riemannZeta (1 + Commons.Analysis.Complex.gam β t)
              * riemannZeta (1 - Commons.Analysis.Complex.gam β t)
              * (Commons.Analysis.Complex.gam β t) ^ 4))
          * Commons.Analysis.Complex.gamDot β t‖
        ≤ B * (‖Commons.Analysis.Complex.gamDot β t‖
            / (‖riemannZeta (1 + Commons.Analysis.Complex.gam β t)‖
                * ‖riemannZeta (1 - Commons.Analysis.Complex.gam β t)‖
                * ‖Commons.Analysis.Complex.gam β t‖ ^ 4)) := by
      intro t
      have hb : ‖f (Commons.Analysis.Complex.gam β t)
          (-(Commons.Analysis.Complex.gam β t))‖ ≤ B :=
        hbound _ _ (hgam_reg t) (hgam_le t) (hreg_neg t) (hneg_le t)
      have hden : ‖riemannZeta (1 + Commons.Analysis.Complex.gam β t)
              * riemannZeta (1 - Commons.Analysis.Complex.gam β t)
              * (Commons.Analysis.Complex.gam β t) ^ 4‖
          = ‖riemannZeta (1 + Commons.Analysis.Complex.gam β t)‖
            * ‖riemannZeta (1 - Commons.Analysis.Complex.gam β t)‖
            * ‖Commons.Analysis.Complex.gam β t‖ ^ 4 := by
        rw [norm_mul, norm_mul, norm_pow]
      rw [show (f (Commons.Analysis.Complex.gam β t) (-(Commons.Analysis.Complex.gam β t))
            / (riemannZeta (1 + Commons.Analysis.Complex.gam β t)
                * riemannZeta (1 - Commons.Analysis.Complex.gam β t)
                * (Commons.Analysis.Complex.gam β t) ^ 4))
            * Commons.Analysis.Complex.gamDot β t
          = f (Commons.Analysis.Complex.gam β t) (-(Commons.Analysis.Complex.gam β t))
            * (Commons.Analysis.Complex.gamDot β t
              / (riemannZeta (1 + Commons.Analysis.Complex.gam β t)
                  * riemannZeta (1 - Commons.Analysis.Complex.gam β t)
                  * (Commons.Analysis.Complex.gam β t) ^ 4)) by ring,
        norm_mul, norm_div, hden]
      exact mul_le_mul hb le_rfl (by positivity) hB0
    refine le_trans (MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun t => norm_nonneg _))
      (hQint.const_mul B) (Filter.Eventually.of_forall hpt)) ?_
    rw [MeasureTheory.integral_const_mul, mul_comm Cq B]
    exact mul_le_mul_of_nonneg_left hQle hB0
  have hW2b : ‖W2‖ ≤ K2 * B := by
    rw [hW2]
    refine le_trans (MeasureTheory.norm_integral_le_integral_norm _) ?_
    set Kg : ℝ := B * Cn * C₁ * C₁ * Commons.Analysis.Complex.curveConst β ^ 2 with hKg
    have hpt : ∀ t : ℝ, ‖(∫ t' : ℝ, zetaM1Kernel R f (Commons.Analysis.Complex.gam β t)
          (Commons.Analysis.Complex.gam β t') * Commons.Analysis.Complex.gamDot β t')
          * Commons.Analysis.Complex.gamDot β t‖
        ≤ (Kg * (∫ s : ℝ, uScale s)) * uScale t := by
      intro t
      have hpt' : ∀ t' : ℝ, ‖zetaM1Kernel R f (Commons.Analysis.Complex.gam β t)
            (Commons.Analysis.Complex.gam β t')
            * Commons.Analysis.Complex.gamDot β t'‖
            * ‖Commons.Analysis.Complex.gamDot β t‖ ≤ (Kg * uScale t) * uScale t' := by
        intro t'
        have h := gamma_gamma_pointwise hβpos hRone f B C₁ Cn hB0 hC₁pos hCnpos hinvb hbound
          hnum_gam_gam t t'
        rw [hKg]
        calc ‖zetaM1Kernel R f (Commons.Analysis.Complex.gam β t)
              (Commons.Analysis.Complex.gam β t')
              * Commons.Analysis.Complex.gamDot β t'‖
              * ‖Commons.Analysis.Complex.gamDot β t‖
            ≤ (B * Cn * C₁ * C₁ * Commons.Analysis.Complex.curveConst β ^ 2)
              * (uScale t * uScale t') := h
          _ = (B * Cn * C₁ * C₁ * Commons.Analysis.Complex.curveConst β ^ 2 * uScale t)
              * uScale t' := by ring
      have hInt : MeasureTheory.Integrable (fun t' : ℝ => (Kg * uScale t) * uScale t')
          MeasureTheory.volume := hUint.const_mul _
      calc ‖(∫ t' : ℝ, zetaM1Kernel R f (Commons.Analysis.Complex.gam β t)
              (Commons.Analysis.Complex.gam β t')
              * Commons.Analysis.Complex.gamDot β t')
            * Commons.Analysis.Complex.gamDot β t‖
          = ‖∫ t' : ℝ, zetaM1Kernel R f (Commons.Analysis.Complex.gam β t)
              (Commons.Analysis.Complex.gam β t')
              * Commons.Analysis.Complex.gamDot β t'‖
            * ‖Commons.Analysis.Complex.gamDot β t‖ := norm_mul _ _
        _ ≤ (∫ t' : ℝ, ‖zetaM1Kernel R f (Commons.Analysis.Complex.gam β t)
              (Commons.Analysis.Complex.gam β t')
              * Commons.Analysis.Complex.gamDot β t'‖)
            * ‖Commons.Analysis.Complex.gamDot β t‖ :=
            mul_le_mul_of_nonneg_right (MeasureTheory.norm_integral_le_integral_norm _) (norm_nonneg _)
        _ = ∫ t' : ℝ, ‖zetaM1Kernel R f (Commons.Analysis.Complex.gam β t)
              (Commons.Analysis.Complex.gam β t')
              * Commons.Analysis.Complex.gamDot β t'‖
            * ‖Commons.Analysis.Complex.gamDot β t‖ :=
            (MeasureTheory.integral_mul_const _ _).symm
        _ ≤ ∫ t' : ℝ, (Kg * uScale t) * uScale t' :=
            MeasureTheory.integral_mono_of_nonneg
              (Filter.Eventually.of_forall (fun t' => by positivity)) hInt
              (Filter.Eventually.of_forall hpt')
        _ = (Kg * uScale t) * (∫ s : ℝ, uScale s) :=
            MeasureTheory.integral_const_mul _ _
        _ = (Kg * (∫ s : ℝ, uScale s)) * uScale t := by ring
    have hdom : MeasureTheory.Integrable (fun t : ℝ => (Kg * (∫ s : ℝ, uScale s)) * uScale t)
        MeasureTheory.volume := hUint.const_mul _
    refine le_trans (MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun t => norm_nonneg _)) hdom
      (Filter.Eventually.of_forall hpt)) ?_
    rw [show (∫ t : ℝ, (Kg * (∫ s : ℝ, uScale s)) * uScale t)
        = (Kg * (∫ s : ℝ, uScale s)) * (∫ s : ℝ, uScale s) from
          MeasureTheory.integral_const_mul _ _]
    have hu0 : 0 ≤ ∫ s : ℝ, uScale s := MeasureTheory.integral_nonneg (fun s => uScale_nonneg s)
    have hsq : (∫ s : ℝ, uScale s) * (∫ s : ℝ, uScale s) ≤ Ku * Ku :=
      mul_le_mul hUle hUle hu0 hKupos.le
    rw [hKg, hK2def]
    calc ((B * Cn * C₁ * C₁ * Commons.Analysis.Complex.curveConst β ^ 2)
            * (∫ s : ℝ, uScale s)) * (∫ s : ℝ, uScale s)
        = B * Cn * C₁ * C₁ * Commons.Analysis.Complex.curveConst β ^ 2
          * ((∫ s : ℝ, uScale s) * (∫ s : ℝ, uScale s)) := by ring
      _ ≤ B * Cn * C₁ * C₁ * Commons.Analysis.Complex.curveConst β ^ 2 * (Ku * Ku) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = Cn * C₁ * C₁ * Commons.Analysis.Complex.curveConst β ^ 2 * Ku ^ 2 * B := by ring
  have hH : deriv (fun w : ℂ => f 0 w * (R : ℂ) ^ w) 0
      = f 0 0 * Real.log R + deriv (fun w : ℂ => f 0 w) 0 := by
    have hd : DifferentiableAt ℂ (fun w : ℂ => f 0 w) 0 := hd0 0 hzero_reg hzero_le
    have hRw : HasDerivAt (fun w : ℂ => (R : ℂ) ^ w) (Real.log R) 0 := by
      have h := (Complex.hasStrictDerivAt_const_cpow (x := (R:ℂ)) (y := 0)
        (Or.inl hRne)).hasDerivAt
      have h2 : (R : ℂ) ^ (0:ℂ) * Complex.log (R : ℂ) = (Real.log R : ℂ) := by
        rw [Complex.cpow_zero, one_mul]
        exact (Complex.ofReal_log (le_of_lt hRpos)).symm
      rwa [h2] at h
    have hmul : deriv (fun w : ℂ => f 0 w * (R : ℂ) ^ w) 0
        = deriv (fun w : ℂ => f 0 w) 0 + f 0 0 * (Real.log R) := by
      have h := (hd.hasDerivAt.mul hRw).deriv
      have h2 : deriv (fun w : ℂ => f 0 w * (R : ℂ) ^ w) 0
          = deriv (fun w : ℂ => f 0 w) 0 * (R : ℂ) ^ (0:ℂ) + f 0 0 * (Real.log R) := h
      rw [Complex.cpow_zero, mul_one] at h2
      exact h2
    rw [hmul]
    ring
  have hres : (fun g1 : ℝ → ℂ =>
          (2 * (Real.pi : ℂ) * Complex.I)⁻¹ ^ 2 *
            ∫ t : ℝ, ∫ t' : ℝ,
              f (g1 t) (g1 t') *
                (riemannZeta (1 + g1 t + g1 t') / (riemannZeta (1 + g1 t) * riemannZeta (1 + g1 t'))) *
                (R : ℂ) ^ (g1 t + g1 t') / ((g1 t) ^ 2 * (g1 t') ^ 2) * Complex.I * Complex.I)
        (fun t => ((1 / Real.log R : ℝ) : ℂ) + (t : ℂ) * Complex.I)
      - (f 0 0 * Real.log R + deriv (fun w : ℂ => f 0 w) 0)
      = M * W1 + M ^ 2 * W2 + M * (W3 + W4) := by
    have hchain : (fun g1 : ℝ → ℂ =>
          (2 * (Real.pi : ℂ) * Complex.I)⁻¹ ^ 2 *
            ∫ t : ℝ, ∫ t' : ℝ,
              f (g1 t) (g1 t') *
                (riemannZeta (1 + g1 t + g1 t') / (riemannZeta (1 + g1 t) * riemannZeta (1 + g1 t'))) *
                (R : ℂ) ^ (g1 t + g1 t') / ((g1 t) ^ 2 * (g1 t') ^ 2) * Complex.I * Complex.I)
        (fun t => ((1 / Real.log R : ℝ) : ℂ) + (t : ℂ) * Complex.I)
        = M ^ 2 * ((W2 + 2 * (Real.pi : ℂ) * Complex.I * (W3 + W4))
            + 2 * (Real.pi : ℂ) * Complex.I *
              (2 * (Real.pi : ℂ) * Complex.I
                  * (f 0 0 * Real.log R + deriv (fun w : ℂ => f 0 w) 0) + W1)) := by
      rw [hE, hstep1, hstep2, hstep3, hstep4, hpart1, hpart2, hH]
    rw [hchain, mul_add, mul_add]
    have hA : M ^ 2 * (2 * (Real.pi : ℂ) * Complex.I * (W3 + W4)) = M * (W3 + W4) := by
      rw [show M ^ 2 * (2 * (Real.pi : ℂ) * Complex.I * (W3 + W4))
          = (M * (2 * (Real.pi : ℂ) * Complex.I)) * (M * (W3 + W4)) by ring, hMM, one_mul]
    have hB : M ^ 2 * (2 * (Real.pi : ℂ) * Complex.I *
        (2 * (Real.pi : ℂ) * Complex.I
            * (f 0 0 * Real.log R + deriv (fun w : ℂ => f 0 w) 0) + W1))
        = (f 0 0 * Real.log R + deriv (fun w : ℂ => f 0 w) 0) + M * W1 := by
      rw [show M ^ 2 * (2 * (Real.pi : ℂ) * Complex.I *
            (2 * (Real.pi : ℂ) * Complex.I
                * (f 0 0 * Real.log R + deriv (fun w : ℂ => f 0 w) 0) + W1))
          = (M * (2 * (Real.pi : ℂ) * Complex.I))
            * (M * (2 * (Real.pi : ℂ) * Complex.I
                * (f 0 0 * Real.log R + deriv (fun w : ℂ => f 0 w) 0) + W1)) by ring,
        hMM, one_mul, mul_add]
      rw [show M * (2 * (Real.pi : ℂ) * Complex.I
            * (f 0 0 * Real.log R + deriv (fun w : ℂ => f 0 w) 0))
          = (M * (2 * (Real.pi : ℂ) * Complex.I))
            * (f 0 0 * Real.log R + deriv (fun w : ℂ => f 0 w) 0) by ring, hMM, one_mul]
    rw [hA, hB]
    ring
  have hsub : (fun g1 : ℝ → ℂ =>
        (2 * (Real.pi : ℂ) * Complex.I)⁻¹ ^ 2 *
          ∫ t : ℝ, ∫ t' : ℝ,
            f (g1 t) (g1 t') *
              (riemannZeta (1 + g1 t + g1 t') / (riemannZeta (1 + g1 t) * riemannZeta (1 + g1 t'))) *
              (R : ℂ) ^ (g1 t + g1 t') / ((g1 t) ^ 2 * (g1 t') ^ 2) * Complex.I * Complex.I)
      (fun t => ((1 / Real.log R : ℝ) : ℂ) + (t : ℂ) * Complex.I)
      = M ^ 2 * (∫ t : ℝ, ∫ t' : ℝ, f (zetaM1Eta R t) (zetaM1Eta R t')
          * (riemannZeta (1 + zetaM1Eta R t + zetaM1Eta R t')
              / (riemannZeta (1 + zetaM1Eta R t) * riemannZeta (1 + zetaM1Eta R t')))
          * (R : ℂ) ^ (zetaM1Eta R t + zetaM1Eta R t')
          / ((zetaM1Eta R t) ^ 2 * (zetaM1Eta R t') ^ 2) * Complex.I * Complex.I) := by
    rw [hMdef]
    simp only [zetaM1Eta]
  have key : M ^ 2 * (∫ t : ℝ, ∫ t' : ℝ, f (zetaM1Eta R t) (zetaM1Eta R t')
        * (riemannZeta (1 + zetaM1Eta R t + zetaM1Eta R t')
            / (riemannZeta (1 + zetaM1Eta R t) * riemannZeta (1 + zetaM1Eta R t')))
        * (R : ℂ) ^ (zetaM1Eta R t + zetaM1Eta R t')
        / ((zetaM1Eta R t) ^ 2 * (zetaM1Eta R t') ^ 2) * Complex.I * Complex.I)
      - (f 0 0 * Real.log R + deriv (fun w : ℂ => f 0 w) 0)
      = M * W1 + M ^ 2 * W2 + M * (W3 + W4) := by
    rw [← hsub]; exact hres
  have h2 : (2 * (Real.pi : ℂ) * Complex.I) ^ 2 *
      (M ^ 2 * (∫ t : ℝ, ∫ t' : ℝ, f (zetaM1Eta R t) (zetaM1Eta R t')
        * (riemannZeta (1 + zetaM1Eta R t + zetaM1Eta R t')
            / (riemannZeta (1 + zetaM1Eta R t) * riemannZeta (1 + zetaM1Eta R t')))
        * (R : ℂ) ^ (zetaM1Eta R t + zetaM1Eta R t')
        / ((zetaM1Eta R t) ^ 2 * (zetaM1Eta R t') ^ 2) * Complex.I * Complex.I))
      = (∫ t : ℝ, ∫ t' : ℝ, f (zetaM1Eta R t) (zetaM1Eta R t')
          * (riemannZeta (1 + zetaM1Eta R t + zetaM1Eta R t')
              / (riemannZeta (1 + zetaM1Eta R t) * riemannZeta (1 + zetaM1Eta R t')))
        * (R : ℂ) ^ (zetaM1Eta R t + zetaM1Eta R t')
        / ((zetaM1Eta R t) ^ 2 * (zetaM1Eta R t') ^ 2) * Complex.I * Complex.I) := by
    rw [← mul_assoc, mul_comm ((2 * (Real.pi : ℂ) * Complex.I) ^ 2) (M ^ 2), hM2, one_mul]
  have hW : (2 * (Real.pi : ℂ) * Complex.I) ^ 2 * (M * W1 + M ^ 2 * W2 + M * (W3 + W4))
      = (2 * (Real.pi : ℂ) * Complex.I) * W1 + W2
        + (2 * (Real.pi : ℂ) * Complex.I) * (W3 + W4) := by
    rw [show (2 * (Real.pi : ℂ) * Complex.I) ^ 2 * (M * W1 + M ^ 2 * W2 + M * (W3 + W4))
        = ((2 * (Real.pi : ℂ) * Complex.I) ^ 2 * M) * W1
          + ((2 * (Real.pi : ℂ) * Complex.I) ^ 2 * M ^ 2) * W2
          + ((2 * (Real.pi : ℂ) * Complex.I) ^ 2 * M) * (W3 + W4) by ring]
    have hA : (2 * (Real.pi : ℂ) * Complex.I) ^ 2 * M = 2 * (Real.pi : ℂ) * Complex.I := by
      rw [sq, mul_assoc, mul_comm (2 * (Real.pi : ℂ) * Complex.I) M, hMM, mul_one]
    have hB : (2 * (Real.pi : ℂ) * Complex.I) ^ 2 * M ^ 2 = 1 := by
      rw [mul_comm, hM2]
    rw [hA, hB, one_mul]
  have hfin := congrArg (fun z : ℂ => (2 * (Real.pi : ℂ) * Complex.I) ^ 2 * z) key
  rw [mul_sub, h2, hW] at hfin
  linear_combination hfin

/-! ## The `m`-fold functional `J_m` -/

/-- The `m`-fold Green–Tao functional, written with the single-pair kernels. -/
noncomputable def zetaMmf (R : ℝ) (m : ℕ)
    (F : (Fin m → ℂ) → (Fin m → ℂ) → ℂ) : ℂ :=
  ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ (2 * m) * Complex.I ^ (2 * m) *
    ∫ t : Fin m → ℝ, ∫ t' : Fin m → ℝ,
      F (fun j => zetaM1Eta R (t j)) (fun j => zetaM1Eta R (t' j))
        * ∏ j, zetaM1Kernel R (fun _ _ => (1:ℂ)) (zetaM1Eta R (t j)) (zetaM1Eta R (t' j))

/-- `R ^ (∑ i ∈ s, f i) = ∏ i ∈ s, R ^ (f i)` for `R ≠ 0`. -/
lemma cpow_finset_sum {ι : Type*} {R : ℂ} (hR : R ≠ 0) (s : Finset ι) (f : ι → ℂ) :
    R ^ (s.sum f) = s.prod (fun i => R ^ f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha, Complex.cpow_add _ _ hR, ih]

/-- Pointwise rewriting of the Green–Tao `m`-fold integrand as a product of single-pair
kernels. -/
lemma zetaMmf_integrand_eq {R : ℝ} (hR : (R : ℂ) ≠ 0) (m : ℕ)
    (F : (Fin m → ℂ) → (Fin m → ℂ) → ℂ) (t t' : Fin m → ℝ) :
    F (fun j => zetaM1Eta R (t j)) (fun j => zetaM1Eta R (t' j))
        * (∏ j, (riemannZeta (1 + zetaM1Eta R (t j) + zetaM1Eta R (t' j))
            / (riemannZeta (1 + zetaM1Eta R (t j)) * riemannZeta (1 + zetaM1Eta R (t' j)))))
        * (R : ℂ) ^ (∑ j, (zetaM1Eta R (t j) + zetaM1Eta R (t' j)))
        * (∏ j, ((zetaM1Eta R (t j)) ^ 2 * (zetaM1Eta R (t' j)) ^ 2)⁻¹)
      = F (fun j => zetaM1Eta R (t j)) (fun j => zetaM1Eta R (t' j))
        * ∏ j, zetaM1Kernel R (fun _ _ => (1:ℂ)) (zetaM1Eta R (t j)) (zetaM1Eta R (t' j)) := by
  rw [cpow_finset_sum hR Finset.univ (fun j => zetaM1Eta R (t j) + zetaM1Eta R (t' j))]
  have hK : ∀ j : Fin m, zetaM1Kernel R (fun _ _ => (1:ℂ)) (zetaM1Eta R (t j)) (zetaM1Eta R (t' j))
      = (riemannZeta (1 + zetaM1Eta R (t j) + zetaM1Eta R (t' j))
          / (riemannZeta (1 + zetaM1Eta R (t j)) * riemannZeta (1 + zetaM1Eta R (t' j))))
        * (R : ℂ) ^ (zetaM1Eta R (t j) + zetaM1Eta R (t' j))
        * ((zetaM1Eta R (t j)) ^ 2 * (zetaM1Eta R (t' j)) ^ 2)⁻¹ := by
    intro j; rw [zetaM1Kernel]; ring
  simp only [hK]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  ring

/-- The full pointwise integrand identity, including the two factors `Complex.I ^ m`. -/
lemma zetaMmf_integrand_eq' {R : ℝ} (hR : (R : ℂ) ≠ 0) (m : ℕ)
    (F : (Fin m → ℂ) → (Fin m → ℂ) → ℂ) (t t' : Fin m → ℝ) :
    F (fun j => zetaM1Eta R (t j)) (fun j => zetaM1Eta R (t' j))
        * (∏ j, (riemannZeta (1 + zetaM1Eta R (t j) + zetaM1Eta R (t' j))
            / (riemannZeta (1 + zetaM1Eta R (t j)) * riemannZeta (1 + zetaM1Eta R (t' j)))))
        * (R : ℂ) ^ (∑ j, (zetaM1Eta R (t j) + zetaM1Eta R (t' j)))
        * (∏ j, ((zetaM1Eta R (t j)) ^ 2 * (zetaM1Eta R (t' j)) ^ 2)⁻¹)
        * Complex.I ^ m * Complex.I ^ m
      = (F (fun j => zetaM1Eta R (t j)) (fun j => zetaM1Eta R (t' j))
        * ∏ j, zetaM1Kernel R (fun _ _ => (1:ℂ)) (zetaM1Eta R (t j)) (zetaM1Eta R (t' j)))
        * (Complex.I ^ m * Complex.I ^ m) := by
  rw [zetaMmf_integrand_eq hR]
  ring

/-- The `m`-fold functional rewritten in the "explicit quotient" shape used in the statement. -/
lemma zetaMmf_eq_explicit {R : ℝ} (hR : (R : ℂ) ≠ 0) (m : ℕ)
    (F : (Fin m → ℂ) → (Fin m → ℂ) → ℂ) :
    zetaMmf R m F
      = ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ (2 * m) *
          ∫ t : Fin m → ℝ, ∫ t' : Fin m → ℝ,
            F (fun j => zetaM1Eta R (t j)) (fun j => zetaM1Eta R (t' j))
              * (∏ j, (riemannZeta (1 + zetaM1Eta R (t j) + zetaM1Eta R (t' j))
                  / (riemannZeta (1 + zetaM1Eta R (t j)) * riemannZeta (1 + zetaM1Eta R (t' j)))))
              * (R : ℂ) ^ (∑ j, (zetaM1Eta R (t j) + zetaM1Eta R (t' j)))
              * (∏ j, ((zetaM1Eta R (t j)) ^ 2 * (zetaM1Eta R (t' j)) ^ 2)⁻¹)
              * Complex.I ^ m * Complex.I ^ m := by
  unfold zetaMmf
  rw [show Complex.I ^ (2 * m) = Complex.I ^ m * Complex.I ^ m by rw [← pow_add]; ring_nf]
  set C : ℂ := Complex.I ^ m * Complex.I ^ m with hCdef
  have hUU : (∫ t : Fin m → ℝ, ∫ t' : Fin m → ℝ,
        ((F (fun j => zetaM1Eta R (t j)) (fun j => zetaM1Eta R (t' j))
          * ∏ j, zetaM1Kernel R (fun _ _ => (1:ℂ)) (zetaM1Eta R (t j)) (zetaM1Eta R (t' j))) * C))
      = ∫ t : Fin m → ℝ, ∫ t' : Fin m → ℝ,
            F (fun j => zetaM1Eta R (t j)) (fun j => zetaM1Eta R (t' j))
              * (∏ j, (riemannZeta (1 + zetaM1Eta R (t j) + zetaM1Eta R (t' j))
                  / (riemannZeta (1 + zetaM1Eta R (t j)) * riemannZeta (1 + zetaM1Eta R (t' j)))))
              * (R : ℂ) ^ (∑ j, (zetaM1Eta R (t j) + zetaM1Eta R (t' j)))
              * (∏ j, ((zetaM1Eta R (t j)) ^ 2 * (zetaM1Eta R (t' j)) ^ 2)⁻¹)
              * Complex.I ^ m * Complex.I ^ m := by
    refine integral_congr_ae ?_
    filter_upwards with t
    refine integral_congr_ae ?_
    filter_upwards with t'
    exact (zetaMmf_integrand_eq' hR m F t t').symm
  have hC : (∫ t : Fin m → ℝ, ∫ t' : Fin m → ℝ,
        F (fun j => zetaM1Eta R (t j)) (fun j => zetaM1Eta R (t' j))
          * ∏ j, zetaM1Kernel R (fun _ _ => (1:ℂ)) (zetaM1Eta R (t j)) (zetaM1Eta R (t' j))) * C
      = ∫ t : Fin m → ℝ, ∫ t' : Fin m → ℝ,
        ((F (fun j => zetaM1Eta R (t j)) (fun j => zetaM1Eta R (t' j))
          * ∏ j, zetaM1Kernel R (fun _ _ => (1:ℂ)) (zetaM1Eta R (t j)) (zetaM1Eta R (t' j))) * C) := by
    rw [← MeasureTheory.integral_mul_const (μ := MeasureTheory.volume) C
      (fun t : Fin m → ℝ => ∫ t' : Fin m → ℝ,
        F (fun j => zetaM1Eta R (t j)) (fun j => zetaM1Eta R (t' j))
          * ∏ j, zetaM1Kernel R (fun _ _ => (1:ℂ)) (zetaM1Eta R (t j)) (zetaM1Eta R (t' j)))]
    refine integral_congr_ae ?_
    filter_upwards with t
    rw [← MeasureTheory.integral_mul_const (μ := MeasureTheory.volume) C
      (fun t' : Fin m → ℝ => F (fun j => zetaM1Eta R (t j)) (fun j => zetaM1Eta R (t' j))
          * ∏ j, zetaM1Kernel R (fun _ _ => (1:ℂ)) (zetaM1Eta R (t j)) (zetaM1Eta R (t' j)))]
  rw [show ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ (2 * m) * C *
        (∫ t : Fin m → ℝ, ∫ t' : Fin m → ℝ,
          F (fun j => zetaM1Eta R (t j)) (fun j => zetaM1Eta R (t' j))
            * ∏ j, zetaM1Kernel R (fun _ _ => (1:ℂ)) (zetaM1Eta R (t j)) (zetaM1Eta R (t' j)))
      = ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ (2 * m) *
        ((∫ t : Fin m → ℝ, ∫ t' : Fin m → ℝ,
          F (fun j => zetaM1Eta R (t j)) (fun j => zetaM1Eta R (t' j))
            * ∏ j, zetaM1Kernel R (fun _ _ => (1:ℂ)) (zetaM1Eta R (t j)) (zetaM1Eta R (t' j))) * C)
      by ring]
  rw [hC, hUU]






/-- The `m = 1` functional with `ℝ`-parametrised contour integrals. -/
noncomputable def zetaMf1 (R : ℝ) (f : ℂ → ℂ → ℂ) : ℂ :=
  ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ 2 * Complex.I ^ 2 *
    ∫ s : ℝ, ∫ s' : ℝ, f (zetaM1Eta R s) (zetaM1Eta R s')
      * zetaM1Kernel R (fun _ _ => (1:ℂ)) (zetaM1Eta R s) (zetaM1Eta R s')


def ZetaReg (β : ℝ) (z : ℂ) : Prop :=
  -(β / Real.log (|z.im| + 2)) ≤ z.re ∧ z.re ≤ 1

lemma zetaReg_zero {β : ℝ} (hβ : 0 < β) : ZetaReg β 0 := by
  constructor
  · rw [Complex.zero_re]
    have h : 0 < β / Real.log (|(0:ℂ).im| + 2) :=
      div_pos hβ (Real.log_pos (by norm_num))
    simpa using neg_nonpos.mpr h.le
  · rw [Complex.zero_re]; norm_num

lemma phi_mem_ZetaReg {β : ℝ} (hβ : 0 < β) (t : ℝ) :
    ZetaReg β (gam β t) := by
  constructor
  · rw [gam_re, gam_im]
  · rw [gam_re]
    have h := phi_lt_c hβ zero_lt_one t
    simpa [phi] using le_of_lt h

lemma eta_mem_ZetaReg {β R : ℝ} (hβ : 0 < β) (hR : 3 ≤ R) (t : ℝ) :
    ZetaReg β (zetaM1Eta R t) := by
  have hlogR : 0 < Real.log R := Real.log_pos (by linarith)
  constructor
  · rw [zetaM1Eta_re, zetaM1Eta_im]
    have h1 : 0 < β / Real.log (|t| + 2) :=
      div_pos hβ (Real.log_pos (by linarith [abs_nonneg t]))
    have h2 : 0 < 1 / Real.log R := div_pos zero_lt_one hlogR
    linarith
  · rw [zetaM1Eta_re]
    exact one_div_log_le_one hR

lemma eta_ne_zero {R : ℝ} (hR : 3 ≤ R) (t : ℝ) : zetaM1Eta R t ≠ 0 := by
  intro h
  have h0 : (zetaM1Eta R t).re = 0 := by rw [h]; simp
  rw [zetaM1Eta_re] at h0
  have := one_div_log_pos hR
  linarith


/-- `β`-region condition on a vector. -/
def ZetaRegVec (β : ℝ) {m : ℕ} (z : Fin m → ℂ) : Prop := ∀ i, ZetaReg β (z i)

lemma ZetaRegVec_cons {β : ℝ} {m : ℕ} {a : ℂ} (ha : ZetaReg β a) {z : Fin m → ℂ}
    (hz : ZetaRegVec β z) : ZetaRegVec β (Fin.cons (α := fun _ => ℂ) a z) := by
  intro i
  induction i using Fin.cases with
  | zero => simpa [Fin.cons_zero] using ha
  | succ j => simpa [Fin.cons_succ] using hz j

lemma ZetaRegVec_eta {β R : ℝ} (hβ : 0 < β) (hR : 3 ≤ R) {m : ℕ} (w : Fin m → ℝ) :
    ZetaRegVec β (fun j => zetaM1Eta R (w j)) := fun j => eta_mem_ZetaReg hβ hR (w j)


/-! ## Bounds for the four `Γ₀`-contour terms -/

lemma zetaM0W1_le {β R : ℝ} (hβ : 0 < β) (hR : 1 ≤ R) (f : ℂ → ℂ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ z : ℂ, ZetaReg β z → ‖f 0 z‖ ≤ B) :
    ‖zetaM0W1 R β f‖
      ≤ (Commons.Analysis.Complex.curveConst β * ∫ t : ℝ, (1 + t ^ 2)⁻¹) * B := by
  rw [zetaM0W1]
  refine le_trans (MeasureTheory.norm_integral_le_integral_norm _) ?_
  have hg : MeasureTheory.Integrable
      (fun t : ℝ => B * (Commons.Analysis.Complex.curveConst β * (1 + t ^ 2)⁻¹))
      MeasureTheory.volume :=
    (integrable_inv_one_add_sq.const_mul (Commons.Analysis.Complex.curveConst β)).const_mul B
  refine le_trans (MeasureTheory.integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun t => norm_nonneg _)) hg
    (Filter.Eventually.of_forall (fun t => ?_))) ?_
  · exact norm_integrand_le hβ hR hB (fun z => f 0 z) (fun z h1 h2 => hbound z ⟨h1, h2⟩) t
  · rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    exact le_of_eq (by ring)

lemma zetaM0W3_le {β R : ℝ} (hβ : 0 < β) (hR : 1 ≤ R) (f : ℂ → ℂ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ z : ℂ, ZetaReg β z → ‖f z 0‖ ≤ B) :
    ‖zetaM0W3 R β f‖
      ≤ (Commons.Analysis.Complex.curveConst β * ∫ t : ℝ, (1 + t ^ 2)⁻¹) * B := by
  rw [zetaM0W3]
  refine le_trans (MeasureTheory.norm_integral_le_integral_norm _) ?_
  have hg : MeasureTheory.Integrable
      (fun t : ℝ => B * (Commons.Analysis.Complex.curveConst β * (1 + t ^ 2)⁻¹))
      MeasureTheory.volume :=
    (integrable_inv_one_add_sq.const_mul (Commons.Analysis.Complex.curveConst β)).const_mul B
  refine le_trans (MeasureTheory.integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun t => norm_nonneg _)) hg
    (Filter.Eventually.of_forall (fun t => ?_))) ?_
  · exact norm_integrand_le hβ hR hB (fun z => f z 0) (fun z h1 h2 => hbound z ⟨h1, h2⟩) t
  · rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    exact le_of_eq (by ring)


lemma neg_phi_mem_ZetaReg {β : ℝ} (hβ : 0 < β) (hβ10 : β ≤ 1 / 10) (t : ℝ) :
    ZetaReg β (-(gam β t)) := by
  have hlog : 0 < Real.log (|t| + 2) := Real.log_pos (by linarith [abs_nonneg t])
  have hβle : β ≤ Real.log 2 := by nlinarith [Real.log_two_gt_d9, hβ10]
  have hlogle : Real.log 2 ≤ Real.log (|t| + 2) := Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
  constructor
  · simp only [Complex.neg_re, Complex.neg_im, gam_re, gam_im, abs_neg]
    have h1 : 0 ≤ β / Real.log (|t| + 2) := div_nonneg hβ.le hlog.le
    linarith
  · simp only [Complex.neg_re, Complex.neg_im, gam_re, gam_im, abs_neg, neg_neg]
    rw [div_le_one hlog]
    linarith

lemma zetaM0W4_le {β R Cq : ℝ} (hβ : 0 < β) (hR : 3 ≤ R) (f : ℂ → ℂ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hQint : MeasureTheory.Integrable (fun t : ℝ =>
      ‖Commons.Analysis.Complex.gamDot β t‖
        / (‖riemannZeta (1 + Commons.Analysis.Complex.gam β t)‖
            * ‖riemannZeta (1 - Commons.Analysis.Complex.gam β t)‖
            * ‖Commons.Analysis.Complex.gam β t‖ ^ 4)))
    (hQle : (∫ t : ℝ, ‖Commons.Analysis.Complex.gamDot β t‖
        / (‖riemannZeta (1 + Commons.Analysis.Complex.gam β t)‖
            * ‖riemannZeta (1 - Commons.Analysis.Complex.gam β t)‖
            * ‖Commons.Analysis.Complex.gam β t‖ ^ 4)) ≤ Cq)
    (hbound : ∀ t : ℝ, ‖f (Commons.Analysis.Complex.gam β t)
        (-(Commons.Analysis.Complex.gam β t))‖ ≤ B) :
    ‖zetaM0W4 R β f‖ ≤ Cq * B := by
  rw [zetaM0W4]
  refine le_trans (MeasureTheory.norm_integral_le_integral_norm _) ?_
  have hpt : ∀ t : ℝ, ‖(f (Commons.Analysis.Complex.gam β t)
        (-(Commons.Analysis.Complex.gam β t))
        / (riemannZeta (1 + Commons.Analysis.Complex.gam β t)
            * riemannZeta (1 - Commons.Analysis.Complex.gam β t)
            * (Commons.Analysis.Complex.gam β t) ^ 4))
        * Commons.Analysis.Complex.gamDot β t‖
      ≤ B * (‖Commons.Analysis.Complex.gamDot β t‖
          / (‖riemannZeta (1 + Commons.Analysis.Complex.gam β t)‖
              * ‖riemannZeta (1 - Commons.Analysis.Complex.gam β t)‖
              * ‖Commons.Analysis.Complex.gam β t‖ ^ 4)) := by
    intro t
    have hb : ‖f (Commons.Analysis.Complex.gam β t) (-(Commons.Analysis.Complex.gam β t))‖ ≤ B :=
      hbound t
    have hden : ‖riemannZeta (1 + Commons.Analysis.Complex.gam β t)
            * riemannZeta (1 - Commons.Analysis.Complex.gam β t)
            * (Commons.Analysis.Complex.gam β t) ^ 4‖
        = ‖riemannZeta (1 + Commons.Analysis.Complex.gam β t)‖
          * ‖riemannZeta (1 - Commons.Analysis.Complex.gam β t)‖
          * ‖Commons.Analysis.Complex.gam β t‖ ^ 4 := by
      rw [norm_mul, norm_mul, norm_pow]
    rw [show (f (Commons.Analysis.Complex.gam β t) (-(Commons.Analysis.Complex.gam β t))
          / (riemannZeta (1 + Commons.Analysis.Complex.gam β t)
              * riemannZeta (1 - Commons.Analysis.Complex.gam β t)
              * (Commons.Analysis.Complex.gam β t) ^ 4))
          * Commons.Analysis.Complex.gamDot β t
        = f (Commons.Analysis.Complex.gam β t) (-(Commons.Analysis.Complex.gam β t))
          * (Commons.Analysis.Complex.gamDot β t
            / (riemannZeta (1 + Commons.Analysis.Complex.gam β t)
                * riemannZeta (1 - Commons.Analysis.Complex.gam β t)
                * (Commons.Analysis.Complex.gam β t) ^ 4)) by ring,
      norm_mul, norm_div, hden]
    exact mul_le_mul hb le_rfl (by positivity) hB
  refine le_trans (MeasureTheory.integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun t => norm_nonneg _))
    (hQint.const_mul B) (Filter.Eventually.of_forall hpt)) ?_
  rw [MeasureTheory.integral_const_mul, mul_comm Cq B]
  exact mul_le_mul_of_nonneg_left hQle hB

lemma zetaM0W2_le {β R Cn C₁ Ku : ℝ} (hβ : 0 < β) (hR : 3 ≤ R)
    (f : ℂ → ℂ → ℂ) (B : ℝ) (hB : 0 ≤ B) (hCn : 0 < Cn) (hC1 : 0 < C₁) (hKu : 0 < Ku)
    (hinvb : ∀ z : ℂ, z ≠ 0 → ZetaReg β z →
        ‖(riemannZeta (1 + z))⁻¹‖ ≤ C₁ * (Real.log (|z.im| + 2) + 1))
    (hnum : ∀ t t' : ℝ, ‖riemannZeta (1 + Commons.Analysis.Complex.gam β t
        + Commons.Analysis.Complex.gam β t')‖ ≤ Cn * (|t| + |t'| + 3) ^ ((1:ℝ)/2))
    (hUint : MeasureTheory.Integrable uScale)
    (hUle : (∫ t : ℝ, uScale t) ≤ Ku)
    (hbound : ∀ z z' : ℂ, ZetaReg β z → ZetaReg β z' → ‖f z z'‖ ≤ B) :
    ‖zetaM0W2 R β f‖
      ≤ Cn * C₁ * C₁ * Commons.Analysis.Complex.curveConst β ^ 2 * Ku ^ 2 * B := by
  rw [zetaM0W2]
  refine le_trans (MeasureTheory.norm_integral_le_integral_norm _) ?_
  have hRone : (1:ℝ) ≤ R := by linarith
  set Kg : ℝ := B * Cn * C₁ * C₁ * Commons.Analysis.Complex.curveConst β ^ 2 with hKg
  have hpt : ∀ t : ℝ, ‖(∫ t' : ℝ, zetaM1Kernel R f (Commons.Analysis.Complex.gam β t)
        (Commons.Analysis.Complex.gam β t') * Commons.Analysis.Complex.gamDot β t')
        * Commons.Analysis.Complex.gamDot β t‖ ≤ (Kg * (∫ s : ℝ, uScale s)) * uScale t := by
    intro t
    have hpt' : ∀ t' : ℝ, ‖zetaM1Kernel R f (Commons.Analysis.Complex.gam β t)
          (Commons.Analysis.Complex.gam β t') * Commons.Analysis.Complex.gamDot β t'‖
          * ‖Commons.Analysis.Complex.gamDot β t‖ ≤ (Kg * uScale t) * uScale t' := by
      intro t'
      have h := gamma_gamma_pointwise hβ hRone f B C₁ Cn hB hC1 hCn
        (fun z hz h1 h2 => hinvb z hz ⟨h1, h2⟩)
        (fun z z' h1 h2 h3 h4 => hbound z z' ⟨h1, h2⟩ ⟨h3, h4⟩) hnum t t'
      rw [hKg]
      calc ‖zetaM1Kernel R f (Commons.Analysis.Complex.gam β t)
            (Commons.Analysis.Complex.gam β t') * Commons.Analysis.Complex.gamDot β t'‖
            * ‖Commons.Analysis.Complex.gamDot β t‖
          ≤ (B * Cn * C₁ * C₁ * Commons.Analysis.Complex.curveConst β ^ 2)
            * (uScale t * uScale t') := h
        _ = (B * Cn * C₁ * C₁ * Commons.Analysis.Complex.curveConst β ^ 2 * uScale t)
            * uScale t' := by ring
    have hInt : MeasureTheory.Integrable (fun t' : ℝ => (Kg * uScale t) * uScale t')
        MeasureTheory.volume := hUint.const_mul _
    calc ‖(∫ t' : ℝ, zetaM1Kernel R f (Commons.Analysis.Complex.gam β t)
            (Commons.Analysis.Complex.gam β t') * Commons.Analysis.Complex.gamDot β t')
          * Commons.Analysis.Complex.gamDot β t‖
        = ‖∫ t' : ℝ, zetaM1Kernel R f (Commons.Analysis.Complex.gam β t)
            (Commons.Analysis.Complex.gam β t') * Commons.Analysis.Complex.gamDot β t'‖
          * ‖Commons.Analysis.Complex.gamDot β t‖ := norm_mul _ _
      _ ≤ (∫ t' : ℝ, ‖zetaM1Kernel R f (Commons.Analysis.Complex.gam β t)
            (Commons.Analysis.Complex.gam β t') * Commons.Analysis.Complex.gamDot β t'‖)
          * ‖Commons.Analysis.Complex.gamDot β t‖ :=
          mul_le_mul_of_nonneg_right (MeasureTheory.norm_integral_le_integral_norm _) (norm_nonneg _)
      _ = ∫ t' : ℝ, ‖zetaM1Kernel R f (Commons.Analysis.Complex.gam β t)
            (Commons.Analysis.Complex.gam β t') * Commons.Analysis.Complex.gamDot β t'‖
          * ‖Commons.Analysis.Complex.gamDot β t‖ :=
          (MeasureTheory.integral_mul_const _ _).symm
      _ ≤ ∫ t' : ℝ, (Kg * uScale t) * uScale t' :=
          MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall (fun t' => by positivity)) hInt
            (Filter.Eventually.of_forall hpt')
      _ = (Kg * uScale t) * (∫ s : ℝ, uScale s) := MeasureTheory.integral_const_mul _ _
      _ = (Kg * (∫ s : ℝ, uScale s)) * uScale t := by ring
  have hdom : MeasureTheory.Integrable (fun t : ℝ => (Kg * (∫ s : ℝ, uScale s)) * uScale t)
      MeasureTheory.volume := hUint.const_mul _
  refine le_trans (MeasureTheory.integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun t => norm_nonneg _)) hdom
    (Filter.Eventually.of_forall hpt)) ?_
  rw [show (∫ t : ℝ, (Kg * (∫ s : ℝ, uScale s)) * uScale t)
      = (Kg * (∫ s : ℝ, uScale s)) * (∫ s : ℝ, uScale s) from
        MeasureTheory.integral_const_mul _ _]
  have hu0 : 0 ≤ ∫ s : ℝ, uScale s := MeasureTheory.integral_nonneg (fun s => uScale_nonneg s)
  have hsq : (∫ s : ℝ, uScale s) * (∫ s : ℝ, uScale s) ≤ Ku * Ku :=
    mul_le_mul hUle hUle hu0 hKu.le
  rw [hKg]
  calc ((B * Cn * C₁ * C₁ * Commons.Analysis.Complex.curveConst β ^ 2)
          * (∫ s : ℝ, uScale s)) * (∫ s : ℝ, uScale s)
      = B * Cn * C₁ * C₁ * Commons.Analysis.Complex.curveConst β ^ 2
        * ((∫ s : ℝ, uScale s) * (∫ s : ℝ, uScale s)) := by ring
    _ ≤ B * Cn * C₁ * C₁ * Commons.Analysis.Complex.curveConst β ^ 2 * (Ku * Ku) :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = Cn * C₁ * C₁ * Commons.Analysis.Complex.curveConst β ^ 2 * Ku ^ 2 * B := by ring

/-! ## The `m = 1` sharp bound -/

noncomputable def zetaRho (β : ℝ) : ℝ := min (β / (4 * Real.log 2)) (1/4)

lemma zetaRho_pos {β : ℝ} (hβ : 0 < β) : 0 < zetaRho β := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [zetaRho]
  exact lt_min (div_pos hβ (by positivity)) (by norm_num)

lemma zetaRho_le_quarter (β : ℝ) : zetaRho β ≤ 1/4 := by
  rw [zetaRho]; exact min_le_right _ _

lemma zetaRho_log_le {β : ℝ} (hβ : 0 < β) (hβ10 : β ≤ 1/10) :
    zetaRho β * Real.log (zetaRho β + 2) ≤ β := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hρle : zetaRho β ≤ β / (4 * Real.log 2) := by rw [zetaRho]; exact min_le_left _ _
  have hρpos : 0 < zetaRho β := zetaRho_pos hβ
  have hρ3 : zetaRho β + 2 ≤ 3 := by
    have := zetaRho_le_quarter β; linarith
  have hρ2 : 0 < zetaRho β + 2 := by linarith
  have hlog : Real.log (zetaRho β + 2) ≤ Real.log 3 := Real.log_le_log hρ2 hρ3
  have hlog3 : Real.log 3 ≤ 2 * Real.log 2 := by
    have : Real.log 3 ≤ Real.log (2 ^ 2) := Real.log_le_log (by norm_num) (by norm_num)
    rwa [Real.log_pow] at this
  have hβle : β ≤ 4 * Real.log 2 := by
    nlinarith [Real.log_two_gt_d9, hβ10]
  calc zetaRho β * Real.log (zetaRho β + 2)
      ≤ (β / (4 * Real.log 2)) * Real.log 3 :=
        mul_le_mul hρle hlog (Real.log_nonneg (by linarith)) (by positivity)
    _ ≤ (β / (4 * Real.log 2)) * (2 * Real.log 2) := by
        exact mul_le_mul_of_nonneg_left hlog3 (by positivity)
    _ = β / 2 := by field_simp; ring
    _ ≤ β := by linarith [hβ]

lemma closedBall_subset_ZetaReg {β : ℝ} (hβ : 0 < β) (hβ10 : β ≤ 1/10) :
    Metric.closedBall (0:ℂ) (zetaRho β) ⊆ {z : ℂ | ZetaReg β z} := by
  intro z hz
  have hzn : ‖z‖ ≤ zetaRho β := by
    rw [Metric.mem_closedBall, dist_zero_right] at hz; exact hz
  have hρpos : 0 < zetaRho β := zetaRho_pos hβ
  constructor
  · have hlogp : 0 < Real.log (|z.im| + 2) := Real.log_pos (by linarith [abs_nonneg z.im])
    have him : |z.im| ≤ zetaRho β := le_trans (Complex.abs_im_le_norm z) hzn
    have hlogle : Real.log (|z.im| + 2) ≤ Real.log (zetaRho β + 2) :=
      Real.log_le_log (by linarith [abs_nonneg z.im]) (by linarith)
    have hrelow : -z.re ≤ zetaRho β := by
      have h1 : -z.re ≤ |z.re| := neg_le_abs z.re
      have h2 : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
      linarith
    have hkey : zetaRho β * Real.log (zetaRho β + 2) ≤ β := zetaRho_log_le hβ hβ10
    have h1 : zetaRho β ≤ β / Real.log (zetaRho β + 2) := by
      rw [le_div_iff₀ (Real.log_pos (by linarith))]; linarith [hkey]
    have h2 : β / Real.log (zetaRho β + 2) ≤ β / Real.log (|z.im| + 2) :=
      div_le_div_of_nonneg_left hβ.le hlogp hlogle
    linarith
  · have hq : zetaRho β ≤ 1 := by have := zetaRho_le_quarter β; linarith
    have hr := Complex.re_le_norm z
    linarith

lemma deriv_bound_ZetaReg {β : ℝ} (hβ : 0 < β) (hβ10 : β ≤ 1/10)
    (g : ℂ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hd : ∀ z : ℂ, ZetaReg β z → DifferentiableAt ℂ g z)
    (hb : ∀ z : ℂ, ZetaReg β z → ‖g z‖ ≤ B) :
    ‖deriv g 0‖ ≤ B / zetaRho β := by
  have hρpos : 0 < zetaRho β := zetaRho_pos hβ
  have hsub := closedBall_subset_ZetaReg hβ hβ10
  have hdiff : DifferentiableOn ℂ g (Metric.closedBall (0:ℂ) (zetaRho β)) :=
    fun z hz => (hd z (hsub hz)).differentiableWithinAt
  have hdc : DiffContOnCl ℂ g (Metric.ball (0:ℂ) (zetaRho β)) := by
    have hcl : closure (Metric.ball (0:ℂ) (zetaRho β)) = Metric.closedBall (0:ℂ) (zetaRho β) :=
      closure_ball _ (ne_of_gt hρpos)
    refine DifferentiableOn.diffContOnCl ?_
    rw [hcl]; exact hdiff
  have hball : ∀ z ∈ Metric.sphere (0:ℂ) (zetaRho β), ‖g z‖ ≤ B := by
    intro z hz
    refine hb z (hsub ?_)
    rw [Metric.mem_closedBall, dist_zero_right]
    exact le_of_eq (by rw [Metric.mem_sphere, dist_zero_right] at hz; exact hz)
  exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρpos hdc hball

lemma zetaMf1_eq {β R : ℝ} (hβ : 0 < β) (hβ10 : β ≤ 1 / 10) (hR : 3 ≤ R)
    (f : ℂ → ℂ → ℂ) (B C₁ Cs Cn : ℝ)
    (hC₁pos : 0 < C₁) (hCspos : 0 < Cs) (hCnpos : 0 < Cn)
    (hreg : ∀ z : ℂ, z ≠ 0 → -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 →
        riemannZeta (1 + z) ≠ 0 ∧
        DifferentiableAt ℂ (fun u : ℂ => (riemannZeta (1 + u))⁻¹) z ∧
        ‖(riemannZeta (1 + z))⁻¹‖ ≤ C₁ * (Real.log (|z.im| + 2) + 1))
    (hCs : ∀ z : ℂ, 3 / 2 ≤ z.re → ‖riemannZeta z‖ ≤ Cs)
    (hCn : ∀ z z' : ℂ, -(β / Real.log 2) ≤ z.re → z.re ≤ -(β / Real.log (|z.im| + 2)) →
        -(β / Real.log 2) ≤ z'.re → z'.re ≤ -(β / Real.log (|z'.im| + 2)) →
        ‖riemannZeta (1 + z + z')‖ ≤ Cn * (|z.im| + |z'.im| + 3) ^ ((1:ℝ)/2))
    (hd1 : ∀ z z' : ℂ, ZetaReg β z → ZetaReg β z' →
        DifferentiableAt ℂ (fun u : ℂ => f u z') z)
    (hd2 : ∀ z z' : ℂ, ZetaReg β z → ZetaReg β z' →
        DifferentiableAt ℂ (fun u : ℂ => f z u) z')
    (hcont : Continuous (Function.uncurry f))
    (hbound : ∀ z z' : ℂ, ZetaReg β z → ZetaReg β z' → ‖f z z'‖ ≤ B) :
    zetaMf1 R f = f 0 0 * Real.log R + deriv (fun w : ℂ => f 0 w) 0
      + (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * zetaM0W1 R β f
      + ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ 2 * zetaM0W2 R β f
      + (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * (zetaM0W3 R β f + zetaM0W4 R β f) := by
  have key := zetaM1Kernel_exact hβ hβ10 hR f B C₁ Cs Cn hC₁pos hCspos hCnpos hreg hCs hCn
    (fun z z' h1 h2 h3 h4 => hd1 z z' ⟨h1, h2⟩ ⟨h3, h4⟩)
    (fun z z' h1 h2 h3 h4 => hd2 z z' ⟨h1, h2⟩ ⟨h3, h4⟩) hcont
    (fun z z' h1 h2 h3 h4 => hbound z z' ⟨h1, h2⟩ ⟨h3, h4⟩)
  have hz : zetaMf1 R f = ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ 2 *
      (∫ t : ℝ, ∫ t' : ℝ, f (zetaM1Eta R t) (zetaM1Eta R t')
        * (riemannZeta (1 + zetaM1Eta R t + zetaM1Eta R t')
            / (riemannZeta (1 + zetaM1Eta R t) * riemannZeta (1 + zetaM1Eta R t')))
        * (R : ℂ) ^ (zetaM1Eta R t + zetaM1Eta R t')
        / ((zetaM1Eta R t) ^ 2 * (zetaM1Eta R t') ^ 2) * Complex.I * Complex.I) := by
    rw [zetaMf1, mul_assoc]
    simp only [zetaM1Kernel, Pi.one_apply, one_mul]
    congr 1
    rw [← MeasureTheory.integral_const_mul (μ := MeasureTheory.volume) (Complex.I ^ 2)]
    refine integral_congr_ae ?_
    filter_upwards with t
    rw [← MeasureTheory.integral_const_mul (μ := MeasureTheory.volume) (Complex.I ^ 2)]
    refine integral_congr_ae ?_
    filter_upwards with t'
    ring
  rw [hz, key]
  set M : ℂ := (2 * (Real.pi : ℂ) * Complex.I)⁻¹ with hMdef
  have hpiI : 2 * (Real.pi : ℂ) * Complex.I ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (by norm_num) ?_) Complex.I_ne_zero
    exact_mod_cast Real.pi_ne_zero
  have hMM : M * (2 * (Real.pi : ℂ) * Complex.I) = 1 := by
    rw [hMdef]; exact inv_mul_cancel₀ hpiI
  have hA : M ^ 2 * (2 * (Real.pi : ℂ) * Complex.I) ^ 2 = 1 := by
    rw [← mul_pow, hMM]; simp
  have hB' : M ^ 2 * (2 * (Real.pi : ℂ) * Complex.I) = M := by
    rw [sq, mul_assoc, hMM, mul_one]
  have harith : M ^ 2 * ((2 * (Real.pi : ℂ) * Complex.I) ^ 2
        * (f 0 0 * Real.log R + deriv (fun w : ℂ => f 0 w) 0)
      + (2 * (Real.pi : ℂ) * Complex.I) * zetaM0W1 R β f
      + zetaM0W2 R β f
      + (2 * (Real.pi : ℂ) * Complex.I) * (zetaM0W3 R β f + zetaM0W4 R β f))
      = f 0 0 * Real.log R + deriv (fun w : ℂ => f 0 w) 0
        + M * zetaM0W1 R β f + M ^ 2 * zetaM0W2 R β f
        + M * (zetaM0W3 R β f + zetaM0W4 R β f) := by
    rw [show M ^ 2 * ((2 * (Real.pi : ℂ) * Complex.I) ^ 2
          * (f 0 0 * Real.log R + deriv (fun w : ℂ => f 0 w) 0)
        + (2 * (Real.pi : ℂ) * Complex.I) * zetaM0W1 R β f
        + zetaM0W2 R β f
        + (2 * (Real.pi : ℂ) * Complex.I) * (zetaM0W3 R β f + zetaM0W4 R β f))
        = (M ^ 2 * (2 * (Real.pi : ℂ) * Complex.I) ^ 2)
            * (f 0 0 * Real.log R + deriv (fun w : ℂ => f 0 w) 0)
          + (M ^ 2 * (2 * (Real.pi : ℂ) * Complex.I)) * zetaM0W1 R β f
          + M ^ 2 * zetaM0W2 R β f
          + (M ^ 2 * (2 * (Real.pi : ℂ) * Complex.I)) * (zetaM0W3 R β f + zetaM0W4 R β f)
        from by ring]
    rw [hA, hB', one_mul]
  rw [harith]

lemma zetaMf1_sharp {β R : ℝ} (hβ : 0 < β) (hβ10 : β ≤ 1 / 10) (hR : 3 ≤ R)
    (f : ℂ → ℂ → ℂ) (B C₁ Cs Cn Ku Cq : ℝ)
    (hC₁pos : 0 < C₁) (hCspos : 0 < Cs) (hCnpos : 0 < Cn) (hKupos : 0 < Ku)
    (hreg : ∀ z : ℂ, z ≠ 0 → -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 →
        riemannZeta (1 + z) ≠ 0 ∧
        DifferentiableAt ℂ (fun u : ℂ => (riemannZeta (1 + u))⁻¹) z ∧
        ‖(riemannZeta (1 + z))⁻¹‖ ≤ C₁ * (Real.log (|z.im| + 2) + 1))
    (hCs : ∀ z : ℂ, 3 / 2 ≤ z.re → ‖riemannZeta z‖ ≤ Cs)
    (hCn : ∀ z z' : ℂ, -(β / Real.log 2) ≤ z.re → z.re ≤ -(β / Real.log (|z.im| + 2)) →
        -(β / Real.log 2) ≤ z'.re → z'.re ≤ -(β / Real.log (|z'.im| + 2)) →
        ‖riemannZeta (1 + z + z')‖ ≤ Cn * (|z.im| + |z'.im| + 3) ^ ((1:ℝ)/2))
    (hd1 : ∀ z z' : ℂ, ZetaReg β z → ZetaReg β z' →
        DifferentiableAt ℂ (fun u : ℂ => f u z') z)
    (hd2 : ∀ z z' : ℂ, ZetaReg β z → ZetaReg β z' →
        DifferentiableAt ℂ (fun u : ℂ => f z u) z')
    (hcont : Continuous (Function.uncurry f))
    (hbound : ∀ z z' : ℂ, ZetaReg β z → ZetaReg β z' → ‖f z z'‖ ≤ B) (hB : 0 ≤ B)
    (hnum : ∀ t t' : ℝ, ‖riemannZeta (1 + Commons.Analysis.Complex.gam β t
        + Commons.Analysis.Complex.gam β t')‖ ≤ Cn * (|t| + |t'| + 3) ^ ((1:ℝ)/2))
    (hUint : MeasureTheory.Integrable uScale)
    (hUle : (∫ t : ℝ, uScale t) ≤ Ku)
    (hQint : MeasureTheory.Integrable (fun t : ℝ =>
      ‖Commons.Analysis.Complex.gamDot β t‖
        / (‖riemannZeta (1 + Commons.Analysis.Complex.gam β t)‖
            * ‖riemannZeta (1 - Commons.Analysis.Complex.gam β t)‖
            * ‖Commons.Analysis.Complex.gam β t‖ ^ 4)))
    (hQle : (∫ t : ℝ, ‖Commons.Analysis.Complex.gamDot β t‖
        / (‖riemannZeta (1 + Commons.Analysis.Complex.gam β t)‖
            * ‖riemannZeta (1 - Commons.Analysis.Complex.gam β t)‖
            * ‖Commons.Analysis.Complex.gam β t‖ ^ 4)) ≤ Cq) :
    ‖zetaMf1 R f - (f 0 0 * Real.log R + deriv (fun w : ℂ => f 0 w) 0)‖
      ≤ ((2 * Real.pi)⁻¹
            * (2 * (Commons.Analysis.Complex.curveConst β * ∫ t : ℝ, (1 + t ^ 2)⁻¹) + Cq)
          + (2 * Real.pi)⁻¹ ^ 2
            * (Cn * C₁ * C₁ * Commons.Analysis.Complex.curveConst β ^ 2 * Ku ^ 2)
          + 1 / zetaRho β) * B := by
  have hinvb : ∀ z : ℂ, z ≠ 0 → ZetaReg β z →
      ‖(riemannZeta (1 + z))⁻¹‖ ≤ C₁ * (Real.log (|z.im| + 2) + 1) :=
    fun z hz h => (hreg z hz h.1 h.2).2.2
  have hid := zetaMf1_eq hβ hβ10 hR f B C₁ Cs Cn hC₁pos hCspos hCnpos hreg hCs hCn
    hd1 hd2 hcont hbound
  set K1 : ℝ := Commons.Analysis.Complex.curveConst β * ∫ t : ℝ, (1 + t ^ 2)⁻¹ with hK1
  set K2 : ℝ := Cn * C₁ * C₁ * Commons.Analysis.Complex.curveConst β ^ 2 * Ku ^ 2 with hK2
  have hW1 : ‖zetaM0W1 R β f‖ ≤ K1 * B :=
    zetaM0W1_le hβ (by linarith) f B hB (fun z hz => hbound 0 z (zetaReg_zero hβ) hz)
  have hW3 : ‖zetaM0W3 R β f‖ ≤ K1 * B :=
    zetaM0W3_le hβ (by linarith) f B hB (fun z hz => hbound z 0 hz (zetaReg_zero hβ))
  have hW4 : ‖zetaM0W4 R β f‖ ≤ Cq * B :=
    zetaM0W4_le hβ hR f B hB hQint hQle
      (fun t => hbound (gam β t) (-(gam β t)) (phi_mem_ZetaReg hβ t) (neg_phi_mem_ZetaReg hβ hβ10 t))
  have hW2 : ‖zetaM0W2 R β f‖ ≤ K2 * B := by
    rw [hK2]
    exact zetaM0W2_le hβ hR f B hB hCnpos hC₁pos hKupos hinvb hnum hUint hUle hbound
  have hder : ‖deriv (fun w : ℂ => f 0 w) 0‖ ≤ B / zetaRho β :=
    deriv_bound_ZetaReg hβ hβ10 (fun w => f 0 w) B hB
      (fun z hz => hd2 0 z (zetaReg_zero hβ) hz) (fun z hz => hbound 0 z (zetaReg_zero hβ) hz)
  have hMnorm : ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹‖ = (2 * Real.pi)⁻¹ := by
    rw [norm_inv, norm_mul, norm_mul, Complex.norm_I, mul_one]
    have h2 : ‖(2:ℂ)‖ = 2 := by norm_num
    have hp : ‖(Real.pi : ℂ)‖ = Real.pi := by
      have hsq : ‖(Real.pi : ℂ)‖ ^ 2 = Real.pi ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_ofReal]; ring
      nlinarith [norm_nonneg (Real.pi : ℂ), Real.pi_pos]
    rw [h2, hp]
  have hM2norm : ‖((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ 2‖ = (2 * Real.pi)⁻¹ ^ 2 := by
    rw [norm_pow, hMnorm]
  have hrearr : zetaMf1 R f - (f 0 0 * Real.log R + deriv (fun w : ℂ => f 0 w) 0)
      = zetaM0W1 R β f * ((2 * (Real.pi : ℂ) * Complex.I)⁻¹)
        + zetaM0W2 R β f * ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ 2
        + (zetaM0W3 R β f + zetaM0W4 R β f) * ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) := by
    rw [hid]; ring
  rw [hrearr]
  calc ‖zetaM0W1 R β f * ((2 * (Real.pi : ℂ) * Complex.I)⁻¹)
      + zetaM0W2 R β f * ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ 2
      + (zetaM0W3 R β f + zetaM0W4 R β f) * ((2 * (Real.pi : ℂ) * Complex.I)⁻¹)‖
      ≤ ‖zetaM0W1 R β f * ((2 * (Real.pi : ℂ) * Complex.I)⁻¹)‖
        + ‖zetaM0W2 R β f * ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ 2‖
        + ‖(zetaM0W3 R β f + zetaM0W4 R β f) * ((2 * (Real.pi : ℂ) * Complex.I)⁻¹)‖ := by
        have h1 := norm_add_le (zetaM0W1 R β f * ((2 * (Real.pi : ℂ) * Complex.I)⁻¹)
          + zetaM0W2 R β f * ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ 2)
          ((zetaM0W3 R β f + zetaM0W4 R β f) * ((2 * (Real.pi : ℂ) * Complex.I)⁻¹))
        have h2 := norm_add_le (zetaM0W1 R β f * ((2 * (Real.pi : ℂ) * Complex.I)⁻¹))
          (zetaM0W2 R β f * ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ 2)
        linarith
    _ = ‖zetaM0W1 R β f‖ * (2 * Real.pi)⁻¹
        + ‖zetaM0W2 R β f‖ * (2 * Real.pi)⁻¹ ^ 2
        + ‖zetaM0W3 R β f + zetaM0W4 R β f‖ * (2 * Real.pi)⁻¹ := by
        rw [norm_mul, norm_mul, norm_mul, hMnorm, hM2norm]
    _ ≤ ((2 * Real.pi)⁻¹ * (K1 + K1 + Cq) + (2 * Real.pi)⁻¹ ^ 2 * K2) * B := by
        have h34 : ‖zetaM0W3 R β f + zetaM0W4 R β f‖ ≤ K1 * B + Cq * B := by
          have h := norm_add_le (zetaM0W3 R β f) (zetaM0W4 R β f)
          linarith
        have h1 : ‖zetaM0W1 R β f‖ * (2 * Real.pi)⁻¹ ≤ K1 * B * (2 * Real.pi)⁻¹ :=
          mul_le_mul_of_nonneg_right hW1 (by positivity)
        have h2 : ‖zetaM0W2 R β f‖ * (2 * Real.pi)⁻¹ ^ 2 ≤ K2 * B * (2 * Real.pi)⁻¹ ^ 2 :=
          mul_le_mul_of_nonneg_right hW2 (by positivity)
        have h3 : ‖zetaM0W3 R β f + zetaM0W4 R β f‖ * (2 * Real.pi)⁻¹
            ≤ (K1 * B + Cq * B) * (2 * Real.pi)⁻¹ :=
          mul_le_mul_of_nonneg_right h34 (by positivity)
        linarith [h1, h2, h3]
    _ = (((2 * Real.pi)⁻¹
            * (2 * (Commons.Analysis.Complex.curveConst β * ∫ t : ℝ, (1 + t ^ 2)⁻¹) + Cq)
          + (2 * Real.pi)⁻¹ ^ 2
            * (Cn * C₁ * C₁ * Commons.Analysis.Complex.curveConst β ^ 2 * Ku ^ 2))) * B := by
        rw [hK1, hK2]; ring
    _ ≤ ((2 * Real.pi)⁻¹
            * (2 * (Commons.Analysis.Complex.curveConst β * ∫ t : ℝ, (1 + t ^ 2)⁻¹) + Cq)
          + (2 * Real.pi)⁻¹ ^ 2
            * (Cn * C₁ * C₁ * Commons.Analysis.Complex.curveConst β ^ 2 * Ku ^ 2)
          + 1 / zetaRho β) * B := by
        refine mul_le_mul_of_nonneg_right ?_ hB
        linarith [one_div_pos.mpr (zetaRho_pos hβ)]


/-! ## The `(2π)^{2m}`-normalised `m`-fold functional -/

/-- The product of single-pair kernels along `Γ₁`. -/
noncomputable def WmK (R : ℝ) (m : ℕ) (w w' : Fin m → ℝ) : ℂ :=
  ∏ j, zetaM1Kernel R (fun _ _ => (1:ℂ)) (zetaM1Eta R (w j)) (zetaM1Eta R (w' j))

/-- The weight of the `Γ₀`-single-pole term. -/
noncomputable def gW1 (R β : ℝ) (t : ℝ) : ℂ :=
  (R : ℂ) ^ (Commons.Analysis.Complex.gam β t) / (Commons.Analysis.Complex.gam β t) ^ 2
    * Commons.Analysis.Complex.gamDot β t

/-- The weight of the `Γ₀`-quartic term. -/
noncomputable def gW4 (β : ℝ) (t : ℝ) : ℂ :=
  (riemannZeta (1 + Commons.Analysis.Complex.gam β t)
      * riemannZeta (1 - Commons.Analysis.Complex.gam β t)
      * (Commons.Analysis.Complex.gam β t) ^ 4)⁻¹
    * Commons.Analysis.Complex.gamDot β t

lemma measurable_comp_pair {m : ℕ} {g : ℝ × ℝ → ℂ} (hg : Measurable g) (j : Fin m) :
    Measurable (fun p : (Fin m → ℝ) × (Fin m → ℝ) => g (p.1 j, p.2 j)) :=
  hg.comp ((((continuous_apply j).comp continuous_fst).prodMk
      ((continuous_apply j).comp continuous_snd)).measurable)

lemma measurable_WmK (R : ℝ) (hR : R ≠ 0) (m : ℕ) :
    Measurable (fun p : (Fin m → ℝ) × (Fin m → ℝ) => WmK R m p.1 p.2) := by
  have hfac : ∀ j : Fin m, Measurable (fun p : (Fin m → ℝ) × (Fin m → ℝ) =>
      zetaM1Kernel R (fun _ _ => (1:ℂ)) (zetaM1Eta R (p.1 j)) (zetaM1Eta R (p.2 j))) := by
    intro j
    exact measurable_comp_pair
      (g := fun r : ℝ × ℝ => zetaM1Kernel R (fun _ _ => (1:ℂ)) (zetaM1Eta R r.1) (zetaM1Eta R r.2))
      (measurable_zetaM1Kernel_eta hR) j
  have h := Finset.measurable_prod (M := ℂ) (Finset.univ : Finset (Fin m)) (fun j _ => hfac j)
  have h2 : Measurable (fun p : (Fin m → ℝ) × (Fin m → ℝ) =>
      ∏ j, zetaM1Kernel R (fun _ _ => (1:ℂ)) (zetaM1Eta R (p.1 j)) (zetaM1Eta R (p.2 j))) := by
    simpa using h
  exact h2

lemma two_pi_pow_mul {m : ℕ} :
    ((2:ℂ)*(Real.pi:ℂ))^(2*m) * (((2*(Real.pi:ℂ)*Complex.I)⁻¹)^(2*m) * Complex.I^(2*m)) = 1 := by
  have hI : (Complex.I:ℂ)^(2*m) ≠ 0 := pow_ne_zero _ Complex.I_ne_zero
  have ha : ((2:ℂ)*(Real.pi:ℂ))^(2*m) ≠ 0 := by
    refine pow_ne_zero _ ?_
    have : ((2:ℂ)*(Real.pi:ℂ)) = ((2*Real.pi : ℝ) : ℂ) := by push_cast; ring
    rw [this]
    exact_mod_cast (by positivity : (2*Real.pi : ℝ) ≠ 0)
  have key : ((2*(Real.pi:ℂ)*Complex.I)⁻¹)^(2*m)
      = (((2:ℂ)*(Real.pi:ℂ))^(2*m))⁻¹ * ((Complex.I:ℂ)^(2*m))⁻¹ := by
    rw [inv_pow, show (2*(Real.pi:ℂ)*Complex.I)^(2*m)
        = ((2:ℂ)*(Real.pi:ℂ))^(2*m) * Complex.I^(2*m) from by
          rw [show (2*(Real.pi:ℂ)*Complex.I) = ((2:ℂ)*(Real.pi:ℂ))*Complex.I by ring, mul_pow],
      mul_inv]
  rw [key, show ((2:ℂ)*(Real.pi:ℂ))^(2*m)
        * ((((2:ℂ)*(Real.pi:ℂ))^(2*m))⁻¹ * ((Complex.I:ℂ)^(2*m))⁻¹ * (Complex.I:ℂ)^(2*m))
      = (((2:ℂ)*(Real.pi:ℂ))^(2*m) * (((2:ℂ)*(Real.pi:ℂ))^(2*m))⁻¹)
        * (((Complex.I:ℂ)^(2*m))⁻¹ * (Complex.I:ℂ)^(2*m)) by ring,
    mul_inv_cancel₀ ha, inv_mul_cancel₀ hI, mul_one]

/-- `(2π)^{2m}` times the `m`-fold functional is the `m`-fold integral. -/
lemma two_pi_pow_mul_zetaMmf {R : ℝ} (m : ℕ)
    (G : (Fin m → ℂ) → (Fin m → ℂ) → ℂ) :
    ((2:ℂ)*(Real.pi:ℂ))^(2*m) * zetaMmf R m G
      = ∫ w : Fin m → ℝ, ∫ w' : Fin m → ℝ,
          G (fun j => zetaM1Eta R (w j)) (fun j => zetaM1Eta R (w' j)) * WmK R m w w' := by
  simp only [zetaMmf, WmK]
  rw [← mul_assoc, two_pi_pow_mul, one_mul]


lemma measurable_gW1 (R β : ℝ) (hR : R ≠ 0) : Measurable (gW1 R β) := by
  have hRne : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR
  have hcp : Measurable (fun t : ℝ => (R : ℂ) ^ (Commons.Analysis.Complex.gam β t)) := by
    have heq : (fun t : ℝ => (R : ℂ) ^ (Commons.Analysis.Complex.gam β t))
        = fun t => Complex.exp (Complex.log (R : ℂ) * Commons.Analysis.Complex.gam β t) := by
      funext t; rw [Complex.cpow_def_of_ne_zero hRne]
    rw [heq]
    exact Complex.measurable_exp.comp
      ((continuous_const.mul (Commons.Analysis.Complex.gam_continuous β)).measurable)
  unfold gW1
  exact (hcp.div (((Commons.Analysis.Complex.gam_continuous β).pow 2).measurable)).mul
    (Commons.Analysis.Complex.measurable_gamDot β)

lemma measurable_gW4 (β : ℝ) : Measurable (gW4 β) := by
  unfold gW4
  refine (Measurable.inv ?_).mul (Commons.Analysis.Complex.measurable_gamDot β)
  exact ((measurable_riemannZeta.comp
        ((continuous_const.add (Commons.Analysis.Complex.gam_continuous β)).measurable)).mul
      (measurable_riemannZeta.comp
        ((continuous_const.sub (Commons.Analysis.Complex.gam_continuous β)).measurable))).mul
    (((Commons.Analysis.Complex.gam_continuous β).pow 4).measurable)

lemma norm_gW1_le {β R : ℝ} (hβ : 0 < β) (hR : 1 ≤ R) (t : ℝ) :
    ‖gW1 R β t‖ ≤ Commons.Analysis.Complex.curveConst β * (1 + t ^ 2)⁻¹ := by
  have h := norm_integrand_le hβ hR (by norm_num : (0:ℝ) ≤ 1) (fun _ : ℂ => (1:ℂ))
    (fun z h1 h2 => by simp) t
  simpa [gW1] using h

lemma norm_gW4_le (β : ℝ) (t : ℝ) :
    ‖gW4 β t‖ ≤ ‖Commons.Analysis.Complex.gamDot β t‖
      / (‖riemannZeta (1 + Commons.Analysis.Complex.gam β t)‖
          * ‖riemannZeta (1 - Commons.Analysis.Complex.gam β t)‖
          * ‖Commons.Analysis.Complex.gam β t‖ ^ 4) := by
  rw [gW4, norm_mul, norm_inv, norm_mul, norm_mul, norm_pow, div_eq_mul_inv]
  exact le_of_eq (by ring)

/-- The scalar weight `A t = (log(|t|+2)+1)/(1+t²)`. -/
noncomputable def Awt (t : ℝ) : ℝ := (Real.log (|t| + 2) + 1) / (1 + t ^ 2)

lemma integrable_weighted {m : ℕ}
    (Ψ : ((Fin m → ℝ) × (Fin m → ℝ)) × ℝ → ℂ) (Cw : ℝ) (hCw : 0 ≤ Cw)
    (ρw : ℝ → ℝ) (hρw : MeasureTheory.Integrable ρw (MeasureTheory.volume : MeasureTheory.Measure ℝ))
    (hmeas : AEStronglyMeasurable Ψ
      (((MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ)).prod
        (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ))).prod
        (MeasureTheory.volume : MeasureTheory.Measure ℝ)))
    (hdom : ∀ q : ((Fin m → ℝ) × (Fin m → ℝ)) × ℝ,
      ‖Ψ q‖ ≤ Cw * ((∏ j, Awt (q.1.1 j)) * (∏ j, Awt (q.1.2 j)) * ρw q.2)) :
    MeasureTheory.Integrable Ψ
      (((MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ)).prod
        (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ))).prod
        (MeasureTheory.volume : MeasureTheory.Measure ℝ)) := by
  have hprod : MeasureTheory.Integrable (fun p : (Fin m → ℝ) × (Fin m → ℝ) =>
      (∏ j, Awt (p.1 j)) * (∏ j, Awt (p.2 j)))
      ((MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ)).prod
        (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ))) := by
    simpa [Awt] using Commons.Analysis.Measure.integrable_weight_prod_fin m
  have hbig : MeasureTheory.Integrable (fun q : ((Fin m → ℝ) × (Fin m → ℝ)) × ℝ =>
      (∏ j, Awt (q.1.1 j)) * (∏ j, Awt (q.1.2 j)) * ρw q.2)
      (((MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ)).prod
        (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ))).prod
        (MeasureTheory.volume : MeasureTheory.Measure ℝ)) := by
    have h := hprod.mul_prod hρw
    refine h.congr ?_
    filter_upwards with q
    simp only [Awt]
  exact (hbig.const_mul Cw).mono' hmeas (Filter.Eventually.of_forall fun q => by
    exact hdom q)

lemma measurable_cons_eta_vec {R : ℝ} {m : ℕ} {Y : Type*} [MeasurableSpace Y]
    {γ : Y → ℂ} (hγ : Measurable γ) {w : Y → Fin m → ℝ} (hw : Measurable w) :
    Measurable (fun y : Y =>
      Fin.cons (α := fun _ => ℂ) (γ y) (fun j => zetaM1Eta R (w y j))) := by
  refine measurable_pi_iff.mpr (fun i => ?_)
  induction i using Fin.cases with
  | zero => simpa [Fin.cons_zero] using hγ
  | succ j =>
      simp only [Fin.cons_succ]
      exact (zetaM1Eta_continuous R).measurable.comp ((continuous_apply j).measurable.comp hw)

lemma measurable_pair_F {R : ℝ} {m : ℕ} {Y : Type*} [MeasurableSpace Y]
    (F : (Fin (m+1) → ℂ) → (Fin (m+1) → ℂ) → ℂ) (hcont : Continuous (Function.uncurry F))
    {A B : Y → Fin (m+1) → ℂ} (hA : Measurable A) (hB : Measurable B) :
    Measurable (fun q : Y => F (A q) (B q)) :=
  hcont.measurable.comp (hA.prodMk hB)

lemma measurable_cons2 {R : ℝ} {m : ℕ} {Y : Type*} [MeasurableSpace Y]
    {γ : Y → ℂ} (hγ : Measurable γ) {w : Y → Fin m → ℝ} (hw : Measurable w) :
    Measurable (fun y : Y =>
      Fin.cons (α := fun _ => ℂ) (γ y) (fun j => zetaM1Eta R (w y j))) :=
  measurable_cons_eta_vec (R := R) hγ hw

lemma measurable_F_cons {R : ℝ} {m : ℕ} {Y : Type*} [MeasurableSpace Y]
    (F : (Fin (m+1) → ℂ) → (Fin (m+1) → ℂ) → ℂ) (hcont : Continuous (Function.uncurry F))
    {a₁ a₂ : Y → ℂ} (ha₁ : Measurable a₁) (ha₂ : Measurable a₂)
    {w₁ w₂ : Y → Fin m → ℝ} (hw₁ : Measurable w₁) (hw₂ : Measurable w₂) :
    Measurable (fun q : Y => F (Fin.cons (α := fun _ => ℂ) (a₁ q) (fun j => zetaM1Eta R (w₁ q j)))
        (Fin.cons (α := fun _ => ℂ) (a₂ q) (fun j => zetaM1Eta R (w₂ q j)))) :=
  measurable_pair_F (R := R) F hcont (measurable_cons2 (R := R) ha₁ hw₁) (measurable_cons2 (R := R) ha₂ hw₂)

lemma norm_WmK_le {R K : ℝ}
    (hK : ∀ x y : ℝ, ‖zetaM1Kernel R (fun _ _ => (1:ℂ)) (zetaM1Eta R x) (zetaM1Eta R y)‖
      ≤ K * Awt x * Awt y) (m : ℕ) (w w' : Fin m → ℝ) :
    ‖WmK R m w w'‖ ≤ K ^ m * (∏ j, Awt (w j)) * (∏ j, Awt (w' j)) := by
  rw [WmK, norm_prod]
  refine le_trans (Finset.prod_le_prod (fun j _ => norm_nonneg _) (fun j _ => hK (w j) (w' j))) ?_
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact le_rfl

lemma quartic_weight_integrable {β : ℝ} (β' : ℝ) (hβ : 0 < β) (hβ10 : β ≤ 1 / 10)
    (hQint : MeasureTheory.Integrable (fun t : ℝ =>
      ‖Commons.Analysis.Complex.gamDot β t‖
        / (‖riemannZeta (1 + Commons.Analysis.Complex.gam β t)‖
            * ‖riemannZeta (1 - Commons.Analysis.Complex.gam β t)‖
            * ‖Commons.Analysis.Complex.gam β t‖ ^ 4))) :
    MeasureTheory.Integrable (fun t : ℝ =>
      ‖Commons.Analysis.Complex.gamDot β t‖
        / (‖riemannZeta (1 + Commons.Analysis.Complex.gam β t)‖
            * ‖riemannZeta (1 - Commons.Analysis.Complex.gam β t)‖
            * ‖Commons.Analysis.Complex.gam β t‖ ^ 4))
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) := hQint

/-- Integrability of the `W₁`-shaped integrand. -/
lemma integrable_gW1_integrand {β R : ℝ} (hβ : 0 < β) (hR : 3 ≤ R) {m : ℕ}
    (F : (Fin (m+1) → ℂ) → (Fin (m+1) → ℂ) → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hcont : Continuous (Function.uncurry F))
    (hFb : ∀ z z', ZetaRegVec β z → ZetaRegVec β z' → ‖F z z'‖ ≤ B) :
    MeasureTheory.Integrable (fun q : ((Fin m → ℝ) × (Fin m → ℝ)) × ℝ =>
      (F (Fin.cons 0 (fun j => zetaM1Eta R (q.1.1 j)))
         (Fin.cons (Commons.Analysis.Complex.gam β q.2) (fun j => zetaM1Eta R (q.1.2 j)))
        * gW1 R β q.2) * WmK R m q.1.1 q.1.2)
      (((MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ)).prod
        (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ))).prod
        (MeasureTheory.volume : MeasureTheory.Measure ℝ)) := by
  have hRne : R ≠ 0 := by linarith
  obtain ⟨K, hKpos, hKle⟩ := zetaM1Kernel_eta_bound (R := R) hR
  have hK : ∀ x y : ℝ, ‖zetaM1Kernel R (fun _ _ => (1:ℂ)) (zetaM1Eta R x) (zetaM1Eta R y)‖
      ≤ K * Awt x * Awt y := fun x y => by
    simpa only [Awt, zetaM1Kernel, Pi.one_apply, one_mul, mul_assoc] using hKle x y
  have hRone : (1:ℝ) ≤ R := by linarith
  refine integrable_weighted _ (B * K ^ m * Commons.Analysis.Complex.curveConst β)
    (mul_nonneg (mul_nonneg hB (pow_nonneg hKpos.le m))
      (Commons.Analysis.Complex.curveConst_pos hβ).le)
    (fun t : ℝ => (1 + t ^ 2)⁻¹) integrable_inv_one_add_sq ?_ ?_
  · refine Measurable.aestronglyMeasurable ?_
    have hF : Measurable (fun q : ((Fin m → ℝ) × (Fin m → ℝ)) × ℝ =>
        F (Fin.cons (α := fun _ => ℂ) (0:ℂ) (fun j => zetaM1Eta R (q.1.1 j)))
          (Fin.cons (α := fun _ => ℂ) (Commons.Analysis.Complex.gam β q.2)
            (fun j => zetaM1Eta R (q.1.2 j)))) :=
      measurable_F_cons (R := R) F hcont measurable_const
        ((Commons.Analysis.Complex.gam_continuous β).measurable.comp measurable_snd)
        measurable_fst.fst measurable_fst.snd
    exact (hF.mul ((measurable_gW1 R β hRne).comp measurable_snd)).mul
      ((measurable_WmK R hRne m).comp measurable_fst)
  · intro q
    have hb : ‖F (Fin.cons (α := fun _ => ℂ) 0 (fun j => zetaM1Eta R (q.1.1 j)))
        (Fin.cons (α := fun _ => ℂ) (Commons.Analysis.Complex.gam β q.2)
          (fun j => zetaM1Eta R (q.1.2 j)))‖ ≤ B :=
      hFb _ _ (ZetaRegVec_cons (zetaReg_zero hβ) (ZetaRegVec_eta hβ hR q.1.1))
        (ZetaRegVec_cons (phi_mem_ZetaReg hβ q.2) (ZetaRegVec_eta hβ hR q.1.2))
    have hw : ‖gW1 R β q.2‖ ≤ Commons.Analysis.Complex.curveConst β * (1 + q.2 ^ 2)⁻¹ :=
      norm_gW1_le hβ hRone q.2
    have hW := norm_WmK_le hK m q.1.1 q.1.2
    rw [norm_mul, norm_mul]
    have h2nn : 0 ≤ Commons.Analysis.Complex.curveConst β * (1 + q.2 ^ 2)⁻¹ :=
      mul_nonneg (Commons.Analysis.Complex.curveConst_pos hβ).le (by positivity)
    calc ‖F _ _‖ * ‖gW1 R β q.2‖ * ‖WmK R m q.1.1 q.1.2‖
        ≤ B * (Commons.Analysis.Complex.curveConst β * (1 + q.2 ^ 2)⁻¹)
            * (K ^ m * (∏ j, Awt (q.1.1 j)) * (∏ j, Awt (q.1.2 j))) :=
          mul_le_mul (mul_le_mul hb hw (norm_nonneg _) hB) hW (norm_nonneg _) (mul_nonneg hB h2nn)
      _ = B * K ^ m * Commons.Analysis.Complex.curveConst β
            * ((∏ j, Awt (q.1.1 j)) * (∏ j, Awt (q.1.2 j)) * (1 + q.2 ^ 2)⁻¹) := by ring

/-- Integrability of the `W₄`-shaped integrand. -/
lemma integrable_gW4_integrand {β R : ℝ} (hβ : 0 < β) (hβ10 : β ≤ 1 / 10) (hR : 3 ≤ R) {m : ℕ}
    (F : (Fin (m+1) → ℂ) → (Fin (m+1) → ℂ) → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hcont : Continuous (Function.uncurry F))
    (hFb : ∀ z z', ZetaRegVec β z → ZetaRegVec β z' → ‖F z z'‖ ≤ B)
    (hQint : MeasureTheory.Integrable (fun t : ℝ =>
      ‖Commons.Analysis.Complex.gamDot β t‖
        / (‖riemannZeta (1 + Commons.Analysis.Complex.gam β t)‖
            * ‖riemannZeta (1 - Commons.Analysis.Complex.gam β t)‖
            * ‖Commons.Analysis.Complex.gam β t‖ ^ 4))) :
    MeasureTheory.Integrable (fun q : ((Fin m → ℝ) × (Fin m → ℝ)) × ℝ =>
      (F (Fin.cons (Commons.Analysis.Complex.gam β q.2) (fun j => zetaM1Eta R (q.1.1 j)))
         (Fin.cons (-(Commons.Analysis.Complex.gam β q.2)) (fun j => zetaM1Eta R (q.1.2 j)))
        * gW4 β q.2) * WmK R m q.1.1 q.1.2)
      (((MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ)).prod
        (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ))).prod
        (MeasureTheory.volume : MeasureTheory.Measure ℝ)) := by
  have hRne : R ≠ 0 := by linarith
  obtain ⟨K, hKpos, hKle⟩ := zetaM1Kernel_eta_bound (R := R) hR
  have hK : ∀ x y : ℝ, ‖zetaM1Kernel R (fun _ _ => (1:ℂ)) (zetaM1Eta R x) (zetaM1Eta R y)‖
      ≤ K * Awt x * Awt y := fun x y => by
    simpa only [Awt, zetaM1Kernel, Pi.one_apply, one_mul, mul_assoc] using hKle x y
  refine integrable_weighted _ (B * K ^ m)
    (mul_nonneg hB (pow_nonneg hKpos.le m)) (fun t : ℝ => ‖Commons.Analysis.Complex.gamDot β t‖
        / (‖riemannZeta (1 + Commons.Analysis.Complex.gam β t)‖
            * ‖riemannZeta (1 - Commons.Analysis.Complex.gam β t)‖
            * ‖Commons.Analysis.Complex.gam β t‖ ^ 4)) hQint ?_ ?_
  · refine Measurable.aestronglyMeasurable ?_
    have hF : Measurable (fun q : ((Fin m → ℝ) × (Fin m → ℝ)) × ℝ =>
        F (Fin.cons (α := fun _ => ℂ) (Commons.Analysis.Complex.gam β q.2)
            (fun j => zetaM1Eta R (q.1.1 j)))
          (Fin.cons (α := fun _ => ℂ) (-(Commons.Analysis.Complex.gam β q.2))
            (fun j => zetaM1Eta R (q.1.2 j)))) :=
      measurable_F_cons (R := R) F hcont
        ((Commons.Analysis.Complex.gam_continuous β).measurable.comp measurable_snd)
        (((Commons.Analysis.Complex.gam_continuous β).measurable.comp measurable_snd).neg)
        measurable_fst.fst measurable_fst.snd
    have hg4 : Measurable (gW4 β) := by
      unfold gW4
      refine (Measurable.inv ?_).mul (Commons.Analysis.Complex.measurable_gamDot β)
      exact ((measurable_riemannZeta.comp
            ((continuous_const.add (Commons.Analysis.Complex.gam_continuous β)).measurable)).mul
          (measurable_riemannZeta.comp
            ((continuous_const.sub (Commons.Analysis.Complex.gam_continuous β)).measurable))).mul
        (((Commons.Analysis.Complex.gam_continuous β).pow 4).measurable)
    exact (hF.mul (hg4.comp measurable_snd)).mul
      ((measurable_WmK R hRne m).comp measurable_fst)
  · intro q
    have hb : ‖F (Fin.cons (α := fun _ => ℂ) (Commons.Analysis.Complex.gam β q.2)
            (fun j => zetaM1Eta R (q.1.1 j)))
        (Fin.cons (α := fun _ => ℂ) (-(Commons.Analysis.Complex.gam β q.2))
          (fun j => zetaM1Eta R (q.1.2 j)))‖ ≤ B :=
      hFb _ _ (ZetaRegVec_cons (phi_mem_ZetaReg hβ q.2) (ZetaRegVec_eta hβ hR q.1.1))
        (ZetaRegVec_cons (neg_phi_mem_ZetaReg hβ hβ10 q.2) (ZetaRegVec_eta hβ hR q.1.2))
    have hw := norm_gW4_le β q.2
    have hW := norm_WmK_le hK m q.1.1 q.1.2
    rw [norm_mul, norm_mul]
    have h2nn : 0 ≤ ‖Commons.Analysis.Complex.gamDot β q.2‖
        / (‖riemannZeta (1 + Commons.Analysis.Complex.gam β q.2)‖
            * ‖riemannZeta (1 - Commons.Analysis.Complex.gam β q.2)‖
            * ‖Commons.Analysis.Complex.gam β q.2‖ ^ 4) := by positivity
    calc ‖F _ _‖ * ‖gW4 β q.2‖ * ‖WmK R m q.1.1 q.1.2‖
        ≤ B * (‖Commons.Analysis.Complex.gamDot β q.2‖
              / (‖riemannZeta (1 + Commons.Analysis.Complex.gam β q.2)‖
                  * ‖riemannZeta (1 - Commons.Analysis.Complex.gam β q.2)‖
                  * ‖Commons.Analysis.Complex.gam β q.2‖ ^ 4))
            * (K ^ m * (∏ j, Awt (q.1.1 j)) * (∏ j, Awt (q.1.2 j))) :=
          mul_le_mul (mul_le_mul hb hw (norm_nonneg _) hB) hW (norm_nonneg _) (mul_nonneg hB h2nn)
      _ = B * K ^ m
            * ((∏ j, Awt (q.1.1 j)) * (∏ j, Awt (q.1.2 j))
              * (‖Commons.Analysis.Complex.gamDot β q.2‖
                / (‖riemannZeta (1 + Commons.Analysis.Complex.gam β q.2)‖
                    * ‖riemannZeta (1 - Commons.Analysis.Complex.gam β q.2)‖
                    * ‖Commons.Analysis.Complex.gam β q.2‖ ^ 4))) := by ring


/-- The `W₁`-term of the induction step, after Fubini. -/
lemma zetaT_W1 {β R : ℝ} (hβ : 0 < β) (hR : 3 ≤ R) {m : ℕ}
    (F : (Fin (m+1) → ℂ) → (Fin (m+1) → ℂ) → ℂ)
    (hInt : MeasureTheory.Integrable (fun q : ((Fin m → ℝ) × (Fin m → ℝ)) × ℝ =>
      (F (Fin.cons 0 (fun j => zetaM1Eta R (q.1.1 j)))
         (Fin.cons (Commons.Analysis.Complex.gam β q.2) (fun j => zetaM1Eta R (q.1.2 j)))
        * gW1 R β q.2) * WmK R m q.1.1 q.1.2)
      (((MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ)).prod
        (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ))).prod
        (MeasureTheory.volume : MeasureTheory.Measure ℝ))) :
    (∫ w : Fin m → ℝ, ∫ w' : Fin m → ℝ,
        zetaM0W1 R β (fun ζ ζ' => F (Fin.cons ζ (fun j => zetaM1Eta R (w j)))
          (Fin.cons ζ' (fun j => zetaM1Eta R (w' j)))) * WmK R m w w')
      = ((2:ℂ)*(Real.pi:ℂ))^(2*m) * ∫ t : ℝ,
          zetaMmf R m (fun z z' => F (Fin.cons 0 z)
            (Fin.cons (Commons.Analysis.Complex.gam β t) z')) * gW1 R β t := by
  have h1 : ∀ w w' : Fin m → ℝ,
      zetaM0W1 R β (fun ζ ζ' => F (Fin.cons ζ (fun j => zetaM1Eta R (w j)))
          (Fin.cons ζ' (fun j => zetaM1Eta R (w' j)))) * WmK R m w w'
      = ∫ t : ℝ, (F (Fin.cons 0 (fun j => zetaM1Eta R (w j)))
            (Fin.cons (Commons.Analysis.Complex.gam β t) (fun j => zetaM1Eta R (w' j)))
          * gW1 R β t) * WmK R m w w' := by
    intro w w'
    rw [zetaM0W1]
    rw [← MeasureTheory.integral_mul_const]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with t
    simp only [gW1]
    ring
  simp_rw [h1]
  rw [Commons.Analysis.Measure.integral_fin_fin_real_swap
      (Ψ := fun w w' t => (F (Fin.cons 0 (fun j => zetaM1Eta R (w j)))
            (Fin.cons (Commons.Analysis.Complex.gam β t) (fun j => zetaM1Eta R (w' j)))
          * gW1 R β t) * WmK R m w w') hInt]
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with t
  have hc : (∫ w : Fin m → ℝ, ∫ w' : Fin m → ℝ,
        (F (Fin.cons 0 (fun j => zetaM1Eta R (w j)))
            (Fin.cons (Commons.Analysis.Complex.gam β t) (fun j => zetaM1Eta R (w' j)))
          * gW1 R β t) * WmK R m w w')
      = (∫ w : Fin m → ℝ, ∫ w' : Fin m → ℝ,
        F (Fin.cons 0 (fun j => zetaM1Eta R (w j)))
            (Fin.cons (Commons.Analysis.Complex.gam β t) (fun j => zetaM1Eta R (w' j)))
          * WmK R m w w') * gW1 R β t := by
    have hstep1 : (∫ w : Fin m → ℝ, ∫ w' : Fin m → ℝ,
          (F (Fin.cons 0 (fun j => zetaM1Eta R (w j)))
              (Fin.cons (Commons.Analysis.Complex.gam β t) (fun j => zetaM1Eta R (w' j)))
            * gW1 R β t) * WmK R m w w')
        = ∫ w : Fin m → ℝ, (∫ w' : Fin m → ℝ,
            F (Fin.cons 0 (fun j => zetaM1Eta R (w j)))
              (Fin.cons (Commons.Analysis.Complex.gam β t) (fun j => zetaM1Eta R (w' j)))
            * WmK R m w w') * gW1 R β t := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards with w
      rw [← MeasureTheory.integral_mul_const]
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards with w'
      ring
    rw [hstep1, MeasureTheory.integral_mul_const]
  rw [hc, ← two_pi_pow_mul_zetaMmf m
    (fun z z' => F (Fin.cons 0 z) (Fin.cons (Commons.Analysis.Complex.gam β t) z'))]
  ring

/-- The `W₃`-term of the induction step, after Fubini. -/
lemma zetaT_W3 {β R : ℝ} (hβ : 0 < β) (hR : 3 ≤ R) {m : ℕ}
    (F : (Fin (m+1) → ℂ) → (Fin (m+1) → ℂ) → ℂ)
    (hInt : MeasureTheory.Integrable (fun q : ((Fin m → ℝ) × (Fin m → ℝ)) × ℝ =>
      (F (Fin.cons (Commons.Analysis.Complex.gam β q.2) (fun j => zetaM1Eta R (q.1.1 j)))
         (Fin.cons 0 (fun j => zetaM1Eta R (q.1.2 j)))
        * gW1 R β q.2) * WmK R m q.1.1 q.1.2)
      (((MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ)).prod
        (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ))).prod
        (MeasureTheory.volume : MeasureTheory.Measure ℝ))) :
    (∫ w : Fin m → ℝ, ∫ w' : Fin m → ℝ,
        zetaM0W3 R β (fun ζ ζ' => F (Fin.cons ζ (fun j => zetaM1Eta R (w j)))
          (Fin.cons ζ' (fun j => zetaM1Eta R (w' j)))) * WmK R m w w')
      = ((2:ℂ)*(Real.pi:ℂ))^(2*m) * ∫ t : ℝ,
          zetaMmf R m (fun z z' => F (Fin.cons (Commons.Analysis.Complex.gam β t) z)
            (Fin.cons 0 z')) * gW1 R β t := by
  have h1 : ∀ w w' : Fin m → ℝ,
      zetaM0W3 R β (fun ζ ζ' => F (Fin.cons ζ (fun j => zetaM1Eta R (w j)))
          (Fin.cons ζ' (fun j => zetaM1Eta R (w' j)))) * WmK R m w w'
      = ∫ t : ℝ, (F (Fin.cons (Commons.Analysis.Complex.gam β t) (fun j => zetaM1Eta R (w j)))
            (Fin.cons 0 (fun j => zetaM1Eta R (w' j)))
          * gW1 R β t) * WmK R m w w' := by
    intro w w'
    rw [zetaM0W3]
    rw [← MeasureTheory.integral_mul_const]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with t
    simp only [gW1]
    ring
  simp_rw [h1]
  rw [Commons.Analysis.Measure.integral_fin_fin_real_swap
      (Ψ := fun w w' t => (F (Fin.cons (Commons.Analysis.Complex.gam β t) (fun j => zetaM1Eta R (w j)))
            (Fin.cons 0 (fun j => zetaM1Eta R (w' j)))
          * gW1 R β t) * WmK R m w w') hInt]
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with t
  have hc : (∫ w : Fin m → ℝ, ∫ w' : Fin m → ℝ,
        (F (Fin.cons (Commons.Analysis.Complex.gam β t) (fun j => zetaM1Eta R (w j)))
            (Fin.cons 0 (fun j => zetaM1Eta R (w' j)))
          * gW1 R β t) * WmK R m w w')
      = (∫ w : Fin m → ℝ, ∫ w' : Fin m → ℝ,
        F (Fin.cons (Commons.Analysis.Complex.gam β t) (fun j => zetaM1Eta R (w j)))
            (Fin.cons 0 (fun j => zetaM1Eta R (w' j)))
          * WmK R m w w') * gW1 R β t := by
    have hstep1 : (∫ w : Fin m → ℝ, ∫ w' : Fin m → ℝ,
          (F (Fin.cons (Commons.Analysis.Complex.gam β t) (fun j => zetaM1Eta R (w j)))
              (Fin.cons 0 (fun j => zetaM1Eta R (w' j)))
            * gW1 R β t) * WmK R m w w')
        = ∫ w : Fin m → ℝ, (∫ w' : Fin m → ℝ,
            F (Fin.cons (Commons.Analysis.Complex.gam β t) (fun j => zetaM1Eta R (w j)))
              (Fin.cons 0 (fun j => zetaM1Eta R (w' j)))
            * WmK R m w w') * gW1 R β t := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards with w
      rw [← MeasureTheory.integral_mul_const]
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards with w'
      ring
    rw [hstep1, MeasureTheory.integral_mul_const]
  rw [hc, ← two_pi_pow_mul_zetaMmf m
    (fun z z' => F (Fin.cons (Commons.Analysis.Complex.gam β t) z) (Fin.cons 0 z'))]
  ring

/-- The `W₄`-term of the induction step, after Fubini. -/
lemma zetaT_W4 {β R : ℝ} (hβ : 0 < β) (hR : 3 ≤ R) {m : ℕ}
    (F : (Fin (m+1) → ℂ) → (Fin (m+1) → ℂ) → ℂ)
    (hInt : MeasureTheory.Integrable (fun q : ((Fin m → ℝ) × (Fin m → ℝ)) × ℝ =>
      (F (Fin.cons (Commons.Analysis.Complex.gam β q.2) (fun j => zetaM1Eta R (q.1.1 j)))
         (Fin.cons (-(Commons.Analysis.Complex.gam β q.2)) (fun j => zetaM1Eta R (q.1.2 j)))
        * gW4 β q.2) * WmK R m q.1.1 q.1.2)
      (((MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ)).prod
        (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ))).prod
        (MeasureTheory.volume : MeasureTheory.Measure ℝ))) :
    (∫ w : Fin m → ℝ, ∫ w' : Fin m → ℝ,
        zetaM0W4 R β (fun ζ ζ' => F (Fin.cons ζ (fun j => zetaM1Eta R (w j)))
          (Fin.cons ζ' (fun j => zetaM1Eta R (w' j)))) * WmK R m w w')
      = ((2:ℂ)*(Real.pi:ℂ))^(2*m) * ∫ t : ℝ,
          zetaMmf R m (fun z z' => F (Fin.cons (Commons.Analysis.Complex.gam β t) z)
            (Fin.cons (-(Commons.Analysis.Complex.gam β t)) z')) * gW4 β t := by
  have h1 : ∀ w w' : Fin m → ℝ,
      zetaM0W4 R β (fun ζ ζ' => F (Fin.cons ζ (fun j => zetaM1Eta R (w j)))
          (Fin.cons ζ' (fun j => zetaM1Eta R (w' j)))) * WmK R m w w'
      = ∫ t : ℝ, (F (Fin.cons (Commons.Analysis.Complex.gam β t) (fun j => zetaM1Eta R (w j)))
            (Fin.cons (-(Commons.Analysis.Complex.gam β t)) (fun j => zetaM1Eta R (w' j)))
          * gW4 β t) * WmK R m w w' := by
    intro w w'
    rw [zetaM0W4]
    rw [← MeasureTheory.integral_mul_const]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with t
    simp only [gW4]
    ring
  simp_rw [h1]
  rw [Commons.Analysis.Measure.integral_fin_fin_real_swap
      (Ψ := fun w w' t => (F (Fin.cons (Commons.Analysis.Complex.gam β t) (fun j => zetaM1Eta R (w j)))
            (Fin.cons (-(Commons.Analysis.Complex.gam β t)) (fun j => zetaM1Eta R (w' j)))
          * gW4 β t) * WmK R m w w') hInt]
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with t
  have hc : (∫ w : Fin m → ℝ, ∫ w' : Fin m → ℝ,
        (F (Fin.cons (Commons.Analysis.Complex.gam β t) (fun j => zetaM1Eta R (w j)))
            (Fin.cons (-(Commons.Analysis.Complex.gam β t)) (fun j => zetaM1Eta R (w' j)))
          * gW4 β t) * WmK R m w w')
      = (∫ w : Fin m → ℝ, ∫ w' : Fin m → ℝ,
        F (Fin.cons (Commons.Analysis.Complex.gam β t) (fun j => zetaM1Eta R (w j)))
            (Fin.cons (-(Commons.Analysis.Complex.gam β t)) (fun j => zetaM1Eta R (w' j)))
          * WmK R m w w') * gW4 β t := by
    have hstep1 : (∫ w : Fin m → ℝ, ∫ w' : Fin m → ℝ,
          (F (Fin.cons (Commons.Analysis.Complex.gam β t) (fun j => zetaM1Eta R (w j)))
              (Fin.cons (-(Commons.Analysis.Complex.gam β t)) (fun j => zetaM1Eta R (w' j)))
            * gW4 β t) * WmK R m w w')
        = ∫ w : Fin m → ℝ, (∫ w' : Fin m → ℝ,
            F (Fin.cons (Commons.Analysis.Complex.gam β t) (fun j => zetaM1Eta R (w j)))
              (Fin.cons (-(Commons.Analysis.Complex.gam β t)) (fun j => zetaM1Eta R (w' j)))
            * WmK R m w w') * gW4 β t := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards with w
      rw [← MeasureTheory.integral_mul_const]
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards with w'
      ring
    rw [hstep1, MeasureTheory.integral_mul_const]
  rw [hc, ← two_pi_pow_mul_zetaMmf m
    (fun z z' => F (Fin.cons (Commons.Analysis.Complex.gam β t) z)
      (Fin.cons (-(Commons.Analysis.Complex.gam β t)) z'))]
  ring


/-- The `W₂`-term of the induction step, after Fubini. -/
lemma zetaT_W2 {β R : ℝ} (hβ : 0 < β) (hR : 3 ≤ R) {m : ℕ}
    (F : (Fin (m+1) → ℂ) → (Fin (m+1) → ℂ) → ℂ)
    (hInt : MeasureTheory.Integrable (fun p : ((Fin m → ℝ) × (Fin m → ℝ)) × (ℝ × ℝ) =>
      F (Fin.cons (Commons.Analysis.Complex.gam β p.2.1) (fun j => zetaM1Eta R (p.1.1 j)))
          (Fin.cons (Commons.Analysis.Complex.gam β p.2.2) (fun j => zetaM1Eta R (p.1.2 j)))
        * zetaM1Kernel R (fun _ _ => (1:ℂ))
            (Commons.Analysis.Complex.gam β p.2.1) (Commons.Analysis.Complex.gam β p.2.2)
        * Commons.Analysis.Complex.gamDot β p.2.2
        * Commons.Analysis.Complex.gamDot β p.2.1
        * WmK R m p.1.1 p.1.2)
      (((MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ)).prod
        (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ))).prod
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
          (MeasureTheory.volume : MeasureTheory.Measure ℝ)))) :
    (∫ w : Fin m → ℝ, ∫ w' : Fin m → ℝ,
        zetaM0W2 R β (fun ζ ζ' => F (Fin.cons ζ (fun j => zetaM1Eta R (w j)))
          (Fin.cons ζ' (fun j => zetaM1Eta R (w' j)))) * WmK R m w w')
      = ((2:ℂ)*(Real.pi:ℂ))^(2*m) * ∫ t : ℝ, ∫ t' : ℝ,
          zetaMmf R m (fun z z' => F (Fin.cons (Commons.Analysis.Complex.gam β t) z)
              (Fin.cons (Commons.Analysis.Complex.gam β t') z'))
            * zetaM1Kernel R (fun _ _ => (1:ℂ))
                (Commons.Analysis.Complex.gam β t) (Commons.Analysis.Complex.gam β t')
            * Commons.Analysis.Complex.gamDot β t * Commons.Analysis.Complex.gamDot β t' := by
  have hpt : ∀ (w w' : Fin m → ℝ) (t t' : ℝ),
      zetaM1Kernel R (fun ζ ζ' => F (Fin.cons ζ (fun j => zetaM1Eta R (w j)))
              (Fin.cons ζ' (fun j => zetaM1Eta R (w' j))))
            (Commons.Analysis.Complex.gam β t) (Commons.Analysis.Complex.gam β t')
        * Commons.Analysis.Complex.gamDot β t' * Commons.Analysis.Complex.gamDot β t
        * WmK R m w w'
      = F (Fin.cons (Commons.Analysis.Complex.gam β t) (fun j => zetaM1Eta R (w j)))
            (Fin.cons (Commons.Analysis.Complex.gam β t') (fun j => zetaM1Eta R (w' j)))
          * zetaM1Kernel R (fun _ _ => (1:ℂ))
              (Commons.Analysis.Complex.gam β t) (Commons.Analysis.Complex.gam β t')
          * Commons.Analysis.Complex.gamDot β t' * Commons.Analysis.Complex.gamDot β t
        * WmK R m w w' := by
    intro w w' t t'
    simp only [zetaM1Kernel, Pi.one_apply, one_mul]
    ring
  have h1 : ∀ w w' : Fin m → ℝ,
      zetaM0W2 R β (fun ζ ζ' => F (Fin.cons ζ (fun j => zetaM1Eta R (w j)))
          (Fin.cons ζ' (fun j => zetaM1Eta R (w' j)))) * WmK R m w w'
      = ∫ t : ℝ, ∫ t' : ℝ,
          F (Fin.cons (Commons.Analysis.Complex.gam β t) (fun j => zetaM1Eta R (w j)))
              (Fin.cons (Commons.Analysis.Complex.gam β t') (fun j => zetaM1Eta R (w' j)))
            * zetaM1Kernel R (fun _ _ => (1:ℂ))
                (Commons.Analysis.Complex.gam β t) (Commons.Analysis.Complex.gam β t')
            * Commons.Analysis.Complex.gamDot β t' * Commons.Analysis.Complex.gamDot β t
          * WmK R m w w' := by
    intro w w'
    rw [zetaM0W2]
    rw [← MeasureTheory.integral_mul_const]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with t
    rw [← MeasureTheory.integral_mul_const, ← MeasureTheory.integral_mul_const]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with t'
    exact hpt w w' t t'
  simp_rw [h1]
  have hswap := Commons.Analysis.Measure.integral_fin_fin_real_real_swap
      (Ψ := fun w w' t t' =>
        F (Fin.cons (Commons.Analysis.Complex.gam β t) (fun j => zetaM1Eta R (w j)))
            (Fin.cons (Commons.Analysis.Complex.gam β t') (fun j => zetaM1Eta R (w' j)))
          * zetaM1Kernel R (fun _ _ => (1:ℂ))
              (Commons.Analysis.Complex.gam β t) (Commons.Analysis.Complex.gam β t')
          * Commons.Analysis.Complex.gamDot β t' * Commons.Analysis.Complex.gamDot β t
        * WmK R m w w') hInt
  rw [hswap]
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with t
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with t'
  have hstep : (∫ w : Fin m → ℝ, ∫ w' : Fin m → ℝ,
        F (Fin.cons (Commons.Analysis.Complex.gam β t) (fun j => zetaM1Eta R (w j)))
            (Fin.cons (Commons.Analysis.Complex.gam β t') (fun j => zetaM1Eta R (w' j)))
          * zetaM1Kernel R (fun _ _ => (1:ℂ))
              (Commons.Analysis.Complex.gam β t) (Commons.Analysis.Complex.gam β t')
          * Commons.Analysis.Complex.gamDot β t' * Commons.Analysis.Complex.gamDot β t
        * WmK R m w w')
      = (∫ w : Fin m → ℝ, ∫ w' : Fin m → ℝ,
          F (Fin.cons (Commons.Analysis.Complex.gam β t) (fun j => zetaM1Eta R (w j)))
            (Fin.cons (Commons.Analysis.Complex.gam β t') (fun j => zetaM1Eta R (w' j)))
            * WmK R m w w')
        * (zetaM1Kernel R (fun _ _ => (1:ℂ))
            (Commons.Analysis.Complex.gam β t) (Commons.Analysis.Complex.gam β t')
          * Commons.Analysis.Complex.gamDot β t * Commons.Analysis.Complex.gamDot β t') := by
    have hstep1 : (∫ w : Fin m → ℝ, ∫ w' : Fin m → ℝ,
        F (Fin.cons (Commons.Analysis.Complex.gam β t) (fun j => zetaM1Eta R (w j)))
            (Fin.cons (Commons.Analysis.Complex.gam β t') (fun j => zetaM1Eta R (w' j)))
          * zetaM1Kernel R (fun _ _ => (1:ℂ))
              (Commons.Analysis.Complex.gam β t) (Commons.Analysis.Complex.gam β t')
          * Commons.Analysis.Complex.gamDot β t' * Commons.Analysis.Complex.gamDot β t
        * WmK R m w w')
        = ∫ w : Fin m → ℝ, (∫ w' : Fin m → ℝ,
            F (Fin.cons (Commons.Analysis.Complex.gam β t) (fun j => zetaM1Eta R (w j)))
              (Fin.cons (Commons.Analysis.Complex.gam β t') (fun j => zetaM1Eta R (w' j)))
              * WmK R m w w')
          * (zetaM1Kernel R (fun _ _ => (1:ℂ))
              (Commons.Analysis.Complex.gam β t) (Commons.Analysis.Complex.gam β t')
            * Commons.Analysis.Complex.gamDot β t * Commons.Analysis.Complex.gamDot β t') := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards with w
      rw [← MeasureTheory.integral_mul_const]
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards with w'
      ring
    rw [hstep1, MeasureTheory.integral_mul_const]
  rw [hstep, ← two_pi_pow_mul_zetaMmf m
    (fun z z' => F (Fin.cons (Commons.Analysis.Complex.gam β t) z)
      (Fin.cons (Commons.Analysis.Complex.gam β t') z'))]
  ring


/-! ## Integrability of the `m`-fold summands -/

lemma integrable_eval_WmK {m : ℕ} {R : ℝ} (hR : 3 ≤ R)
    (X : ((Fin m → ℝ) × (Fin m → ℝ)) → ℂ) (c : ℝ) (hc : 0 ≤ c)
    (hXm : AEStronglyMeasurable X
      ((MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ)).prod
        (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ))))
    (hX : ∀ p : (Fin m → ℝ) × (Fin m → ℝ), ‖X p‖ ≤ c) :
    MeasureTheory.Integrable (fun p : (Fin m → ℝ) × (Fin m → ℝ) =>
        X p * WmK R m p.1 p.2)
      ((MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ)).prod
        (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ))) := by
  have hRne : R ≠ 0 := by linarith
  obtain ⟨K, hKpos, hKle⟩ := zetaM1Kernel_eta_bound (R := R) hR
  have hK : ∀ x y : ℝ, ‖zetaM1Kernel R (fun _ _ => (1:ℂ)) (zetaM1Eta R x) (zetaM1Eta R y)‖
      ≤ K * Awt x * Awt y := fun x y => by
    simpa only [Awt, zetaM1Kernel, Pi.one_apply, one_mul, mul_assoc] using hKle x y
  have hprod : MeasureTheory.Integrable (fun p : (Fin m → ℝ) × (Fin m → ℝ) =>
      (∏ j, Awt (p.1 j)) * (∏ j, Awt (p.2 j)))
      ((MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ)).prod
        (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ))) := by
    simpa [Awt] using Commons.Analysis.Measure.integrable_weight_prod_fin m
  refine ((hprod.const_mul (c * K ^ m))).mono'
    (hXm.mul ((measurable_WmK R hRne m).aestronglyMeasurable)) ?_
  filter_upwards with p
  rw [norm_mul]
  calc ‖X p‖ * ‖WmK R m p.1 p.2‖
      ≤ c * (K ^ m * (∏ j, Awt (p.1 j)) * (∏ j, Awt (p.2 j))) :=
        mul_le_mul (hX p) (norm_WmK_le hK m p.1 p.2) (norm_nonneg _) hc
    _ = c * K ^ m * ((∏ j, Awt (p.1 j)) * (∏ j, Awt (p.2 j))) := by ring

lemma integrable_of_norm_gW1 {β R : ℝ} (hβ : 0 < β) (hR : 1 ≤ R) :
    MeasureTheory.Integrable (fun t : ℝ => ‖gW1 R β t‖) (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
  refine (integrable_inv_one_add_sq.const_mul (Commons.Analysis.Complex.curveConst β)).mono'
    ((measurable_gW1 R β (by linarith)).norm.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun t => ?_)
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  exact norm_gW1_le hβ hR t

lemma norm_gW1_integral_le {β R : ℝ} (hβ : 0 < β) (hR : 1 ≤ R) :
    (∫ t : ℝ, ‖gW1 R β t‖)
      ≤ Commons.Analysis.Complex.curveConst β * ∫ t : ℝ, (1 + t ^ 2)⁻¹ := by
  rw [← MeasureTheory.integral_const_mul]
  exact MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall (fun t => norm_nonneg _))
    (integrable_inv_one_add_sq.const_mul _) (Filter.Eventually.of_forall (fun t => norm_gW1_le hβ hR t))

lemma norm_zetaM0W1_le {β R K1 : ℝ} (hβ : 0 < β) (hR : 1 ≤ R)
    (hK1 : (∫ t : ℝ, ‖gW1 R β t‖) ≤ K1)
    (f : ℂ → ℂ → ℂ) (B : ℝ) (hbound : ∀ t : ℝ, ‖f 0 (Commons.Analysis.Complex.gam β t)‖ ≤ B) :
    ‖zetaM0W1 R β f‖ ≤ K1 * B := by
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hbound 0)
  rw [zetaM0W1]
  refine le_trans (MeasureTheory.norm_integral_le_integral_norm _) ?_
  have hpt : ∀ t : ℝ,
      ‖(f 0 (Commons.Analysis.Complex.gam β t) * (R : ℂ) ^ (Commons.Analysis.Complex.gam β t))
          / (Commons.Analysis.Complex.gam β t) ^ 2 * Commons.Analysis.Complex.gamDot β t‖
        ≤ B * ‖gW1 R β t‖ := by
    intro t
    rw [show (f 0 (Commons.Analysis.Complex.gam β t) * (R : ℂ) ^ (Commons.Analysis.Complex.gam β t))
          / (Commons.Analysis.Complex.gam β t) ^ 2 * Commons.Analysis.Complex.gamDot β t
        = f 0 (Commons.Analysis.Complex.gam β t) * gW1 R β t by rw [gW1]; ring]
    rw [norm_mul]
    exact mul_le_mul (hbound t) le_rfl (norm_nonneg _) hB0
  refine le_trans (MeasureTheory.integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun t => norm_nonneg _))
    ((integrable_of_norm_gW1 hβ hR).const_mul B) (Filter.Eventually.of_forall hpt)) ?_
  rw [MeasureTheory.integral_const_mul, mul_comm B]
  exact mul_le_mul_of_nonneg_right hK1 hB0


/-! ## Integrability of the `Γ₀`-joint integrands -/

lemma measurable_comp_gam {m : ℕ} {g : ℝ × ℝ → ℂ} (hg : Measurable g) :
    Measurable (fun q : ((Fin m → ℝ) × (Fin m → ℝ)) × (ℝ × ℝ) => g (q.2.1, q.2.2)) :=
  hg.comp (measurable_snd.fst.prodMk measurable_snd.snd)

lemma integrable_weighted2 {m : ℕ}
    (Ψ : ((Fin m → ℝ) × (Fin m → ℝ)) × (ℝ × ℝ) → ℂ) (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hUint : MeasureTheory.Integrable (fun t : ℝ => uScale t) (MeasureTheory.volume : MeasureTheory.Measure ℝ))
    (hmeas : AEStronglyMeasurable Ψ
      (((MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ)).prod
        (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ))).prod
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
          (MeasureTheory.volume : MeasureTheory.Measure ℝ))))
    (hdom : ∀ q : ((Fin m → ℝ) × (Fin m → ℝ)) × (ℝ × ℝ),
      ‖Ψ q‖ ≤ Cw * ((∏ j, Awt (q.1.1 j)) * (∏ j, Awt (q.1.2 j))
        * (uScale q.2.1 * uScale q.2.2))) :
    MeasureTheory.Integrable Ψ
      (((MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ)).prod
        (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ))).prod
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
          (MeasureTheory.volume : MeasureTheory.Measure ℝ))) := by
  have hprod : MeasureTheory.Integrable (fun p : (Fin m → ℝ) × (Fin m → ℝ) =>
      (∏ j, Awt (p.1 j)) * (∏ j, Awt (p.2 j)))
      ((MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ)).prod
        (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ))) := by
    simpa [Awt] using Commons.Analysis.Measure.integrable_weight_prod_fin m
  have hρ : MeasureTheory.Integrable (fun p : ℝ × ℝ => uScale p.1 * uScale p.2)
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
        (MeasureTheory.volume : MeasureTheory.Measure ℝ)) := hUint.mul_prod hUint
  have hbig : MeasureTheory.Integrable (fun q : ((Fin m → ℝ) × (Fin m → ℝ)) × (ℝ × ℝ) =>
      ((∏ j, Awt (q.1.1 j)) * (∏ j, Awt (q.1.2 j))) * (uScale q.2.1 * uScale q.2.2))
      (((MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ)).prod
        (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ))).prod
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
          (MeasureTheory.volume : MeasureTheory.Measure ℝ))) := by
    have h := hprod.mul_prod hρ
    refine h.congr ?_
    filter_upwards with q
    simp only [Awt]
  exact (hbig.const_mul Cw).mono' hmeas (Filter.Eventually.of_forall fun q => hdom q)

/-- Measurability of the Green–Tao kernel as a function of the two complex arguments. -/
lemma measurable_zetaM1Kernel_self (R : ℝ) (hR : R ≠ 0) :
    Measurable (fun q : ℂ × ℂ => zetaM1Kernel R (fun _ _ => (1:ℂ)) q.1 q.2) := by
  have hRne : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR
  have hpow : Measurable (fun q : ℂ × ℂ => (R : ℂ) ^ (q.1 + q.2)) := by
    have heq : (fun q : ℂ × ℂ => (R : ℂ) ^ (q.1 + q.2))
        = fun q => Complex.exp (Complex.log (R : ℂ) * (q.1 + q.2)) := by
      funext q; rw [Complex.cpow_def_of_ne_zero hRne]
    rw [heq]
    exact Complex.measurable_exp.comp (measurable_const.mul (measurable_fst.add measurable_snd))
  have hnum : Measurable (fun q : ℂ × ℂ => riemannZeta (1 + q.1 + q.2)) :=
    measurable_riemannZeta.comp ((measurable_const.add measurable_fst).add measurable_snd)
  have hd1 : Measurable (fun q : ℂ × ℂ => riemannZeta (1 + q.1)) :=
    measurable_riemannZeta.comp (measurable_const.add measurable_fst)
  have hd2 : Measurable (fun q : ℂ × ℂ => riemannZeta (1 + q.2)) :=
    measurable_riemannZeta.comp (measurable_const.add measurable_snd)
  have heq : (fun q : ℂ × ℂ => zetaM1Kernel R (fun _ _ => (1:ℂ)) q.1 q.2)
      = fun q : ℂ × ℂ =>
        riemannZeta (1 + q.1 + q.2) / (riemannZeta (1 + q.1) * riemannZeta (1 + q.2))
          * (R : ℂ) ^ (q.1 + q.2) / (q.1 * q.1 * (q.2 * q.2)) := by
    funext q
    simp only [zetaM1Kernel, Pi.one_apply, one_mul]
    ring
  have h1 : Measurable (fun q : ℂ × ℂ =>
      riemannZeta (1 + q.1 + q.2) / (riemannZeta (1 + q.1) * riemannZeta (1 + q.2))) :=
    hnum.div (hd1.mul hd2)
  have h2 : Measurable (fun q : ℂ × ℂ =>
      riemannZeta (1 + q.1 + q.2) / (riemannZeta (1 + q.1) * riemannZeta (1 + q.2))
        * (R : ℂ) ^ (q.1 + q.2)) := h1.mul hpow
  have h3 : Measurable (fun q : ℂ × ℂ => q.1 * q.1 * (q.2 * q.2)) :=
    (measurable_fst.mul measurable_fst).mul (measurable_snd.mul measurable_snd)
  have h4 : Measurable (fun q : ℂ × ℂ =>
      riemannZeta (1 + q.1 + q.2) / (riemannZeta (1 + q.1) * riemannZeta (1 + q.2))
        * (R : ℂ) ^ (q.1 + q.2) / (q.1 * q.1 * (q.2 * q.2))) := h2.div h3
  rw [heq]; exact h4

lemma measurable_zetaM1Kernel_gam {β R : ℝ} (hR : R ≠ 0) :
    Measurable (fun p : ℝ × ℝ =>
      zetaM1Kernel R (fun _ _ => (1:ℂ))
        (Commons.Analysis.Complex.gam β p.1) (Commons.Analysis.Complex.gam β p.2)) := by
  have hRne : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR
  have hg1 : Measurable (fun p : ℝ × ℝ => Commons.Analysis.Complex.gam β p.1) :=
    (Commons.Analysis.Complex.gam_continuous β).measurable.comp measurable_fst
  have hg2 : Measurable (fun p : ℝ × ℝ => Commons.Analysis.Complex.gam β p.2) :=
    (Commons.Analysis.Complex.gam_continuous β).measurable.comp measurable_snd
  have hpow : Measurable (fun p : ℝ × ℝ =>
      (R : ℂ) ^ (Commons.Analysis.Complex.gam β p.1 + Commons.Analysis.Complex.gam β p.2)) := by
    have heq : (fun p : ℝ × ℝ =>
          (R : ℂ) ^ (Commons.Analysis.Complex.gam β p.1 + Commons.Analysis.Complex.gam β p.2))
        = fun p => Complex.exp (Complex.log (R : ℂ)
            * (Commons.Analysis.Complex.gam β p.1 + Commons.Analysis.Complex.gam β p.2)) := by
      funext p; rw [Complex.cpow_def_of_ne_zero hRne]
    rw [heq]
    exact Complex.measurable_exp.comp (measurable_const.mul (hg1.add hg2))
  have hnum : Measurable (fun p : ℝ × ℝ =>
      riemannZeta (1 + Commons.Analysis.Complex.gam β p.1 + Commons.Analysis.Complex.gam β p.2)) :=
    measurable_riemannZeta.comp ((measurable_const.add hg1).add hg2)
  have hd1 : Measurable (fun p : ℝ × ℝ =>
      riemannZeta (1 + Commons.Analysis.Complex.gam β p.1)) :=
    measurable_riemannZeta.comp (measurable_const.add hg1)
  have hd2 : Measurable (fun p : ℝ × ℝ =>
      riemannZeta (1 + Commons.Analysis.Complex.gam β p.2)) :=
    measurable_riemannZeta.comp (measurable_const.add hg2)
  have h1 : Measurable (fun p : ℝ × ℝ =>
      riemannZeta (1 + Commons.Analysis.Complex.gam β p.1 + Commons.Analysis.Complex.gam β p.2)
        / (riemannZeta (1 + Commons.Analysis.Complex.gam β p.1)
            * riemannZeta (1 + Commons.Analysis.Complex.gam β p.2))) := hnum.div (hd1.mul hd2)
  have h2 : Measurable (fun p : ℝ × ℝ =>
      riemannZeta (1 + Commons.Analysis.Complex.gam β p.1 + Commons.Analysis.Complex.gam β p.2)
        / (riemannZeta (1 + Commons.Analysis.Complex.gam β p.1)
            * riemannZeta (1 + Commons.Analysis.Complex.gam β p.2))
        * (R : ℂ) ^ (Commons.Analysis.Complex.gam β p.1 + Commons.Analysis.Complex.gam β p.2)) :=
    h1.mul hpow
  have h3 : Measurable (fun p : ℝ × ℝ =>
      Commons.Analysis.Complex.gam β p.1 * Commons.Analysis.Complex.gam β p.1
        * (Commons.Analysis.Complex.gam β p.2 * Commons.Analysis.Complex.gam β p.2)) :=
    (hg1.mul hg1).mul (hg2.mul hg2)
  have h4 : Measurable (fun p : ℝ × ℝ =>
      riemannZeta (1 + Commons.Analysis.Complex.gam β p.1 + Commons.Analysis.Complex.gam β p.2)
        / (riemannZeta (1 + Commons.Analysis.Complex.gam β p.1)
            * riemannZeta (1 + Commons.Analysis.Complex.gam β p.2))
        * (R : ℂ) ^ (Commons.Analysis.Complex.gam β p.1 + Commons.Analysis.Complex.gam β p.2)
        / (Commons.Analysis.Complex.gam β p.1 * Commons.Analysis.Complex.gam β p.1
            * (Commons.Analysis.Complex.gam β p.2 * Commons.Analysis.Complex.gam β p.2))) :=
    h2.div h3
  have heq : (fun p : ℝ × ℝ => zetaM1Kernel R (fun _ _ => (1:ℂ))
        (Commons.Analysis.Complex.gam β p.1) (Commons.Analysis.Complex.gam β p.2))
      = fun p : ℝ × ℝ =>
      riemannZeta (1 + Commons.Analysis.Complex.gam β p.1 + Commons.Analysis.Complex.gam β p.2)
        / (riemannZeta (1 + Commons.Analysis.Complex.gam β p.1)
            * riemannZeta (1 + Commons.Analysis.Complex.gam β p.2))
        * (R : ℂ) ^ (Commons.Analysis.Complex.gam β p.1 + Commons.Analysis.Complex.gam β p.2)
        / (Commons.Analysis.Complex.gam β p.1 * Commons.Analysis.Complex.gam β p.1
            * (Commons.Analysis.Complex.gam β p.2 * Commons.Analysis.Complex.gam β p.2)) := by
    funext p
    simp only [zetaM1Kernel, Pi.one_apply, one_mul]
    ring
  rw [heq]; exact h4

/-- Integrability of the `Γ₀ × Γ₀` joint integrand. -/
lemma integrable_gW2_integrand {β R : ℝ} (hβ : 0 < β) (hR : 3 ≤ R) {m : ℕ}
    (F : (Fin (m+1) → ℂ) → (Fin (m+1) → ℂ) → ℂ) (B C₁ Cn : ℝ)
    (hC1 : 0 < C₁) (hCn : 0 < Cn) (hB : 0 ≤ B)
    (hcont : Continuous (Function.uncurry F))
    (hFb : ∀ z z', ZetaRegVec β z → ZetaRegVec β z' → ‖F z z'‖ ≤ B)
    (hinvb : ∀ z : ℂ, z ≠ 0 → -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 →
        ‖(riemannZeta (1 + z))⁻¹‖ ≤ C₁ * (Real.log (|z.im| + 2) + 1))
    (hnum : ∀ t t' : ℝ, ‖riemannZeta (1 + Commons.Analysis.Complex.gam β t
        + Commons.Analysis.Complex.gam β t')‖ ≤ Cn * (|t| + |t'| + 3) ^ ((1:ℝ)/2))
    (hUint : MeasureTheory.Integrable (fun t : ℝ => uScale t) (MeasureTheory.volume : MeasureTheory.Measure ℝ)) :
    MeasureTheory.Integrable (fun q : ((Fin m → ℝ) × (Fin m → ℝ)) × (ℝ × ℝ) =>
      F (Fin.cons (Commons.Analysis.Complex.gam β q.2.1) (fun j => zetaM1Eta R (q.1.1 j)))
          (Fin.cons (Commons.Analysis.Complex.gam β q.2.2) (fun j => zetaM1Eta R (q.1.2 j)))
        * zetaM1Kernel R (fun _ _ => (1:ℂ))
            (Commons.Analysis.Complex.gam β q.2.1) (Commons.Analysis.Complex.gam β q.2.2)
        * Commons.Analysis.Complex.gamDot β q.2.2
        * Commons.Analysis.Complex.gamDot β q.2.1
        * WmK R m q.1.1 q.1.2)
      (((MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ)).prod
        (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ))).prod
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
          (MeasureTheory.volume : MeasureTheory.Measure ℝ))) := by
  have hRne : R ≠ 0 := by linarith
  obtain ⟨K, hKpos, hKle⟩ := zetaM1Kernel_eta_bound (R := R) hR
  have hK : ∀ x y : ℝ, ‖zetaM1Kernel R (fun _ _ => (1:ℂ)) (zetaM1Eta R x) (zetaM1Eta R y)‖
      ≤ K * Awt x * Awt y := fun x y => by
    simpa only [Awt, zetaM1Kernel, Pi.one_apply, one_mul, mul_assoc] using hKle x y
  refine integrable_weighted2 _ (B * K ^ m * (Cn * C₁ * C₁ * Commons.Analysis.Complex.curveConst β ^ 2))
    (by positivity) hUint ?_ ?_
  · refine Measurable.aestronglyMeasurable ?_
    have hF : Measurable (fun q : ((Fin m → ℝ) × (Fin m → ℝ)) × (ℝ × ℝ) =>
        F (Fin.cons (α := fun _ => ℂ) (Commons.Analysis.Complex.gam β q.2.1)
            (fun j => zetaM1Eta R (q.1.1 j)))
          (Fin.cons (α := fun _ => ℂ) (Commons.Analysis.Complex.gam β q.2.2)
            (fun j => zetaM1Eta R (q.1.2 j)))) :=
      measurable_F_cons (R := R) F hcont
        ((Commons.Analysis.Complex.gam_continuous β).measurable.comp measurable_snd.fst)
        ((Commons.Analysis.Complex.gam_continuous β).measurable.comp measurable_snd.snd)
        measurable_fst.fst measurable_fst.snd
    have hKm : Measurable (fun q : ((Fin m → ℝ) × (Fin m → ℝ)) × (ℝ × ℝ) =>
        zetaM1Kernel R (fun _ _ => (1:ℂ))
          (Commons.Analysis.Complex.gam β q.2.1) (Commons.Analysis.Complex.gam β q.2.2)) :=
      measurable_comp_gam (measurable_zetaM1Kernel_gam (β := β) hRne)
    have hd1 : Measurable (fun q : ((Fin m → ℝ) × (Fin m → ℝ)) × (ℝ × ℝ) =>
        Commons.Analysis.Complex.gamDot β q.2.1) :=
      (Commons.Analysis.Complex.measurable_gamDot β).comp measurable_snd.fst
    have hd2 : Measurable (fun q : ((Fin m → ℝ) × (Fin m → ℝ)) × (ℝ × ℝ) =>
        Commons.Analysis.Complex.gamDot β q.2.2) :=
      (Commons.Analysis.Complex.measurable_gamDot β).comp measurable_snd.snd
    exact (((hF.mul hKm).mul hd2).mul hd1).mul
      ((measurable_WmK R hRne m).comp measurable_fst)
  · intro q
    have hb : ‖F (Fin.cons (α := fun _ => ℂ) (Commons.Analysis.Complex.gam β q.2.1)
          (fun j => zetaM1Eta R (q.1.1 j)))
        (Fin.cons (α := fun _ => ℂ) (Commons.Analysis.Complex.gam β q.2.2)
          (fun j => zetaM1Eta R (q.1.2 j)))‖ ≤ B :=
      hFb _ _ (ZetaRegVec_cons (phi_mem_ZetaReg hβ q.2.1) (ZetaRegVec_eta hβ hR q.1.1))
        (ZetaRegVec_cons (phi_mem_ZetaReg hβ q.2.2) (ZetaRegVec_eta hβ hR q.1.2))
    have hW := norm_WmK_le hK m q.1.1 q.1.2
    have hker := gamma_gamma_pointwise hβ (by linarith : (1:ℝ) ≤ R) (fun _ _ : ℂ => (1:ℂ))
      1 C₁ Cn zero_le_one hC1 hCn hinvb
      (fun z z' _ _ _ _ => by simp) hnum q.2.1 q.2.2
    rw [norm_mul] at hker
    have hker' : ‖zetaM1Kernel R (fun _ _ => (1:ℂ))
          (Commons.Analysis.Complex.gam β q.2.1) (Commons.Analysis.Complex.gam β q.2.2)‖
        * ‖Commons.Analysis.Complex.gamDot β q.2.2‖ * ‖Commons.Analysis.Complex.gamDot β q.2.1‖
        ≤ Cn * C₁ * C₁ * Commons.Analysis.Complex.curveConst β ^ 2
            * (uScale q.2.1 * uScale q.2.2) := by
      simpa only [one_mul] using hker
    have hKnn : 0 ≤ Cn * C₁ * C₁ * Commons.Analysis.Complex.curveConst β ^ 2
        * (uScale q.2.1 * uScale q.2.2) :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCn.le hC1.le) hC1.le)
        (pow_nonneg (Commons.Analysis.Complex.curveConst_pos hβ).le 2))
        (mul_nonneg (uScale_nonneg _) (uScale_nonneg _))
    simp only [norm_mul]
    have h1 : ‖F (Fin.cons (α := fun _ => ℂ) (Commons.Analysis.Complex.gam β q.2.1)
              (fun j => zetaM1Eta R (q.1.1 j)))
            (Fin.cons (α := fun _ => ℂ) (Commons.Analysis.Complex.gam β q.2.2)
              (fun j => zetaM1Eta R (q.1.2 j)))‖
          * (‖zetaM1Kernel R (fun _ _ => (1:ℂ))
              (Commons.Analysis.Complex.gam β q.2.1) (Commons.Analysis.Complex.gam β q.2.2)‖
            * ‖Commons.Analysis.Complex.gamDot β q.2.2‖ * ‖Commons.Analysis.Complex.gamDot β q.2.1‖)
        ≤ B * (Cn * C₁ * C₁ * Commons.Analysis.Complex.curveConst β ^ 2
            * (uScale q.2.1 * uScale q.2.2)) :=
      mul_le_mul hb hker' (by positivity) hB
    rw [show B * K ^ m * (Cn * C₁ * C₁ * Commons.Analysis.Complex.curveConst β ^ 2)
          * ((∏ j, Awt (q.1.1 j)) * (∏ j, Awt (q.1.2 j))
            * (uScale q.2.1 * uScale q.2.2))
        = (B * (Cn * C₁ * C₁ * Commons.Analysis.Complex.curveConst β ^ 2
              * (uScale q.2.1 * uScale q.2.2)))
            * (K ^ m * (∏ j, Awt (q.1.1 j)) * (∏ j, Awt (q.1.2 j))) by ring]
    exact le_trans (le_of_eq (by ring))
      (mul_le_mul h1 hW (norm_nonneg _) (mul_nonneg hB hKnn))


/-- Integrability of the `W₃`-shaped integrand. -/
lemma integrable_gW3_integrand {β R : ℝ} (hβ : 0 < β) (hR : 3 ≤ R) {m : ℕ}
    (F : (Fin (m+1) → ℂ) → (Fin (m+1) → ℂ) → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hcont : Continuous (Function.uncurry F))
    (hFb : ∀ z z', ZetaRegVec β z → ZetaRegVec β z' → ‖F z z'‖ ≤ B) :
    MeasureTheory.Integrable (fun q : ((Fin m → ℝ) × (Fin m → ℝ)) × ℝ =>
      (F (Fin.cons (Commons.Analysis.Complex.gam β q.2) (fun j => zetaM1Eta R (q.1.1 j)))
         (Fin.cons 0 (fun j => zetaM1Eta R (q.1.2 j)))
        * gW1 R β q.2) * WmK R m q.1.1 q.1.2)
      (((MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ)).prod
        (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ))).prod
        (MeasureTheory.volume : MeasureTheory.Measure ℝ)) := by
  have hRne : R ≠ 0 := by linarith
  obtain ⟨K, hKpos, hKle⟩ := zetaM1Kernel_eta_bound (R := R) hR
  have hK : ∀ x y : ℝ, ‖zetaM1Kernel R (fun _ _ => (1:ℂ)) (zetaM1Eta R x) (zetaM1Eta R y)‖
      ≤ K * Awt x * Awt y := fun x y => by
    simpa only [Awt, zetaM1Kernel, Pi.one_apply, one_mul, mul_assoc] using hKle x y
  have hRone : (1:ℝ) ≤ R := by linarith
  refine integrable_weighted _ (B * K ^ m * Commons.Analysis.Complex.curveConst β)
    (mul_nonneg (mul_nonneg hB (pow_nonneg hKpos.le m))
      (Commons.Analysis.Complex.curveConst_pos hβ).le)
    (fun t : ℝ => (1 + t ^ 2)⁻¹) integrable_inv_one_add_sq ?_ ?_
  · refine Measurable.aestronglyMeasurable ?_
    have hF : Measurable (fun q : ((Fin m → ℝ) × (Fin m → ℝ)) × ℝ =>
        F (Fin.cons (α := fun _ => ℂ) (Commons.Analysis.Complex.gam β q.2)
            (fun j => zetaM1Eta R (q.1.1 j)))
          (Fin.cons (α := fun _ => ℂ) (0:ℂ) (fun j => zetaM1Eta R (q.1.2 j)))) :=
      measurable_F_cons (R := R) F hcont
        ((Commons.Analysis.Complex.gam_continuous β).measurable.comp measurable_snd)
        measurable_const measurable_fst.fst measurable_fst.snd
    exact (hF.mul ((measurable_gW1 R β hRne).comp measurable_snd)).mul
      ((measurable_WmK R hRne m).comp measurable_fst)
  · intro q
    have hb : ‖F (Fin.cons (α := fun _ => ℂ) (Commons.Analysis.Complex.gam β q.2)
          (fun j => zetaM1Eta R (q.1.1 j)))
        (Fin.cons (α := fun _ => ℂ) 0 (fun j => zetaM1Eta R (q.1.2 j)))‖ ≤ B :=
      hFb _ _ (ZetaRegVec_cons (phi_mem_ZetaReg hβ q.2) (ZetaRegVec_eta hβ hR q.1.1))
        (ZetaRegVec_cons (zetaReg_zero hβ) (ZetaRegVec_eta hβ hR q.1.2))
    have hw : ‖gW1 R β q.2‖ ≤ Commons.Analysis.Complex.curveConst β * (1 + q.2 ^ 2)⁻¹ :=
      norm_gW1_le hβ hRone q.2
    have hW := norm_WmK_le hK m q.1.1 q.1.2
    rw [norm_mul, norm_mul]
    have h2nn : 0 ≤ Commons.Analysis.Complex.curveConst β * (1 + q.2 ^ 2)⁻¹ :=
      mul_nonneg (Commons.Analysis.Complex.curveConst_pos hβ).le (by positivity)
    calc ‖F _ _‖ * ‖gW1 R β q.2‖ * ‖WmK R m q.1.1 q.1.2‖
        ≤ B * (Commons.Analysis.Complex.curveConst β * (1 + q.2 ^ 2)⁻¹)
            * (K ^ m * (∏ j, Awt (q.1.1 j)) * (∏ j, Awt (q.1.2 j))) :=
          mul_le_mul (mul_le_mul hb hw (norm_nonneg _) hB) hW (norm_nonneg _) (mul_nonneg hB h2nn)
      _ = B * K ^ m * Commons.Analysis.Complex.curveConst β
            * ((∏ j, Awt (q.1.1 j)) * (∏ j, Awt (q.1.2 j)) * (1 + q.2 ^ 2)⁻¹) := by ring


/-! ## Admissibility predicate -/

/-- Admissibility of an `m`-fold Green–Tao datum. -/
def ZetaAdm (β : ℝ) (m : ℕ) (G : (Fin m → ℂ) → (Fin m → ℂ) → ℂ) (B : ℝ) : Prop :=
  Continuous (Function.uncurry G) ∧
  (∀ (j : Fin m) (z z' : Fin m → ℂ), ZetaRegVec β z → ZetaRegVec β z' →
      DifferentiableAt ℂ (fun u : ℂ => G (Function.update z j u) z') (z j)) ∧
  (∀ (j : Fin m) (z z' : Fin m → ℂ), ZetaRegVec β z → ZetaRegVec β z' →
      DifferentiableAt ℂ (fun u : ℂ => G z (Function.update z' j u)) (z' j)) ∧
  (∀ z z' : Fin m → ℂ, ZetaRegVec β z → ZetaRegVec β z' → ‖G z z'‖ ≤ B)

lemma continuous_cons_const {m : ℕ} (a : ℂ) :
    Continuous (fun p : (Fin m → ℂ) × (Fin m → ℂ) =>
      Fin.cons (α := fun _ => ℂ) a p.1) := by
  refine continuous_pi (fun i => ?_)
  rcases Fin.eq_zero_or_eq_succ i with h | ⟨j, rfl⟩
  · subst h
    have heq : (fun p : (Fin m → ℂ) × (Fin m → ℂ) => Fin.cons (α := fun _ => ℂ) a p.1 0)
        = fun _ : (Fin m → ℂ) × (Fin m → ℂ) => a := by funext p; rw [Fin.cons_zero]
    rw [heq]; exact continuous_const
  · have heq : (fun p : (Fin m → ℂ) × (Fin m → ℂ) => Fin.cons (α := fun _ => ℂ) a p.1 j.succ)
        = fun p : (Fin m → ℂ) × (Fin m → ℂ) => p.1 j := by funext p; rw [Fin.cons_succ]
    rw [heq]; exact (continuous_apply j).comp continuous_fst

lemma continuous_cons_snd {m : ℕ} (a : ℂ) :
    Continuous (fun p : (Fin m → ℂ) × (Fin m → ℂ) =>
      Fin.cons (α := fun _ => ℂ) a p.2) := by
  refine continuous_pi (fun i => ?_)
  rcases Fin.eq_zero_or_eq_succ i with h | ⟨j, rfl⟩
  · subst h
    have heq : (fun p : (Fin m → ℂ) × (Fin m → ℂ) => Fin.cons (α := fun _ => ℂ) a p.2 0)
        = fun _ : (Fin m → ℂ) × (Fin m → ℂ) => a := by funext p; rw [Fin.cons_zero]
    rw [heq]; exact continuous_const
  · have heq : (fun p : (Fin m → ℂ) × (Fin m → ℂ) => Fin.cons (α := fun _ => ℂ) a p.2 j.succ)
        = fun p : (Fin m → ℂ) × (Fin m → ℂ) => p.2 j := by funext p; rw [Fin.cons_succ]
    rw [heq]; exact (continuous_apply j).comp continuous_snd

lemma update_cons_succ_apply {m : ℕ} (a : ℂ) (z : Fin m → ℂ) (j : Fin m) (u : ℂ) :
    Function.update (Fin.cons (α := fun _ => ℂ) a z) j.succ u
      = Fin.cons (α := fun _ => ℂ) a (Function.update z j u) := by
  funext i
  rw [Function.update_apply]
  rcases Fin.eq_zero_or_eq_succ i with h | ⟨k, rfl⟩
  · subst h
    rw [if_neg (Fin.succ_ne_zero j).symm, Fin.cons_zero, Fin.cons_zero]
  · by_cases hk : k = j
    · subst hk
      rw [if_pos rfl, Fin.cons_succ, Function.update_self]
    · rw [if_neg (fun h => hk (Fin.succ_injective _ h)), Fin.cons_succ, Fin.cons_succ,
        Function.update_of_ne hk]

lemma ZetaAdm_cons {β : ℝ} {m : ℕ} {G : (Fin (m+1) → ℂ) → (Fin (m+1) → ℂ) → ℂ} {B : ℝ}
    (h : ZetaAdm β (m+1) G B) (a b : ℂ) (ha : ZetaReg β a) (hb : ZetaReg β b) :
    ZetaAdm β m (fun z z' => G (Fin.cons (α := fun _ => ℂ) a z)
      (Fin.cons (α := fun _ => ℂ) b z')) B := by
  obtain ⟨hc, hd1, hd2, hbnd⟩ := h
  refine ⟨hc.comp ((continuous_cons_const a).prodMk (continuous_cons_snd b)), ?_, ?_, ?_⟩
  · intro j z z' hz hz'
    have h := hd1 j.succ (Fin.cons a z) (Fin.cons b z')
      (ZetaRegVec_cons ha hz) (ZetaRegVec_cons hb hz')
    rw [Fin.cons_succ] at h
    have heq : (fun u : ℂ => G (Function.update (Fin.cons a z) j.succ u) (Fin.cons b z'))
        = fun u : ℂ => G (Fin.cons a (Function.update z j u)) (Fin.cons b z') := by
      funext u; rw [update_cons_succ_apply]
    rw [heq] at h
    exact h
  · intro j z z' hz hz'
    have h := hd2 j.succ (Fin.cons a z) (Fin.cons b z')
      (ZetaRegVec_cons ha hz) (ZetaRegVec_cons hb hz')
    rw [Fin.cons_succ] at h
    have heq : (fun u : ℂ => G (Fin.cons a z) (Function.update (Fin.cons b z') j.succ u))
        = fun u : ℂ => G (Fin.cons a z) (Fin.cons b (Function.update z' j u)) := by
      funext u; rw [update_cons_succ_apply]
    rw [heq] at h
    exact h
  · intro z z' hz hz'
    exact hbnd _ _ (ZetaRegVec_cons ha hz) (ZetaRegVec_cons hb hz')

/-- Admissible data are closed under addition (same bound). -/
lemma ZetaAdm_add {β : ℝ} {m : ℕ} {G H : (Fin m → ℂ) → (Fin m → ℂ) → ℂ} {B₁ B₂ : ℝ}
    (hG : ZetaAdm β m G B₁) (hH : ZetaAdm β m H B₂) :
    ZetaAdm β m (fun z z' => G z z' + H z z') (B₁ + B₂) := by
  obtain ⟨hc1, hd11, hd12, hb1⟩ := hG
  obtain ⟨hc2, hd21, hd22, hb2⟩ := hH
  refine ⟨hc1.add hc2, ?_, ?_, ?_⟩
  · intro j z z' hz hz'
    exact (hd11 j z z' hz hz').add (hd21 j z z' hz hz')
  · intro j z z' hz hz'
    exact (hd12 j z z' hz hz').add (hd22 j z z' hz hz')
  · intro z z' hz hz'
    exact le_trans (norm_add_le _ _) (add_le_add (hb1 z z' hz hz') (hb2 z z' hz hz'))


lemma closedBall_half_subset {β : ℝ} (hβ : 0 < β) :
    Metric.closedBall (0:ℂ) (zetaRho β / 2) ⊆ Metric.closedBall (0:ℂ) (zetaRho β) := by
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right] at hz ⊢
  linarith [zetaRho_pos hβ]

lemma deriv_bound_closedBall {β : ℝ} (hβ : 0 < β) (hβ10 : β ≤ 1/10) (g : ℂ → ℂ) (B : ℝ)
    (hd : ∀ z : ℂ, ZetaReg β z → DifferentiableAt ℂ g z)
    (hb : ∀ z : ℂ, ZetaReg β z → ‖g z‖ ≤ B) {w : ℂ}
    (hw : w ∈ Metric.closedBall (0:ℂ) (zetaRho β / 2)) :
    ‖deriv g w‖ ≤ 2 * B / zetaRho β := by
  have hρpos : 0 < zetaRho β := zetaRho_pos hβ
  have hρ2 : 0 < zetaRho β / 2 := by positivity
  have hsub : Metric.closedBall w (zetaRho β / 2) ⊆ {z : ℂ | ZetaReg β z} := by
    intro z hz
    refine closedBall_subset_ZetaReg hβ hβ10 ?_
    rw [Metric.mem_closedBall, dist_zero_right]
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    rw [Metric.mem_closedBall, dist_zero_right] at hw
    calc ‖z‖ = ‖(z - w) + w‖ := by ring_nf
      _ ≤ ‖z - w‖ + ‖w‖ := norm_add_le _ _
      _ ≤ zetaRho β / 2 + zetaRho β / 2 := add_le_add hz hw
      _ = zetaRho β := by ring
  have hdiff : DifferentiableOn ℂ g (Metric.closedBall w (zetaRho β / 2)) :=
    fun z hz => (hd z (hsub hz)).differentiableWithinAt
  have hcl : closure (Metric.ball w (zetaRho β / 2)) = Metric.closedBall w (zetaRho β / 2) :=
    closure_ball _ (ne_of_gt hρ2)
  have hdc : DiffContOnCl ℂ g (Metric.ball w (zetaRho β / 2)) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [hcl]; exact hdiff
  have hbnd : ∀ z ∈ Metric.sphere w (zetaRho β / 2), ‖g z‖ ≤ B := by
    intro z hz
    refine hb z (hsub ?_)
    rw [Metric.mem_closedBall, dist_eq_norm]
    rw [Metric.mem_sphere, dist_eq_norm] at hz
    linarith [hz.le]
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ2 hdc hbnd
  have h2 : B / (zetaRho β / 2) = 2 * B / zetaRho β := by
    rw [div_div_eq_mul_div]; ring
  rwa [h2] at h

lemma slope_bound {β : ℝ} (hβ : 0 < β) (hβ10 : β ≤ 1/10) (g : ℂ → ℂ) (B : ℝ)
    (hd : ∀ z : ℂ, ZetaReg β z → DifferentiableAt ℂ g z)
    (hb : ∀ z : ℂ, ZetaReg β z → ‖g z‖ ≤ B) {h : ℂ} (hh : ‖h‖ ≤ zetaRho β / 2) :
    ‖(g h - g 0) / h‖ ≤ 2 * B / zetaRho β := by
  have hρpos : 0 < zetaRho β := zetaRho_pos hβ
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hb 0 (zetaReg_zero hβ))
  rcases eq_or_ne h 0 with rfl | hne
  · simp only [sub_self, zero_div, norm_zero]
    positivity
  · have hsub : ∀ w ∈ Metric.closedBall (0:ℂ) (zetaRho β / 2), DifferentiableAt ℂ g w :=
      fun w hw => hd w (closedBall_subset_ZetaReg hβ hβ10 (closedBall_half_subset hβ hw))
    have hbnd : ∀ w ∈ Metric.closedBall (0:ℂ) (zetaRho β / 2), ‖deriv g w‖ ≤ 2 * B / zetaRho β :=
      fun w hw => deriv_bound_closedBall hβ hβ10 g B hd hb hw
    have hcvx : Convex ℝ (Metric.closedBall (0:ℂ) (zetaRho β / 2)) := convex_closedBall _ _
    have hmem0 : (0:ℂ) ∈ Metric.closedBall (0:ℂ) (zetaRho β / 2) := by
      rw [Metric.mem_closedBall, dist_zero_right]
      simp only [norm_zero]; positivity
    have hmemh : h ∈ Metric.closedBall (0:ℂ) (zetaRho β / 2) := by
      rw [Metric.mem_closedBall, dist_zero_right]; exact hh
    have hkey := Convex.norm_image_sub_le_of_norm_deriv_le hsub hbnd hcvx hmem0 hmemh
    rw [sub_zero] at hkey
    rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr hne)]
    exact hkey


/-! ## The recursion step -/

lemma zetaMmf_succ {R : ℝ} {m : ℕ}
    (F : (Fin (m + 1) → ℂ) → (Fin (m + 1) → ℂ) → ℂ)
    (hInt : MeasureTheory.Integrable
      (Function.uncurry (fun T T' => F (fun j => zetaM1Eta R (T j))
          (fun j => zetaM1Eta R (T' j))
        * ∏ j : Fin (m + 1),
            zetaM1Kernel R (fun _ _ => (1:ℂ)) (zetaM1Eta R (T j)) (zetaM1Eta R (T' j))))
      ((MeasureTheory.volume : MeasureTheory.Measure (Fin (m + 1) → ℝ)).prod
        (MeasureTheory.volume : MeasureTheory.Measure (Fin (m + 1) → ℝ)))) :
    zetaMmf R (m + 1) F
      = ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ (2 * m) * Complex.I ^ (2 * m) *
        ∫ w : Fin m → ℝ, ∫ w' : Fin m → ℝ,
          zetaMf1 R (fun ζ ζ' => F (Fin.cons ζ (fun j => zetaM1Eta R (w j)))
              (Fin.cons ζ' (fun j => zetaM1Eta R (w' j))))
          * ∏ j : Fin m,
              zetaM1Kernel R (fun _ _ => (1:ℂ)) (zetaM1Eta R (w j)) (zetaM1Eta R (w' j)) := by
  unfold zetaMmf zetaMf1
  rw [Commons.Analysis.Measure.Fubini.integral_fin_cons_split_swap (n := m)
    (Φ := fun T T' => F (fun j => zetaM1Eta R (T j)) (fun j => zetaM1Eta R (T' j))
      * ∏ j : Fin (m + 1), zetaM1Kernel R (fun _ _ => (1:ℂ))
          (zetaM1Eta R (T j)) (zetaM1Eta R (T' j))) hInt]
  have hprod : ∀ (s s' : ℝ) (w w' : Fin m → ℝ),
      F (fun j => zetaM1Eta R ((Fin.cons s w : Fin (m + 1) → ℝ) j))
          (fun j => zetaM1Eta R ((Fin.cons s' w' : Fin (m + 1) → ℝ) j))
        * ∏ j : Fin (m + 1), zetaM1Kernel R (fun _ _ => (1:ℂ))
            (zetaM1Eta R ((Fin.cons s w : Fin (m + 1) → ℝ) j))
            (zetaM1Eta R ((Fin.cons s' w' : Fin (m + 1) → ℝ) j))
        = (F (Fin.cons (zetaM1Eta R s) (fun j => zetaM1Eta R (w j)))
              (Fin.cons (zetaM1Eta R s') (fun j => zetaM1Eta R (w' j)))
            * zetaM1Kernel R (fun _ _ => (1:ℂ)) (zetaM1Eta R s) (zetaM1Eta R s'))
          * ∏ j : Fin m, zetaM1Kernel R (fun _ _ => (1:ℂ))
              (zetaM1Eta R (w j)) (zetaM1Eta R (w' j)) := by
    intro s s' w w'
    have hF1 : (fun j : Fin (m + 1) => zetaM1Eta R ((Fin.cons s w : Fin (m + 1) → ℝ) j))
        = Fin.cons (zetaM1Eta R s) (fun j => zetaM1Eta R (w j)) := by
      funext j; refine Fin.cases ?_ ?_ j <;> simp [Fin.cons_zero, Fin.cons_succ]
    have hF2 : (fun j : Fin (m + 1) => zetaM1Eta R ((Fin.cons s' w' : Fin (m + 1) → ℝ) j))
        = Fin.cons (zetaM1Eta R s') (fun j => zetaM1Eta R (w' j)) := by
      funext j; refine Fin.cases ?_ ?_ j <;> simp [Fin.cons_zero, Fin.cons_succ]
    rw [Fin.prod_univ_succ]
    simp only [hF1, hF2, Fin.cons_zero, Fin.cons_succ]
    ring
  simp only [hprod]
  have hpow : Complex.I ^ (2 * (m + 1)) = Complex.I ^ (2 * m) * (Complex.I ^ 2) := by
    rw [show 2 * (m + 1) = 2 * m + 2 by ring, pow_add]
  have hA : ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ (2 * (m + 1))
      = ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ (2 * m)
        * ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ 2 := by
    rw [show 2 * (m + 1) = 2 * m + 2 by ring, pow_add]
  have hpull : ∀ (w w' : Fin m → ℝ),
      (∫ s : ℝ, ∫ s' : ℝ,
        (F (Fin.cons (zetaM1Eta R s) (fun j => zetaM1Eta R (w j)))
            (Fin.cons (zetaM1Eta R s') (fun j => zetaM1Eta R (w' j)))
          * zetaM1Kernel R (fun _ _ => (1:ℂ)) (zetaM1Eta R s) (zetaM1Eta R s'))
        * ∏ j : Fin m, zetaM1Kernel R (fun _ _ => (1:ℂ))
            (zetaM1Eta R (w j)) (zetaM1Eta R (w' j)))
      = (∫ s : ℝ, ∫ s' : ℝ,
          F (Fin.cons (zetaM1Eta R s) (fun j => zetaM1Eta R (w j)))
            (Fin.cons (zetaM1Eta R s') (fun j => zetaM1Eta R (w' j)))
          * zetaM1Kernel R (fun _ _ => (1:ℂ)) (zetaM1Eta R s) (zetaM1Eta R s'))
        * ∏ j : Fin m, zetaM1Kernel R (fun _ _ => (1:ℂ))
            (zetaM1Eta R (w j)) (zetaM1Eta R (w' j)) := by
    intro w w'
    rw [← MeasureTheory.integral_mul_const]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with s
    rw [← MeasureTheory.integral_mul_const]
  simp only [hpull]
  rw [hpow, hA]
  simp_rw [show ∀ (c a b : ℂ), (c * a) * b = c * (a * b) from fun c a b => by ring,
    MeasureTheory.integral_const_mul]
  try ring


/-- The difference-quotient of a cons-restriction is admissible with bound `2B/ρ`. -/
lemma ZetaAdm_dq {β : ℝ} (hβ : 0 < β) (hβ10 : β ≤ 1/10) {m : ℕ}
    {G : (Fin (m+1) → ℂ) → (Fin (m+1) → ℂ) → ℂ} {B : ℝ} (hB : 0 ≤ B)
    (hh : ZetaAdm β (m+1) G B) {h : ℂ} (hhρ : ‖h‖ ≤ zetaRho β / 2) :
    ZetaAdm β m (fun z z' => (G (Fin.cons 0 z) (Fin.cons h z')
      - G (Fin.cons 0 z) (Fin.cons 0 z')) / h) (2 * B / zetaRho β) := by
  have hhreg : ZetaReg β h :=
    closedBall_subset_ZetaReg hβ hβ10 (closedBall_half_subset hβ (by
      rwa [Metric.mem_closedBall, dist_zero_right]))
  have h1 := ZetaAdm_cons hh 0 h (zetaReg_zero hβ) hhreg
  have h0 := ZetaAdm_cons hh 0 0 (zetaReg_zero hβ) (zetaReg_zero hβ)
  obtain ⟨hc1, hd11, hd12, hb1⟩ := h1
  obtain ⟨hc0, hd01, hd02, hb0⟩ := h0
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (hc1.sub hc0).div_const h
  · intro j z z' hz hz'
    exact ((hd11 j z z' hz hz').sub (hd01 j z z' hz hz')).div_const h
  · intro j z z' hz hz'
    exact ((hd12 j z z' hz hz').sub (hd02 j z z' hz hz')).div_const h
  · intro z z' hz hz'
    have hg : ∀ u : ℂ, ZetaReg β u →
        DifferentiableAt ℂ (fun w => G (Fin.cons 0 z) (Fin.cons w z')) u := by
      intro u hu
      have hh2 := hh.2.2.1 0 (Fin.cons 0 z) (Fin.cons u z')
        (ZetaRegVec_cons (zetaReg_zero hβ) hz) (ZetaRegVec_cons hu hz')
      rw [Fin.cons_zero] at hh2
      have heq : (fun w : ℂ => G (Fin.cons 0 z) (Function.update (Fin.cons u z') 0 w))
          = fun w : ℂ => G (Fin.cons 0 z) (Fin.cons w z') := by
        funext w; rw [Fin.update_cons_zero]
      rwa [heq] at hh2
    have hb' : ∀ u : ℂ, ZetaReg β u → ‖G (Fin.cons 0 z) (Fin.cons u z')‖ ≤ B :=
      fun u hu => hh.2.2.2 _ _ (ZetaRegVec_cons (zetaReg_zero hβ) hz) (ZetaRegVec_cons hu hz')
    exact slope_bound hβ hβ10 _ B hg hb' hhρ


/-- The `z'`-slope of a cons-restriction at a region point is dominated by `2B/ρ`. -/
lemma slope_dom_reg {β R : ℝ} (hβ : 0 < β) (hβ10 : β ≤ 1/10) (hR : 3 ≤ R) {m : ℕ}
    (F : (Fin (m+1) → ℂ) → (Fin (m+1) → ℂ) → ℂ) (B : ℝ)
    (hd2 : ∀ z z' : Fin (m+1) → ℂ, ZetaRegVec β z → ZetaRegVec β z' →
        DifferentiableAt ℂ (fun u : ℂ => F z (Function.update z' 0 u)) (z' 0))
    (w w' : Fin m → ℝ) :
    ∀ u : ℂ, ZetaReg β u → DifferentiableAt ℂ
      (fun v : ℂ => F (Fin.cons 0 (fun j => zetaM1Eta R (w j)))
        (Fin.cons v (fun j => zetaM1Eta R (w' j)))) u := by
    intro u huu
    have h2 := hd2 (Fin.cons 0 (fun j => zetaM1Eta R (w j))) (Fin.cons u (fun j => zetaM1Eta R (w' j)))
      (ZetaRegVec_cons (zetaReg_zero hβ) (fun j => eta_mem_ZetaReg hβ hR (w j)))
      (ZetaRegVec_cons huu (fun j => eta_mem_ZetaReg hβ hR (w' j)))
    rw [Fin.cons_zero] at h2
    have heq : (fun v : ℂ => F (Fin.cons 0 (fun j => zetaM1Eta R (w j)))
          (Function.update (Fin.cons u (fun j => zetaM1Eta R (w' j))) 0 v))
        = fun v : ℂ => F (Fin.cons 0 (fun j => zetaM1Eta R (w j)))
          (Fin.cons v (fun j => zetaM1Eta R (w' j))) := by
      funext v; rw [Fin.update_cons_zero]
    rwa [heq] at h2

lemma slope_dom {β R : ℝ} (hβ : 0 < β) (hβ10 : β ≤ 1/10) (hR : 3 ≤ R) {m : ℕ}
    (F : (Fin (m+1) → ℂ) → (Fin (m+1) → ℂ) → ℂ) (B : ℝ)
    (hd2 : ∀ z z' : Fin (m+1) → ℂ, ZetaRegVec β z → ZetaRegVec β z' →
        DifferentiableAt ℂ (fun u : ℂ => F z (Function.update z' 0 u)) (z' 0))
    (hFb : ∀ z z', ZetaRegVec β z → ZetaRegVec β z' → ‖F z z'‖ ≤ B)
    {h : ℂ} (hh : ‖h‖ ≤ zetaRho β / 2) (w w' : Fin m → ℝ) :
    ‖(F (Fin.cons 0 (fun j => zetaM1Eta R (w j))) (Fin.cons h (fun j => zetaM1Eta R (w' j)))
        - F (Fin.cons 0 (fun j => zetaM1Eta R (w j))) (Fin.cons 0 (fun j => zetaM1Eta R (w' j)))) / h‖
      ≤ 2 * B / zetaRho β := by
  have hz : ZetaRegVec β (Fin.cons 0 (fun j => zetaM1Eta R (w j))) :=
    ZetaRegVec_cons (zetaReg_zero hβ) (fun j => eta_mem_ZetaReg hβ hR (w j))
  have hb : ∀ u : ℂ, ZetaReg β u → ‖F (Fin.cons 0 (fun j => zetaM1Eta R (w j)))
      (Fin.cons u (fun j => zetaM1Eta R (w' j)))‖ ≤ B := fun u hu =>
    hFb _ _ hz (ZetaRegVec_cons hu (fun j => eta_mem_ZetaReg hβ hR (w' j)))
  exact slope_bound hβ hβ10 _ B (slope_dom_reg hβ hβ10 hR F B hd2 w w') hb hh


/-- Measurability of the `cons` map in the second argument (with a fixed head). -/
lemma measurable_cons_snd_fixed {R : ℝ} {m : ℕ} (h : ℂ) :
    Measurable (fun w' : Fin m → ℝ =>
      Fin.cons (α := fun _ => ℂ) h (fun j => zetaM1Eta R (w' j))) := by
  refine measurable_pi_iff.mpr (fun i => ?_)
  rcases Fin.eq_zero_or_eq_succ i with hh | ⟨j, rfl⟩
  · subst hh; simpa only [Fin.cons_zero] using measurable_const
  · have heq : (fun x : Fin m → ℝ =>
        Fin.cons (α := fun _ => ℂ) h (fun j => zetaM1Eta R (x j)) j.succ)
        = fun x : Fin m → ℝ => zetaM1Eta R (x j) := by funext x; rw [Fin.cons_succ]
    rw [heq]
    exact (zetaM1Eta_continuous R).measurable.comp (continuous_apply j).measurable

lemma tendsto_zetaMmf_seq {β R : ℝ} (hβ : 0 < β) (hβ10 : β ≤ 1/10) (hR : 3 ≤ R) {m : ℕ}
    (F : (Fin (m+1) → ℂ) → (Fin (m+1) → ℂ) → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hcont : Continuous (Function.uncurry F))
    (hd2 : ∀ z z' : Fin (m+1) → ℂ, ZetaRegVec β z → ZetaRegVec β z' →
        DifferentiableAt ℂ (fun u : ℂ => F z (Function.update z' 0 u)) (z' 0))
    (hFb : ∀ z z', ZetaRegVec β z → ZetaRegVec β z' → ‖F z z'‖ ≤ B) :
    Tendsto (fun h : ℂ => zetaMmf R m (fun z z' =>
        (F (Fin.cons 0 z) (Fin.cons h z') - F (Fin.cons 0 z) (Fin.cons 0 z')) / h))
      (nhdsWithin (0:ℂ) {(0:ℂ)}ᶜ)
      (𝓝 (zetaMmf R m (fun z z' => deriv (fun u : ℂ => F (Fin.cons 0 z) (Fin.cons u z')) 0))) := by
  have hρpos : 0 < zetaRho β := zetaRho_pos hβ
  obtain ⟨K, hKpos, hKle⟩ := zetaM1Kernel_eta_bound (R := R) hR
  have hK : ∀ x y : ℝ, ‖zetaM1Kernel R (fun _ _ => (1:ℂ)) (zetaM1Eta R x) (zetaM1Eta R y)‖
      ≤ K * Awt x * Awt y := fun x y => by
    simpa only [Awt, zetaM1Kernel, Pi.one_apply, one_mul, mul_assoc] using hKle x y
  have hRne : R ≠ 0 := by linarith
  have hdom : MeasureTheory.Integrable (fun p : (Fin m → ℝ) × (Fin m → ℝ) =>
      (2 * B / zetaRho β) * K ^ m * ((∏ j, Awt (p.1 j)) * (∏ j, Awt (p.2 j))))
      ((MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ)).prod
        (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ))) := by
    have hprod : MeasureTheory.Integrable (fun p : (Fin m → ℝ) × (Fin m → ℝ) =>
        (∏ j, Awt (p.1 j)) * (∏ j, Awt (p.2 j)))
        ((MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ)).prod
          (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ))) := by
      simpa [Awt] using Commons.Analysis.Measure.integrable_weight_prod_fin m
    exact (hprod.const_mul ((2 * B / zetaRho β) * K ^ m))
  have hscale : 0 < zetaRho β / 2 := by positivity
  -- the product-measure DCT
  have hDCT : Tendsto (fun h : ℂ => ∫ p : (Fin m → ℝ) × (Fin m → ℝ),
        (F (Fin.cons 0 (fun j => zetaM1Eta R (p.1 j)))
           (Fin.cons h (fun j => zetaM1Eta R (p.2 j)))
          - F (Fin.cons 0 (fun j => zetaM1Eta R (p.1 j)))
            (Fin.cons 0 (fun j => zetaM1Eta R (p.2 j)))) / h
        * WmK R m p.1 p.2)
        (nhdsWithin (0:ℂ) {(0:ℂ)}ᶜ)
        (𝓝 (∫ p : (Fin m → ℝ) × (Fin m → ℝ),
          deriv (fun u : ℂ => F (Fin.cons 0 (fun j => zetaM1Eta R (p.1 j)))
            (Fin.cons u (fun j => zetaM1Eta R (p.2 j)))) 0 * WmK R m p.1 p.2)) := by
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := ((MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ)).prod
          (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ))))
      (l := nhdsWithin (0:ℂ) {(0:ℂ)}ᶜ)
      (F := fun h : ℂ => fun p : (Fin m → ℝ) × (Fin m → ℝ) =>
        (F (Fin.cons 0 (fun j => zetaM1Eta R (p.1 j)))
           (Fin.cons h (fun j => zetaM1Eta R (p.2 j)))
          - F (Fin.cons 0 (fun j => zetaM1Eta R (p.1 j)))
            (Fin.cons 0 (fun j => zetaM1Eta R (p.2 j)))) / h
        * WmK R m p.1 p.2)
      (f := fun p : (Fin m → ℝ) × (Fin m → ℝ) =>
        deriv (fun u : ℂ => F (Fin.cons 0 (fun j => zetaM1Eta R (p.1 j)))
          (Fin.cons u (fun j => zetaM1Eta R (p.2 j)))) 0 * WmK R m p.1 p.2)
      (fun p => (2 * B / zetaRho β) * K ^ m * ((∏ j, Awt (p.1 j)) * (∏ j, Awt (p.2 j))))
      ?_ ?_ hdom ?_
    · filter_upwards with h
      have h1 : Measurable (fun p : (Fin m → ℝ) × (Fin m → ℝ) =>
          F (Fin.cons (α := fun _ => ℂ) 0 (fun j => zetaM1Eta R (p.1 j)))
            (Fin.cons (α := fun _ => ℂ) h (fun j => zetaM1Eta R (p.2 j)))) :=
        measurable_F_cons (R := R) F hcont measurable_const measurable_const
          measurable_fst measurable_snd
      have h2 : Measurable (fun p : (Fin m → ℝ) × (Fin m → ℝ) =>
          F (Fin.cons (α := fun _ => ℂ) 0 (fun j => zetaM1Eta R (p.1 j)))
            (Fin.cons (α := fun _ => ℂ) 0 (fun j => zetaM1Eta R (p.2 j)))) :=
        measurable_F_cons (R := R) F hcont measurable_const measurable_const
          measurable_fst measurable_snd
      have hk : Measurable (fun p : (Fin m → ℝ) × (Fin m → ℝ) => WmK R m p.1 p.2) :=
        measurable_WmK R hRne m
      exact Measurable.aestronglyMeasurable (((h1.sub h2).div_const h).mul hk)
    · filter_upwards [(nhdsWithin_le_nhds (Metric.ball_mem_nhds (0:ℂ) hscale))] with h hhball
      have hhρ : ‖h‖ ≤ zetaRho β / 2 := by
        rw [Metric.mem_ball, dist_zero_right] at hhball; exact hhball.le
      filter_upwards with p
      rw [norm_mul]
      calc ‖(F (Fin.cons 0 (fun j => zetaM1Eta R (p.1 j)))
                (Fin.cons h (fun j => zetaM1Eta R (p.2 j)))
              - F (Fin.cons 0 (fun j => zetaM1Eta R (p.1 j)))
                (Fin.cons 0 (fun j => zetaM1Eta R (p.2 j)))) / h‖ * ‖WmK R m p.1 p.2‖
          ≤ (2 * B / zetaRho β) * (K ^ m * (∏ j, Awt (p.1 j)) * (∏ j, Awt (p.2 j))) :=
            mul_le_mul (slope_dom hβ hβ10 hR F B hd2 hFb (h := h) hhρ p.1 p.2)
              (norm_WmK_le hK m p.1 p.2) (norm_nonneg _) (by positivity)
        _ = (2 * B / zetaRho β) * K ^ m * ((∏ j, Awt (p.1 j)) * (∏ j, Awt (p.2 j))) := by ring
    · filter_upwards with p
      have hreg : ZetaRegVec β (Fin.cons 0 (fun j => zetaM1Eta R (p.1 j))) :=
        ZetaRegVec_cons (zetaReg_zero hβ) (fun j => eta_mem_ZetaReg hβ hR (p.1 j))
      have hreg' : ZetaRegVec β (Fin.cons 0 (fun j => zetaM1Eta R (p.2 j))) :=
        ZetaRegVec_cons (zetaReg_zero hβ) (fun j => eta_mem_ZetaReg hβ hR (p.2 j))
      have hder : HasDerivAt (fun u : ℂ => F (Fin.cons 0 (fun j => zetaM1Eta R (p.1 j)))
            (Fin.cons u (fun j => zetaM1Eta R (p.2 j))))
          (deriv (fun u : ℂ => F (Fin.cons 0 (fun j => zetaM1Eta R (p.1 j)))
            (Fin.cons u (fun j => zetaM1Eta R (p.2 j)))) 0) 0 := by
        have h2 := hasDerivAt_deriv_iff.mpr (hd2 _ _ hreg hreg')
        simp only [Fin.update_cons_zero, Fin.cons_zero] at h2
        exact h2
      have ht := hder.tendsto_slope
      have heq : slope (fun u : ℂ => F (Fin.cons 0 (fun j => zetaM1Eta R (p.1 j)))
              (Fin.cons u (fun j => zetaM1Eta R (p.2 j)))) 0
          = fun h : ℂ => (F (Fin.cons 0 (fun j => zetaM1Eta R (p.1 j)))
                (Fin.cons h (fun j => zetaM1Eta R (p.2 j)))
              - F (Fin.cons 0 (fun j => zetaM1Eta R (p.1 j)))
                (Fin.cons 0 (fun j => zetaM1Eta R (p.2 j)))) / h := by
        funext h; simp only [slope, sub_zero, vsub_eq_sub, smul_eq_mul]; ring
      rw [heq] at ht
      exact ht.mul_const (WmK R m p.1 p.2)
    -- convert the product integral back to `zetaMmf`
  have hconv : Tendsto (fun h : ℂ => ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ (2 * m)
        * Complex.I ^ (2 * m) * ∫ p : (Fin m → ℝ) × (Fin m → ℝ),
      (F (Fin.cons 0 (fun j => zetaM1Eta R (p.1 j)))
         (Fin.cons h (fun j => zetaM1Eta R (p.2 j)))
        - F (Fin.cons 0 (fun j => zetaM1Eta R (p.1 j)))
          (Fin.cons 0 (fun j => zetaM1Eta R (p.2 j)))) / h
      * WmK R m p.1 p.2)
      (nhdsWithin (0:ℂ) {(0:ℂ)}ᶜ)
      (𝓝 (((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ (2 * m) * Complex.I ^ (2 * m)
        * ∫ p : (Fin m → ℝ) × (Fin m → ℝ),
        deriv (fun u : ℂ => F (Fin.cons 0 (fun j => zetaM1Eta R (p.1 j)))
          (Fin.cons u (fun j => zetaM1Eta R (p.2 j)))) 0 * WmK R m p.1 p.2)) :=
    hDCT.const_mul _
  -- the two integrals are the `zetaMmf` values
  have hbridge : ∀ (G : (Fin m → ℂ) → (Fin m → ℂ) → ℂ)
      (hG : MeasureTheory.Integrable (fun p : (Fin m → ℝ) × (Fin m → ℝ) =>
        G (fun j => zetaM1Eta R (p.1 j)) (fun j => zetaM1Eta R (p.2 j)) * WmK R m p.1 p.2)
        ((MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ)).prod
          (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ)))),
      ∫ p : (Fin m → ℝ) × (Fin m → ℝ),
        G (fun j => zetaM1Eta R (p.1 j)) (fun j => zetaM1Eta R (p.2 j)) * WmK R m p.1 p.2
      = (2 * (Real.pi : ℂ)) ^ (2 * m) * zetaMmf R m G := by
    intro G hG
    rw [two_pi_pow_mul_zetaMmf]
    rw [MeasureTheory.integral_integral (μ := (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ)))
      (ν := (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ)))
      (f := fun x y => G (fun j => zetaM1Eta R (x j)) (fun j => zetaM1Eta R (y j)) * WmK R m x y) hG]
    rfl
  have hInt₁ : ∀ᶠ h : ℂ in nhdsWithin (0:ℂ) {(0:ℂ)}ᶜ,
      MeasureTheory.Integrable (fun p : (Fin m → ℝ) × (Fin m → ℝ) =>
      (F (Fin.cons 0 (fun j => zetaM1Eta R (p.1 j)))
         (Fin.cons h (fun j => zetaM1Eta R (p.2 j)))
        - F (Fin.cons 0 (fun j => zetaM1Eta R (p.1 j)))
          (Fin.cons 0 (fun j => zetaM1Eta R (p.2 j)))) / h
      * WmK R m p.1 p.2)
      ((MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ)).prod
        (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ))) := by
    filter_upwards [(nhdsWithin_le_nhds (Metric.ball_mem_nhds (0:ℂ) hscale))] with h hhball
    have hhρ : ‖h‖ ≤ zetaRho β / 2 := by
      rw [Metric.mem_ball, dist_zero_right] at hhball; exact hhball.le
    have h1 : Measurable (fun p : (Fin m → ℝ) × (Fin m → ℝ) =>
        F (Fin.cons (α := fun _ => ℂ) 0 (fun j => zetaM1Eta R (p.1 j)))
          (Fin.cons (α := fun _ => ℂ) h (fun j => zetaM1Eta R (p.2 j)))) :=
      measurable_F_cons (R := R) F hcont measurable_const measurable_const
        measurable_fst measurable_snd
    have h2 : Measurable (fun p : (Fin m → ℝ) × (Fin m → ℝ) =>
        F (Fin.cons (α := fun _ => ℂ) 0 (fun j => zetaM1Eta R (p.1 j)))
          (Fin.cons (α := fun _ => ℂ) 0 (fun j => zetaM1Eta R (p.2 j)))) :=
      measurable_F_cons (R := R) F hcont measurable_const measurable_const
        measurable_fst measurable_snd
    have hk : Measurable (fun p : (Fin m → ℝ) × (Fin m → ℝ) => WmK R m p.1 p.2) :=
      measurable_WmK R hRne m
    have hdom' : MeasureTheory.Integrable (fun p : (Fin m → ℝ) × (Fin m → ℝ) =>
        (2 * B / ‖h‖) * K ^ m * ((∏ j, Awt (p.1 j)) * (∏ j, Awt (p.2 j))))
        ((MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ)).prod
          (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ))) := by
      have hprod : MeasureTheory.Integrable (fun p : (Fin m → ℝ) × (Fin m → ℝ) =>
          (∏ j, Awt (p.1 j)) * (∏ j, Awt (p.2 j)))
          ((MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ)).prod
            (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ))) := by
        simpa [Awt] using Commons.Analysis.Measure.integrable_weight_prod_fin m
      exact (hprod.const_mul ((2 * B / ‖h‖) * K ^ m))
    refine hdom'.mono' (Measurable.aestronglyMeasurable
      (((h1.sub h2).div_const h).mul hk)) (Filter.Eventually.of_forall ?_)
    intro p
    rw [norm_mul]
    have hnum : ‖F (Fin.cons 0 (fun j => zetaM1Eta R (p.1 j)))
          (Fin.cons h (fun j => zetaM1Eta R (p.2 j)))
        - F (Fin.cons 0 (fun j => zetaM1Eta R (p.1 j)))
          (Fin.cons 0 (fun j => zetaM1Eta R (p.2 j)))‖ ≤ 2 * B := by
      have hz1 : ZetaRegVec β (Fin.cons 0 (fun j => zetaM1Eta R (p.1 j))) :=
        ZetaRegVec_cons (zetaReg_zero hβ) (fun j => eta_mem_ZetaReg hβ hR (p.1 j))
      have hz2 : ZetaRegVec β (Fin.cons 0 (fun j => zetaM1Eta R (p.2 j))) :=
        ZetaRegVec_cons (zetaReg_zero hβ) (fun j => eta_mem_ZetaReg hβ hR (p.2 j))
      have hz3 : ZetaRegVec β (Fin.cons h (fun j => zetaM1Eta R (p.2 j))) :=
        ZetaRegVec_cons
          (closedBall_subset_ZetaReg hβ hβ10 (closedBall_half_subset hβ (by
            rwa [Metric.mem_closedBall, dist_zero_right])))
          (fun j => eta_mem_ZetaReg hβ hR (p.2 j))
      refine le_trans (norm_sub_le _ _) ?_
      linarith [hFb _ _ hz1 hz3, hFb _ _ hz1 hz2]
    calc ‖(F (Fin.cons 0 (fun j => zetaM1Eta R (p.1 j)))
              (Fin.cons h (fun j => zetaM1Eta R (p.2 j)))
            - F (Fin.cons 0 (fun j => zetaM1Eta R (p.1 j)))
              (Fin.cons 0 (fun j => zetaM1Eta R (p.2 j)))) / h‖ * ‖WmK R m p.1 p.2‖
        ≤ (2 * B / ‖h‖) * (K ^ m * (∏ j, Awt (p.1 j)) * (∏ j, Awt (p.2 j))) := by
          refine mul_le_mul ?_ (norm_WmK_le hK m p.1 p.2) (norm_nonneg _) (by positivity)
          rw [norm_div]
          exact div_le_div_of_nonneg_right hnum (norm_nonneg h)
      _ = 2 * B / ‖h‖ * K ^ m * ((∏ j, Awt (p.1 j)) * (∏ j, Awt (p.2 j))) := by ring
  have hInt₂ : MeasureTheory.Integrable (fun p : (Fin m → ℝ) × (Fin m → ℝ) =>
      deriv (fun u : ℂ => F (Fin.cons 0 (fun j => zetaM1Eta R (p.1 j)))
        (Fin.cons u (fun j => zetaM1Eta R (p.2 j)))) 0 * WmK R m p.1 p.2)
      ((MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ)).prod
        (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ))) := by
    have hder : Measurable (fun p : (Fin m → ℝ) × (Fin m → ℝ) =>
        deriv (fun u : ℂ => F (Fin.cons 0 (fun j => zetaM1Eta R (p.1 j)))
          (Fin.cons u (fun j => zetaM1Eta R (p.2 j)))) 0) := by
      have h1 : Continuous (fun q : ((Fin m → ℝ) × (Fin m → ℝ)) × ℂ =>
          Fin.cons (α := fun _ => ℂ) 0 (fun j => zetaM1Eta R (q.1.1 j))) := by
        refine continuous_pi (fun i => ?_)
        rcases Fin.eq_zero_or_eq_succ i with hh | ⟨j, rfl⟩
        · subst hh; simpa only [Fin.cons_zero] using continuous_const
        · have heq : (fun q : ((Fin m → ℝ) × (Fin m → ℝ)) × ℂ =>
              Fin.cons (α := fun _ => ℂ) 0 (fun j => zetaM1Eta R (q.1.1 j)) j.succ)
              = fun q : ((Fin m → ℝ) × (Fin m → ℝ)) × ℂ => zetaM1Eta R (q.1.1 j) := by
            funext q; rw [Fin.cons_succ]
          rw [heq]
          exact (zetaM1Eta_continuous R).comp ((continuous_apply j).comp (continuous_fst.comp continuous_fst))
      have h2 : Continuous (fun q : ((Fin m → ℝ) × (Fin m → ℝ)) × ℂ =>
          Fin.cons (α := fun _ => ℂ) q.2 (fun j => zetaM1Eta R (q.1.2 j))) := by
        refine continuous_pi (fun i => ?_)
        rcases Fin.eq_zero_or_eq_succ i with hh | ⟨j, rfl⟩
        · subst hh; simpa only [Fin.cons_zero] using continuous_snd
        · have heq : (fun q : ((Fin m → ℝ) × (Fin m → ℝ)) × ℂ =>
              Fin.cons (α := fun _ => ℂ) q.2 (fun j => zetaM1Eta R (q.1.2 j)) j.succ)
              = fun q : ((Fin m → ℝ) × (Fin m → ℝ)) × ℂ => zetaM1Eta R (q.1.2 j) := by
            funext q; rw [Fin.cons_succ]
          rw [heq]
          exact (zetaM1Eta_continuous R).comp ((continuous_apply j).comp (continuous_snd.comp continuous_fst))
      exact (measurable_deriv_with_param (𝕜 := ℂ) (F := ℂ)
        (f := fun (p : (Fin m → ℝ) × (Fin m → ℝ)) (u : ℂ) =>
          F (Fin.cons (α := fun _ => ℂ) 0 (fun j => zetaM1Eta R (p.1 j)))
            (Fin.cons (α := fun _ => ℂ) u (fun j => zetaM1Eta R (p.2 j))))
        (hcont.comp (h1.prodMk h2))).comp (continuous_id.prodMk continuous_const).measurable
    have hk : Measurable (fun p : (Fin m → ℝ) × (Fin m → ℝ) => WmK R m p.1 p.2) :=
      measurable_WmK R hRne m
    have hdom2 : MeasureTheory.Integrable (fun p : (Fin m → ℝ) × (Fin m → ℝ) =>
        (B / zetaRho β) * K ^ m * ((∏ j, Awt (p.1 j)) * (∏ j, Awt (p.2 j))))
        ((MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ)).prod
          (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ))) := by
      have hprod : MeasureTheory.Integrable (fun p : (Fin m → ℝ) × (Fin m → ℝ) =>
          (∏ j, Awt (p.1 j)) * (∏ j, Awt (p.2 j)))
          ((MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ)).prod
            (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ))) := by
        simpa [Awt] using Commons.Analysis.Measure.integrable_weight_prod_fin m
      exact (hprod.const_mul ((B / zetaRho β) * K ^ m))
    refine hdom2.mono' ((hder.mul hk).aestronglyMeasurable) (Filter.Eventually.of_forall ?_)
    intro p
    rw [norm_mul]
    have hbd : ‖deriv (fun u : ℂ => F (Fin.cons 0 (fun j => zetaM1Eta R (p.1 j)))
        (Fin.cons u (fun j => zetaM1Eta R (p.2 j)))) 0‖ ≤ B / zetaRho β :=
      deriv_bound_ZetaReg hβ hβ10 _ B hB
        (fun u hu => slope_dom_reg hβ hβ10 hR F B hd2 p.1 p.2 u hu)
        (fun u hu => hFb _ _ (ZetaRegVec_cons (zetaReg_zero hβ) (fun j => eta_mem_ZetaReg hβ hR (p.1 j))) (ZetaRegVec_cons hu (fun j => eta_mem_ZetaReg hβ hR (p.2 j))))
    calc ‖deriv (fun u : ℂ => F (Fin.cons 0 (fun j => zetaM1Eta R (p.1 j)))
          (Fin.cons u (fun j => zetaM1Eta R (p.2 j)))) 0‖ * ‖WmK R m p.1 p.2‖
        ≤ (B / zetaRho β) * (K ^ m * (∏ j, Awt (p.1 j)) * (∏ j, Awt (p.2 j))) :=
          mul_le_mul hbd (norm_WmK_le hK m p.1 p.2) (norm_nonneg _) (by positivity)
      _ = (B / zetaRho β) * K ^ m * ((∏ j, Awt (p.1 j)) * (∏ j, Awt (p.2 j))) := by ring
  have hmu : ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ (2 * m) * Complex.I ^ (2 * m)
      * ((2 * (Real.pi : ℂ)) ^ (2 * m)) = 1 := by
    have h := two_pi_pow_mul (m := m)
    rw [mul_comm] at h
    exact h
  have hgoal : (fun h : ℂ => ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ (2 * m) * Complex.I ^ (2 * m)
      * ∫ p : (Fin m → ℝ) × (Fin m → ℝ),
      (F (Fin.cons 0 (fun j => zetaM1Eta R (p.1 j)))
         (Fin.cons h (fun j => zetaM1Eta R (p.2 j)))
        - F (Fin.cons 0 (fun j => zetaM1Eta R (p.1 j)))
          (Fin.cons 0 (fun j => zetaM1Eta R (p.2 j)))) / h
      * WmK R m p.1 p.2)
      =ᶠ[nhdsWithin (0:ℂ) {(0:ℂ)}ᶜ] fun h : ℂ => zetaMmf R m (fun z z' =>
        (F (Fin.cons 0 z) (Fin.cons h z') - F (Fin.cons 0 z) (Fin.cons 0 z')) / h) := by
    filter_upwards [hInt₁] with h hh
    rw [hbridge (fun z z' => (F (Fin.cons 0 z) (Fin.cons h z') - F (Fin.cons 0 z) (Fin.cons 0 z')) / h) hh]
    rw [show ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ (2 * m) * Complex.I ^ (2 * m)
        * ((2 * (Real.pi : ℂ)) ^ (2 * m) * zetaMmf R m (fun z z' =>
          (F (Fin.cons 0 z) (Fin.cons h z') - F (Fin.cons 0 z) (Fin.cons 0 z')) / h))
        = (((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ (2 * m) * Complex.I ^ (2 * m)
            * (2 * (Real.pi : ℂ)) ^ (2 * m))
          * zetaMmf R m (fun z z' =>
            (F (Fin.cons 0 z) (Fin.cons h z') - F (Fin.cons 0 z) (Fin.cons 0 z')) / h) from by ring,
      hmu, one_mul]
  have hgoal₀ : ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ (2 * m) * Complex.I ^ (2 * m)
      * ∫ p : (Fin m → ℝ) × (Fin m → ℝ),
        deriv (fun u : ℂ => F (Fin.cons 0 (fun j => zetaM1Eta R (p.1 j)))
          (Fin.cons u (fun j => zetaM1Eta R (p.2 j)))) 0 * WmK R m p.1 p.2
      = zetaMmf R m (fun z z' => deriv (fun u : ℂ => F (Fin.cons 0 z) (Fin.cons u z')) 0) := by
    rw [hbridge (fun z z' => deriv (fun u : ℂ => F (Fin.cons 0 z) (Fin.cons u z')) 0) hInt₂]
    rw [show ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ (2 * m) * Complex.I ^ (2 * m)
        * ((2 * (Real.pi : ℂ)) ^ (2 * m) * zetaMmf R m
          (fun z z' => deriv (fun u : ℂ => F (Fin.cons 0 z) (Fin.cons u z')) 0))
        = (((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ (2 * m) * Complex.I ^ (2 * m)
            * (2 * (Real.pi : ℂ)) ^ (2 * m))
          * zetaMmf R m (fun z z' => deriv (fun u : ℂ => F (Fin.cons 0 z) (Fin.cons u z')) 0) from by ring,
      hmu, one_mul]
  have hconv' : Tendsto (fun h : ℂ => zetaMmf R m (fun z z' =>
      (F (Fin.cons 0 z) (Fin.cons h z') - F (Fin.cons 0 z) (Fin.cons 0 z')) / h))
      (nhdsWithin (0:ℂ) {(0:ℂ)}ᶜ)
      (𝓝 (((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ (2 * m) * Complex.I ^ (2 * m)
        * ∫ p : (Fin m → ℝ) × (Fin m → ℝ),
        deriv (fun u : ℂ => F (Fin.cons 0 (fun j => zetaM1Eta R (p.1 j)))
          (Fin.cons u (fun j => zetaM1Eta R (p.2 j)))) 0 * WmK R m p.1 p.2)) :=
    Filter.Tendsto.congr' hgoal hconv
  rwa [hgoal₀] at hconv'


lemma update_zero_cons {m : ℕ} (u : ℂ) :
    Function.update (0 : Fin (m+1) → ℂ) 0 u = Fin.cons (α := fun _ => ℂ) u (0 : Fin m → ℂ) := by
  funext i
  rcases Fin.eq_zero_or_eq_succ i with h | ⟨j, rfl⟩
  · subst h; simp [Fin.cons_zero]
  · simp [Fin.cons_succ, Fin.succ_ne_zero]

lemma cons_zero_zero {m : ℕ} :
    Fin.cons (α := fun _ => ℂ) (0:ℂ) (0 : Fin m → ℂ) = 0 := by
  funext i
  induction i using Fin.cases with
  | zero => simp [Fin.cons_zero]
  | succ j => simp [Fin.cons_succ]

/-- Bound for the `∂_{z'}`-term of the induction step. -/
lemma deriv_mfold_bound {β R : ℝ} (hβ : 0 < β) (hβ10 : β ≤ 1/10) (hR : 3 ≤ R)
    {m : ℕ} (hm : 1 ≤ m)
    (C : ℝ) (hC1 : 1 ≤ C)
    (F : (Fin (m+1) → ℂ) → (Fin (m+1) → ℂ) → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hF : ZetaAdm β (m+1) F B)
    (IH : ∀ (G : (Fin m → ℂ) → (Fin m → ℂ) → ℂ) (B' : ℝ), 0 ≤ B' → ZetaAdm β m G B' →
        ‖zetaMmf R m G - G 0 0 * (Real.log R)^m‖ ≤ C^m * B' * (1 + (Real.log R)^(m-1))) :
    ‖zetaMmf R m (fun z z' => deriv (fun u : ℂ => F (Fin.cons 0 z) (Fin.cons u z')) 0)
        - deriv (fun u : ℂ => F (0 : Fin (m+1) → ℂ) (Fin.cons u 0)) 0
          * (Real.log R)^m‖
      ≤ C^m * (2 * B / zetaRho β) * (1 + (Real.log R)^(m-1)) := by
  have hρpos : 0 < zetaRho β := zetaRho_pos hβ
  have hcont : Continuous (Function.uncurry F) := hF.1
  have hd2 : ∀ z z' : Fin (m+1) → ℂ, ZetaRegVec β z → ZetaRegVec β z' →
      DifferentiableAt ℂ (fun u : ℂ => F z (Function.update z' 0 u)) (z' 0) :=
    fun z z' hz hz' => hF.2.2.1 0 z z' hz hz'
  have hFb : ∀ z z', ZetaRegVec β z → ZetaRegVec β z' → ‖F z z'‖ ≤ B := hF.2.2.2
  have h2B : 0 ≤ 2 * B / zetaRho β := div_nonneg (by linarith) hρpos.le
  set hs : ℕ → ℂ := fun n => ((min (1 / ((n : ℝ) + 1)) (zetaRho β / 2) : ℝ) : ℂ) with hsdef
  have hs_tendsto : Tendsto hs Filter.atTop (𝓝 (0:ℂ)) := by
    have h1 : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1) : ℝ)) Filter.atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 : Tendsto (fun _ : ℕ => zetaRho β / 2) Filter.atTop (𝓝 (zetaRho β / 2)) :=
      tendsto_const_nhds
    have h3 : Tendsto (fun n : ℕ => min (1 / ((n : ℝ) + 1)) (zetaRho β / 2)) Filter.atTop
        (𝓝 (min 0 (zetaRho β / 2))) := h1.min h2
    rw [min_eq_left (by positivity : (0:ℝ) ≤ zetaRho β / 2)] at h3
    exact (Complex.continuous_ofReal.tendsto 0).comp h3
  have hs_ne : ∀ n : ℕ, hs n ≠ 0 := by
    intro n
    have h1 : 0 < 1 / ((n : ℝ) + 1) := by positivity
    have h2 : 0 < min (1 / ((n : ℝ) + 1)) (zetaRho β / 2) := lt_min h1 (by positivity)
    have hne : ((min (1 / ((n : ℝ) + 1)) (zetaRho β / 2) : ℝ) : ℂ) ≠ 0 := by
      simpa using h2.ne'
    rw [hsdef]; exact hne
  have hs_le : ∀ n : ℕ, ‖hs n‖ ≤ zetaRho β / 2 := by
    intro n
    have h2 : 0 ≤ min (1 / ((n : ℝ) + 1)) (zetaRho β / 2) :=
      le_of_lt (lt_min (by positivity) (by positivity))
    have h3 : min (1 / ((n : ℝ) + 1)) (zetaRho β / 2) ≤ zetaRho β / 2 := min_le_right _ _
    have hnorm_sq : ‖hs n‖ ^ 2 = (min (1 / ((n : ℝ) + 1)) (zetaRho β / 2)) ^ 2 := by
      rw [hsdef, Complex.sq_norm, Complex.normSq_ofReal]; ring
    have hnn : 0 ≤ ‖hs n‖ := norm_nonneg _
    nlinarith [h2, h3, hnn, hnorm_sq, hρpos]
  have hs_event : ∀ᶠ n : ℕ in Filter.atTop, hs n ∈ ({(0:ℂ)}ᶜ : Set ℂ) :=
    Filter.Eventually.of_forall hs_ne
  have hconv := tendsto_zetaMmf_seq hβ hβ10 hR F B hB hcont hd2 hFb
  have hconv1 : Tendsto (fun n : ℕ => zetaMmf R m (fun z z' =>
      (F (Fin.cons 0 z) (Fin.cons (hs n) z') - F (Fin.cons 0 z) (Fin.cons 0 z')) / (hs n)))
      Filter.atTop (𝓝 (zetaMmf R m (fun z z' =>
        deriv (fun u : ℂ => F (Fin.cons 0 z) (Fin.cons u z')) 0))) :=
    hconv.comp (tendsto_nhdsWithin_iff.mpr ⟨hs_tendsto, hs_event⟩)
  -- the slope at `(0,0)`
  have hder : HasDerivAt (fun u : ℂ => F (0 : Fin (m+1) → ℂ) (Fin.cons u 0))
      (deriv (fun u : ℂ => F (0 : Fin (m+1) → ℂ) (Fin.cons u 0)) 0) 0 := by
    have h2 := hasDerivAt_deriv_iff.mpr
      (hd2 (0 : Fin (m+1) → ℂ) (0 : Fin (m+1) → ℂ)
        (fun i => zetaReg_zero hβ) (fun i => zetaReg_zero hβ))
    simpa only [update_zero_cons, Fin.cons_zero, Pi.zero_apply] using h2
  have hconv2 : Tendsto (fun n : ℕ =>
      (F (Fin.cons 0 (0 : Fin m → ℂ)) (Fin.cons (hs n) 0) - F (Fin.cons 0 (0 : Fin m → ℂ)) (Fin.cons 0 0))
        / (hs n))
      Filter.atTop (𝓝 (deriv (fun u : ℂ => F (0 : Fin (m+1) → ℂ) (Fin.cons u 0)) 0)) := by
    have ht := hder.tendsto_slope
    have heq : slope (fun u : ℂ => F (0 : Fin (m+1) → ℂ) (Fin.cons u 0)) 0
        = fun h : ℂ => (F (Fin.cons 0 (0 : Fin m → ℂ)) (Fin.cons h 0)
            - F (Fin.cons 0 (0 : Fin m → ℂ)) (Fin.cons 0 0)) / h := by
      funext h
      simp only [slope, sub_zero, vsub_eq_sub, smul_eq_mul]
      rw [cons_zero_zero]
      ring
    rw [heq] at ht
    exact ht.comp (tendsto_nhdsWithin_iff.mpr ⟨hs_tendsto, hs_event⟩)
  have hbd : ∀ᶠ n : ℕ in Filter.atTop,
      ‖zetaMmf R m (fun z z' => (F (Fin.cons 0 z) (Fin.cons (hs n) z')
          - F (Fin.cons 0 z) (Fin.cons 0 z')) / (hs n))
        - (F (Fin.cons 0 (0 : Fin m → ℂ)) (Fin.cons (hs n) 0)
            - F (Fin.cons 0 (0 : Fin m → ℂ)) (Fin.cons 0 0)) / (hs n)
          * (Real.log R)^m‖
        ≤ C^m * (2 * B / zetaRho β) * (1 + (Real.log R)^(m-1)) :=
    Filter.Eventually.of_forall (fun n =>
      IH (fun z z' => (F (Fin.cons 0 z) (Fin.cons (hs n) z')
        - F (Fin.cons 0 z) (Fin.cons 0 z')) / (hs n)) (2 * B / zetaRho β) h2B
        (ZetaAdm_dq hβ hβ10 hB hF (hs_le n)))
  have hc3 : Tendsto (fun n : ℕ => (F (Fin.cons 0 (0 : Fin m → ℂ)) (Fin.cons (hs n) 0)
      - F (Fin.cons 0 (0 : Fin m → ℂ)) (Fin.cons 0 0)) / (hs n) * ((Real.log R : ℂ))^m)
      Filter.atTop (𝓝 (deriv (fun u : ℂ => F (0 : Fin (m+1) → ℂ) (Fin.cons u 0)) 0
        * ((Real.log R : ℂ))^m)) :=
    Filter.Tendsto.mul_const (((Real.log R : ℂ))^m) hconv2
  have := le_of_tendsto (hconv1.sub hc3 |>.norm) hbd
  exact this


structure ZetaAux (β : ℝ) where
  C₁ : ℝ
  Cs : ℝ
  Cn : ℝ
  Ku : ℝ
  Cq : ℝ
  hC₁pos : 0 < C₁
  hCspos : 0 < Cs
  hCnpos : 0 < Cn
  hKupos : 0 < Ku
  hCqpos : 0 < Cq
  hreg : ∀ z : ℂ, z ≠ 0 → -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 →
      riemannZeta (1 + z) ≠ 0 ∧
      DifferentiableAt ℂ (fun u : ℂ => (riemannZeta (1 + u))⁻¹) z ∧
      ‖(riemannZeta (1 + z))⁻¹‖ ≤ C₁ * (Real.log (|z.im| + 2) + 1)
  hCs : ∀ z : ℂ, 3 / 2 ≤ z.re → ‖riemannZeta z‖ ≤ Cs
  hCn : ∀ z z' : ℂ, -(β / Real.log 2) ≤ z.re → z.re ≤ -(β / Real.log (|z.im| + 2)) →
      -(β / Real.log 2) ≤ z'.re → z'.re ≤ -(β / Real.log (|z'.im| + 2)) →
      ‖riemannZeta (1 + z + z')‖ ≤ Cn * (|z.im| + |z'.im| + 3) ^ ((1:ℝ)/2)
  hnum : ∀ t t' : ℝ, ‖riemannZeta (1 + gam β t + gam β t')‖
      ≤ Cn * (|t| + |t'| + 3) ^ ((1:ℝ)/2)
  hUint : Integrable (fun t : ℝ => uScale t)
  hUle : (∫ t : ℝ, uScale t) ≤ Ku
  hQint : Integrable (fun t : ℝ => ‖gamDot β t‖
      / (‖riemannZeta (1 + gam β t)‖ * ‖riemannZeta (1 - gam β t)‖ * ‖gam β t‖ ^ 4))
  hQle : (∫ t : ℝ, ‖gamDot β t‖
      / (‖riemannZeta (1 + gam β t)‖ * ‖riemannZeta (1 - gam β t)‖ * ‖gam β t‖ ^ 4)) ≤ Cq

/-- `β` and the number-theoretic data exist. -/
lemma zetaAux_exists : ∃ (β : ℝ) (D : ZetaAux β), 0 < β ∧ β ≤ 1 / 10 := by
  obtain ⟨β₀, hβ₀pos, hβ₀10, C₁, hC₁pos, hreg⟩ := zeta_region_inv_analytic_bound_ne
  obtain ⟨Cn, hCnpos, hCn⟩ := zeta_one_add_add_bound_curve_sqrt_curve (β := β₀) hβ₀pos hβ₀10
  obtain ⟨Cs, hCspos, hCs⟩ := norm_riemannZeta_le_const_of_one_lt_re (σ := 3/2) (by norm_num)
  obtain ⟨Ku, hKupos, hUint, hUle⟩ := Commons.Analysis.Integral.uScaleHalf_integrable
  have hinvb : ∀ z : ℂ, z ≠ 0 → -(β₀ / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 →
      ‖(riemannZeta (1 + z))⁻¹‖ ≤ C₁ * (Real.log (|z.im| + 2) + 1) :=
    fun z hz h1 h2 => (hreg z hz h1 h2).2.2
  obtain ⟨Cq, hCqpos, hQle⟩ :=
    gam0_zeta_quartic_integral_le (β := β₀) hβ₀pos hβ₀10 C₁ hC₁pos hinvb
  have hQint := gam0_zeta_quartic_integrable (β := β₀) hβ₀pos hβ₀10 C₁ hC₁pos hinvb
  have hgam_lo : ∀ s : ℝ, -(β₀ / Real.log 2) ≤ (gam β₀ s).re := by
    intro s
    rw [gam_re β₀ s]
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hle : β₀ / Real.log (|s| + 2) ≤ β₀ / Real.log 2 :=
      div_le_div_of_nonneg_left hβ₀pos.le hlog2
        (Real.log_le_log (by norm_num) (by linarith [abs_nonneg s]))
    linarith
  have hgam_reg' : ∀ s : ℝ, (gam β₀ s).re ≤ -(β₀ / Real.log (|(gam β₀ s).im| + 2)) := by
    intro s; rw [gam_re β₀ s, gam_im]
  have hnum : ∀ t t' : ℝ, ‖riemannZeta (1 + gam β₀ t + gam β₀ t')‖
      ≤ Cn * (|t| + |t'| + 3) ^ ((1:ℝ)/2) := by
    intro t t'
    have h := hCn (gam β₀ t) (gam β₀ t') (hgam_lo t) (hgam_reg' t) (hgam_lo t') (hgam_reg' t')
    simpa [gam_im] using h
  exact ⟨β₀, ⟨C₁, Cs, Cn, Ku, Cq, hC₁pos, hCspos, hCnpos, hKupos, hCqpos, hreg, hCs, hCn,
    hnum, hUint, hUle, hQint, hQle⟩, hβ₀pos, hβ₀10⟩

/-! ## Elementary helpers -/

/-- Updating the `0`-th coordinate of a `cons`. -/
lemma update_cons_zero {m : ℕ} (a : ℂ) (z : Fin m → ℂ) (u : ℂ) :
    Function.update (Fin.cons (α := fun _ => ℂ) a z) 0 u
      = Fin.cons (α := fun _ => ℂ) u z := by
  funext i
  rcases Fin.eq_zero_or_eq_succ i with h | ⟨j, rfl⟩
  · subst h; simp [Fin.cons_zero]
  · simp [Fin.cons_succ, Fin.succ_ne_zero]

/-- `a ↦ Fin.cons a v` is continuous. -/
lemma continuous_cons_fst {m : ℕ} (v : Fin m → ℂ) :
    Continuous (fun a : ℂ => Fin.cons (α := fun _ => ℂ) a v) := by
  refine continuous_pi (fun i => ?_)
  rcases Fin.eq_zero_or_eq_succ i with h | ⟨j, rfl⟩
  · subst h
    have heq : (fun a : ℂ => Fin.cons (α := fun _ => ℂ) a v 0) = fun a : ℂ => a := by
      funext a; rw [Fin.cons_zero]
    rw [heq]; exact continuous_id
  · have heq : (fun a : ℂ => Fin.cons (α := fun _ => ℂ) a v j.succ) = fun _ : ℂ => v j := by
      funext a; rw [Fin.cons_succ]
    rw [heq]; exact continuous_const

/-! ## Slices and corestrictions -/

/-- The `m`-fold corestriction of an `(m+1)`-fold datum, with the `0`-th coordinate fixed at `a`,
`b` in the two variables. -/
def zcore {m : ℕ} (F : (Fin (m+1) → ℂ) → (Fin (m+1) → ℂ) → ℂ) (a b : ℂ) :
    (Fin m → ℂ) → (Fin m → ℂ) → ℂ :=
  fun z z' => F (Fin.cons (α := fun _ => ℂ) a z) (Fin.cons (α := fun _ => ℂ) b z')

/-- The single-variable slice of an `(m+1)`-fold datum along a fixed tail. -/
def zslice {m : ℕ} (F : (Fin (m+1) → ℂ) → (Fin (m+1) → ℂ) → ℂ) (u v : Fin m → ℂ) :
    ℂ → ℂ → ℂ :=
  fun a b => F (Fin.cons (α := fun _ => ℂ) a u) (Fin.cons (α := fun _ => ℂ) b v)

lemma zcore_apply {m : ℕ} (F : (Fin (m+1) → ℂ) → (Fin (m+1) → ℂ) → ℂ) (a b : ℂ)
    (z z' : Fin m → ℂ) : zcore F a b z z' = F (Fin.cons a z) (Fin.cons b z') := rfl

lemma zslice_apply {m : ℕ} (F : (Fin (m+1) → ℂ) → (Fin (m+1) → ℂ) → ℂ)
    (u v : Fin m → ℂ) (a b : ℂ) : zslice F u v a b = F (Fin.cons a u) (Fin.cons b v) := rfl

/-- The constant in the `W₁`/`W₃` bounds. -/
noncomputable def K1c (β : ℝ) : ℝ := curveConst β * ∫ t : ℝ, (1 + t ^ 2)⁻¹

/-- The constant in the `W₂` bound. -/
noncomputable def K2c {β : ℝ} (D : ZetaAux β) : ℝ :=
  D.Cn * D.C₁ * D.C₁ * curveConst β ^ 2 * D.Ku ^ 2

lemma K1c_nonneg (β : ℝ) (hβ : 0 < β) : 0 ≤ K1c β :=
  mul_nonneg (curveConst_pos hβ).le (by positivity)

lemma K2c_nonneg {β : ℝ} (D : ZetaAux β) (hβ : 0 < β) : 0 ≤ K2c D := by
  unfold K2c
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg D.hCnpos.le D.hC₁pos.le) D.hC₁pos.le)
    (pow_nonneg (curveConst_pos hβ).le 2)) (pow_nonneg D.hKupos.le 2)

/-- The pointwise `m = 1` contour-shift identity for a slice of an `(m+1)`-fold datum. -/
lemma zetaMf1_zslice_eq {β R : ℝ} (D : ZetaAux β) (hβ : 0 < β) (hβ10 : β ≤ 1 / 10)
    (hR : 3 ≤ R) {m : ℕ}
    (F : (Fin (m+1) → ℂ) → (Fin (m+1) → ℂ) → ℂ) (B : ℝ)
    (hF : ZetaAdm β (m+1) F B) {u v : Fin m → ℂ} (hu : ZetaRegVec β u) (hv : ZetaRegVec β v) :
    zetaMf1 R (zslice F u v)
      = F (Fin.cons 0 u) (Fin.cons 0 v) * Real.log R
        + deriv (fun x : ℂ => F (Fin.cons 0 u) (Fin.cons x v)) 0
        + (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * zetaM0W1 R β (zslice F u v)
        + ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ 2 * zetaM0W2 R β (zslice F u v)
        + (2 * (Real.pi : ℂ) * Complex.I)⁻¹
            * (zetaM0W3 R β (zslice F u v) + zetaM0W4 R β (zslice F u v)) := by
  have hcont : Continuous (Function.uncurry (zslice F u v)) := by
    change Continuous (fun p : ℂ × ℂ => F (Fin.cons (α := fun _ => ℂ) p.1 u)
        (Fin.cons (α := fun _ => ℂ) p.2 v))
    have h1 : Continuous (fun p : ℂ × ℂ => Fin.cons (α := fun _ => ℂ) p.1 u) :=
      (continuous_cons_fst u).comp continuous_fst
    have h2 : Continuous (fun p : ℂ × ℂ => Fin.cons (α := fun _ => ℂ) p.2 v) :=
      (continuous_cons_fst v).comp continuous_snd
    exact hF.1.comp (h1.prodMk h2)
  have hd1 : ∀ ζ ζ' : ℂ, ZetaReg β ζ → ZetaReg β ζ' →
      DifferentiableAt ℂ (fun x : ℂ => zslice F u v x ζ') ζ := by
    intro ζ ζ' hζ hζ'
    have h := hF.2.1 0 (Fin.cons (α := fun _ => ℂ) ζ u) (Fin.cons (α := fun _ => ℂ) ζ' v)
      (ZetaRegVec_cons hζ hu) (ZetaRegVec_cons hζ' hv)
    rw [Fin.cons_zero] at h
    have heq : (fun x : ℂ => F (Function.update (Fin.cons (α := fun _ => ℂ) ζ u) 0 x)
          (Fin.cons (α := fun _ => ℂ) ζ' v))
        = fun x : ℂ => zslice F u v x ζ' := by
      funext x; rw [update_cons_zero]; rfl
    rwa [heq] at h
  have hd2 : ∀ ζ ζ' : ℂ, ZetaReg β ζ → ZetaReg β ζ' →
      DifferentiableAt ℂ (fun x : ℂ => zslice F u v ζ x) ζ' := by
    intro ζ ζ' hζ hζ'
    have h := hF.2.2.1 0 (Fin.cons (α := fun _ => ℂ) ζ u) (Fin.cons (α := fun _ => ℂ) ζ' v)
      (ZetaRegVec_cons hζ hu) (ZetaRegVec_cons hζ' hv)
    rw [Fin.cons_zero] at h
    have heq : (fun x : ℂ => F (Fin.cons (α := fun _ => ℂ) ζ u)
          (Function.update (Fin.cons (α := fun _ => ℂ) ζ' v) 0 x))
        = fun x : ℂ => zslice F u v ζ x := by
      funext x; rw [update_cons_zero]; rfl
    rwa [heq] at h
  have hbound : ∀ ζ ζ' : ℂ, ZetaReg β ζ → ZetaReg β ζ' → ‖zslice F u v ζ ζ'‖ ≤ B :=
    fun ζ ζ' hζ hζ' => hF.2.2.2 _ _ (ZetaRegVec_cons hζ hu) (ZetaRegVec_cons hζ' hv)
  exact zetaMf1_eq hβ hβ10 hR (zslice F u v) B D.C₁ D.Cs D.Cn D.hC₁pos D.hCspos D.hCnpos
    D.hreg D.hCs D.hCn hd1 hd2 hcont hbound

/-- Bounds for the four `Γ₀`-terms applied to a slice. -/
lemma zetaM0W_zslice_le {β R : ℝ} (D : ZetaAux β) (hβ : 0 < β) (hβ10 : β ≤ 1 / 10)
    (hR : 3 ≤ R) {m : ℕ}
    (F : (Fin (m+1) → ℂ) → (Fin (m+1) → ℂ) → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hF : ZetaAdm β (m+1) F B) {u v : Fin m → ℂ} (hu : ZetaRegVec β u) (hv : ZetaRegVec β v) :
    ‖zetaM0W1 R β (zslice F u v)‖ ≤ K1c β * B ∧
    ‖zetaM0W2 R β (zslice F u v)‖ ≤ K2c D * B ∧
    ‖zetaM0W3 R β (zslice F u v)‖ ≤ K1c β * B ∧
    ‖zetaM0W4 R β (zslice F u v)‖ ≤ D.Cq * B := by
  have hinvb : ∀ z : ℂ, z ≠ 0 → ZetaReg β z →
      ‖(riemannZeta (1 + z))⁻¹‖ ≤ D.C₁ * (Real.log (|z.im| + 2) + 1) :=
    fun z hz hzreg => (D.hreg z hz hzreg.1 hzreg.2).2.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact zetaM0W1_le hβ (by linarith) _ B hB
      (fun z hz => hF.2.2.2 _ _ (ZetaRegVec_cons (zetaReg_zero hβ) hu) (ZetaRegVec_cons hz hv))
  · rw [K2c]
    exact zetaM0W2_le hβ hR _ B hB D.hCnpos D.hC₁pos D.hKupos hinvb D.hnum D.hUint D.hUle
      (fun z z' hz hz' => hF.2.2.2 _ _ (ZetaRegVec_cons hz hu) (ZetaRegVec_cons hz' hv))
  · exact zetaM0W3_le hβ (by linarith) _ B hB
      (fun z hz => hF.2.2.2 _ _ (ZetaRegVec_cons hz hu) (ZetaRegVec_cons (zetaReg_zero hβ) hv))
  · exact zetaM0W4_le hβ hR _ B hB D.hQint D.hQle
      (fun t => hF.2.2.2 _ _ (ZetaRegVec_cons (phi_mem_ZetaReg hβ t) hu)
        (ZetaRegVec_cons (neg_phi_mem_ZetaReg hβ hβ10 t) hv))

/-! ## The split integrands of the induction step -/

/-- `‖(x : ℂ)‖ = x` for `x ≥ 0`. -/
lemma norm_ofReal_of_nonneg {x : ℝ} (hx : 0 ≤ x) : ‖(x : ℂ)‖ = x := by
  have h : ‖(x : ℂ)‖ ^ 2 = x ^ 2 := by rw [Complex.sq_norm, Complex.normSq_ofReal]; ring
  nlinarith [norm_nonneg (x : ℂ), h]

lemma continuous_eta_vec {R : ℝ} {n : ℕ} :
    Continuous (fun w : Fin n → ℝ => fun j => zetaM1Eta R (w j)) :=
  continuous_pi (fun j => (zetaM1Eta_continuous R).comp (continuous_apply j))

/-- The "main term" integrand of the recursion. -/
noncomputable def zfA {m : ℕ} (R : ℝ) (F : (Fin (m+1) → ℂ) → (Fin (m+1) → ℂ) → ℂ)
    (p : (Fin m → ℝ) × (Fin m → ℝ)) : ℂ :=
  F (Fin.cons 0 (fun j => zetaM1Eta R (p.1 j))) (Fin.cons 0 (fun j => zetaM1Eta R (p.2 j)))
    * Real.log R * WmK R m p.1 p.2

/-- The `∂`-term integrand of the recursion. -/
noncomputable def zfD {m : ℕ} (R : ℝ) (F : (Fin (m+1) → ℂ) → (Fin (m+1) → ℂ) → ℂ)
    (p : (Fin m → ℝ) × (Fin m → ℝ)) : ℂ :=
  deriv (fun x : ℂ => F (Fin.cons 0 (fun j => zetaM1Eta R (p.1 j)))
      (Fin.cons x (fun j => zetaM1Eta R (p.2 j)))) 0 * WmK R m p.1 p.2

/-- The `W₁` integrand of the recursion. -/
noncomputable def zfW1 {m : ℕ} (R β : ℝ) (F : (Fin (m+1) → ℂ) → (Fin (m+1) → ℂ) → ℂ)
    (p : (Fin m → ℝ) × (Fin m → ℝ)) : ℂ :=
  zetaM0W1 R β (zslice F (fun j => zetaM1Eta R (p.1 j)) (fun j => zetaM1Eta R (p.2 j)))
    * WmK R m p.1 p.2

/-- The `W₂` integrand of the recursion. -/
noncomputable def zfW2 {m : ℕ} (R β : ℝ) (F : (Fin (m+1) → ℂ) → (Fin (m+1) → ℂ) → ℂ)
    (p : (Fin m → ℝ) × (Fin m → ℝ)) : ℂ :=
  zetaM0W2 R β (zslice F (fun j => zetaM1Eta R (p.1 j)) (fun j => zetaM1Eta R (p.2 j)))
    * WmK R m p.1 p.2

/-- The `W₃` integrand of the recursion. -/
noncomputable def zfW3 {m : ℕ} (R β : ℝ) (F : (Fin (m+1) → ℂ) → (Fin (m+1) → ℂ) → ℂ)
    (p : (Fin m → ℝ) × (Fin m → ℝ)) : ℂ :=
  zetaM0W3 R β (zslice F (fun j => zetaM1Eta R (p.1 j)) (fun j => zetaM1Eta R (p.2 j)))
    * WmK R m p.1 p.2

/-- The `W₄` integrand of the recursion. -/
noncomputable def zfW4 {m : ℕ} (R β : ℝ) (F : (Fin (m+1) → ℂ) → (Fin (m+1) → ℂ) → ℂ)
    (p : (Fin m → ℝ) × (Fin m → ℝ)) : ℂ :=
  zetaM0W4 R β (zslice F (fun j => zetaM1Eta R (p.1 j)) (fun j => zetaM1Eta R (p.2 j)))
    * WmK R m p.1 p.2

section SplitIntegrability

variable {β R : ℝ} {m : ℕ}
variable (F : (Fin (m+1) → ℂ) → (Fin (m+1) → ℂ) → ℂ) (B : ℝ)

lemma integrable_zfA (hβ : 0 < β) (hβ10 : β ≤ 1/10) (hR : 3 ≤ R)
    (hB : 0 ≤ B) (hF : ZetaAdm β (m+1) F B) :
    Integrable (zfA R F) (volume : Measure ((Fin m → ℝ) × (Fin m → ℝ))) := by
  have hlogR : 0 ≤ Real.log R := Real.log_nonneg (by linarith)
  refine integrable_eval_WmK (R := R) hR
    (fun p : (Fin m → ℝ) × (Fin m → ℝ) => F (Fin.cons 0 (fun j => zetaM1Eta R (p.1 j)))
      (Fin.cons 0 (fun j => zetaM1Eta R (p.2 j))) * Real.log R)
    (B * Real.log R) (mul_nonneg hB hlogR) ?_ ?_
  · refine Measurable.aestronglyMeasurable ?_
    exact (measurable_F_cons (R := R) F hF.1 measurable_const measurable_const
      measurable_fst measurable_snd).mul_const _
  · intro p
    rw [norm_mul, norm_ofReal_of_nonneg hlogR]
    exact mul_le_mul_of_nonneg_right
      (hF.2.2.2 _ _ (ZetaRegVec_cons (zetaReg_zero hβ) (ZetaRegVec_eta hβ hR p.1))
        (ZetaRegVec_cons (zetaReg_zero hβ) (ZetaRegVec_eta hβ hR p.2))) hlogR

lemma integrable_zfD (hβ : 0 < β) (hβ10 : β ≤ 1/10) (hR : 3 ≤ R)
    (hB : 0 ≤ B) (hF : ZetaAdm β (m+1) F B) :
    Integrable (zfD R F) (volume : Measure ((Fin m → ℝ) × (Fin m → ℝ))) := by
  have hρpos : 0 < zetaRho β := zetaRho_pos hβ
  refine integrable_eval_WmK (R := R) hR
    (fun p : (Fin m → ℝ) × (Fin m → ℝ) => deriv (fun x : ℂ =>
      F (Fin.cons 0 (fun j => zetaM1Eta R (p.1 j)))
        (Fin.cons x (fun j => zetaM1Eta R (p.2 j)))) 0)
    (B / zetaRho β) (div_nonneg hB hρpos.le) ?_ ?_
  · refine (Commons.Analysis.Complex.aemeasurable_deriv_parametric
      (volume : Measure ((Fin m → ℝ) × (Fin m → ℝ)))
      (fun (p : (Fin m → ℝ) × (Fin m → ℝ)) (x : ℂ) =>
        F (Fin.cons 0 (fun j => zetaM1Eta R (p.1 j))) (Fin.cons x (fun j => zetaM1Eta R (p.2 j))))
      ?_ ?_).aestronglyMeasurable
    · exact measurable_F_cons (R := R) F hF.1 measurable_const measurable_snd
        measurable_fst.fst measurable_fst.snd
    · intro p
      have h := hF.2.2.1 0 (Fin.cons (α := fun _ => ℂ) 0 (fun j => zetaM1Eta R (p.1 j)))
        (Fin.cons (α := fun _ => ℂ) 0 (fun j => zetaM1Eta R (p.2 j)))
        (ZetaRegVec_cons (zetaReg_zero hβ) (ZetaRegVec_eta hβ hR p.1))
        (ZetaRegVec_cons (zetaReg_zero hβ) (ZetaRegVec_eta hβ hR p.2))
      rw [Fin.cons_zero] at h
      have heq : (fun x : ℂ => F (Fin.cons (α := fun _ => ℂ) 0 (fun j => zetaM1Eta R (p.1 j)))
            (Function.update (Fin.cons (α := fun _ => ℂ) 0 (fun j => zetaM1Eta R (p.2 j))) 0 x))
          = fun x : ℂ => F (Fin.cons (α := fun _ => ℂ) 0 (fun j => zetaM1Eta R (p.1 j)))
            (Fin.cons (α := fun _ => ℂ) x (fun j => zetaM1Eta R (p.2 j))) := by
        funext x; rw [update_cons_zero]
      rwa [heq] at h
  · intro p
    refine deriv_bound_ZetaReg hβ hβ10 _ B hB ?_ ?_
    · intro x hx
      have h := hF.2.2.1 0 (Fin.cons (α := fun _ => ℂ) 0 (fun j => zetaM1Eta R (p.1 j)))
        (Fin.cons (α := fun _ => ℂ) x (fun j => zetaM1Eta R (p.2 j)))
        (ZetaRegVec_cons (zetaReg_zero hβ) (ZetaRegVec_eta hβ hR p.1))
        (ZetaRegVec_cons hx (ZetaRegVec_eta hβ hR p.2))
      rw [Fin.cons_zero] at h
      have heq : (fun y : ℂ => F (Fin.cons (α := fun _ => ℂ) 0 (fun j => zetaM1Eta R (p.1 j)))
            (Function.update (Fin.cons (α := fun _ => ℂ) x (fun j => zetaM1Eta R (p.2 j))) 0 y))
          = fun y : ℂ => F (Fin.cons (α := fun _ => ℂ) 0 (fun j => zetaM1Eta R (p.1 j)))
            (Fin.cons (α := fun _ => ℂ) y (fun j => zetaM1Eta R (p.2 j))) := by
        funext y; rw [update_cons_zero]
      rwa [heq] at h
    · intro x hx
      exact hF.2.2.2 _ _ (ZetaRegVec_cons (zetaReg_zero hβ) (ZetaRegVec_eta hβ hR p.1))
        (ZetaRegVec_cons hx (ZetaRegVec_eta hβ hR p.2))

lemma integrable_zfW1 {β R : ℝ} {m : ℕ} (D : ZetaAux β) (hβ : 0 < β) (hβ10 : β ≤ 1 / 10)
    (hR : 3 ≤ R) (F : (Fin (m+1) → ℂ) → (Fin (m+1) → ℂ) → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hF : ZetaAdm β (m+1) F B) :
    Integrable (zfW1 R β F) (volume : Measure ((Fin m → ℝ) × (Fin m → ℝ))) := by
  have hInt := integrable_gW1_integrand (β := β) (R := R) hβ hR F B hB hF.1
    (fun z z' hz hz' => hF.2.2.2 z z' hz hz')
  refine hInt.integral_prod_left.congr ?_
  filter_upwards with p
  rw [zfW1, zetaM0W1, ← MeasureTheory.integral_mul_const]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with t
  simp only [gW1, zslice_apply]
  ring

lemma integrable_zfW3 {β R : ℝ} {m : ℕ} (D : ZetaAux β) (hβ : 0 < β) (hβ10 : β ≤ 1 / 10)
    (hR : 3 ≤ R) (F : (Fin (m+1) → ℂ) → (Fin (m+1) → ℂ) → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hF : ZetaAdm β (m+1) F B) :
    Integrable (zfW3 R β F) (volume : Measure ((Fin m → ℝ) × (Fin m → ℝ))) := by
  have hInt := integrable_gW3_integrand (β := β) (R := R) hβ hR F B hB hF.1
    (fun z z' hz hz' => hF.2.2.2 z z' hz hz')
  refine hInt.integral_prod_left.congr ?_
  filter_upwards with p
  rw [zfW3, zetaM0W3, ← MeasureTheory.integral_mul_const]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with t
  simp only [gW1, zslice_apply]
  ring

lemma integrable_zfW4 {β R : ℝ} {m : ℕ} (D : ZetaAux β) (hβ : 0 < β) (hβ10 : β ≤ 1 / 10)
    (hR : 3 ≤ R) (F : (Fin (m+1) → ℂ) → (Fin (m+1) → ℂ) → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hF : ZetaAdm β (m+1) F B) :
    Integrable (zfW4 R β F) (volume : Measure ((Fin m → ℝ) × (Fin m → ℝ))) := by
  have hInt := integrable_gW4_integrand (β := β) (R := R) hβ hβ10 hR F B hB hF.1
    (fun z z' hz hz' => hF.2.2.2 z z' hz hz') D.hQint
  refine hInt.integral_prod_left.congr ?_
  filter_upwards with p
  rw [zfW4, zetaM0W4, ← MeasureTheory.integral_mul_const]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with t
  simp only [gW4, zslice_apply]
  ring

lemma integrable_zfW2 {β R : ℝ} {m : ℕ} (D : ZetaAux β) (hβ : 0 < β) (hβ10 : β ≤ 1 / 10)
    (hR : 3 ≤ R) (F : (Fin (m+1) → ℂ) → (Fin (m+1) → ℂ) → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hF : ZetaAdm β (m+1) F B) :
    Integrable (zfW2 R β F) (volume : Measure ((Fin m → ℝ) × (Fin m → ℝ))) := by
  have hinvb : ∀ z : ℂ, z ≠ 0 → -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 →
      ‖(riemannZeta (1 + z))⁻¹‖ ≤ D.C₁ * (Real.log (|z.im| + 2) + 1) :=
    fun z hz h1 h2 => (D.hreg z hz h1 h2).2.2
  have hInt := integrable_gW2_integrand (β := β) (R := R) hβ hR F B D.C₁ D.Cn
    D.hC₁pos D.hCnpos hB hF.1 (fun z z' hz hz' => hF.2.2.2 z z' hz hz')
    hinvb D.hnum D.hUint
  have hae := hInt.prod_right_ae
  have h1 := hInt.integral_prod_left
  refine h1.congr ?_
  filter_upwards [hae] with p hp
  rw [zfW2, zetaM0W2]
  have hcp := MeasureTheory.integral_prod (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
      (fun z : ℝ × ℝ => F (Fin.cons (gam β z.1) (fun j => zetaM1Eta R (p.1 j)))
        (Fin.cons (gam β z.2) (fun j => zetaM1Eta R (p.2 j)))
        * zetaM1Kernel R (fun _ _ => (1:ℂ)) (gam β z.1) (gam β z.2)
        * gamDot β z.2 * gamDot β z.1 * WmK R m p.1 p.2) hp
  rw [hcp, ← MeasureTheory.integral_mul_const]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with t
  rw [← MeasureTheory.integral_mul_const, ← MeasureTheory.integral_mul_const]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with t'
  simp only [zslice_apply, zetaM1Kernel, Pi.one_apply, one_mul]
  ring

/-! ## The pointwise identity and integrability of the sliced integrand -/

lemma integrable_norm_WmK {R : ℝ} (hR : 3 ≤ R) (m : ℕ) :
    Integrable (fun p : (Fin m → ℝ) × (Fin m → ℝ) => ‖WmK R m p.1 p.2‖)
      (volume : Measure ((Fin m → ℝ) × (Fin m → ℝ))) := by
  obtain ⟨K, hKpos, hKle⟩ := zetaM1Kernel_eta_bound (R := R) hR
  have hK : ∀ x y : ℝ, ‖zetaM1Kernel R (fun _ _ => (1:ℂ)) (zetaM1Eta R x) (zetaM1Eta R y)‖
      ≤ K * Awt x * Awt y := fun x y => by
    simpa only [Awt, zetaM1Kernel, Pi.one_apply, one_mul, mul_assoc] using hKle x y
  have hprod : Integrable (fun p : (Fin m → ℝ) × (Fin m → ℝ) =>
      (∏ j, Awt (p.1 j)) * (∏ j, Awt (p.2 j)))
      ((volume : Measure (Fin m → ℝ)).prod (volume : Measure (Fin m → ℝ))) := by
    simpa [Awt] using Commons.Analysis.Measure.integrable_weight_prod_fin m
  refine (hprod.const_mul (K ^ m)).mono' ?_ ?_
  · exact (measurable_WmK R (by linarith) m).norm.aestronglyMeasurable
  · filter_upwards with p
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    calc ‖WmK R m p.1 p.2‖ ≤ K ^ m * (∏ j, Awt (p.1 j)) * (∏ j, Awt (p.2 j)) :=
          norm_WmK_le hK m p.1 p.2
      _ = K ^ m * ((∏ j, Awt (p.1 j)) * (∏ j, Awt (p.2 j))) := by ring

/-- The sliced `m = 1` integrand in the `(m+1)`-fold recursion. -/
noncomputable def zz {m : ℕ} (R β : ℝ) (F : (Fin (m+1) → ℂ) → (Fin (m+1) → ℂ) → ℂ)
    (w w' : Fin m → ℝ) : ℂ :=
  zetaMf1 R (zslice F (fun j => zetaM1Eta R (w j)) (fun j => zetaM1Eta R (w' j)))
    * WmK R m w w'

/-- The pointwise decomposition of the sliced integrand. -/
lemma zetaMf1_zz_eq {β R : ℝ} (D : ZetaAux β) (hβ : 0 < β) (hβ10 : β ≤ 1 / 10)
    (hR : 3 ≤ R) {m : ℕ} (F : (Fin (m+1) → ℂ) → (Fin (m+1) → ℂ) → ℂ) (B : ℝ)
    (hF : ZetaAdm β (m+1) F B) (w w' : Fin m → ℝ) :
    zz R β F w w' = (zfA R F (w, w') + zfD R F (w, w'))
      + (((2 * (Real.pi : ℂ) * Complex.I)⁻¹ * zfW1 R β F (w, w')
            + ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ 2 * zfW2 R β F (w, w'))
          + ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ * zfW3 R β F (w, w')
              + (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * zfW4 R β F (w, w'))) := by
  rw [zz, zetaMf1_zslice_eq D hβ hβ10 hR F B hF (ZetaRegVec_eta hβ hR w)
    (ZetaRegVec_eta hβ hR w')]
  simp only [zfA, zfD, zfW1, zfW2, zfW3, zfW4]
  ring

lemma norm_two_pi_I_inv_le_one : ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹‖ ≤ 1 := by
  rw [norm_inv, norm_mul, norm_mul, Complex.norm_I, mul_one]
  have h2 : ‖(2:ℂ)‖ = 2 := by norm_num
  have hp : ‖(Real.pi : ℂ)‖ = Real.pi := norm_ofReal_of_nonneg Real.pi_pos.le
  rw [h2, hp]
  exact inv_le_one_of_one_le₀ (by nlinarith [Real.pi_gt_three])

lemma integrable_zz {β R : ℝ} (D : ZetaAux β) (hβ : 0 < β) (hβ10 : β ≤ 1 / 10)
    (hR : 3 ≤ R) {m : ℕ} (F : (Fin (m+1) → ℂ) → (Fin (m+1) → ℂ) → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hF : ZetaAdm β (m+1) F B) :
    Integrable (Function.uncurry (zz R β F))
      ((volume : Measure (Fin m → ℝ)).prod (volume : Measure (Fin m → ℝ))) := by
  have hρpos : 0 < zetaRho β := zetaRho_pos hβ
  have hlogR : 0 ≤ Real.log R := Real.log_nonneg (by linarith)
  have hK1 : 0 ≤ K1c β := K1c_nonneg β hβ
  have hK2 : 0 ≤ K2c D := K2c_nonneg D hβ
  have hCbd : 0 ≤ Real.log R + 1 / zetaRho β + 2 * K1c β + K2c D + D.Cq := by
    have h1 : 0 ≤ 1 / zetaRho β := div_nonneg zero_le_one hρpos.le
    linarith [hlogR, hK1, hK2, D.hCqpos.le, h1]
  have hdom : Integrable (fun p : (Fin m → ℝ) × (Fin m → ℝ) =>
      (Real.log R + 1 / zetaRho β + 2 * K1c β + K2c D + D.Cq) * B * ‖WmK R m p.1 p.2‖)
      (volume : Measure ((Fin m → ℝ) × (Fin m → ℝ))) :=
    (integrable_norm_WmK hR m).const_mul _
  have hzfA := integrable_zfA F B hβ hβ10 hR hB hF
  have hzfD := integrable_zfD F B hβ hβ10 hR hB hF
  have hzfW1 := integrable_zfW1 D hβ hβ10 hR F B hB hF
  have hzfW2 := integrable_zfW2 D hβ hβ10 hR F B hB hF
  have hzfW3 := integrable_zfW3 D hβ hβ10 hR F B hB hF
  have hzfW4 := integrable_zfW4 D hβ hβ10 hR F B hB hF
  refine hdom.mono' ?_ ?_
  · rw [show Function.uncurry (zz R β F) = fun p : (Fin m → ℝ) × (Fin m → ℝ) =>
        (zfA R F p + zfD R F p)
          + (((2 * (Real.pi : ℂ) * Complex.I)⁻¹ * zfW1 R β F p
                + ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ 2 * zfW2 R β F p)
              + ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ * zfW3 R β F p
                  + (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * zfW4 R β F p))
      from funext (fun p => zetaMf1_zz_eq D hβ hβ10 hR F B hF p.1 p.2)]
    exact ((hzfA.aestronglyMeasurable.add hzfD.aestronglyMeasurable).add
      (((hzfW1.aestronglyMeasurable.const_mul _).add
        (hzfW2.aestronglyMeasurable.const_mul _)).add
        ((hzfW3.aestronglyMeasurable.const_mul _).add
          (hzfW4.aestronglyMeasurable.const_mul _))))
  · filter_upwards with p
    rw [show Function.uncurry (zz R β F) p = zz R β F p.1 p.2 from rfl,
      zetaMf1_zz_eq D hβ hβ10 hR F B hF p.1 p.2]
    obtain ⟨hW1, hW2, hW3, hW4⟩ :=
      zetaM0W_zslice_le D hβ hβ10 hR F B hB hF (ZetaRegVec_eta hβ hR p.1)
        (ZetaRegVec_eta hβ hR p.2)
    have hAn : ‖zfA R F p‖ ≤ B * Real.log R * ‖WmK R m p.1 p.2‖ := by
      rw [zfA, norm_mul, norm_mul, norm_ofReal_of_nonneg hlogR]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hF.2.2.2 _ _
        (ZetaRegVec_cons (zetaReg_zero hβ) (ZetaRegVec_eta hβ hR p.1))
        (ZetaRegVec_cons (zetaReg_zero hβ) (ZetaRegVec_eta hβ hR p.2))) hlogR)
        (norm_nonneg _)
    have hDn : ‖zfD R F p‖ ≤ B / zetaRho β * ‖WmK R m p.1 p.2‖ := by
      rw [zfD, norm_mul]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      refine deriv_bound_ZetaReg hβ hβ10 _ B hB ?_ ?_
      · intro x hx
        have h := hF.2.2.1 0 (Fin.cons (α := fun _ => ℂ) 0 (fun j => zetaM1Eta R (p.1 j)))
          (Fin.cons (α := fun _ => ℂ) x (fun j => zetaM1Eta R (p.2 j)))
          (ZetaRegVec_cons (zetaReg_zero hβ) (ZetaRegVec_eta hβ hR p.1))
          (ZetaRegVec_cons hx (ZetaRegVec_eta hβ hR p.2))
        rw [Fin.cons_zero] at h
        have heq : (fun y : ℂ => F (Fin.cons (α := fun _ => ℂ) 0 (fun j => zetaM1Eta R (p.1 j)))
              (Function.update (Fin.cons (α := fun _ => ℂ) x (fun j => zetaM1Eta R (p.2 j))) 0 y))
            = fun y : ℂ => F (Fin.cons (α := fun _ => ℂ) 0 (fun j => zetaM1Eta R (p.1 j)))
              (Fin.cons (α := fun _ => ℂ) y (fun j => zetaM1Eta R (p.2 j))) := by
          funext y; rw [update_cons_zero]
        rwa [heq] at h
      · intro x hx
        exact hF.2.2.2 _ _ (ZetaRegVec_cons (zetaReg_zero hβ) (ZetaRegVec_eta hβ hR p.1))
          (ZetaRegVec_cons hx (ZetaRegVec_eta hβ hR p.2))
    have hE1n : ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹ * zfW1 R β F p‖
        ≤ K1c β * B * ‖WmK R m p.1 p.2‖ := by
      rw [norm_mul, zfW1, norm_mul]
      calc ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹‖ * (‖zetaM0W1 R β _‖ * ‖WmK R m p.1 p.2‖)
          ≤ 1 * (K1c β * B * ‖WmK R m p.1 p.2‖) :=
            mul_le_mul norm_two_pi_I_inv_le_one
              (mul_le_mul_of_nonneg_right (by simpa only [K1c] using hW1) (norm_nonneg _))
              (by positivity) zero_le_one
        _ = K1c β * B * ‖WmK R m p.1 p.2‖ := by ring
    have hE2n : ‖((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ 2 * zfW2 R β F p‖
        ≤ K2c D * B * ‖WmK R m p.1 p.2‖ := by
      have hM2 : ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹‖ ^ 2 ≤ 1 := by
        nlinarith [norm_two_pi_I_inv_le_one,
          norm_nonneg ((2 * (Real.pi : ℂ) * Complex.I)⁻¹)]
      rw [norm_mul, norm_pow, zfW2, norm_mul]
      calc ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹‖ ^ 2
            * (‖zetaM0W2 R β _‖ * ‖WmK R m p.1 p.2‖)
          ≤ 1 * (K2c D * B * ‖WmK R m p.1 p.2‖) :=
            mul_le_mul hM2 (mul_le_mul_of_nonneg_right hW2 (norm_nonneg _))
              (by positivity) zero_le_one
        _ = K2c D * B * ‖WmK R m p.1 p.2‖ := by ring
    have hE3n : ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹ * zfW3 R β F p‖
        ≤ K1c β * B * ‖WmK R m p.1 p.2‖ := by
      rw [norm_mul, zfW3, norm_mul]
      calc ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹‖ * (‖zetaM0W3 R β _‖ * ‖WmK R m p.1 p.2‖)
          ≤ 1 * (K1c β * B * ‖WmK R m p.1 p.2‖) :=
            mul_le_mul norm_two_pi_I_inv_le_one
              (mul_le_mul_of_nonneg_right (by simpa only [K1c] using hW3) (norm_nonneg _))
              (by positivity) zero_le_one
        _ = K1c β * B * ‖WmK R m p.1 p.2‖ := by ring
    have hE4n : ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹ * zfW4 R β F p‖
        ≤ D.Cq * B * ‖WmK R m p.1 p.2‖ := by
      rw [norm_mul, zfW4, norm_mul]
      calc ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹‖ * (‖zetaM0W4 R β _‖ * ‖WmK R m p.1 p.2‖)
          ≤ 1 * (D.Cq * B * ‖WmK R m p.1 p.2‖) :=
            mul_le_mul norm_two_pi_I_inv_le_one
              (mul_le_mul_of_nonneg_right hW4 (norm_nonneg _)) (by positivity) zero_le_one
        _ = D.Cq * B * ‖WmK R m p.1 p.2‖ := by ring
    have h1 := norm_add_le (zfA R F p + zfD R F p)
      (((2 * (Real.pi : ℂ) * Complex.I)⁻¹ * zfW1 R β F p
            + ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ 2 * zfW2 R β F p)
          + ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ * zfW3 R β F p
              + (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * zfW4 R β F p))
    have h2 := norm_add_le (zfA R F p) (zfD R F p)
    have h3 := norm_add_le ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ * zfW1 R β F p
        + ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ 2 * zfW2 R β F p)
      ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ * zfW3 R β F p
        + (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * zfW4 R β F p)
    have h4 := norm_add_le ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ * zfW1 R β F p)
      (((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ 2 * zfW2 R β F p)
    have h5 := norm_add_le ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ * zfW3 R β F p)
      ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ * zfW4 R β F p)
    have heq : B * Real.log R * ‖WmK R m p.1 p.2‖ + B / zetaRho β * ‖WmK R m p.1 p.2‖
          + (K1c β * B * ‖WmK R m p.1 p.2‖ + K2c D * B * ‖WmK R m p.1 p.2‖)
          + (K1c β * B * ‖WmK R m p.1 p.2‖ + D.Cq * B * ‖WmK R m p.1 p.2‖)
        = (Real.log R + 1 / zetaRho β + 2 * K1c β + K2c D + D.Cq) * B
            * ‖WmK R m p.1 p.2‖ := by ring
    linarith [h1, h2, h3, h4, h5, hAn, hDn, hE1n, hE2n, hE3n, hE4n, heq]

/-! ## The recursion identity -/

/-! ## The recursion identity -/

lemma zetaMmf_step_decomp {β R : ℝ} (D : ZetaAux β) (hβ : 0 < β) (hβ10 : β ≤ 1 / 10)
    (hR : 3 ≤ R) {m : ℕ}
    (F : (Fin (m+1) → ℂ) → (Fin (m+1) → ℂ) → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hF : ZetaAdm β (m+1) F B) :
    zetaMmf R (m+1) F
      = Real.log R * zetaMmf R m (zcore F 0 0)
        + (zetaMmf R m (fun z z' => deriv (fun x : ℂ => F (Fin.cons 0 z) (Fin.cons x z')) 0)
          + (((2 * (Real.pi : ℂ) * Complex.I)⁻¹
                * (∫ t : ℝ, zetaMmf R m (zcore F 0 (gam β t)) * gW1 R β t)
              + ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ 2
                * (∫ t : ℝ, ∫ t' : ℝ, zetaMmf R m (zcore F (gam β t) (gam β t'))
                    * zetaM1Kernel R (fun _ _ => (1:ℂ)) (gam β t) (gam β t')
                    * gamDot β t * gamDot β t'))
            + ((2 * (Real.pi : ℂ) * Complex.I)⁻¹
                  * (∫ t : ℝ, zetaMmf R m (zcore F (gam β t) 0) * gW1 R β t)
                + (2 * (Real.pi : ℂ) * Complex.I)⁻¹
                  * (∫ t : ℝ, zetaMmf R m (zcore F (gam β t) (-(gam β t))) * gW4 β t)))) := by
  have hRone : (1:ℝ) ≤ R := by linarith
  -- (1) integrability of the `(m+1)`-fold integrand
  have hInt : Integrable (fun p : (Fin (m+1) → ℝ) × (Fin (m+1) → ℝ) =>
      F (fun j => zetaM1Eta R (p.1 j)) (fun j => zetaM1Eta R (p.2 j))
        * ∏ j : Fin (m+1), zetaM1Kernel R (fun _ _ => (1:ℂ)) (zetaM1Eta R (p.1 j))
            (zetaM1Eta R (p.2 j)))
      ((volume : Measure (Fin (m+1) → ℝ)).prod volume) := by
    have h := integrable_eval_WmK (R := R) hR
      (fun p : (Fin (m+1) → ℝ) × (Fin (m+1) → ℝ) =>
        F (fun j => zetaM1Eta R (p.1 j)) (fun j => zetaM1Eta R (p.2 j))) B hB ?_ ?_
    · simpa only [WmK] using h
    · exact (hF.1.comp (((continuous_eta_vec (R := R)).comp continuous_fst).prodMk
        ((continuous_eta_vec (R := R)).comp continuous_snd))).aestronglyMeasurable
    · intro p
      exact hF.2.2.2 _ _ (ZetaRegVec_eta hβ hR p.1) (ZetaRegVec_eta hβ hR p.2)
  have hzz := integrable_zz D hβ hβ10 hR F B hB hF
  have hA := integrable_zfA F B hβ hβ10 hR hB hF
  have hD := integrable_zfD F B hβ hβ10 hR hB hF
  have hW1 := integrable_zfW1 D hβ hβ10 hR F B hB hF
  have hW2 := integrable_zfW2 D hβ hβ10 hR F B hB hF
  have hW3 := integrable_zfW3 D hβ hβ10 hR F B hB hF
  have hW4 := integrable_zfW4 D hβ hβ10 hR F B hB hF
  -- (2) the recursion, rewritten as a single integral over the product space
  have hstep : zetaMmf R (m+1) F
      = ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ (2*m) * Complex.I ^ (2*m)
          * (∫ p : (Fin m → ℝ) × (Fin m → ℝ), Function.uncurry (zz R β F) p) := by
    rw [zetaMmf_succ (R := R) F hInt]
    congr 1
    exact MeasureTheory.integral_integral (f := zz R β F) hzz
  rw [hstep]
  -- (3) the pointwise identity in the shape needed for the split
  have hpt : ∀ p : (Fin m → ℝ) × (Fin m → ℝ), Function.uncurry (zz R β F) p
      = zfA R F p + (zfD R F p + (((2 * (Real.pi : ℂ) * Complex.I)⁻¹ * zfW1 R β F p
            + ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ 2 * zfW2 R β F p)
          + ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ * zfW3 R β F p
              + (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * zfW4 R β F p))) := by
    intro p
    rw [show Function.uncurry (zz R β F) p = zz R β F p.1 p.2 from rfl,
      zetaMf1_zz_eq D hβ hβ10 hR F B hF p.1 p.2]
    ring
  -- (4) integrability of the pieces
  have hE1 : Integrable (fun p : (Fin m → ℝ) × (Fin m → ℝ) =>
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * zfW1 R β F p) volume := hW1.const_mul _
  have hE2 : Integrable (fun p : (Fin m → ℝ) × (Fin m → ℝ) =>
      ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ 2 * zfW2 R β F p) volume := hW2.const_mul _
  have hE3 : Integrable (fun p : (Fin m → ℝ) × (Fin m → ℝ) =>
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * zfW3 R β F p) volume := hW3.const_mul _
  have hE4 : Integrable (fun p : (Fin m → ℝ) × (Fin m → ℝ) =>
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * zfW4 R β F p) volume := hW4.const_mul _
  have hE12 : Integrable (fun p : (Fin m → ℝ) × (Fin m → ℝ) =>
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * zfW1 R β F p
        + ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ 2 * zfW2 R β F p) volume := hE1.add hE2
  have hE34 : Integrable (fun p : (Fin m → ℝ) × (Fin m → ℝ) =>
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * zfW3 R β F p
        + (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * zfW4 R β F p) volume := hE3.add hE4
  have hE : Integrable (fun p : (Fin m → ℝ) × (Fin m → ℝ) =>
      ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ * zfW1 R β F p
          + ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ 2 * zfW2 R β F p)
        + ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ * zfW3 R β F p
            + (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * zfW4 R β F p)) volume := hE12.add hE34
  have hDE : Integrable (fun p : (Fin m → ℝ) × (Fin m → ℝ) =>
      zfD R F p + (((2 * (Real.pi : ℂ) * Complex.I)⁻¹ * zfW1 R β F p
            + ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ 2 * zfW2 R β F p)
          + ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ * zfW3 R β F p
              + (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * zfW4 R β F p))) volume := hD.add hE
  -- (5) the split
  have hsp1 : (∫ p : (Fin m → ℝ) × (Fin m → ℝ), zfA R F p
        + (zfD R F p + (((2 * (Real.pi : ℂ) * Complex.I)⁻¹ * zfW1 R β F p
              + ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ 2 * zfW2 R β F p)
            + ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ * zfW3 R β F p
                + (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * zfW4 R β F p))))
      = (∫ p, zfA R F p) + (∫ p, zfD R F p
          + (((2 * (Real.pi : ℂ) * Complex.I)⁻¹ * zfW1 R β F p
                + ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ 2 * zfW2 R β F p)
              + ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ * zfW3 R β F p
                  + (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * zfW4 R β F p))) :=
    MeasureTheory.integral_add hA hDE
  have hsp2 : (∫ p : (Fin m → ℝ) × (Fin m → ℝ), zfD R F p
        + (((2 * (Real.pi : ℂ) * Complex.I)⁻¹ * zfW1 R β F p
              + ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ 2 * zfW2 R β F p)
            + ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ * zfW3 R β F p
                + (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * zfW4 R β F p)))
      = (∫ p, zfD R F p) + (∫ p, ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ * zfW1 R β F p
              + ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ 2 * zfW2 R β F p)
            + ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ * zfW3 R β F p
                + (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * zfW4 R β F p)) :=
    MeasureTheory.integral_add hD hE
  have hsp3 : (∫ p : (Fin m → ℝ) × (Fin m → ℝ), ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ * zfW1 R β F p
              + ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ 2 * zfW2 R β F p)
            + ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ * zfW3 R β F p
                + (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * zfW4 R β F p))
      = (∫ p, ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ * zfW1 R β F p
              + ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ 2 * zfW2 R β F p))
        + (∫ p, ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ * zfW3 R β F p
                + (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * zfW4 R β F p)) :=
    MeasureTheory.integral_add hE12 hE34
  have hsp4 : (∫ p : (Fin m → ℝ) × (Fin m → ℝ), ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ * zfW1 R β F p
              + ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ 2 * zfW2 R β F p))
      = (∫ p, (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * zfW1 R β F p)
        + (∫ p, ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ 2 * zfW2 R β F p) :=
    MeasureTheory.integral_add hE1 hE2
  have hsp5 : (∫ p : (Fin m → ℝ) × (Fin m → ℝ), ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ * zfW3 R β F p
                + (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * zfW4 R β F p))
      = (∫ p, (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * zfW3 R β F p)
        + (∫ p, (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * zfW4 R β F p) :=
    MeasureTheory.integral_add hE3 hE4
  have hsp6 : (∫ p : (Fin m → ℝ) × (Fin m → ℝ), (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * zfW1 R β F p)
      = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * (∫ p, zfW1 R β F p) :=
    MeasureTheory.integral_const_mul ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) (zfW1 R β F)
  have hsp7 : (∫ p : (Fin m → ℝ) × (Fin m → ℝ), ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ 2 * zfW2 R β F p)
      = ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ 2 * (∫ p, zfW2 R β F p) :=
    MeasureTheory.integral_const_mul (((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ 2) (zfW2 R β F)
  have hsp8 : (∫ p : (Fin m → ℝ) × (Fin m → ℝ), (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * zfW3 R β F p)
      = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * (∫ p, zfW3 R β F p) :=
    MeasureTheory.integral_const_mul ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) (zfW3 R β F)
  have hsp9 : (∫ p : (Fin m → ℝ) × (Fin m → ℝ), (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * zfW4 R β F p)
      = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * (∫ p, zfW4 R β F p) :=
    MeasureTheory.integral_const_mul ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) (zfW4 R β F)
  have hsplit : (∫ p : (Fin m → ℝ) × (Fin m → ℝ), Function.uncurry (zz R β F) p)
      = (∫ p, zfA R F p) + ((∫ p, zfD R F p)
          + (((2 * (Real.pi : ℂ) * Complex.I)⁻¹ * (∫ p, zfW1 R β F p)
                + ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ 2 * (∫ p, zfW2 R β F p))
              + ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ * (∫ p, zfW3 R β F p)
                  + (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * (∫ p, zfW4 R β F p)))) := by
    rw [show (∫ p : (Fin m → ℝ) × (Fin m → ℝ), Function.uncurry (zz R β F) p)
        = ∫ p, zfA R F p + (zfD R F p + (((2 * (Real.pi : ℂ) * Complex.I)⁻¹ * zfW1 R β F p
              + ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ 2 * zfW2 R β F p)
            + ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ * zfW3 R β F p
                + (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * zfW4 R β F p)))
        from MeasureTheory.integral_congr_ae (Eventually.of_forall hpt)]
    rw [hsp1, hsp2, hsp3, hsp4, hsp5, hsp6, hsp7, hsp8, hsp9]
  rw [hsplit]
  -- (6) the six identifications
  have hIdA : (∫ p : (Fin m → ℝ) × (Fin m → ℝ), zfA R F p)
      = Real.log R * (((2:ℂ)*(Real.pi:ℂ))^(2*m) * zetaMmf R m (zcore F 0 0)) := by
    have hIA : Integrable (fun p : (Fin m → ℝ) × (Fin m → ℝ) =>
        F (Fin.cons 0 (fun j => zetaM1Eta R (p.1 j)))
          (Fin.cons 0 (fun j => zetaM1Eta R (p.2 j))) * WmK R m p.1 p.2) volume :=
      integrable_eval_WmK (R := R) hR
        (fun p : (Fin m → ℝ) × (Fin m → ℝ) =>
          F (Fin.cons 0 (fun j => zetaM1Eta R (p.1 j)))
            (Fin.cons 0 (fun j => zetaM1Eta R (p.2 j)))) B hB
        ((measurable_F_cons (R := R) F hF.1 measurable_const measurable_const
          measurable_fst measurable_snd).aestronglyMeasurable)
        (fun p => hF.2.2.2 _ _ (ZetaRegVec_cons (zetaReg_zero hβ) (ZetaRegVec_eta hβ hR p.1))
          (ZetaRegVec_cons (zetaReg_zero hβ) (ZetaRegVec_eta hβ hR p.2)))
    rw [show (∫ p, zfA R F p) = ∫ p, Real.log R * (F (Fin.cons 0 (fun j => zetaM1Eta R (p.1 j)))
          (Fin.cons 0 (fun j => zetaM1Eta R (p.2 j))) * WmK R m p.1 p.2)
        from MeasureTheory.integral_congr_ae
          (Eventually.of_forall (fun p => by rw [zfA]; ring))]
    rw [MeasureTheory.integral_const_mul]
    congr 1
    have hconv : (∫ p : (Fin m → ℝ) × (Fin m → ℝ),
          F (Fin.cons 0 (fun j => zetaM1Eta R (p.1 j)))
            (Fin.cons 0 (fun j => zetaM1Eta R (p.2 j))) * WmK R m p.1 p.2)
        = ∫ w : Fin m → ℝ, ∫ w' : Fin m → ℝ, F (Fin.cons 0 (fun j => zetaM1Eta R (w j)))
            (Fin.cons 0 (fun j => zetaM1Eta R (w' j))) * WmK R m w w' :=
      (MeasureTheory.integral_integral (f := fun (w w' : Fin m → ℝ) =>
        F (Fin.cons 0 (fun j => zetaM1Eta R (w j)))
          (Fin.cons 0 (fun j => zetaM1Eta R (w' j))) * WmK R m w w') hIA).symm
    rw [hconv]
    exact (two_pi_pow_mul_zetaMmf m (zcore F 0 0)).symm
  rw [hIdA]
  have hIdD : (∫ p : (Fin m → ℝ) × (Fin m → ℝ), zfD R F p)
      = ((2:ℂ)*(Real.pi:ℂ))^(2*m)
          * zetaMmf R m (fun z z' => deriv (fun x : ℂ => F (Fin.cons 0 z) (Fin.cons x z')) 0) := by
    have hmeas : AEStronglyMeasurable (fun p : (Fin m → ℝ) × (Fin m → ℝ) =>
        deriv (fun x : ℂ => F (Fin.cons 0 (fun j => zetaM1Eta R (p.1 j)))
          (Fin.cons x (fun j => zetaM1Eta R (p.2 j)))) 0) volume := by
      refine (Commons.Analysis.Complex.aemeasurable_deriv_parametric
        (volume : Measure ((Fin m → ℝ) × (Fin m → ℝ)))
        (fun (p : (Fin m → ℝ) × (Fin m → ℝ)) (x : ℂ) =>
          F (Fin.cons 0 (fun j => zetaM1Eta R (p.1 j)))
            (Fin.cons x (fun j => zetaM1Eta R (p.2 j)))) ?_ ?_).aestronglyMeasurable
      · exact measurable_F_cons (R := R) F hF.1 measurable_const measurable_snd
          measurable_fst.fst measurable_fst.snd
      · intro p
        have h := hF.2.2.1 0 (Fin.cons (α := fun _ => ℂ) 0 (fun j => zetaM1Eta R (p.1 j)))
          (Fin.cons (α := fun _ => ℂ) 0 (fun j => zetaM1Eta R (p.2 j)))
          (ZetaRegVec_cons (zetaReg_zero hβ) (ZetaRegVec_eta hβ hR p.1))
          (ZetaRegVec_cons (zetaReg_zero hβ) (ZetaRegVec_eta hβ hR p.2))
        rw [Fin.cons_zero] at h
        have heq : (fun x : ℂ => F (Fin.cons (α := fun _ => ℂ) 0 (fun j => zetaM1Eta R (p.1 j)))
              (Function.update (Fin.cons (α := fun _ => ℂ) 0 (fun j => zetaM1Eta R (p.2 j))) 0 x))
            = fun x : ℂ => F (Fin.cons (α := fun _ => ℂ) 0 (fun j => zetaM1Eta R (p.1 j)))
              (Fin.cons (α := fun _ => ℂ) x (fun j => zetaM1Eta R (p.2 j))) := by
          funext x; rw [update_cons_zero]
        rwa [heq] at h
    have hID : Integrable (fun p : (Fin m → ℝ) × (Fin m → ℝ) =>
        deriv (fun x : ℂ => F (Fin.cons 0 (fun j => zetaM1Eta R (p.1 j)))
          (Fin.cons x (fun j => zetaM1Eta R (p.2 j)))) 0 * WmK R m p.1 p.2) volume :=
      integrable_eval_WmK (R := R) hR
        (fun p : (Fin m → ℝ) × (Fin m → ℝ) => deriv (fun x : ℂ =>
          F (Fin.cons 0 (fun j => zetaM1Eta R (p.1 j)))
            (Fin.cons x (fun j => zetaM1Eta R (p.2 j)))) 0) (B / zetaRho β)
        (div_nonneg hB (zetaRho_pos hβ).le) hmeas
        (fun p => deriv_bound_ZetaReg hβ hβ10 _ B hB
          (fun x hx => by
            have h := hF.2.2.1 0 (Fin.cons (α := fun _ => ℂ) 0 (fun j => zetaM1Eta R (p.1 j)))
              (Fin.cons (α := fun _ => ℂ) x (fun j => zetaM1Eta R (p.2 j)))
              (ZetaRegVec_cons (zetaReg_zero hβ) (ZetaRegVec_eta hβ hR p.1))
              (ZetaRegVec_cons hx (ZetaRegVec_eta hβ hR p.2))
            rw [Fin.cons_zero] at h
            have heq : (fun y : ℂ => F (Fin.cons (α := fun _ => ℂ) 0 (fun j => zetaM1Eta R (p.1 j)))
                  (Function.update (Fin.cons (α := fun _ => ℂ) x (fun j => zetaM1Eta R (p.2 j))) 0 y))
                = fun y : ℂ => F (Fin.cons (α := fun _ => ℂ) 0 (fun j => zetaM1Eta R (p.1 j)))
                  (Fin.cons (α := fun _ => ℂ) y (fun j => zetaM1Eta R (p.2 j))) := by
              funext y; rw [update_cons_zero]
            rwa [heq] at h)
          (fun x hx => hF.2.2.2 _ _ (ZetaRegVec_cons (zetaReg_zero hβ) (ZetaRegVec_eta hβ hR p.1))
            (ZetaRegVec_cons hx (ZetaRegVec_eta hβ hR p.2))))
    rw [show (∫ p, zfD R F p) = ∫ p, deriv (fun x : ℂ =>
          F (Fin.cons 0 (fun j => zetaM1Eta R (p.1 j)))
            (Fin.cons x (fun j => zetaM1Eta R (p.2 j)))) 0 * WmK R m p.1 p.2
        from MeasureTheory.integral_congr_ae
          (Eventually.of_forall (fun p => by rw [zfD]))]
    have hconv : (∫ p : (Fin m → ℝ) × (Fin m → ℝ), deriv (fun x : ℂ =>
          F (Fin.cons 0 (fun j => zetaM1Eta R (p.1 j)))
            (Fin.cons x (fun j => zetaM1Eta R (p.2 j)))) 0 * WmK R m p.1 p.2)
        = ∫ w : Fin m → ℝ, ∫ w' : Fin m → ℝ, deriv (fun x : ℂ =>
            F (Fin.cons 0 (fun j => zetaM1Eta R (w j)))
              (Fin.cons x (fun j => zetaM1Eta R (w' j)))) 0 * WmK R m w w' :=
      (MeasureTheory.integral_integral (f := fun (w w' : Fin m → ℝ) => deriv (fun x : ℂ =>
        F (Fin.cons 0 (fun j => zetaM1Eta R (w j)))
          (Fin.cons x (fun j => zetaM1Eta R (w' j)))) 0 * WmK R m w w') hID).symm
    rw [hconv]
    exact (two_pi_pow_mul_zetaMmf m
      (fun z z' => deriv (fun x : ℂ => F (Fin.cons 0 z) (Fin.cons x z')) 0)).symm
  have hIdW1 : (∫ p : (Fin m → ℝ) × (Fin m → ℝ), zfW1 R β F p)
      = ((2:ℂ)*(Real.pi:ℂ))^(2*m)
          * (∫ t : ℝ, zetaMmf R m (zcore F 0 (gam β t)) * gW1 R β t) := by
    have hconv : (∫ p : (Fin m → ℝ) × (Fin m → ℝ), zfW1 R β F p)
        = ∫ w : Fin m → ℝ, ∫ w' : Fin m → ℝ, zfW1 R β F (w, w') :=
      (MeasureTheory.integral_integral (f := fun (w w' : Fin m → ℝ) => zfW1 R β F (w, w')) hW1).symm
    rw [hconv]
    exact zetaT_W1 hβ hR F (integrable_gW1_integrand hβ hR F B hB hF.1
      (fun z z' hz hz' => hF.2.2.2 z z' hz hz'))
  have hIdW2 : (∫ p : (Fin m → ℝ) × (Fin m → ℝ), zfW2 R β F p)
      = ((2:ℂ)*(Real.pi:ℂ))^(2*m)
          * (∫ t : ℝ, ∫ t' : ℝ, zetaMmf R m (zcore F (gam β t) (gam β t'))
              * zetaM1Kernel R (fun _ _ => (1:ℂ)) (gam β t) (gam β t')
              * gamDot β t * gamDot β t') := by
    have hconv : (∫ p : (Fin m → ℝ) × (Fin m → ℝ), zfW2 R β F p)
        = ∫ w : Fin m → ℝ, ∫ w' : Fin m → ℝ, zfW2 R β F (w, w') :=
      (MeasureTheory.integral_integral (f := fun (w w' : Fin m → ℝ) => zfW2 R β F (w, w')) hW2).symm
    rw [hconv]
    exact zetaT_W2 hβ hR F (integrable_gW2_integrand hβ hR F B D.C₁ D.Cn D.hC₁pos D.hCnpos hB
      hF.1 (fun z z' hz hz' => hF.2.2.2 z z' hz hz')
      (fun z hz h1 h2 => (D.hreg z hz h1 h2).2.2) D.hnum D.hUint)
  have hIdW3 : (∫ p : (Fin m → ℝ) × (Fin m → ℝ), zfW3 R β F p)
      = ((2:ℂ)*(Real.pi:ℂ))^(2*m)
          * (∫ t : ℝ, zetaMmf R m (zcore F (gam β t) 0) * gW1 R β t) := by
    have hconv : (∫ p : (Fin m → ℝ) × (Fin m → ℝ), zfW3 R β F p)
        = ∫ w : Fin m → ℝ, ∫ w' : Fin m → ℝ, zfW3 R β F (w, w') :=
      (MeasureTheory.integral_integral (f := fun (w w' : Fin m → ℝ) => zfW3 R β F (w, w')) hW3).symm
    rw [hconv]
    exact zetaT_W3 hβ hR F (integrable_gW3_integrand hβ hR F B hB hF.1
      (fun z z' hz hz' => hF.2.2.2 z z' hz hz'))
  have hIdW4 : (∫ p : (Fin m → ℝ) × (Fin m → ℝ), zfW4 R β F p)
      = ((2:ℂ)*(Real.pi:ℂ))^(2*m)
          * (∫ t : ℝ, zetaMmf R m (zcore F (gam β t) (-(gam β t))) * gW4 β t) := by
    have hconv : (∫ p : (Fin m → ℝ) × (Fin m → ℝ), zfW4 R β F p)
        = ∫ w : Fin m → ℝ, ∫ w' : Fin m → ℝ, zfW4 R β F (w, w') :=
      (MeasureTheory.integral_integral (f := fun (w w' : Fin m → ℝ) => zfW4 R β F (w, w')) hW4).symm
    rw [hconv]
    exact zetaT_W4 hβ hR F (integrable_gW4_integrand hβ hβ10 hR F B hB hF.1
      (fun z z' hz hz' => hF.2.2.2 z z' hz hz') D.hQint)
  rw [hIdD, hIdW1, hIdW2, hIdW3, hIdW4]
  have hCPi : ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ (2 * m) * Complex.I ^ (2 * m)
      * (((2:ℂ) * (Real.pi:ℂ)) ^ (2 * m)) = 1 := by
    rw [show ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ (2 * m) * Complex.I ^ (2 * m)
          * ((2:ℂ) * (Real.pi:ℂ)) ^ (2 * m)
        = ((2:ℂ) * (Real.pi:ℂ)) ^ (2 * m)
          * (((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ (2 * m) * Complex.I ^ (2 * m)) from by ring,
      two_pi_pow_mul]
  rw [show ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ (2 * m) * Complex.I ^ (2 * m) *
      (Real.log R * (((2:ℂ) * (Real.pi:ℂ)) ^ (2 * m) * zetaMmf R m (zcore F 0 0)) +
        ((((2:ℂ) * (Real.pi:ℂ)) ^ (2 * m) * zetaMmf R m
              (fun z z' => deriv (fun x => F (Fin.cons 0 z) (Fin.cons x z')) 0)) +
          ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
                (((2:ℂ) * (Real.pi:ℂ)) ^ (2 * m) * ∫ t : ℝ, zetaMmf R m (zcore F 0 (gam β t)) * gW1 R β t) +
              ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ 2 *
                (((2:ℂ) * (Real.pi:ℂ)) ^ (2 * m) *
                  ∫ t : ℝ, ∫ t' : ℝ, zetaMmf R m (zcore F (gam β t) (gam β t')) *
                      zetaM1Kernel R (fun _ _ => (1:ℂ)) (gam β t) (gam β t') * gamDot β t * gamDot β t') +
            ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
                (((2:ℂ) * (Real.pi:ℂ)) ^ (2 * m) * ∫ t : ℝ, zetaMmf R m (zcore F (gam β t) 0) * gW1 R β t) +
              (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
                (((2:ℂ) * (Real.pi:ℂ)) ^ (2 * m) *
                  ∫ t : ℝ, zetaMmf R m (zcore F (gam β t) (-(gam β t))) * gW4 β t)))))
      = ((((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ (2 * m) * Complex.I ^ (2 * m)
            * (((2:ℂ) * (Real.pi:ℂ)) ^ (2 * m)))
          * (Real.log R * zetaMmf R m (zcore F 0 0)
            + (zetaMmf R m (fun z z' => deriv (fun x : ℂ => F (Fin.cons 0 z) (Fin.cons x z')) 0)
              + (((2 * (Real.pi : ℂ) * Complex.I)⁻¹
                    * (∫ t : ℝ, zetaMmf R m (zcore F 0 (gam β t)) * gW1 R β t)
                  + ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ 2
                    * (∫ t : ℝ, ∫ t' : ℝ, zetaMmf R m (zcore F (gam β t) (gam β t'))
                        * zetaM1Kernel R (fun _ _ => (1:ℂ)) (gam β t) (gam β t')
                        * gamDot β t * gamDot β t'))
                + ((2 * (Real.pi : ℂ) * Complex.I)⁻¹
                      * (∫ t : ℝ, zetaMmf R m (zcore F (gam β t) 0) * gW1 R β t)
                    + (2 * (Real.pi : ℂ) * Complex.I)⁻¹
                      * (∫ t : ℝ, zetaMmf R m (zcore F (gam β t) (-(gam β t))) * gW4 β t)))))) from by
        ring,
    hCPi, one_mul]

/-! ## The four `Γ₀`-contributions of the recursion -/

noncomputable def WA1 {m : ℕ} (R β : ℝ) (F : (Fin (m+1) → ℂ) → (Fin (m+1) → ℂ) → ℂ) : ℂ :=
  ∫ t : ℝ, zetaMmf R m (zcore F 0 (gam β t)) * gW1 R β t

noncomputable def WA2 {m : ℕ} (R β : ℝ) (F : (Fin (m+1) → ℂ) → (Fin (m+1) → ℂ) → ℂ) : ℂ :=
  ∫ t : ℝ, ∫ t' : ℝ, zetaMmf R m (zcore F (gam β t) (gam β t'))
    * zetaM1Kernel R (fun _ _ => (1:ℂ)) (gam β t) (gam β t') * gamDot β t * gamDot β t'

noncomputable def WA3 {m : ℕ} (R β : ℝ) (F : (Fin (m+1) → ℂ) → (Fin (m+1) → ℂ) → ℂ) : ℂ :=
  ∫ t : ℝ, zetaMmf R m (zcore F (gam β t) 0) * gW1 R β t

noncomputable def WA4 {m : ℕ} (R β : ℝ) (F : (Fin (m+1) → ℂ) → (Fin (m+1) → ℂ) → ℂ) : ℂ :=
  ∫ t : ℝ, zetaMmf R m (zcore F (gam β t) (-(gam β t))) * gW4 β t

/-- The total error term of the recursion. -/
noncomputable def Wtot {m : ℕ} (R β : ℝ) (F : (Fin (m+1) → ℂ) → (Fin (m+1) → ℂ) → ℂ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * WA1 R β F
    + (((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ 2 * WA2 R β F
      + ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ * WA3 R β F
          + (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * WA4 R β F))

lemma zetaMmf_step_decomp' {β R : ℝ} (D : ZetaAux β) (hβ : 0 < β) (hβ10 : β ≤ 1 / 10)
    (hR : 3 ≤ R) {m : ℕ}
    (F : (Fin (m+1) → ℂ) → (Fin (m+1) → ℂ) → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hF : ZetaAdm β (m+1) F B) :
    zetaMmf R (m+1) F
      = Real.log R * zetaMmf R m (zcore F 0 0)
        + (zetaMmf R m (fun z z' => deriv (fun x : ℂ => F (Fin.cons 0 z) (Fin.cons x z')) 0)
          + Wtot R β F) := by
  have h := zetaMmf_step_decomp D hβ hβ10 hR F B hB hF
  rw [h]
  simp only [Wtot, WA1, WA2, WA3, WA4]
  ring

/-- Bound for the `W₂`-weight. -/
lemma integral_norm_W2weight_le {β R : ℝ} (D : ZetaAux β) (hβ : 0 < β) (hβ10 : β ≤ 1 / 10)
    (hR : 3 ≤ R) :
    (∫ t : ℝ, ∫ t' : ℝ, ‖zetaM1Kernel R (fun _ _ => (1:ℂ)) (gam β t) (gam β t')
        * gamDot β t * gamDot β t'‖) ≤ K2c D := by
  have hRone : (1:ℝ) ≤ R := by linarith
  set cw : ℝ := D.Cn * D.C₁ * D.C₁ * curveConst β ^ 2 with hcw
  have hcw0 : 0 ≤ cw := by
    rw [hcw]
    exact mul_nonneg (mul_nonneg (mul_nonneg D.hCnpos.le D.hC₁pos.le) D.hC₁pos.le)
      (pow_nonneg (curveConst_pos hβ).le 2)
  have hpt : ∀ t t' : ℝ, ‖zetaM1Kernel R (fun _ _ => (1:ℂ)) (gam β t) (gam β t')
        * gamDot β t * gamDot β t'‖ ≤ cw * (uScale t * uScale t') := by
    intro t t'
    have h := gamma_gamma_pointwise hβ hRone (fun _ _ : ℂ => (1:ℂ)) 1 D.C₁ D.Cn
      zero_le_one D.hC₁pos D.hCnpos
      (fun z hz h1 h2 => (D.hreg z hz h1 h2).2.2)
      (fun z z' h1 h2 h3 h4 => by simp)
      D.hnum t t'
    have h1 : ‖zetaM1Kernel R (fun _ _ => (1:ℂ)) (gam β t) (gam β t')
          * gamDot β t * gamDot β t'‖
        = ‖zetaM1Kernel R (fun _ _ => (1:ℂ)) (gam β t) (gam β t') * gamDot β t'‖
          * ‖gamDot β t‖ := by simp only [norm_mul]; ring
    rw [h1, hcw]
    calc ‖zetaM1Kernel R (fun _ _ => (1:ℂ)) (gam β t) (gam β t') * gamDot β t'‖
          * ‖gamDot β t‖
        ≤ (1 * D.Cn * D.C₁ * D.C₁ * curveConst β ^ 2) * (uScale t * uScale t') := h
      _ = D.Cn * D.C₁ * D.C₁ * curveConst β ^ 2 * (uScale t * uScale t') := by ring
  have hdom : Integrable (fun z : ℝ × ℝ => cw * (uScale z.1 * uScale z.2))
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) :=
    ((D.hUint.mul_prod D.hUint).const_mul cw)
  have hint : Integrable (fun z : ℝ × ℝ => ‖zetaM1Kernel R (fun _ _ => (1:ℂ))
      (gam β z.1) (gam β z.2) * gamDot β z.1 * gamDot β z.2‖)
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
    refine hdom.mono' ?_ ?_
    · refine Measurable.aestronglyMeasurable ?_
      exact (((measurable_zetaM1Kernel_gam (β := β) (R := R) (by linarith)).mul
        ((Commons.Analysis.Complex.measurable_gamDot β).comp measurable_fst)).mul
        ((Commons.Analysis.Complex.measurable_gamDot β).comp measurable_snd)).norm
    · filter_upwards with z
      rw [Real.norm_of_nonneg (norm_nonneg _)]
      exact hpt z.1 z.2
  rw [← MeasureTheory.integral_prod (fun z : ℝ × ℝ => ‖zetaM1Kernel R (fun _ _ => (1:ℂ))
      (gam β z.1) (gam β z.2) * gamDot β z.1 * gamDot β z.2‖) hint]
  calc (∫ z : ℝ × ℝ, ‖zetaM1Kernel R (fun _ _ => (1:ℂ)) (gam β z.1) (gam β z.2)
        * gamDot β z.1 * gamDot β z.2‖)
      ≤ ∫ z : ℝ × ℝ, cw * (uScale z.1 * uScale z.2) :=
        MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall (fun z => norm_nonneg _)) hdom
          (Filter.Eventually.of_forall (fun z => hpt z.1 z.2))
    _ = cw * ((∫ t : ℝ, uScale t) * (∫ t : ℝ, uScale t)) := by
        rw [MeasureTheory.integral_const_mul,
          show (∫ z : ℝ × ℝ, uScale z.1 * uScale z.2)
            = (∫ t : ℝ, uScale t) * (∫ t : ℝ, uScale t) from
          MeasureTheory.integral_prod_mul (fun t : ℝ => uScale t) (fun t : ℝ => uScale t)]
    _ ≤ cw * (D.Ku * D.Ku) := by
        refine mul_le_mul_of_nonneg_left ?_ hcw0
        exact mul_le_mul D.hUle D.hUle (MeasureTheory.integral_nonneg (fun t => uScale_nonneg t)) D.hKupos.le
    _ = K2c D := by rw [hcw, K2c]; ring

/-- The pointwise bound for the `m`-fold functional applied to a `cons`-restriction. -/
lemma zetaMmf_cons_bound {β R : ℝ} {m : ℕ} (D : ZetaAux β) (hβ : 0 < β) (hβ10 : β ≤ 1 / 10)
    (hR : 3 ≤ R) (hm : 1 ≤ m) (C : ℝ) (hC1 : 1 ≤ C)
    (F : (Fin (m+1) → ℂ) → (Fin (m+1) → ℂ) → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hF : ZetaAdm β (m+1) F B)
    (IH : ∀ (G : (Fin m → ℂ) → (Fin m → ℂ) → ℂ) (B' : ℝ), 0 ≤ B' → ZetaAdm β m G B' →
        ‖zetaMmf R m G - G 0 0 * (Real.log R)^m‖ ≤ C^m * B' * (1 + (Real.log R)^(m-1)))
    {a b : ℂ} (ha : ZetaReg β a) (hb : ZetaReg β b) :
    ‖zetaMmf R m (zcore F a b)‖ ≤ 2 * C^m * B * (1 + (Real.log R)^m) := by
  have hlogR0 : 0 ≤ Real.log R := Real.log_nonneg (by linarith)
  have hlogR1 : (1:ℝ) ≤ Real.log R := by
    have h3 : (1:ℝ) < Real.log 3 := by
      rw [← Real.log_exp 1]
      exact Real.log_lt_log (Real.exp_pos 1) Real.exp_one_lt_three
    exact le_trans h3.le (Real.log_le_log (by norm_num) hR)
  have hCm : (1:ℝ) ≤ C^m := one_le_pow₀ hC1
  have h1 := IH (zcore F a b) B hB (ZetaAdm_cons hF a b ha hb)
  have hbnd : ‖zcore F a b (0 : Fin m → ℂ) (0 : Fin m → ℂ)‖ ≤ B := by
    rw [zcore_apply]
    exact hF.2.2.2 _ _ (ZetaRegVec_cons ha (fun j => zetaReg_zero hβ))
      (ZetaRegVec_cons hb (fun j => zetaReg_zero hβ))
  have hnorm : ‖((Real.log R) : ℂ)^m‖ = (Real.log R)^m := by
    rw [← Complex.ofReal_pow, norm_ofReal_of_nonneg (pow_nonneg hlogR0 m)]
  have hpow : (Real.log R)^(m-1) ≤ (Real.log R)^m :=
    pow_le_pow_right₀ hlogR1 (Nat.sub_le m 1)
  have hlogm : 0 ≤ (Real.log R)^m := pow_nonneg hlogR0 m
  have hsub : ‖zetaMmf R m (zcore F a b) - zcore F a b 0 0 * (Real.log R)^m‖
      ≤ C^m * B * (1 + (Real.log R)^(m-1)) := h1
  have hsec : ‖zcore F a b 0 0 * ((Real.log R) : ℂ)^m‖ ≤ B * (Real.log R)^m := by
    rw [norm_mul, hnorm]
    exact mul_le_mul_of_nonneg_right hbnd hlogm
  have hC0 : 0 ≤ C^m := le_trans zero_le_one hCm
  have hstep1 : C^m * B * (1 + (Real.log R)^(m-1)) + B * (Real.log R)^m
      ≤ 2 * C^m * B * (1 + (Real.log R)^m) := by
    have h2 : B * (Real.log R)^m ≤ C^m * B * (Real.log R)^m := by
      have h2' := le_mul_of_one_le_left (mul_nonneg hB hlogm) hCm
      calc B * (Real.log R)^m ≤ C^m * (B * (Real.log R)^m) := h2'
        _ = C^m * B * (Real.log R)^m := by ring
    have h3 : 1 + (Real.log R)^(m-1) ≤ 1 + (Real.log R)^m := by linarith
    have h4 : C^m * B * (1 + (Real.log R)^(m-1)) ≤ C^m * B * (1 + (Real.log R)^m) :=
      mul_le_mul_of_nonneg_left h3 (mul_nonneg hC0 hB)
    have h5 : C^m * B * (Real.log R)^m ≤ C^m * B * (1 + (Real.log R)^m) :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hC0 hB)
    linarith
  calc ‖zetaMmf R m (zcore F a b)‖
      ≤ ‖zetaMmf R m (zcore F a b) - zcore F a b 0 0 * (Real.log R)^m‖
          + ‖zcore F a b 0 0 * (Real.log R)^m‖ := by
        have h := norm_le_norm_sub_add (zetaMmf R m (zcore F a b))
          (zcore F a b 0 0 * (Real.log R)^m)
        simpa using h
    _ ≤ C^m * B * (1 + (Real.log R)^(m-1)) + B * (Real.log R)^m := add_le_add hsub hsec
    _ ≤ 2 * C^m * B * (1 + (Real.log R)^m) := hstep1

/-- The induction step: the `(m+1)`-fold bound from the `m`-fold bound. -/
lemma zetaMmf_step_bound {β R : ℝ} (D : ZetaAux β) (hβ : 0 < β) (hβ10 : β ≤ 1 / 10)
    (hR : 3 ≤ R) {m : ℕ} (hm : 1 ≤ m) (C : ℝ) (hC1 : 1 ≤ C)
    (hCbig : 2 + 3 / zetaRho β + 2 * (2 * Real.pi)⁻¹ * (2 * K1c β + D.Cq)
        + 2 * (2 * Real.pi)⁻¹ ^ 2 * K2c D ≤ C)
    (F : (Fin (m+1) → ℂ) → (Fin (m+1) → ℂ) → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hF : ZetaAdm β (m+1) F B)
    (IH : ∀ (G : (Fin m → ℂ) → (Fin m → ℂ) → ℂ) (B' : ℝ), 0 ≤ B' → ZetaAdm β m G B' →
        ‖zetaMmf R m G - G 0 0 * (Real.log R)^m‖ ≤ C^m * B' * (1 + (Real.log R)^(m-1))) :
    ‖zetaMmf R (m+1) F - F 0 0 * (Real.log R)^(m+1)‖ ≤ C^(m+1) * B * (1 + (Real.log R)^m) := by
  have hRone : (1:ℝ) ≤ R := by linarith
  have hρpos : 0 < zetaRho β := zetaRho_pos hβ
  have hlogR0 : 0 ≤ Real.log R := Real.log_nonneg hRone
  have hlogR1 : (1:ℝ) ≤ Real.log R := by
    have h3 : (1:ℝ) < Real.log 3 := by
      rw [← Real.log_exp 1]
      exact Real.log_lt_log (Real.exp_pos 1) Real.exp_one_lt_three
    exact le_trans h3.le (Real.log_le_log (by norm_num) hR)
  have hCm : (1:ℝ) ≤ C^m := one_le_pow₀ hC1
  have hK1 : 0 ≤ K1c β := K1c_nonneg β hβ
  have hK2 : 0 ≤ K2c D := K2c_nonneg D hβ
  set cc : ℝ := 2 * C^m * B * (1 + (Real.log R)^m) with hcc
  have hcc0 : 0 ≤ cc := by
    rw [hcc]
    have h1 : 0 ≤ C^m := le_trans zero_le_one hCm
    positivity
  set K : ℝ := (2 * Real.pi)⁻¹ * (2 * K1c β + D.Cq) + (2 * Real.pi)⁻¹ ^ 2 * K2c D with hK
  have hK0 : 0 ≤ K := by
    rw [hK]
    have h1 : 0 ≤ (2 * Real.pi)⁻¹ := by positivity
    have h2 : 0 ≤ 2 * K1c β + D.Cq := by linarith [hK1, D.hCqpos.le]
    have h3 : 0 ≤ (2 * Real.pi)⁻¹ ^ 2 := by positivity
    have h4 : 0 ≤ K2c D := hK2
    linarith [mul_nonneg h1 h2, mul_nonneg h3 h4, h1, h3]
  -- bounds for the four `Γ₀`-contributions
  have hA1 : ‖WA1 R β F‖ ≤ cc * K1c β := by
    rw [WA1, hcc]
    have hbd : ∀ t : ℝ, ‖zetaMmf R m (zcore F 0 (gam β t)) * gW1 R β t‖
        ≤ (2 * C^m * B * (1 + (Real.log R)^m)) * ‖gW1 R β t‖ := by
      intro t
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right
        (zetaMmf_cons_bound D hβ hβ10 hR hm C hC1 F B hB hF IH (zetaReg_zero hβ)
          (phi_mem_ZetaReg hβ t)) (norm_nonneg _)
    have hdom : Integrable (fun t : ℝ =>
        (2 * C^m * B * (1 + (Real.log R)^m)) * ‖gW1 R β t‖) volume :=
      (integrable_of_norm_gW1 hβ hRone).const_mul _
    calc ‖∫ t, zetaMmf R m (zcore F 0 (gam β t)) * gW1 R β t‖
        ≤ ∫ t, ‖zetaMmf R m (zcore F 0 (gam β t)) * gW1 R β t‖ :=
          MeasureTheory.norm_integral_le_integral_norm _
      _ ≤ ∫ t, (2 * C^m * B * (1 + (Real.log R)^m)) * ‖gW1 R β t‖ :=
          MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall (fun t => norm_nonneg _)) hdom
            (Filter.Eventually.of_forall hbd)
      _ = (2 * C^m * B * (1 + (Real.log R)^m)) * ∫ t, ‖gW1 R β t‖ :=
          MeasureTheory.integral_const_mul _ _
      _ ≤ (2 * C^m * B * (1 + (Real.log R)^m)) * K1c β :=
          mul_le_mul_of_nonneg_left (by simpa only [K1c] using norm_gW1_integral_le hβ hRone)
            (by positivity)
  have hA3 : ‖WA3 R β F‖ ≤ cc * K1c β := by
    rw [WA3, hcc]
    have hbd : ∀ t : ℝ, ‖zetaMmf R m (zcore F (gam β t) 0) * gW1 R β t‖
        ≤ (2 * C^m * B * (1 + (Real.log R)^m)) * ‖gW1 R β t‖ := by
      intro t
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right
        (zetaMmf_cons_bound D hβ hβ10 hR hm C hC1 F B hB hF IH (phi_mem_ZetaReg hβ t)
          (zetaReg_zero hβ)) (norm_nonneg _)
    have hdom : Integrable (fun t : ℝ =>
        (2 * C^m * B * (1 + (Real.log R)^m)) * ‖gW1 R β t‖) volume :=
      (integrable_of_norm_gW1 hβ hRone).const_mul _
    calc ‖∫ t, zetaMmf R m (zcore F (gam β t) 0) * gW1 R β t‖
        ≤ ∫ t, ‖zetaMmf R m (zcore F (gam β t) 0) * gW1 R β t‖ :=
          MeasureTheory.norm_integral_le_integral_norm _
      _ ≤ ∫ t, (2 * C^m * B * (1 + (Real.log R)^m)) * ‖gW1 R β t‖ :=
          MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall (fun t => norm_nonneg _)) hdom
            (Filter.Eventually.of_forall hbd)
      _ = (2 * C^m * B * (1 + (Real.log R)^m)) * ∫ t, ‖gW1 R β t‖ :=
          MeasureTheory.integral_const_mul _ _
      _ ≤ (2 * C^m * B * (1 + (Real.log R)^m)) * K1c β :=
          mul_le_mul_of_nonneg_left (by simpa only [K1c] using norm_gW1_integral_le hβ hRone)
            (by positivity)
  have hA4 : ‖WA4 R β F‖ ≤ cc * D.Cq := by
    rw [WA4, hcc]
    set qw : ℝ → ℝ := fun t => ‖gamDot β t‖
      / (‖riemannZeta (1 + gam β t)‖ * ‖riemannZeta (1 - gam β t)‖ * ‖gam β t‖ ^ 4) with hqw
    have hbd : ∀ t : ℝ, ‖zetaMmf R m (zcore F (gam β t) (-(gam β t))) * gW4 β t‖
        ≤ (2 * C^m * B * (1 + (Real.log R)^m)) * qw t := by
      intro t
      rw [norm_mul, hqw]
      exact mul_le_mul_of_nonneg_right
        (zetaMmf_cons_bound D hβ hβ10 hR hm C hC1 F B hB hF IH (phi_mem_ZetaReg hβ t)
          (neg_phi_mem_ZetaReg hβ hβ10 t)) (norm_nonneg _) |>.trans
        (mul_le_mul_of_nonneg_left (by simpa only [hqw] using norm_gW4_le β t) (by positivity))
    have hdom : Integrable (fun t : ℝ =>
        (2 * C^m * B * (1 + (Real.log R)^m)) * qw t) volume := by
      rw [hqw]
      exact D.hQint.const_mul _
    calc ‖∫ t, zetaMmf R m (zcore F (gam β t) (-(gam β t))) * gW4 β t‖
        ≤ ∫ t, ‖zetaMmf R m (zcore F (gam β t) (-(gam β t))) * gW4 β t‖ :=
          MeasureTheory.norm_integral_le_integral_norm _
      _ ≤ ∫ t, (2 * C^m * B * (1 + (Real.log R)^m)) * qw t :=
          MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall (fun t => norm_nonneg _)) hdom
            (Filter.Eventually.of_forall hbd)
      _ = (2 * C^m * B * (1 + (Real.log R)^m)) * ∫ t, qw t :=
          MeasureTheory.integral_const_mul _ _
      _ ≤ (2 * C^m * B * (1 + (Real.log R)^m)) * D.Cq := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact (by simpa only [hqw] using D.hQle)
  have hA2 : ‖WA2 R β F‖ ≤ cc * K2c D := by
    rw [WA2, hcc, K2c]
    set cw0 : ℝ := D.Cn * D.C₁ * D.C₁ * curveConst β ^ 2 with hcw0
    have hcw0nn : 0 ≤ cw0 := by
      rw [hcw0]
      exact mul_nonneg (mul_nonneg (mul_nonneg D.hCnpos.le D.hC₁pos.le) D.hC₁pos.le)
        (pow_nonneg (curveConst_pos hβ).le 2)
    have hinner : ∀ t : ℝ, ‖∫ t' : ℝ, zetaMmf R m (zcore F (gam β t) (gam β t'))
          * zetaM1Kernel R (fun _ _ => (1:ℂ)) (gam β t) (gam β t') * gamDot β t * gamDot β t'‖
        ≤ (2 * C^m * B * (1 + (Real.log R)^m)) * (cw0 * (∫ s : ℝ, uScale s)) * uScale t := by
      intro t
      have hdom : Integrable (fun t' : ℝ => (2 * C^m * B * (1 + (Real.log R)^m)) * cw0
          * uScale t * uScale t') volume := D.hUint.const_mul _
      refine le_trans (MeasureTheory.norm_integral_le_of_norm_le hdom
        (Filter.Eventually.of_forall (fun t' => ?_))) ?_
      · have h1 := zetaMmf_cons_bound D hβ hβ10 hR hm C hC1 F B hB hF IH
          (phi_mem_ZetaReg hβ t) (phi_mem_ZetaReg hβ t')
        have hK : ‖zetaM1Kernel R (fun _ _ => (1:ℂ)) (gam β t) (gam β t')‖ * ‖gamDot β t‖
            * ‖gamDot β t'‖ ≤ cw0 * (uScale t * uScale t') := by
          have h := gamma_gamma_pointwise hβ hRone (fun _ _ : ℂ => (1:ℂ)) 1 D.C₁ D.Cn
            zero_le_one D.hC₁pos D.hCnpos
            (fun z hz h1 h2 => (D.hreg z hz h1 h2).2.2)
            (fun z z' h1 h2 h3 h4 => by simp) D.hnum t t'
          have he : ‖zetaM1Kernel R (fun _ _ => (1:ℂ)) (gam β t) (gam β t')‖ * ‖gamDot β t‖
              * ‖gamDot β t'‖
              = ‖zetaM1Kernel R (fun _ _ => (1:ℂ)) (gam β t) (gam β t')
                  * gamDot β t'‖ * ‖gamDot β t‖ := by simp only [norm_mul]; ring
          rw [he, hcw0]
          calc ‖zetaM1Kernel R (fun _ _ => (1:ℂ)) (gam β t) (gam β t') * gamDot β t'‖
                * ‖gamDot β t‖
              ≤ (1 * D.Cn * D.C₁ * D.C₁ * curveConst β ^ 2) * (uScale t * uScale t') := h
            _ = D.Cn * D.C₁ * D.C₁ * curveConst β ^ 2 * (uScale t * uScale t') := by ring
        have he : ‖zetaMmf R m (zcore F (gam β t) (gam β t'))
              * zetaM1Kernel R (fun _ _ => (1:ℂ)) (gam β t) (gam β t') * gamDot β t
              * gamDot β t'‖
            = ‖zetaMmf R m (zcore F (gam β t) (gam β t'))‖
              * (‖zetaM1Kernel R (fun _ _ => (1:ℂ)) (gam β t) (gam β t')‖ * ‖gamDot β t‖
                * ‖gamDot β t'‖) := by simp only [norm_mul]; ring
        rw [he]
        calc ‖zetaMmf R m (zcore F (gam β t) (gam β t'))‖
              * (‖zetaM1Kernel R (fun _ _ => (1:ℂ)) (gam β t) (gam β t')‖ * ‖gamDot β t‖
                * ‖gamDot β t'‖)
            ≤ (2 * C^m * B * (1 + (Real.log R)^m)) * (cw0 * (uScale t * uScale t')) :=
              mul_le_mul h1 hK (by positivity) (by positivity)
          _ = (2 * C^m * B * (1 + (Real.log R)^m)) * cw0 * uScale t * uScale t' := by ring
      · refine le_of_eq ?_
        have hstep : (∫ t' : ℝ, (2 * C^m * B * (1 + (Real.log R)^m)) * cw0 * uScale t * uScale t')
            = ((2 * C^m * B * (1 + (Real.log R)^m)) * cw0 * uScale t) * (∫ s : ℝ, uScale s) := by
          rw [MeasureTheory.integral_const_mul]
        rw [hstep]
        ring
    have hdom2 : Integrable (fun t : ℝ => (2 * C^m * B * (1 + (Real.log R)^m))
        * (cw0 * (∫ s : ℝ, uScale s)) * uScale t) volume := D.hUint.const_mul _
    calc ‖∫ t, ∫ t', zetaMmf R m (zcore F (gam β t) (gam β t'))
          * zetaM1Kernel R (fun _ _ => (1:ℂ)) (gam β t) (gam β t') * gamDot β t * gamDot β t'‖
        ≤ ∫ t, ‖∫ t', zetaMmf R m (zcore F (gam β t) (gam β t'))
            * zetaM1Kernel R (fun _ _ => (1:ℂ)) (gam β t) (gam β t') * gamDot β t
            * gamDot β t'‖ := MeasureTheory.norm_integral_le_integral_norm _
      _ ≤ ∫ t, (2 * C^m * B * (1 + (Real.log R)^m)) * (cw0 * (∫ s : ℝ, uScale s))
            * uScale t := MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall (fun t => norm_nonneg _)) hdom2
            (Filter.Eventually.of_forall hinner)
      _ = (2 * C^m * B * (1 + (Real.log R)^m)) * (cw0 * (∫ s : ℝ, uScale s))
            * (∫ s : ℝ, uScale s) := by rw [MeasureTheory.integral_const_mul]
      _ ≤ (2 * C^m * B * (1 + (Real.log R)^m)) * (cw0 * D.Ku) * D.Ku := by
          have hU : (∫ s : ℝ, uScale s) * (∫ s : ℝ, uScale s) ≤ D.Ku * D.Ku :=
            mul_le_mul D.hUle D.hUle (MeasureTheory.integral_nonneg (fun s => uScale_nonneg s))
              D.hKupos.le
          have hA : 0 ≤ 2 * C^m * B * (1 + (Real.log R)^m) := by positivity
          calc (2 * C^m * B * (1 + (Real.log R)^m)) * (cw0 * (∫ s : ℝ, uScale s))
                * (∫ s : ℝ, uScale s)
              = (2 * C^m * B * (1 + (Real.log R)^m))
                * (cw0 * ((∫ s : ℝ, uScale s) * (∫ s : ℝ, uScale s))) := by ring
            _ ≤ (2 * C^m * B * (1 + (Real.log R)^m)) * (cw0 * (D.Ku * D.Ku)) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hU hcw0nn) hA
            _ = (2 * C^m * B * (1 + (Real.log R)^m)) * (cw0 * D.Ku) * D.Ku := by ring
      _ = 2 * C^m * B * (1 + (Real.log R)^m)
            * (D.Cn * D.C₁ * D.C₁ * curveConst β ^ 2 * D.Ku ^ 2) := by rw [hcw0]; ring
  -- the `Γ₀`-part of the recursion
  have hW : ‖Wtot R β F‖ ≤ cc * K := by
    rw [Wtot]
    have hc1 : ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹‖ = (2 * Real.pi)⁻¹ := by
      rw [norm_inv, norm_mul, norm_mul, Complex.norm_I, mul_one]
      have h2 : ‖(2:ℂ)‖ = 2 := by norm_num
      have hp : ‖(Real.pi : ℂ)‖ = Real.pi := norm_ofReal_of_nonneg Real.pi_pos.le
      rw [h2, hp]
    have hc2 : ‖((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ 2‖ = (2 * Real.pi)⁻¹ ^ 2 := by
      rw [norm_pow, hc1]
    have h1 : ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹ * WA1 R β F‖ ≤ (2 * Real.pi)⁻¹ * (cc * K1c β) := by
      rw [norm_mul, hc1]
      exact mul_le_mul_of_nonneg_left hA1 (by positivity)
    have h2 : ‖((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ 2 * WA2 R β F‖
        ≤ (2 * Real.pi)⁻¹ ^ 2 * (cc * K2c D) := by
      rw [norm_mul, hc2]
      exact mul_le_mul_of_nonneg_left hA2 (by positivity)
    have h3 : ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹ * WA3 R β F‖ ≤ (2 * Real.pi)⁻¹ * (cc * K1c β) := by
      rw [norm_mul, hc1]
      exact mul_le_mul_of_nonneg_left hA3 (by positivity)
    have h4 : ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹ * WA4 R β F‖ ≤ (2 * Real.pi)⁻¹ * (cc * D.Cq) := by
      rw [norm_mul, hc1]
      exact mul_le_mul_of_nonneg_left hA4 (by positivity)
    linarith [norm_add_le ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ * WA1 R β F)
        (((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ 2 * WA2 R β F
          + ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ * WA3 R β F
              + (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * WA4 R β F)),
      norm_add_le (((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ 2 * WA2 R β F)
        ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ * WA3 R β F
          + (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * WA4 R β F),
      norm_add_le ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ * WA3 R β F)
        ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ * WA4 R β F),
      h1, h2, h3, h4]
  -- the decomposition of the difference
  have hzz : zcore F 0 0 (0 : Fin m → ℂ) (0 : Fin m → ℂ) = F 0 0 := by
    rw [zcore_apply, cons_zero_zero]
  have hder : ‖deriv (fun u : ℂ => F 0 (Fin.cons u 0)) 0‖ ≤ B / zetaRho β := by
    refine deriv_bound_ZetaReg hβ hβ10 _ B hB ?_ ?_
    · intro z hz
      have h := hF.2.2.1 0 (0 : Fin (m+1) → ℂ) (Fin.cons (α := fun _ => ℂ) z (0 : Fin m → ℂ))
        (fun i => zetaReg_zero hβ) (ZetaRegVec_cons hz (fun j => zetaReg_zero hβ))
      have heq : (fun u : ℂ => F (0 : Fin (m+1) → ℂ)
            (Function.update (Fin.cons (α := fun _ => ℂ) z (0 : Fin m → ℂ)) 0 u))
          = fun u : ℂ => F (0 : Fin (m+1) → ℂ) (Fin.cons (α := fun _ => ℂ) u (0 : Fin m → ℂ)) := by
        funext u; rw [update_cons_zero]
      rw [Fin.cons_zero] at h
      rwa [heq] at h
    · intro z hz
      exact hF.2.2.2 _ _ (fun i => zetaReg_zero hβ) (ZetaRegVec_cons hz (fun j => zetaReg_zero hβ))
  have hb1 : ‖Real.log R * (zetaMmf R m (zcore F 0 0) - zcore F 0 0 0 0 * (Real.log R)^m)‖
      ≤ 2 * C^m * B * (Real.log R)^m := by
    rw [norm_mul, norm_ofReal_of_nonneg hlogR0]
    have hIH := IH (zcore F 0 0) B hB (ZetaAdm_cons hF 0 0 (zetaReg_zero hβ) (zetaReg_zero hβ))
    have hCm0 : 0 ≤ C^m := le_trans zero_le_one hCm
    have hL0 : 0 ≤ (Real.log R)^m := pow_nonneg hlogR0 m
    have h1 : Real.log R * (1 + (Real.log R)^(m-1)) ≤ 2 * (Real.log R)^m := by
      have h2 : Real.log R * (1 + (Real.log R)^(m-1)) = Real.log R + (Real.log R)^m := by
        rw [mul_add, mul_one]
        congr 1
        rw [← pow_succ', Nat.sub_add_cancel hm]
      have h3 : Real.log R ≤ (Real.log R)^m := by
        have := pow_le_pow_right₀ hlogR1 hm
        simpa using this
      rw [h2]; linarith
    calc Real.log R * ‖zetaMmf R m (zcore F 0 0) - zcore F 0 0 0 0 * (Real.log R)^m‖
        ≤ Real.log R * (C^m * B * (1 + (Real.log R)^(m-1))) := mul_le_mul_of_nonneg_left hIH hlogR0
      _ = C^m * B * (Real.log R * (1 + (Real.log R)^(m-1))) := by ring
      _ ≤ C^m * B * (2 * (Real.log R)^m) := mul_le_mul_of_nonneg_left h1 (mul_nonneg hCm0 hB)
      _ = 2 * C^m * B * (Real.log R)^m := by ring
  have hb2 : ‖zetaMmf R m (fun z z' => deriv (fun x : ℂ => F (Fin.cons 0 z) (Fin.cons x z')) 0)
        - deriv (fun u : ℂ => F 0 (Fin.cons u 0)) 0 * (Real.log R)^m‖
      ≤ C^m * (2 * B / zetaRho β) * (1 + (Real.log R)^(m-1)) :=
    deriv_mfold_bound hβ hβ10 hR hm C hC1 F B hB hF IH
  have hb3 : ‖deriv (fun u : ℂ => F 0 (Fin.cons u 0)) 0 * (Real.log R)^m‖
      ≤ B / zetaRho β * (Real.log R)^m := by
    rw [norm_mul]
    have hnorm : ‖((Real.log R) : ℂ)^m‖ = (Real.log R)^m := by
      rw [← Complex.ofReal_pow, norm_ofReal_of_nonneg (pow_nonneg hlogR0 m)]
    rw [hnorm]
    exact mul_le_mul_of_nonneg_right hder (pow_nonneg hlogR0 m)
  have hb4 : ‖Wtot R β F‖ ≤ cc * K := hW
  rw [zetaMmf_step_decomp' D hβ hβ10 hR F B hB hF]
  rw [show ‖(Real.log R * zetaMmf R m (zcore F 0 0)
          + (zetaMmf R m (fun z z' => deriv (fun x : ℂ => F (Fin.cons 0 z) (Fin.cons x z')) 0)
            + Wtot R β F)) - F 0 0 * (Real.log R)^(m+1)‖
      = ‖Real.log R * (zetaMmf R m (zcore F 0 0)
            - zcore F 0 0 (0 : Fin m → ℂ) (0 : Fin m → ℂ) * (Real.log R)^m)
        + ((zetaMmf R m (fun z z' => deriv (fun x : ℂ => F (Fin.cons 0 z) (Fin.cons x z')) 0)
              - deriv (fun u : ℂ => F 0 (Fin.cons u 0)) 0 * (Real.log R)^m)
            + (deriv (fun u : ℂ => F 0 (Fin.cons u 0)) 0 * (Real.log R)^m + Wtot R β F))‖
      from by rw [← hzz]; ring]
  refine le_trans (show ‖Real.log R * (zetaMmf R m (zcore F 0 0)
            - zcore F 0 0 (0 : Fin m → ℂ) (0 : Fin m → ℂ) * (Real.log R)^m)
        + ((zetaMmf R m (fun z z' => deriv (fun x : ℂ => F (Fin.cons 0 z) (Fin.cons x z')) 0)
              - deriv (fun u : ℂ => F 0 (Fin.cons u 0)) 0 * (Real.log R)^m)
            + (deriv (fun u : ℂ => F 0 (Fin.cons u 0)) 0 * (Real.log R)^m + Wtot R β F))‖
      ≤ ((2 * C^m * B * (Real.log R)^m
            + C^m * (2 * B / zetaRho β) * (1 + (Real.log R)^(m-1)))
          + B / zetaRho β * (Real.log R)^m) + 2 * C^m * B * (1 + (Real.log R)^m) * K from by
    have h1 := norm_add_le (Real.log R * (zetaMmf R m (zcore F 0 0)
          - zcore F 0 0 (0 : Fin m → ℂ) (0 : Fin m → ℂ) * (Real.log R)^m))
        ((zetaMmf R m (fun z z' => deriv (fun x : ℂ => F (Fin.cons 0 z) (Fin.cons x z')) 0)
            - deriv (fun u : ℂ => F 0 (Fin.cons u 0)) 0 * (Real.log R)^m)
          + (deriv (fun u : ℂ => F 0 (Fin.cons u 0)) 0 * (Real.log R)^m + Wtot R β F))
    have h2 := norm_add_le (zetaMmf R m (fun z z' => deriv (fun x : ℂ => F (Fin.cons 0 z) (Fin.cons x z')) 0)
            - deriv (fun u : ℂ => F 0 (Fin.cons u 0)) 0 * (Real.log R)^m)
        (deriv (fun u : ℂ => F 0 (Fin.cons u 0)) 0 * (Real.log R)^m + Wtot R β F)
    have h3 := norm_add_le (deriv (fun u : ℂ => F 0 (Fin.cons u 0)) 0 * (Real.log R)^m)
        (Wtot R β F)
    rw [hcc] at hb4
    linarith [h1, h2, h3, hb1, hb2, hb3, hb4]) ?_
  -- final arithmetic
  have hCC : 2 + 3 / zetaRho β + 2 * K ≤ C := by rw [hK]; linarith [hCbig]
  have hmul : C^m * B * (1 + (Real.log R)^m) * C = C^(m+1) * B * (1 + (Real.log R)^m) := by
    rw [pow_succ]
    ring
  have hL0 : 0 ≤ (Real.log R)^m := pow_nonneg hlogR0 m
  have hP : (Real.log R)^(m-1) ≤ (Real.log R)^m :=
    pow_le_pow_right₀ hlogR1 (Nat.sub_le m 1)
  have hL : (Real.log R)^m ≤ 1 + (Real.log R)^m := by linarith
  have hρ : 0 ≤ 1 / zetaRho β := by positivity
  have ht1 : 2 * C^m * B * (Real.log R)^m ≤ 2 * C^m * B * (1 + (Real.log R)^m) :=
    mul_le_mul_of_nonneg_left hL (by positivity)
  have ht2 : C^m * (2 * B / zetaRho β) * (1 + (Real.log R)^(m-1))
      ≤ C^m * B * (1 + (Real.log R)^m) * (2 / zetaRho β) := by
    calc C^m * (2 * B / zetaRho β) * (1 + (Real.log R)^(m-1))
        ≤ C^m * (2 * B / zetaRho β) * (1 + (Real.log R)^m) :=
          mul_le_mul_of_nonneg_left (add_le_add le_rfl hP) (by positivity)
      _ = C^m * B * (1 + (Real.log R)^m) * (2 / zetaRho β) := by ring
  have ht3 : B / zetaRho β * (Real.log R)^m
      ≤ C^m * B * (1 + (Real.log R)^m) * (1 / zetaRho β) := by
    calc B / zetaRho β * (Real.log R)^m ≤ B / zetaRho β * (1 + (Real.log R)^m) :=
          mul_le_mul_of_nonneg_left hL (by positivity)
      _ ≤ C^m * (B / zetaRho β * (1 + (Real.log R)^m)) := by
          refine le_mul_of_one_le_left ?_ hCm
          positivity
      _ = C^m * B * (1 + (Real.log R)^m) * (1 / zetaRho β) := by ring
  have ht4 : 2 * C^m * B * (1 + (Real.log R)^m) * K
      = C^m * B * (1 + (Real.log R)^m) * (2 * K) := by ring
  have hkey : 2 * C^m * B * (1 + (Real.log R)^m) + C^m * B * (1 + (Real.log R)^m) * (2 / zetaRho β)
        + C^m * B * (1 + (Real.log R)^m) * (1 / zetaRho β)
        + C^m * B * (1 + (Real.log R)^m) * (2 * K)
      = C^m * B * (1 + (Real.log R)^m) * (2 + 3 / zetaRho β + 2 * K) := by ring
  refine le_trans (le_trans (add_le_add (add_le_add (add_le_add ht1 ht2) ht3) (le_of_eq ht4)) ?_)
    (le_trans (le_of_eq hkey) ?_)
  · exact le_of_eq (by ring)
  · calc C^m * B * (1 + (Real.log R)^m) * (2 + 3 / zetaRho β + 2 * K)
        ≤ C^m * B * (1 + (Real.log R)^m) * C :=
          mul_le_mul_of_nonneg_left hCC (by positivity)
      _ = C^(m+1) * B * (1 + (Real.log R)^m) := hmul

/-! ## The `m = 1` base case -/

lemma zetaMmf_one_eq {R : ℝ} (F : (Fin 1 → ℂ) → (Fin 1 → ℂ) → ℂ) :
    zetaMmf R 1 F = zetaMf1 R (fun u v => F (fun _ => u) (fun _ => v)) := by
  rw [zetaMmf, zetaMf1, Nat.mul_one]
  congr 1
  rw [Commons.Analysis.Measure.integral_fin_one]
  congr 1 with s
  rw [Commons.Analysis.Measure.integral_fin_one]
  congr 1 with s'
  rw [Fin.prod_univ_one]

lemma zetaMmf_base {β R : ℝ} (D : ZetaAux β) (hβ : 0 < β) (hβ10 : β ≤ 1 / 10)
    (hR : 3 ≤ R) (C : ℝ) (hC1 : 1 ≤ C)
    (hCbig : 2 + 3 / zetaRho β + 2 * (2 * Real.pi)⁻¹ * (2 * K1c β + D.Cq)
        + 2 * (2 * Real.pi)⁻¹ ^ 2 * K2c D ≤ C)
    (F : (Fin 1 → ℂ) → (Fin 1 → ℂ) → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hF : ZetaAdm β 1 F B) :
    ‖zetaMmf R 1 F - F 0 0 * (Real.log R)^1‖ ≤ C^1 * B * (1 + (Real.log R)^(1-1)) := by
  have hRone : (1:ℝ) ≤ R := by linarith
  have hρpos : 0 < zetaRho β := zetaRho_pos hβ
  have hlogR0 : 0 ≤ Real.log R := Real.log_nonneg hRone
  rw [zetaMmf_one_eq (R := R) F]
  have hupd : ∀ z u : ℂ, Function.update (fun _ : Fin 1 => z) 0 u = fun _ : Fin 1 => u := by
    intro z u
    funext i
    have hi : i = 0 := by omega
    rw [hi, Function.update_self]
  have hbnd : ∀ z z' : ℂ, ZetaReg β z → ZetaReg β z' →
      ‖(fun u v => F (fun _ => u) (fun _ => v)) z z'‖ ≤ B := by
    intro z z' hz hz'
    exact hF.2.2.2 _ _ (fun i => hz) (fun i => hz')
  have hd1 : ∀ z z' : ℂ, ZetaReg β z → ZetaReg β z' →
      DifferentiableAt ℂ (fun u : ℂ => (fun u v => F (fun _ => u) (fun _ => v)) u z') z := by
    intro z z' hz hz'
    have h := hF.2.1 0 (fun _ : Fin 1 => z) (fun _ : Fin 1 => z') (fun i => hz) (fun i => hz')
    have heq : (fun u : ℂ => F (Function.update (fun _ : Fin 1 => z) 0 u) (fun _ : Fin 1 => z'))
        = fun u : ℂ => F (fun _ : Fin 1 => u) (fun _ : Fin 1 => z') := by
      funext u; rw [hupd]
    rwa [heq] at h
  have hd2 : ∀ z z' : ℂ, ZetaReg β z → ZetaReg β z' →
      DifferentiableAt ℂ (fun u : ℂ => (fun u v => F (fun _ => u) (fun _ => v)) z u) z' := by
    intro z z' hz hz'
    have h := hF.2.2.1 0 (fun _ : Fin 1 => z) (fun _ : Fin 1 => z') (fun i => hz) (fun i => hz')
    have heq : (fun u : ℂ => F (fun _ : Fin 1 => z) (Function.update (fun _ : Fin 1 => z') 0 u))
        = fun u : ℂ => F (fun _ : Fin 1 => z) (fun _ : Fin 1 => u) := by
      funext u; rw [hupd]
    rwa [heq] at h
  have hcont : Continuous (Function.uncurry (fun u v : ℂ => F (fun _ : Fin 1 => u)
      (fun _ : Fin 1 => v))) := by
    change Continuous (fun p : ℂ × ℂ => F (fun _ : Fin 1 => p.1) (fun _ : Fin 1 => p.2))
    have h1 : Continuous (fun p : ℂ × ℂ => (fun _ : Fin 1 => p.1)) :=
      continuous_pi (fun i => continuous_fst)
    have h2 : Continuous (fun p : ℂ × ℂ => (fun _ : Fin 1 => p.2)) :=
      continuous_pi (fun i => continuous_snd)
    exact hF.1.comp (h1.prodMk h2)
  have hsharp := zetaMf1_sharp hβ hβ10 hR (fun u v : ℂ => F (fun _ : Fin 1 => u)
      (fun _ : Fin 1 => v)) B D.C₁ D.Cs D.Cn D.Ku D.Cq D.hC₁pos D.hCspos D.hCnpos D.hKupos
    D.hreg D.hCs D.hCn hd1 hd2 hcont hbnd hB D.hnum D.hUint D.hUle D.hQint D.hQle
  have hder : ‖deriv (fun w : ℂ => (fun u v : ℂ => F (fun _ : Fin 1 => u) (fun _ : Fin 1 => v))
      0 w) 0‖ ≤ B / zetaRho β := by
    refine deriv_bound_ZetaReg hβ hβ10 _ B hB ?_ ?_
    · intro z hz
      have h := hF.2.2.1 0 (fun _ : Fin 1 => (0:ℂ)) (fun _ : Fin 1 => z)
        (fun i => zetaReg_zero hβ) (fun i => hz)
      have heq : (fun u : ℂ => F (fun _ : Fin 1 => (0:ℂ))
            (Function.update (fun _ : Fin 1 => z) 0 u))
          = fun u : ℂ => F (fun _ : Fin 1 => (0:ℂ)) (fun _ : Fin 1 => u) := by
        funext u; rw [hupd]
      rwa [heq] at h
    · intro z hz
      exact hF.2.2.2 _ _ (fun i => zetaReg_zero hβ) (fun i => hz)
  have hCsh : (2 * Real.pi)⁻¹ * (2 * (curveConst β * ∫ t : ℝ, (1 + t ^ 2)⁻¹) + D.Cq)
      + (2 * Real.pi)⁻¹ ^ 2 * (D.Cn * D.C₁ * D.C₁ * curveConst β ^ 2 * D.Ku ^ 2)
      + 1 / zetaRho β ≤ C := by
    have hp1 : 0 ≤ (2 * Real.pi)⁻¹ := by positivity
    have hp2 : 0 ≤ (2 * Real.pi)⁻¹ ^ 2 := by positivity
    have h1 : (2 * Real.pi)⁻¹ * (2 * K1c β + D.Cq)
        ≤ 2 * (2 * Real.pi)⁻¹ * (2 * K1c β + D.Cq) := by
      nlinarith [hp1, K1c_nonneg β hβ, D.hCqpos.le]
    have h2 : (2 * Real.pi)⁻¹ ^ 2 * K2c D ≤ 2 * (2 * Real.pi)⁻¹ ^ 2 * K2c D := by
      nlinarith [hp2, K2c_nonneg D hβ]
    have h3 : 1 / zetaRho β ≤ 3 / zetaRho β := by
      rw [div_le_div_iff_of_pos_right hρpos]; norm_num
    have h4 : (2 * Real.pi)⁻¹ * (2 * (curveConst β * ∫ t : ℝ, (1 + t ^ 2)⁻¹) + D.Cq)
        = (2 * Real.pi)⁻¹ * (2 * K1c β + D.Cq) := by rw [K1c]
    have h5 : (2 * Real.pi)⁻¹ ^ 2 * (D.Cn * D.C₁ * D.C₁ * curveConst β ^ 2 * D.Ku ^ 2)
        = (2 * Real.pi)⁻¹ ^ 2 * K2c D := by rw [K2c]
    rw [h4, h5]
    linarith [hCbig, h1, h2, h3]
  have hCsh2 : (2 * Real.pi)⁻¹ * (2 * (curveConst β * ∫ t : ℝ, (1 + t ^ 2)⁻¹) + D.Cq)
      + (2 * Real.pi)⁻¹ ^ 2 * (D.Cn * D.C₁ * D.C₁ * curveConst β ^ 2 * D.Ku ^ 2)
      + 1 / zetaRho β = ((2 * Real.pi)⁻¹ * (2 * (curveConst β * ∫ t : ℝ, (1 + t ^ 2)⁻¹) + D.Cq)
      + (2 * Real.pi)⁻¹ ^ 2 * (D.Cn * D.C₁ * D.C₁ * curveConst β ^ 2 * D.Ku ^ 2)
      + 1 / zetaRho β) := rfl
  have hf00 : (fun u v : ℂ => F (fun _ : Fin 1 => u) (fun _ : Fin 1 => v)) 0 0 = F 0 0 := rfl
  have hsum : ‖zetaMf1 R (fun u v : ℂ => F (fun _ : Fin 1 => u) (fun _ : Fin 1 => v))
        - ((fun u v : ℂ => F (fun _ : Fin 1 => u) (fun _ : Fin 1 => v)) 0 0 * Real.log R
            + deriv (fun w : ℂ => (fun u v : ℂ => F (fun _ : Fin 1 => u) (fun _ : Fin 1 => v)) 0 w) 0)‖
      + ‖deriv (fun w : ℂ => (fun u v : ℂ => F (fun _ : Fin 1 => u) (fun _ : Fin 1 => v)) 0 w) 0‖
      ≤ 2 * C * B := by
    have hρC : 1 / zetaRho β ≤ C := by
      have h0a : 0 ≤ (2 * Real.pi)⁻¹ * (2 * (curveConst β * ∫ t : ℝ, (1 + t ^ 2)⁻¹) + D.Cq) := by
        have hh : 0 ≤ 2 * (curveConst β * ∫ t : ℝ, (1 + t ^ 2)⁻¹) + D.Cq := by
          have := K1c_nonneg β hβ
          rw [K1c] at this
          linarith [D.hCqpos.le]
        exact mul_nonneg (by positivity) hh
      have h0b : 0 ≤ (2 * Real.pi)⁻¹ ^ 2 * (D.Cn * D.C₁ * D.C₁ * curveConst β ^ 2 * D.Ku ^ 2) := by
        have := K2c_nonneg D hβ
        rw [K2c] at this
        exact mul_nonneg (by positivity) this
      linarith [hCsh, h0a, h0b]
    have h1 : ‖zetaMf1 R (fun u v : ℂ => F (fun _ : Fin 1 => u) (fun _ : Fin 1 => v))
          - ((fun u v : ℂ => F (fun _ : Fin 1 => u) (fun _ : Fin 1 => v)) 0 0 * Real.log R
              + deriv (fun w : ℂ =>
                  (fun u v : ℂ => F (fun _ : Fin 1 => u) (fun _ : Fin 1 => v)) 0 w) 0)‖ ≤ C * B :=
      le_trans hsharp (mul_le_mul_of_nonneg_right hCsh hB)
    have h2 : ‖deriv (fun w : ℂ => (fun u v : ℂ =>
          F (fun _ : Fin 1 => u) (fun _ : Fin 1 => v)) 0 w) 0‖ ≤ C * B := by
      calc ‖deriv (fun w : ℂ => (fun u v : ℂ =>
            F (fun _ : Fin 1 => u) (fun _ : Fin 1 => v)) 0 w) 0‖ ≤ B / zetaRho β := hder
        _ = (1 / zetaRho β) * B := by ring
        _ ≤ C * B := mul_le_mul_of_nonneg_right hρC hB
    linarith [h1, h2]
  calc ‖zetaMf1 R (fun u v : ℂ => F (fun _ : Fin 1 => u) (fun _ : Fin 1 => v))
        - F 0 0 * (Real.log R)^1‖
      = ‖zetaMf1 R (fun u v : ℂ => F (fun _ : Fin 1 => u) (fun _ : Fin 1 => v))
          - (fun u v : ℂ => F (fun _ : Fin 1 => u) (fun _ : Fin 1 => v)) 0 0 * Real.log R‖ := by
        rw [pow_one, hf00]
    _ ≤ ‖zetaMf1 R (fun u v : ℂ => F (fun _ : Fin 1 => u) (fun _ : Fin 1 => v))
          - ((fun u v : ℂ => F (fun _ : Fin 1 => u) (fun _ : Fin 1 => v)) 0 0 * Real.log R
              + deriv (fun w : ℂ =>
                  (fun u v : ℂ => F (fun _ : Fin 1 => u) (fun _ : Fin 1 => v)) 0 w) 0)‖
        + ‖deriv (fun w : ℂ =>
            (fun u v : ℂ => F (fun _ : Fin 1 => u) (fun _ : Fin 1 => v)) 0 w) 0‖ := by
        have h := norm_add_le
          (zetaMf1 R (fun u v : ℂ => F (fun _ : Fin 1 => u) (fun _ : Fin 1 => v))
            - ((fun u v : ℂ => F (fun _ : Fin 1 => u) (fun _ : Fin 1 => v)) 0 0 * Real.log R
                + deriv (fun w : ℂ =>
                    (fun u v : ℂ => F (fun _ : Fin 1 => u) (fun _ : Fin 1 => v)) 0 w) 0))
          (deriv (fun w : ℂ =>
            (fun u v : ℂ => F (fun _ : Fin 1 => u) (fun _ : Fin 1 => v)) 0 w) 0)
        have he : zetaMf1 R (fun u v : ℂ => F (fun _ : Fin 1 => u) (fun _ : Fin 1 => v))
              - ((fun u v : ℂ => F (fun _ : Fin 1 => u) (fun _ : Fin 1 => v)) 0 0 * Real.log R
                  + deriv (fun w : ℂ =>
                      (fun u v : ℂ => F (fun _ : Fin 1 => u) (fun _ : Fin 1 => v)) 0 w) 0)
              + deriv (fun w : ℂ =>
                  (fun u v : ℂ => F (fun _ : Fin 1 => u) (fun _ : Fin 1 => v)) 0 w) 0
            = zetaMf1 R (fun u v : ℂ => F (fun _ : Fin 1 => u) (fun _ : Fin 1 => v))
              - (fun u v : ℂ => F (fun _ : Fin 1 => u) (fun _ : Fin 1 => v)) 0 0 * Real.log R := by
          ring
        rwa [he] at h
    _ ≤ 2 * C * B := hsum
    _ = C^1 * B * (1 + (Real.log R)^(1-1)) := by
        rw [pow_one, show (1:ℕ) - 1 = 0 by norm_num, pow_zero]
        ring

/-- The `m`-fold bound, by induction on `m`. -/
theorem zetaMmf_bound {β : ℝ} (D : ZetaAux β) (hβ : 0 < β) (hβ10 : β ≤ 1 / 10) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ R : ℝ, 3 ≤ R → ∀ (m : ℕ), 1 ≤ m →
      ∀ (F : (Fin m → ℂ) → (Fin m → ℂ) → ℂ) (B : ℝ), 0 ≤ B → ZetaAdm β m F B →
      ‖zetaMmf R m F - F 0 0 * (Real.log R)^m‖
        ≤ C^m * B * (1 + (Real.log R)^(m-1)) := by
  have hp1 : 0 ≤ (2 * Real.pi)⁻¹ :=
    le_of_lt (inv_pos.mpr (mul_pos (by norm_num) Real.pi_pos))
  have h1 : 0 ≤ (2 * Real.pi)⁻¹ * (2 * K1c β + D.Cq) :=
    mul_nonneg hp1 (by linarith [K1c_nonneg β hβ, D.hCqpos.le])
  have h2 : 0 ≤ (2 * Real.pi)⁻¹ ^ 2 * K2c D :=
    mul_nonneg (pow_nonneg hp1 2) (K2c_nonneg D hβ)
  have h3 : 0 ≤ 3 / zetaRho β :=
    div_nonneg (by norm_num) (zetaRho_pos hβ).le
  have hmn : 0 ≤ 2 + 3 / zetaRho β + 2 * (2 * Real.pi)⁻¹ * (2 * K1c β + D.Cq)
      + 2 * (2 * Real.pi)⁻¹ ^ 2 * K2c D := by linarith
  refine ⟨1 + (2 + 3 / zetaRho β + 2 * (2 * Real.pi)⁻¹ * (2 * K1c β + D.Cq)
      + 2 * (2 * Real.pi)⁻¹ ^ 2 * K2c D), ?_, ?_⟩
  · linarith
  · intro R hR m hm
    refine Nat.le_induction (m := 1)
      (P := fun n (_ : 1 ≤ n) => ∀ (F : (Fin n → ℂ) → (Fin n → ℂ) → ℂ) (B : ℝ), 0 ≤ B →
        ZetaAdm β n F B →
        ‖zetaMmf R n F - F 0 0 * (Real.log R)^n‖
          ≤ (1 + (2 + 3 / zetaRho β + 2 * (2 * Real.pi)⁻¹ * (2 * K1c β + D.Cq)
              + 2 * (2 * Real.pi)⁻¹ ^ 2 * K2c D))^n * B * (1 + (Real.log R)^(n-1)))
      ?_ ?_ m hm
    · intro F B hB hF
      exact zetaMmf_base D hβ hβ10 hR
        (1 + (2 + 3 / zetaRho β + 2 * (2 * Real.pi)⁻¹ * (2 * K1c β + D.Cq)
          + 2 * (2 * Real.pi)⁻¹ ^ 2 * K2c D)) (by linarith)
        (by linarith [hmn]) F B hB hF
    · intro n hn IH F B hB hF
      exact zetaMmf_step_bound D hβ hβ10 hR hn
        (1 + (2 + 3 / zetaRho β + 2 * (2 * Real.pi)⁻¹ * (2 * K1c β + D.Cq)
          + 2 * (2 * Real.pi)⁻¹ ^ 2 * K2c D)) (by linarith)
        (by linarith [hmn]) F B hB hF IH

end SplitIntegrability


theorem zeta_bound_m_v2 :
    ∃ β δ C : ℝ, 0 < β ∧ β ≤ 1 / 10 ∧ 0 < δ ∧ 0 < C ∧
      ∀ R : ℝ, 3 ≤ R → ∀ (m : ℕ), 1 ≤ m →
      ∀ F : (Fin m → ℂ) → (Fin m → ℂ) → ℂ, ∀ B : ℝ, 0 ≤ B →
      Continuous (Function.uncurry F) →
      (∀ (j : Fin m) (z z' : Fin m → ℂ),
        (∀ i, -(β / Real.log (|(z i).im| + 2)) ≤ (z i).re ∧ (z i).re ≤ 1) →
        (∀ i, -(β / Real.log (|(z' i).im| + 2)) ≤ (z' i).re ∧ (z' i).re ≤ 1) →
        DifferentiableAt ℂ (fun u : ℂ => F (Function.update z j u) z') (z j)) →
      (∀ (j : Fin m) (z z' : Fin m → ℂ),
        (∀ i, -(β / Real.log (|(z i).im| + 2)) ≤ (z i).re ∧ (z i).re ≤ 1) →
        (∀ i, -(β / Real.log (|(z' i).im| + 2)) ≤ (z' i).re ∧ (z' i).re ≤ 1) →
        DifferentiableAt ℂ (fun u : ℂ => F z (Function.update z' j u)) (z' j)) →
      (∀ z z' : Fin m → ℂ,
        (∀ i, -(β / Real.log (|(z i).im| + 2)) ≤ (z i).re ∧ (z i).re ≤ 1) →
        (∀ i, -(β / Real.log (|(z' i).im| + 2)) ≤ (z' i).re ∧ (z' i).re ≤ 1) →
        ‖F z z'‖ ≤ B) →
      ‖((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ (2 * m) *
          (∫ t : Fin m → ℝ, ∫ t' : Fin m → ℝ,
            F (fun j => Commons.NumberTheory.Zeta.zetaM1Eta R (t j))
              (fun j => Commons.NumberTheory.Zeta.zetaM1Eta R (t' j))
            * (∏ j, (riemannZeta (1 + Commons.NumberTheory.Zeta.zetaM1Eta R (t j)
                    + Commons.NumberTheory.Zeta.zetaM1Eta R (t' j))
                  / (riemannZeta (1 + Commons.NumberTheory.Zeta.zetaM1Eta R (t j))
                      * riemannZeta (1 + Commons.NumberTheory.Zeta.zetaM1Eta R (t' j)))))
            * (R : ℂ) ^ (∑ j, (Commons.NumberTheory.Zeta.zetaM1Eta R (t j)
                + Commons.NumberTheory.Zeta.zetaM1Eta R (t' j)))
            * (∏ j, ((Commons.NumberTheory.Zeta.zetaM1Eta R (t j)) ^ 2
                  * (Commons.NumberTheory.Zeta.zetaM1Eta R (t' j)) ^ 2)⁻¹)
            * Complex.I ^ m * Complex.I ^ m)
        - F 0 0 * (Real.log R) ^ m‖
        ≤ C ^ m * B * (1 + (Real.log R) ^ (m - 1))
          + C ^ m * B * Real.exp (-(δ * Real.sqrt (Real.log R))) := by
  obtain ⟨β₀, D, hβ₀pos, hβ₀10⟩ := zetaAux_exists
  obtain ⟨C, hC1, hmain⟩ := zetaMmf_bound D hβ₀pos hβ₀10
  refine ⟨β₀, 1, C, hβ₀pos, hβ₀10, one_pos, lt_of_lt_of_le one_pos hC1, ?_⟩
  intro R hR m hm F B hB hcont hd1 hd2 hbound
  have hRne : (R : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (by linarith : (0:ℝ) < R))
  have hF : ZetaAdm β₀ m F B := ⟨hcont, hd1, hd2, hbound⟩
  have hb := hmain R hR m hm F B hB hF
  rw [← zetaMmf_eq_explicit hRne m F]
  have hpos : 0 ≤ C ^ m * B * Real.exp (-(1 * Real.sqrt (Real.log R))) :=
    mul_nonneg (mul_nonneg (pow_nonneg (le_of_lt (lt_of_lt_of_le one_pos hC1)) m) hB)
      (Real.exp_pos _).le
  exact le_trans hb (le_add_of_nonneg_right hpos)


end

end Commons.NumberTheory.Zeta

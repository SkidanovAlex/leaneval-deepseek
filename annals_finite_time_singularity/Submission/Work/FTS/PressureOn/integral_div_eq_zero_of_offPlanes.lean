import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.PhiStar.Honesty.rgG2_sq_div_z4_Ioo
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.PressureOn.Auxiliary.integral_mul_div_eq_neg_inner_gradient
import Submission.Work.FTS.PressureOn.Green.integral_mul_laplaceTrace_comm
import Submission.Work.FTS.PressureOn.integral_div_eq_zero_of_hasFDerivAt
import Submission.Work.FTS.PressureOn.omegaSliceRegularPos
import Submission.Work.FTS.PressureOn.weakCurl.int2_integrable
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.conv_shift_sq_integral_le
import Submission.Work.FTS_MuLamOK.Rows.rl0_final
import Submission.Work.FTS_RegExport.RXT.SysAux.explicit_piece_bounds
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS.BSSwirl.integral_inv_norm_mul_laplacian =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter Topology
open scoped Topology NNReal ENNReal InnerProductSpace

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FTS.BSSwirl

noncomputable section

/-- The `i`-th vector of the standard basis of `ℝ³`. -/
abbrev eb (i : Fin 3) : R3 := EuclideanSpace.single i (1 : ℝ)

/-! ## The Laplacian in the standard basis -/

/-- Mathlib's Laplacian is the sum of the pure second derivatives in the standard basis. -/
theorem laplacian_eq_sum_single {ψ : R3 → ℝ} (hψ : ContDiff ℝ 2 ψ) (z : R3) :
    Laplacian.laplacian ψ z = ∑ i : Fin 3,
      (fderiv ℝ (fun y => fderiv ℝ ψ y (eb i)) z) (eb i) := by
  have hkey : ∀ (w : R3) (i : Fin 3),
      fderiv ℝ (fun y => fderiv ℝ ψ y (eb i)) w
        = (fderiv ℝ (fderiv ℝ ψ) w).flip (eb i) := by
    intro w i
    have h : DifferentiableAt ℝ (fderiv ℝ ψ) w :=
      (hψ.fderiv_right (m := 1) (by norm_num)).contDiffAt.differentiableAt (by norm_num)
    have h2 := fderiv_clm_apply (𝕜 := ℝ) (c := fderiv ℝ ψ)
      (u := fun _ : R3 => eb i) h (differentiableAt_const _)
    simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add] at h2
    exact h2
  have hlap : Laplacian.laplacian ψ = fun w => ∑ i : Fin 3,
      (fderiv ℝ (fun y => fderiv ℝ ψ y (eb i)) w) (eb i) := by
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis ψ
      (EuclideanSpace.basisFun (Fin 3) ℝ)]
    funext w
    apply Finset.sum_congr rfl
    intro i _
    rw [EuclideanSpace.basisFun_apply, iteratedFDeriv_two_apply, hkey w i]
    rfl
  rw [hlap]

/-! ## Support of derivatives of a compactly supported function -/

/-- The support of the derivative of `f` in a direction is contained in the (closed) support
of `f`. -/
theorem support_fderiv_apply_subset_tsupport {f : R3 → ℝ} (v : R3) :
    Function.support (fun z => fderiv ℝ f z v) ⊆ tsupport f := by
  intro z hz
  by_contra hzc
  rw [notMem_tsupport_iff_eventuallyEq] at hzc
  refine (Function.mem_support.mp hz) ?_
  rw [hzc.fderiv_eq]
  simp

/-- The support of the second derivative of `f` is contained in the (closed) support of `f`. -/
theorem support_fderiv_fderiv_apply_subset_tsupport {f : R3 → ℝ} (v w : R3) :
    Function.support (fun z => fderiv ℝ (fun y => fderiv ℝ f y v) z w) ⊆ tsupport f :=
  subset_trans (support_fderiv_apply_subset_tsupport w)
    (closure_minimal (support_fderiv_apply_subset_tsupport v) (isClosed_tsupport f))

/-- Integrability of a continuous function whose support is contained in the support of a
compactly supported function. -/
theorem integrable_of_support_subset_tsupport {F : R3 → ℝ} (hF : Continuous F)
    {f : R3 → ℝ} (hf : HasCompactSupport f) (hsub : Function.support F ⊆ tsupport f) :
    Integrable F :=
  hF.integrable_of_hasCompactSupport (HasCompactSupport.of_support_subset_isCompact hf hsub)

/-! ## Integration by parts against the Laplacian -/

/-- **Integration by parts against the Laplacian.**  For `C¹` `φ` and `C²` `ψ` for which the
relevant products are integrable, `∫ φ Δψ = -∑ᵢ ∫ (∂ᵢφ)(∂ᵢψ)`. -/
theorem laplacian_ibp_of_integrable {φ ψ : R3 → ℝ} (hφ : ContDiff ℝ 1 φ) (hψ : ContDiff ℝ 2 ψ)
    (h1 : ∀ i : Fin 3, Integrable (fun z => (fderiv ℝ φ z (eb i)) * (fderiv ℝ ψ z (eb i))))
    (h2 : ∀ i : Fin 3, Integrable (fun z => φ z *
      (fderiv ℝ (fun y => fderiv ℝ ψ y (eb i)) z) (eb i)))
    (h3 : ∀ i : Fin 3, Integrable (fun z => φ z * (fderiv ℝ ψ z (eb i)))) :
    ∫ z, φ z * Laplacian.laplacian ψ z
      = -∑ i : Fin 3, ∫ z, (fderiv ℝ φ z (eb i)) * (fderiv ℝ ψ z (eb i)) := by
  have hdiffφ : ∀ z : R3, DifferentiableAt ℝ φ z := fun z => hφ.differentiable (by norm_num) z
  have hdiffg : ∀ (i : Fin 3) (z : R3),
      DifferentiableAt ℝ (fun y => fderiv ℝ ψ y (eb i)) z := by
    intro i z
    have h : DifferentiableAt ℝ (fderiv ℝ ψ) z :=
      (hψ.fderiv_right (m := 1) (by norm_num)).contDiffAt.differentiableAt (by norm_num)
    exact (h.clm_apply (differentiableAt_const _))
  calc ∫ z, φ z * Laplacian.laplacian ψ z
      = ∫ z, φ z * ∑ i : Fin 3,
          (fderiv ℝ (fun y => fderiv ℝ ψ y (eb i)) z) (eb i) := by
        simp_rw [laplacian_eq_sum_single hψ]
    _ = ∫ z, ∑ i : Fin 3,
          φ z * ((fderiv ℝ (fun y => fderiv ℝ ψ y (eb i)) z) (eb i)) := by
        simp_rw [Finset.mul_sum]
    _ = ∑ i : Fin 3, ∫ z,
          φ z * ((fderiv ℝ (fun y => fderiv ℝ ψ y (eb i)) z) (eb i)) := by
        rw [integral_finset_sum]
        intro i _
        exact h2 i
    _ = ∑ i : Fin 3, -∫ z, (fderiv ℝ φ z (eb i)) * (fderiv ℝ ψ z (eb i)) := by
        apply Finset.sum_congr rfl
        intro i _
        exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (h1 i) (h2 i) (h3 i)
          (fun x _ => hdiffφ x) (fun x _ => hdiffg i x)
    _ = -∑ i : Fin 3, ∫ z, (fderiv ℝ φ z (eb i)) * (fderiv ℝ ψ z (eb i)) := by
        rw [Finset.sum_neg_distrib]

/-- Integration by parts against the Laplacian, when `ψ` is compactly supported. -/
theorem laplacian_ibp_of_cs_right {φ ψ : R3 → ℝ} (hφ : ContDiff ℝ 1 φ) (hψ : ContDiff ℝ 2 ψ)
    (hcψ : HasCompactSupport ψ) :
    ∫ z, φ z * Laplacian.laplacian ψ z
      = -∑ i : Fin 3, ∫ z, (fderiv ℝ φ z (eb i)) * (fderiv ℝ ψ z (eb i)) := by
  refine laplacian_ibp_of_integrable hφ hψ (fun i => ?_) (fun i => ?_) (fun i => ?_)
  · refine integrable_of_support_subset_tsupport ?_ hcψ ?_
    · exact ((hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const).mul
        ((hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const)
    · intro z hz
      exact support_fderiv_apply_subset_tsupport (eb i) (Function.support_mul_subset_right _ _ hz)
  · refine integrable_of_support_subset_tsupport ?_ hcψ ?_
    · exact hφ.continuous.mul
        (((hψ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).continuous_fderiv
          (by norm_num) |>.clm_apply continuous_const)
    · intro z hz
      exact support_fderiv_fderiv_apply_subset_tsupport (eb i) (eb i)
        (Function.support_mul_subset_right _ _ hz)
  · refine integrable_of_support_subset_tsupport ?_ hcψ ?_
    · exact hφ.continuous.mul ((hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const)
    · intro z hz
      exact support_fderiv_apply_subset_tsupport (eb i) (Function.support_mul_subset_right _ _ hz)

/-- Integration by parts against the Laplacian, when `φ` is compactly supported. -/
theorem laplacian_ibp_of_cs_left {φ ψ : R3 → ℝ} (hφ : ContDiff ℝ 1 φ) (hψ : ContDiff ℝ 2 ψ)
    (hcφ : HasCompactSupport φ) :
    ∫ z, φ z * Laplacian.laplacian ψ z
      = -∑ i : Fin 3, ∫ z, (fderiv ℝ φ z (eb i)) * (fderiv ℝ ψ z (eb i)) := by
  refine laplacian_ibp_of_integrable hφ hψ (fun i => ?_) (fun i => ?_) (fun i => ?_)
  · refine integrable_of_support_subset_tsupport ?_ hcφ ?_
    · exact ((hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const).mul
        ((hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const)
    · intro z hz
      exact support_fderiv_apply_subset_tsupport (eb i) (Function.support_mul_subset_left _ _ hz)
  · refine integrable_of_support_subset_tsupport ?_ hcφ ?_
    · exact hφ.continuous.mul
        (((hψ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).continuous_fderiv
          (by norm_num) |>.clm_apply continuous_const)
    · intro z hz
      exact subset_tsupport _ (Function.support_mul_subset_left _ _ hz)
  · refine integrable_of_support_subset_tsupport ?_ hcφ ?_
    · exact hφ.continuous.mul ((hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const)
    · intro z hz
      exact subset_tsupport _ (Function.support_mul_subset_left _ _ hz)

/-- **Self-adjointness of the Laplacian**: `∫ φ Δψ = ∫ ψ Δφ` for smooth `φ`, `ψ` one of which is
compactly supported. -/
theorem laplacian_pairing_comm {φ ψ : R3 → ℝ} (hφ : ContDiff ℝ 2 φ) (hψ : ContDiff ℝ 2 ψ)
    (hcψ : HasCompactSupport ψ) :
    ∫ z, φ z * Laplacian.laplacian ψ z = ∫ z, ψ z * Laplacian.laplacian φ z := by
  rw [laplacian_ibp_of_cs_right (hφ := hφ.of_le (by norm_num)) hψ hcψ,
    laplacian_ibp_of_cs_left (hφ := hψ.of_le (by norm_num)) hφ hcψ]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  funext z
  ring

/-! ## The cutoff family `φ_ε` -/

/-- `φ_ε z = fcut (‖z‖/ε) / ‖z‖`: a smooth function equal to `‖z‖⁻¹` outside the ball of radius
`2ε` and to `0` inside the ball of radius `ε`. -/
def phiCut (ε : ℝ) (z : R3) : ℝ := fcut (‖z‖ / ε) / ‖z‖

lemma phiCut_eq_zero_of_norm_le {ε : ℝ} (hε : 0 < ε) {z : R3} (hz : ‖z‖ ≤ ε) :
    phiCut ε z = 0 := by
  have h : ‖z‖ / ε ≤ 1 := by rw [div_le_one hε]; exact hz
  simp [phiCut, fcut_of_le_one h]


lemma contDiff_phiCut (ε : ℝ) : ContDiff ℝ 2 (phiCut ε) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  rcases le_or_gt ε 0 with hε | hε
  · have hzero : phiCut ε = fun _ : R3 => (0 : ℝ) := by
      funext y
      rw [phiCut]
      have h1 : fcut (‖y‖ / ε) = 0 := by
        refine fcut_of_le_one ?_
        rcases lt_or_eq_of_le hε with h | h
        · exact le_trans (div_nonpos_of_nonneg_of_nonpos (norm_nonneg y) h.le) (by norm_num)
        · simp [h]
      rw [h1, zero_div]
    rw [hzero]
    exact contDiffAt_const
  · rcases eq_or_ne z 0 with rfl | hz
    · refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [Metric.ball_mem_nhds (0 : R3) hε] with y hy
      rw [Metric.mem_ball, dist_zero_right] at hy
      exact phiCut_eq_zero_of_norm_le hε hy.le
    · have h1 : ContDiffAt ℝ 2 (fun y : R3 => fcut (‖y‖ / ε)) z := by
        change ContDiffAt ℝ 2 (fun y : R3 => Real.smoothTransition (‖y‖ / ε - 1)) z
        have hinner : ContDiffAt ℝ 2 (fun y : R3 => ‖y‖ / ε - 1) z :=
          ContDiffAt.sub (ContDiffAt.div_const (contDiffAt_norm ℝ (n := 2) hz) ε) contDiffAt_const
        exact (Real.smoothTransition.contDiffAt (n := (2 : ℕ∞))
          (x := ‖z‖ / ε - 1)).comp z hinner
      have h2 : ContDiffAt ℝ 2 (fun y : R3 => (‖y‖)⁻¹) z :=
        (contDiffAt_norm ℝ (n := 2) hz).inv (by simpa using norm_ne_zero_iff.mpr hz)
      have h3 : ContDiffAt ℝ 2 (fun y : R3 => fcut (‖y‖ / ε) * (‖y‖)⁻¹) z := h1.mul h2
      refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
      rw [phiCut, div_eq_mul_inv]

/-! ## The substitution `z = ε w` -/

/-- The substitution `z = ε w` in the (singular) explicit form of `Δφ_ε`. -/
theorem integral_fcut_div_eq {ε : ℝ} (hε : 0 < ε) {ψ : R3 → ℝ} :
    ∫ z, ψ z * (deriv (deriv fcut) (‖z‖ / ε) / (ε ^ 2 * ‖z‖))
      = ∫ w, ψ (ε • w) * (deriv (deriv fcut) ‖w‖ / ‖w‖) := by
  set F : R3 → ℝ := fun w => ψ (ε • w) * (deriv (deriv fcut) ‖w‖ / ‖w‖) with hF
  have hsmul : ∀ z : R3, ε • (ε⁻¹ • z) = z := fun z => by
    rw [smul_smul, mul_inv_cancel₀ hε.ne', one_smul]
  have hnorm : ∀ z : R3, ‖ε⁻¹ • z‖ = ‖z‖ / ε := fun z => by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hε.le), inv_mul_eq_div]
  have hpt : ∀ z : R3, F (ε⁻¹ • z)
      = ε ^ 3 * (ψ z * (deriv (deriv fcut) (‖z‖ / ε) / (ε ^ 2 * ‖z‖))) := by
    intro z
    rcases eq_or_ne z 0 with rfl | hz
    · simp [hF]
    · have hzn : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz
      simp only [hF, hsmul z, hnorm z]
      field_simp
  have h1 : (∫ z, F (ε⁻¹ • z)) = ε ^ 3 * ∫ z, ψ z *
      (deriv (deriv fcut) (‖z‖ / ε) / (ε ^ 2 * ‖z‖)) := by
    rw [show (fun z : R3 => F (ε⁻¹ • z)) = fun z =>
        ε ^ 3 * (ψ z * (deriv (deriv fcut) (‖z‖ / ε) / (ε ^ 2 * ‖z‖))) from funext hpt]
    rw [integral_const_mul]
  have h := Measure.integral_comp_inv_smul_of_nonneg (μ := volume) (R := ε) (f := F) hε.le
  rw [finrank_euclideanSpace_fin, smul_eq_mul, h1] at h
  exact mul_left_cancel₀ (pow_ne_zero 3 hε.ne') h

/-! ## Continuity and support of the Laplacian -/

theorem continuous_laplacian {ψ : R3 → ℝ} (hψ : ContDiff ℝ 2 ψ) :
    Continuous (Laplacian.laplacian ψ) := by
  have h : Laplacian.laplacian ψ
      = fun z => ∑ i : Fin 3, (fderiv ℝ (fun y => fderiv ℝ ψ y (eb i)) z) (eb i) :=
    funext (laplacian_eq_sum_single hψ)
  rw [h]
  refine continuous_finset_sum Finset.univ fun i _ => ?_
  exact ((hψ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).continuous_fderiv
    (by norm_num) |>.clm_apply continuous_const

theorem hasCompactSupport_laplacian {ψ : R3 → ℝ} (hψ : ContDiff ℝ 2 ψ)
    (hc : HasCompactSupport ψ) : HasCompactSupport (Laplacian.laplacian ψ) := by
  have h : Laplacian.laplacian ψ
      = fun z => ∑ i : Fin 3, (fderiv ℝ (fun y => fderiv ℝ ψ y (eb i)) z) (eb i) :=
    funext (laplacian_eq_sum_single hψ)
  rw [h]
  refine HasCompactSupport.of_support_subset_isCompact (show IsCompact (tsupport ψ) from hc) ?_
  intro z hz
  by_contra hzc
  refine hz ?_
  show (∑ i : Fin 3, (fderiv ℝ (fun y => fderiv ℝ ψ y (eb i)) z) (eb i)) = 0
  refine Finset.sum_eq_zero fun i _ => ?_
  exact Function.notMem_support.mp fun hmem =>
    hzc (support_fderiv_fderiv_apply_subset_tsupport (eb i) (eb i) hmem)

/-! ## Integrability and convergence of the right-hand side -/

/-- The function `w ↦ ρ''(‖w‖)/‖w‖` is integrable (its numerator is compactly supported away from
the origin). -/
theorem integrable_deriv_deriv_fcut_div :
    Integrable (fun w : R3 => deriv (deriv fcut) ‖w‖ / ‖w‖) := by
  have hF : Continuous (deriv (deriv fcut)) := by
    have h := (contDiff_fcut 2).continuous_iteratedDeriv (m := 2) (by norm_num)
    simpa [iteratedDeriv_succ, iteratedDeriv_one] using h
  refine (MeasureTheory.integrable_fun_norm_addHaar (μ := volume)
    (f := fun y : ℝ => deriv (deriv fcut) y / y)).mpr ?_
  refine IntegrableOn.congr_fun (f := fun y : ℝ => deriv (deriv fcut) y * y) ?_ ?_
    measurableSet_Ioi
  · exact (hF.mul continuous_id).integrable_of_hasCompactSupport
      (hasCompactSupport_deriv_deriv_fcut.mul_right)
  · intro y hy
    have hy0 : y ≠ 0 := ne_of_gt hy
    simp only [smul_eq_mul, finrank_euclideanSpace_fin]
    norm_num
    field_simp

/-- **Dominated convergence** for the regularised integral: for continuous compactly supported `ψ`
and integrable `g`, `∫ w, ψ (εw) g w → ψ 0 · ∫ w, g w` as `ε → 0⁺`. -/
theorem tendsto_integral_smul_mul {ψ : R3 → ℝ} (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ)
    {g : R3 → ℝ} (hg : Integrable g) :
    Filter.Tendsto (fun ε : ℝ => ∫ w, ψ (ε • w) * g w) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (ψ 0 * ∫ w, g w)) := by
  obtain ⟨C, hC⟩ := (show IsCompact (tsupport ψ) from hcψ).exists_bound_of_continuousOn
    hψ.continuousOn
  have hbound : ∀ w : R3, ‖ψ w‖ ≤ max C 0 := fun w => by
    by_cases hw : w ∈ tsupport ψ
    · exact le_trans (hC w hw) (le_max_left _ _)
    · rw [image_eq_zero_of_notMem_tsupport hw, norm_zero]
      exact le_max_right _ _
  have hmeas : ∀ᶠ ε in nhdsWithin (0:ℝ) (Set.Ioi 0),
      AEStronglyMeasurable (fun w : R3 => ψ (ε • w) * g w) volume :=
    Filter.Eventually.of_forall fun ε =>
      ((hψ.comp ((continuous_const : Continuous (fun _ : R3 => ε)).smul
        continuous_id)).aestronglyMeasurable.mul hg.aestronglyMeasurable)
  have hdom : ∀ᶠ ε in nhdsWithin (0:ℝ) (Set.Ioi 0),
      ∀ᵐ w ∂volume, ‖ψ (ε • w) * g w‖ ≤ max C 0 * ‖g w‖ := by
    filter_upwards with ε
    filter_upwards with w
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hbound (ε • w)) (norm_nonneg _)
  have hconv : ∀ᵐ w ∂volume, Filter.Tendsto (fun ε : ℝ => ψ (ε • w) * g w)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (ψ 0 * g w)) := by
    filter_upwards with w
    have h2 : Filter.Tendsto (fun ε : ℝ => ε • w) (nhdsWithin 0 (Set.Ioi 0))
        (nhds (0 : R3)) := by
      simpa using ((tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).smul tendsto_const_nhds :
        Filter.Tendsto (fun ε : ℝ => ε • w) (nhdsWithin 0 (Set.Ioi 0)) (nhds ((0:ℝ) • w)))
    exact (hψ.continuousAt.tendsto.comp h2).mul tendsto_const_nhds
  have := tendsto_integral_filter_of_dominated_convergence (fun w : R3 => max C 0 * ‖g w‖)
    hmeas hdom (hg.norm.const_mul _) hconv
  simpa [integral_const_mul] using this

/-! ## The Laplacian of `φ_ε` and the two limits -/

theorem laplacian_phiCut (ε : ℝ) (hε : 0 < ε) (z : R3) :
    Laplacian.laplacian (phiCut ε) z
      = deriv (deriv fcut) (‖z‖ / ε) / (ε ^ 2 * ‖z‖) := by
  rcases eq_or_ne z 0 with rfl | hz
  · have hcong : phiCut ε =ᶠ[𝓝 (0 : R3)] 0 := by
      filter_upwards [Metric.ball_mem_nhds (0 : R3) hε] with y hy
      rw [Metric.mem_ball, dist_zero_right] at hy
      exact phiCut_eq_zero_of_norm_le hε hy.le
    have h0 : Laplacian.laplacian (phiCut ε) 0 = 0 := by
      rw [(InnerProductSpace.laplacian_congr_nhds hcong).eq_of_nhds]
      exact congr_fun InnerProductSpace.laplacian_const 0
    rw [h0]
    simp
  · have hr : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz
    have hg : ContDiffAt ℝ 2 (fun r : ℝ => fcut (r / ε) * r⁻¹) ‖z‖ := by
      change ContDiffAt ℝ 2 (fun r : ℝ => Real.smoothTransition (r / ε - 1) * r⁻¹) ‖z‖
      refine ContDiffAt.mul ?_ ?_
      · exact (Real.smoothTransition.contDiffAt (n := (2 : ℕ∞)) (x := ‖z‖ / ε - 1)).comp
          (‖z‖) (ContDiffAt.sub (ContDiffAt.div_const contDiffAt_id ε) contDiffAt_const)
      · have hid : ContDiffAt ℝ 2 (id : ℝ → ℝ) ‖z‖ := contDiff_id.contDiffAt
        exact hid.inv (by simpa using hr.ne')
    have hfun : phiCut ε = fun y : R3 => (fun r : ℝ => fcut (r / ε) * r⁻¹) ‖y‖ := by
      funext y
      rw [phiCut, div_eq_mul_inv]
    rw [hfun, laplacian_radial hz hg, deriv_deriv_fcut_div_add ε hε hr]

/-- The regularised `Δφ_ε` integrated against `ψ` converges to `-4π ψ 0`. -/
theorem tendsto_integral_laplacian_phiCut {ψ : R3 → ℝ} (hψ : ∀ n : ℕ, ContDiff ℝ n ψ)
    (hc : HasCompactSupport ψ) :
    Filter.Tendsto (fun ε : ℝ => ∫ z, ψ z *
        (deriv (deriv fcut) (‖z‖ / ε) / (ε ^ 2 * ‖z‖)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (-4 * Real.pi * ψ 0)) := by
  have h2 : Filter.Tendsto (fun ε : ℝ => ∫ w, ψ (ε • w) *
        (deriv (deriv fcut) ‖w‖ / ‖w‖))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (ψ 0 * ∫ w : R3, deriv (deriv fcut) ‖w‖ / ‖w‖)) :=
    tendsto_integral_smul_mul (hψ 0).continuous hc integrable_deriv_deriv_fcut_div
  have h3 : ψ 0 * ∫ w : R3, deriv (deriv fcut) ‖w‖ / ‖w‖ = -4 * Real.pi * ψ 0 := by
    rw [integral_deriv_deriv_fcut_over_norm]
    ring
  rw [h3] at h2
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (integral_fcut_div_eq (ε := ε) hε).symm

theorem integral_inv_norm_mul_laplacian {ψ : Work.FTS.BSSwirl.R3 → ℝ}
    (hψ : ∀ n : ℕ, ContDiff ℝ n ψ) (hc : HasCompactSupport ψ) :
    ∫ z, (‖z‖)⁻¹ * Laplacian.laplacian ψ z = - 4 * Real.pi * ψ 0 := by
  have hψ2 : ContDiff ℝ 2 ψ := hψ 2
  -- The two sides agree for every `ε > 0`.
  have hpair : (fun ε : ℝ => ∫ z, phiCut ε z * Laplacian.laplacian ψ z)
      =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      fun ε : ℝ => ∫ z, ψ z * (deriv (deriv fcut) (‖z‖ / ε) / (ε ^ 2 * ‖z‖)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [laplacian_pairing_comm (contDiff_phiCut ε) hψ2 hc]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    show ψ z * Laplacian.laplacian (phiCut ε) z = ψ z * (deriv (deriv fcut) (‖z‖ / ε) / (ε ^ 2 * ‖z‖))
    rw [laplacian_phiCut ε hε z]
  -- Left-hand side limit.
  have hL : Filter.Tendsto (fun ε : ℝ => ∫ z, phiCut ε z * Laplacian.laplacian ψ z)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (∫ z, (‖z‖)⁻¹ * Laplacian.laplacian ψ z)) := by
    have h := tendsto_fcut_div_mul (continuous_laplacian hψ2)
      (hasCompactSupport_laplacian hψ2 hc)
    refine h.congr' ?_
    filter_upwards with ε
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    show fcut (‖z‖ / ε) / ‖z‖ * Laplacian.laplacian ψ z
      = phiCut ε z * Laplacian.laplacian ψ z
    rw [phiCut]
  exact tendsto_nhds_unique hL (tendsto_integral_laplacian_phiCut hψ hc |>.congr' hpair.symm)

end

end Work.FTS.BSSwirl
end
-- ===== merged: Submission.Work.FTS.BSSwirl.vorticity_vorticity_eq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

set_option autoImplicit false

namespace Work.FTS.BSSwirl

noncomputable section

/-! ## Elementary identifications in the standard basis -/

/-- The standard basis vector `e i` of `ChallengeDeps` is the `i`-th vector of Mathlib's
standard orthonormal basis of `ℝ³`.  (Private: `Work.FTS.BSSwirl.laplacian_radial` already
contains a lemma of this name and statement, and the two modules must be importable together.) -/
private lemma basisFun_eq_e_prv (i : Fin 3) : EuclideanSpace.basisFun (Fin 3) ℝ i = e i := by
  rw [EuclideanSpace.basisFun_apply]
  rfl

/-- **The standard basis expansion of a vector of `ℝ³`**: `w = ∑ i, ⟪e i, w⟫ • e i`. -/
private lemma sum_inner_smul_e_eq (w : R3) : ∑ i : Fin 3, inner ℝ (e i) w • e i = w := by
  have h := (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr w
  simpa [OrthonormalBasis.repr_apply_apply, FiniteTimeSingularity.e] using h

/-- **The trace in the standard basis**: `tr L = ∑ i, ⟪e i, L (e i)⟫`. -/
private lemma trace_eq_sum_inner_e (L : R3 →L[ℝ] R3) :
    L.trace ℝ R3 = ∑ i : Fin 3, inner ℝ (e i) (L (e i)) := by
  rw [show L.trace ℝ R3 = ((L : R3 →ₗ[ℝ] R3)).trace ℝ R3 from rfl,
    LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin 3) ℝ)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [basisFun_eq_e_prv]
  rfl

/-- **The gradient in the standard basis**: `∇f x = ∑ k, ∂ₖf(x) • e k`.  (A vector `w` equals
`∑ k, ⟪e k, w⟫ • e k`, and `⟪e k, ∇f x⟫ = ∂ₖf(x)`.) -/
private lemma gradient_eq_sum_e (f : R3 → ℝ) (x : R3) :
    gradient f x = ∑ k : Fin 3, fderiv ℝ f x (e k) • e k := by
  conv_lhs => rw [← sum_inner_smul_e_eq (gradient f x)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [inner_gradient_right]
  simp

/-! ## The curl-curl identity -/

theorem vorticity_vorticity_eq {Ψ : Work.FTS.BSSwirl.R3 → Work.FTS.BSSwirl.R3}
    (hΨ : ∀ n : ℕ, ContDiff ℝ n Ψ) (x : Work.FTS.BSSwirl.R3) :
    FiniteTimeSingularity.vorticity (FiniteTimeSingularity.vorticity Ψ) x
      = gradient (FiniteTimeSingularity.div Ψ) x - Laplacian.laplacian Ψ x := by
  -- the second derivative of `Ψ` at `x` is symmetric (Clairaut)
  have hsymm : ∀ u v : R3, fderiv ℝ (fderiv ℝ Ψ) x u v = fderiv ℝ (fderiv ℝ Ψ) x v u := by
    have h : ContDiffAt ℝ 2 Ψ x := (hΨ 2).contDiffAt
    exact h.isSymmSndFDerivAt (by simp)
  -- the left-hand side, in the standard basis
  have hcurl : vorticity (vorticity Ψ) x
      = ∑ i : Fin 3, crossR3 (e i)
          (∑ j : Fin 3, crossR3 (e j) (fderiv ℝ (fderiv ℝ Ψ) x (e i) (e j))) := by
    rw [vorticity_eq_sum_crossR3]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [VortVV.fderiv_vorticity_apply Ψ hΨ x (e i)]
  -- the gradient of the divergence, in the standard basis
  have hgrad : gradient (div Ψ) x
      = ∑ k : Fin 3,
          (∑ i : Fin 3, inner ℝ (e i) (fderiv ℝ (fderiv ℝ Ψ) x (e k) (e i))) • e k := by
    rw [gradient_eq_sum_e]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [VortVV.fderiv_div_apply Ψ hΨ x (e k), trace_eq_sum_inner_e]
  -- the Laplacian, in the standard basis
  have hlap : Laplacian.laplacian Ψ x
      = ∑ k : Fin 3, fderiv ℝ (fderiv ℝ Ψ) x (e k) (e k) := VortVV.laplacian_apply_e Ψ x
  rw [hcurl, hgrad, hlap, VortVV.curl_curl_algebra (fderiv ℝ (fderiv ℝ Ψ) x) hsymm]

end

end Work.FTS.BSSwirl
end
-- ===== merged: Submission.Work.FTS.Physical.Clock.A_le_two_mul_tail =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set MeasureTheory
open scoped Topology

namespace Work.FTS.Physical.Clock

/-- **The amplitude decreases at most like `e^{-2(s-τ)}`**: `A τ e^{-2(s-τ)} ≤ A s` for
`0 ≤ τ ≤ s`.  This is the modulation bound `1 + μ ≤ 2` in integrated form. -/
theorem A_exp_two_le (C : Work.FTS.Physical.PhysClock) {τ s : ℝ} (hτ : 0 ≤ τ) (hτs : τ ≤ s) :
    C.A τ * Real.exp (-2 * (s - τ)) ≤ C.A s := by
  have hcont : ContinuousOn (fun x : ℝ => C.A x * Real.exp (2 * x)) (Set.Ici (0 : ℝ)) :=
    C.hAcont.mul (Real.continuous_exp.comp (continuous_id.const_mul 2)).continuousOn
  have hderiv : ∀ x ∈ interior (Set.Ici (0 : ℝ)),
      HasDerivWithinAt (fun x : ℝ => C.A x * Real.exp (2 * x))
        ((-(1 + C.mu x) * C.A x) * Real.exp (2 * x) + C.A x * (Real.exp (2 * x) * 2))
        (interior (Set.Ici (0 : ℝ))) x := by
    intro x hx
    have hx' : (0 : ℝ) < x := by simpa [interior_Ici] using hx
    have h1 : HasDerivAt (fun x : ℝ => C.A x) (-(1 + C.mu x) * C.A x) x := C.hAderiv x hx'.le
    have h2 : HasDerivAt (fun x : ℝ => Real.exp (2 * x)) (Real.exp (2 * x) * 2) x := by
      simpa using (((hasDerivAt_id x).const_mul 2)).exp
    exact (h1.mul h2).hasDerivWithinAt
  have hnonneg : ∀ x ∈ interior (Set.Ici (0 : ℝ)),
      0 ≤ (-(1 + C.mu x) * C.A x) * Real.exp (2 * x) + C.A x * (Real.exp (2 * x) * 2) := by
    intro x hx
    have hx' : (0 : ℝ) < x := by simpa [interior_Ici] using hx
    have hA : 0 < C.A x := C.hApos x hx'.le
    have hE : 0 < Real.exp (2 * x) := Real.exp_pos _
    have hmu : 1 + C.mu x ≤ 2 := C.hmu_hi x hx'.le
    have heq : (-(1 + C.mu x) * C.A x) * Real.exp (2 * x) + C.A x * (Real.exp (2 * x) * 2)
        = Real.exp (2 * x) * C.A x * (2 - (1 + C.mu x)) := by ring
    rw [heq]
    exact mul_nonneg (mul_nonneg hE.le hA.le) (by linarith)
  have hmono : MonotoneOn (fun x : ℝ => C.A x * Real.exp (2 * x)) (Set.Ici (0 : ℝ)) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0) hcont hderiv hnonneg
  have h1 : C.A τ * Real.exp (2 * τ) ≤ C.A s * Real.exp (2 * s) :=
    hmono hτ (le_trans hτ hτs) hτs
  have hpos : 0 < Real.exp (2 * s) := Real.exp_pos _
  have key : (C.A τ * Real.exp (-2 * (s - τ))) * Real.exp (2 * s) ≤ C.A s * Real.exp (2 * s) := by
    calc (C.A τ * Real.exp (-2 * (s - τ))) * Real.exp (2 * s)
        = C.A τ * Real.exp (2 * τ) := by
          rw [mul_assoc, ← Real.exp_add]
          congr 1
          ring_nf
      _ ≤ C.A s * Real.exp (2 * s) := h1
  exact (mul_le_mul_iff_left₀ hpos).mp key

/-- `s ↦ e^{-2(s-τ)}` is integrable on `[τ,∞)`. -/
theorem integrableOn_exp_two_shift (τ : ℝ) :
    IntegrableOn (fun s : ℝ => Real.exp (-2 * (s - τ))) (Set.Ici τ) := by
  have heq : (fun s : ℝ => Real.exp (-2 * (s - τ)))
      = fun s : ℝ => Real.exp (2 * τ) * Real.exp ((-2 : ℝ) * s) := by
    funext s
    rw [← Real.exp_add]
    congr 1
    ring_nf
  rw [heq]
  exact (integrable_exp_mul_Ici (-2) (by norm_num) τ).const_mul (Real.exp (2 * τ))

/-- `∫_τ^∞ e^{-2(s-τ)} ds = 1/2`. -/
theorem integral_exp_two_shift (τ : ℝ) :
    ∫ s in Set.Ici τ, Real.exp (-2 * (s - τ)) = 1 / 2 := by
  rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
  have heq : (fun s : ℝ => Real.exp (-2 * (s - τ)))
      = fun s : ℝ => Real.exp (2 * τ) * Real.exp ((-2 : ℝ) * s) := by
    funext s
    rw [← Real.exp_add]
    congr 1
    ring_nf
  rw [heq, integral_const_mul, integral_exp_mul_Ioi (by norm_num : (-2 : ℝ) < 0) τ]
  have hval : -Real.exp ((-2 : ℝ) * τ) / (-2 : ℝ) = Real.exp (-2 * τ) / 2 := by ring
  rw [hval]
  have h1 : Real.exp (2 * τ) * Real.exp (-2 * τ) = 1 := by
    rw [← Real.exp_add, show 2 * τ + -2 * τ = 0 by ring, Real.exp_zero]
  calc Real.exp (2 * τ) * (Real.exp (-2 * τ) / 2)
      = (Real.exp (2 * τ) * Real.exp (-2 * τ)) / 2 := by ring
    _ = 1 / 2 := by rw [h1]

/-- **The lower half of the clock comparison**: `A τ ≤ 2 (T - t τ)` for `τ ≥ 0`. -/
theorem A_le_two_mul_tail (C : Work.FTS.Physical.PhysClock) {τ : ℝ} (hτ : 0 ≤ τ) :
    C.A τ ≤ 2 * (C.T - C.t τ) := by
  rw [tail_eq_integral C hτ]
  have hIntA : IntegrableOn C.A (Set.Ici τ) :=
    (integrableOn_A_local C).mono_set (Set.Ici_subset_Ici.mpr hτ)
  have hIntg : IntegrableOn (fun s : ℝ => C.A τ * Real.exp (-2 * (s - τ))) (Set.Ici τ) :=
    (integrableOn_exp_two_shift τ).const_mul (C.A τ)
  have hmono : ∫ s in Set.Ici τ, C.A τ * Real.exp (-2 * (s - τ)) ≤ ∫ s in Set.Ici τ, C.A s :=
    setIntegral_mono_on hIntg hIntA measurableSet_Ici (fun s hs => A_exp_two_le C hτ hs)
  have hval : ∫ s in Set.Ici τ, C.A τ * Real.exp (-2 * (s - τ)) = C.A τ * (1 / 2) := by
    rw [integral_const_mul, integral_exp_two_shift τ]
  have key : C.A τ * (1 / 2) ≤ ∫ s in Set.Ici τ, C.A s := by rw [← hval]; exact hmono
  linarith

end Work.FTS.Physical.Clock
end
-- ===== merged: Submission.Work.FTS.Physical.Clock.exists_inverse_clock =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Filter Topology MeasureTheory
open scoped Topology NNReal ENNReal

set_option autoImplicit false

namespace Work.FTS.Physical.Clock

open Work.FTS.Physical (PhysClock)
open Work.FTS.Physical.PhysClock

/-- **The inverse clock.**  There is a function `τ : ℝ → ℝ` such that for every physical time
`t < T`: `t(τ(t)) = t`, `τ(t) ≥ 0`, `T - t ≤ 2 A(τ(t))`, and `τ` is differentiable at every
interior time with derivative `1/A(τ(t))`. -/
theorem exists_inverse_clock (C : Work.FTS.Physical.PhysClock) :
    ∃ tau : ℝ → ℝ, (∀ t ∈ Set.Ico 0 C.T, C.t (tau t) = t) ∧
      (∀ t ∈ Set.Ico 0 C.T, 0 ≤ tau t) ∧
      (∀ t ∈ Set.Ico 0 C.T, C.T - t ≤ 2 * C.A (tau t)) ∧
      ∀ t ∈ Set.Ioo 0 C.T, HasDerivAt tau ((C.A (tau t))⁻¹) t := by
  classical
  -- the inverse, built by choice from the surjectivity of the clock
  let tau : ℝ → ℝ := fun t => if h : t ∈ Set.Ico 0 C.T then (Work.FTS.Physical.Clock.exists_t_eq C h).choose else 0
  have htau : ∀ t ∈ Set.Ico 0 C.T, 0 ≤ tau t ∧ C.t (tau t) = t := by
    intro t ht
    have h := (Work.FTS.Physical.Clock.exists_t_eq C ht).choose_spec
    simpa only [tau, dif_pos ht] using h
  have hmono : MonotoneOn C.t (Set.Ici (0 : ℝ)) := (Work.FTS.Physical.Clock.t_strictMonoOn C).monotoneOn
  refine ⟨tau, fun t ht => (htau t ht).2, fun t ht => (htau t ht).1, fun t ht => ?_, ?_⟩
  · have h1 : C.T - C.t (tau t) ≤ 2 * C.A (tau t) := Work.FTS.Physical.Clock.tail_le_two_mul C (htau t ht).1
    rwa [(htau t ht).2] at h1
  intro t ht
  obtain ⟨ht0, htT⟩ := ht
  have htIco : t ∈ Set.Ico 0 C.T := ⟨ht0.le, htT⟩
  have hτpos : 0 < tau t := by
    rcases lt_or_eq_of_le (htau t htIco).1 with h | h
    · exact h
    · exfalso
      have h0 : C.t (tau t) = 0 := by rw [← h]; exact PhysClock.t_zero C
      rw [(htau t htIco).2] at h0
      exact absurd h0 (ne_of_gt ht0)
  have hτnn : 0 ≤ tau t := hτpos.le
  -- the one-sided windows
  have hη'le : ∀ η' , η' ≤ tau t / 2 → 0 ≤ tau t - η' := fun η' h => by linarith
  -- continuity of `tau` at `t`, from the strict monotonicity of `C.t`
  have hcont : ContinuousAt tau t := by
    rw [Metric.continuousAt_iff]
    intro η hη
    set η' : ℝ := min η (tau t / 2) with hη'def
    have hη'pos : 0 < η' := lt_min hη (by linarith)
    have hη'leη : η' ≤ η := min_le_left _ _
    have hη'let : η' ≤ tau t / 2 := min_le_right _ _
    have hmem_lo : (0 : ℝ) ≤ tau t - η' := by linarith
    have hmem_hi : (0 : ℝ) ≤ tau t + η' := by linarith
    have hmem_t : (0 : ℝ) ≤ tau t := hτnn
    set δ : ℝ := min (min (C.t (tau t + η') - t) (t - C.t (tau t - η'))) (min (C.T - t) t)
      with hδdef
    have hδ1 : 0 < C.t (tau t + η') - t := by
      have h : C.t (tau t) < C.t (tau t + η') :=
        Work.FTS.Physical.Clock.t_strictMonoOn C hmem_t hmem_hi (by linarith)
      rw [(htau t htIco).2] at h
      linarith
    have hδ2 : 0 < t - C.t (tau t - η') := by
      have h : C.t (tau t - η') < C.t (tau t) :=
        Work.FTS.Physical.Clock.t_strictMonoOn C hmem_lo hmem_t (by linarith)
      rw [(htau t htIco).2] at h
      linarith
    have hδpos : 0 < δ := lt_min (lt_min hδ1 hδ2) (lt_min (by linarith) ht0)
    have hδle1 : δ ≤ C.t (tau t + η') - t := le_trans (min_le_left _ _) (min_le_left _ _)
    have hδle2 : δ ≤ t - C.t (tau t - η') := le_trans (min_le_left _ _) (min_le_right _ _)
    have hδleT : δ ≤ C.T - t := le_trans (min_le_right _ _) (min_le_left _ _)
    have hδlet : δ ≤ t := le_trans (min_le_right _ _) (min_le_right _ _)
    refine ⟨δ, hδpos, fun s hs => ?_⟩
    have hsδ : |s - t| < δ := by rwa [Real.dist_eq] at hs
    have hw := abs_lt.mp hsδ
    rw [Real.dist_eq]
    rcases lt_trichotomy s t with hst | heq | hts
    · -- `s < t`
      have hsIco : s ∈ Set.Ico 0 C.T := by
        refine ⟨?_, by linarith⟩
        linarith [hw.1, hδlet]
      have hlt : tau s < tau t := by
        rcases lt_trichotomy (tau s) (tau t) with h | h | h
        · exact h
        · have hst_eq : s = t := by rw [← (htau s hsIco).2, ← (htau t htIco).2, h]
          exact absurd hst_eq (ne_of_lt hst)
        · have hle : C.t (tau t) ≤ C.t (tau s) :=
            hmono (htau t htIco).1 (htau s hsIco).1 h.le
          rw [(htau s hsIco).2, (htau t htIco).2] at hle
          exact absurd hle (not_le.mpr hst)
      have hlow : tau t - η' < tau s := by
        by_contra hcon
        push_neg at hcon
        have hle : C.t (tau s) ≤ C.t (tau t - η') :=
          hmono (show tau s ∈ Set.Ici (0 : ℝ) from (htau s hsIco).1)
            (show tau t - η' ∈ Set.Ici (0 : ℝ) from hmem_lo) hcon
        rw [(htau s hsIco).2] at hle
        linarith [hw.1, hδle2]
      rw [abs_of_neg (by linarith)]
      have : tau t - tau s < η' := by linarith
      linarith
    · subst heq
      simpa using hη
    · -- `t < s`
      have hsIco : s ∈ Set.Ico 0 C.T := by
        refine ⟨by linarith, ?_⟩
        linarith [hw.2, hδleT]
      have hlt : tau t < tau s := by
        rcases lt_trichotomy (tau t) (tau s) with h | h | h
        · exact h
        · have hst_eq : s = t := by rw [← (htau s hsIco).2, ← (htau t htIco).2, ← h]
          exact absurd hst_eq (ne_of_gt hts)
        · have hle : C.t (tau s) ≤ C.t (tau t) :=
            hmono (htau s hsIco).1 (htau t htIco).1 h.le
          rw [(htau s hsIco).2, (htau t htIco).2] at hle
          exact absurd hle (not_le.mpr hts)
      have hhigh : tau s < tau t + η' := by
        by_contra hcon
        push_neg at hcon
        have hle : C.t (tau t + η') ≤ C.t (tau s) :=
          hmono (show tau t + η' ∈ Set.Ici (0 : ℝ) from hmem_hi)
            (show tau s ∈ Set.Ici (0 : ℝ) from (htau s hsIco).1) hcon
        rw [(htau s hsIco).2] at hle
        linarith [hw.2, hδle1]
      rw [abs_of_pos (by linarith)]
      have : tau s - tau t < η' := by linarith
      linarith
  -- the local identity and the inverse function theorem
  have hloc : ∀ᶠ s in 𝓝 t, C.t (tau s) = s := by
    filter_upwards [isOpen_Ioo.mem_nhds (show t ∈ Set.Ioo (t - min (t / 2) ((C.T - t) / 2))
      (t + min (t / 2) ((C.T - t) / 2)) from
      ⟨by have h := lt_min (by linarith : (0 : ℝ) < t / 2)
            (by linarith : (0 : ℝ) < (C.T - t) / 2); linarith,
       by have h := lt_min (by linarith : (0 : ℝ) < t / 2)
            (by linarith : (0 : ℝ) < (C.T - t) / 2); linarith⟩)] with s hs
    obtain ⟨hs1, hs2⟩ := hs
    have hεt : min (t / 2) ((C.T - t) / 2) ≤ t / 2 := min_le_left _ _
    have hεT : min (t / 2) ((C.T - t) / 2) ≤ (C.T - t) / 2 := min_le_right _ _
    exact (htau s ⟨by linarith, by linarith⟩).2
  exact HasDerivAt.of_local_left_inverse hcont (Work.FTS.Physical.Clock.hasDerivAt_t C hτpos)
    (ne_of_gt (C.hApos (tau t) hτnn)) hloc

end Work.FTS.Physical.Clock
end
-- ===== merged: Submission.Work.FTS.PressureOn.Auxiliary.gaussShift.integrable_poly_exp_neg_normSq_sub =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Integrability of a quadratic times a shifted Gaussian on `ℝ³`

For `a ≥ 0`, `b ≥ 0`, `c > 0` and any centre `w : ℝ³`, the function

`z ↦ (a + b‖z - w‖²) exp (-(c‖z - w‖²))`

is integrable on `ℝ³`.  This is the shifted (translation-invariant) form of the Gauss majorant
estimate `Work.FTS.PressureOn.Auxiliary.integrable_gaussMajorant`, and it is obtained from it by
composing with the translation `z ↦ z - w` (`MeasureTheory.Integrable.comp_sub_right`, valid
because Lebesgue measure on `ℝ³` is translation invariant).
-/

namespace Work.FTS.PressureOn.Auxiliary.gaussShift

theorem integrable_poly_exp_neg_normSq_sub (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 < c) (w : Work.FTS.PressureOn.R3) :
    MeasureTheory.Integrable (fun z : Work.FTS.PressureOn.R3 =>
      (a + b * ‖z - w‖ ^ 2) * Real.exp (-(c * ‖z - w‖ ^ 2))) := by
  have h := (Work.FTS.PressureOn.Auxiliary.integrable_gaussMajorant a b c ha hb hc).comp_sub_right w
  simpa only [Pi.sub_apply] using h

end Work.FTS.PressureOn.Auxiliary.gaussShift
end
-- ===== merged: Submission.Work.FTS.PressureOn.Auxiliary.greenWeightedIntegral =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity MeasureTheory Set Filter Topology
open scoped Topology

set_option autoImplicit false

namespace Work.FTS.PressureOn.Auxiliary

noncomputable section

/-- **The weighted Green identity.**  For `u` harmonic on `ℝ³`, a compactly supported weight `χ` and
a `C²` function `F`,

  `∫ χ u ΔF = -∫ u F Δχ - 2 ∫ u ⟪∇χ, ∇F⟫`.

Proof: three integrations by parts (`integral_inner_gradient_mul_eq_neg`) on the compactly
supported fields `χ ∇F`, `χ ∇u` and `F ∇χ`; the harmonicity of `u` kills the `Δu` term, and the
mixed terms combine to the stated expression. -/
lemma integral_green_weighted (u χ F : R3 → ℝ)
    (hu1 : ContDiff ℝ 1 u) (hu2 : ContDiff ℝ 2 u)
    (hχ1 : ContDiff ℝ 1 χ) (hχ2 : ContDiff ℝ 2 χ) (hχcs : HasCompactSupport χ)
    (hF1 : ContDiff ℝ 1 F) (hF2 : ContDiff ℝ 2 F) (hlapu : ∀ y, laplaceTrace u y = 0)
    (hint1 : Integrable (fun y => (χ y * laplaceTrace F y) * u y))
    (hint2 : Integrable (fun y => inner ℝ (gradient χ y) (gradient F y) * u y))
    (hint3 : Integrable (fun y => (F y * laplaceTrace χ y) * u y)) :
    ∫ y, χ y * u y * laplaceTrace F y
      = -(∫ y, u y * F y * laplaceTrace χ y)
        - 2 * ∫ y, u y * inner ℝ (gradient χ y) (gradient F y) := by
  have hgχ : ContDiff ℝ 1 (fun y : R3 => gradient χ y) := Green.contDiff_gradient χ hχ2
  have hgu : ContDiff ℝ 1 (fun y : R3 => gradient u y) := Green.contDiff_gradient u hu2
  have hgF : ContDiff ℝ 1 (fun y : R3 => gradient F y) := Green.contDiff_gradient F hF2
  have hdivF : ∀ y : R3, div (fun z : R3 => gradient F z) y = laplaceTrace F y :=
    fun y => congrFun (Green.div_gradient_eq_laplaceTrace F hF2) y
  have hdivχ : ∀ y : R3, div (fun z : R3 => gradient χ z) y = laplaceTrace χ y :=
    fun y => congrFun (Green.div_gradient_eq_laplaceTrace χ hχ2) y
  have hdivu : ∀ y : R3, div (fun z : R3 => gradient u z) y = laplaceTrace u y :=
    fun y => congrFun (Green.div_gradient_eq_laplaceTrace u hu2) y
  -- (A)  ω = χ ∇F, ψ = u
  have hAcs : HasCompactSupport (fun y : R3 => χ y • gradient F y) := hχcs.mono' (fun y hy => by
    by_contra hyt
    rw [Function.mem_support] at hy
    exact hy (by rw [image_eq_zero_of_notMem_tsupport hyt, zero_smul]))
  have hAibp := Work.FTS.PressureOn.integral_inner_gradient_mul_eq_neg
    (fun y : R3 => χ y • gradient F y) (hχ1.smul hgF) hAcs hu1
  have hAlhs : ∫ y, inner ℝ (χ y • gradient F y) (gradient u y)
      = ∫ y, χ y * inner ℝ (gradient F y) (gradient u y) := by
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [real_inner_smul_left]
  have hArhs : ∫ y, div (fun z : R3 => χ z • gradient F z) y * u y
      = ∫ y, ((χ y * laplaceTrace F y) * u y
          + inner ℝ (gradient χ y) (gradient F y) * u y) := by
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    show div (fun z : R3 => χ z • gradient F z) y * u y = _
    rw [Work.FTS.PressureOn.div_smul (ψ := χ) (ω := fun y : R3 => gradient F y) hχ1 hgF y,
      hdivF y]
    ring
  have hAsplit : ∫ y, ((χ y * laplaceTrace F y) * u y
        + inner ℝ (gradient χ y) (gradient F y) * u y)
      = (∫ y, (χ y * laplaceTrace F y) * u y)
        + (∫ y, inner ℝ (gradient χ y) (gradient F y) * u y) :=
    integral_add hint1 hint2
  have hAeq : ∫ y, χ y * inner ℝ (gradient F y) (gradient u y)
      = -((∫ y, (χ y * laplaceTrace F y) * u y)
          + (∫ y, inner ℝ (gradient χ y) (gradient F y) * u y)) := by
    have h := hAibp
    rw [hAlhs, hArhs, hAsplit] at h
    exact h
  -- (B)  ω = χ ∇u, ψ = F
  have hBcs : HasCompactSupport (fun y : R3 => χ y • gradient u y) := hχcs.mono' (fun y hy => by
    by_contra hyt
    rw [Function.mem_support] at hy
    exact hy (by rw [image_eq_zero_of_notMem_tsupport hyt, zero_smul]))
  have hBibp := Work.FTS.PressureOn.integral_inner_gradient_mul_eq_neg
    (fun y : R3 => χ y • gradient u y) (hχ1.smul hgu) hBcs hF1
  have hBlhs : ∫ y, inner ℝ (χ y • gradient u y) (gradient F y)
      = ∫ y, χ y * inner ℝ (gradient u y) (gradient F y) := by
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [real_inner_smul_left]
  have hBrhs : ∫ y, div (fun z : R3 => χ z • gradient u z) y * F y
      = ∫ y, inner ℝ (gradient χ y) (gradient u y) * F y := by
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    show div (fun z : R3 => χ z • gradient u z) y * F y
      = inner ℝ (gradient χ y) (gradient u y) * F y
    rw [Work.FTS.PressureOn.div_smul (ψ := χ) (ω := fun y : R3 => gradient u y) hχ1 hgu y,
      hdivu y, hlapu y]
    ring
  have hBeq : ∫ y, χ y * inner ℝ (gradient u y) (gradient F y)
      = -(∫ y, inner ℝ (gradient χ y) (gradient u y) * F y) := by
    have h := hBibp
    rw [hBlhs, hBrhs] at h
    exact h
  -- (D)  ω = F ∇χ, ψ = u
  have hDcs : HasCompactSupport (fun y : R3 => F y • gradient χ y) := hχcs.mono' (fun y hy => by
    by_contra hyt
    rw [Function.mem_support] at hy
    exact hy (by rw [Green.gradient_eq_zero_of_notMem_tsupport hyt, smul_zero]))
  have hDibp := Work.FTS.PressureOn.integral_inner_gradient_mul_eq_neg
    (fun y : R3 => F y • gradient χ y) (hF1.smul hgχ) hDcs hu1
  have hDlhs : ∫ y, inner ℝ (F y • gradient χ y) (gradient u y)
      = ∫ y, inner ℝ (gradient χ y) (gradient u y) * F y := by
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [real_inner_smul_left]
    ring
  have hDrhs : ∫ y, div (fun z : R3 => F z • gradient χ z) y * u y
      = ∫ y, ((F y * laplaceTrace χ y) * u y
          + inner ℝ (gradient χ y) (gradient F y) * u y) := by
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    show div (fun z : R3 => F z • gradient χ z) y * u y = _
    rw [Work.FTS.PressureOn.div_smul (ψ := F) (ω := fun y : R3 => gradient χ y) hF1 hgχ y,
      hdivχ y, real_inner_comm]
    ring
  have hDsplit : ∫ y, ((F y * laplaceTrace χ y) * u y
        + inner ℝ (gradient χ y) (gradient F y) * u y)
      = (∫ y, (F y * laplaceTrace χ y) * u y)
        + (∫ y, inner ℝ (gradient χ y) (gradient F y) * u y) :=
    integral_add hint3 hint2
  have hDeq : ∫ y, inner ℝ (gradient χ y) (gradient u y) * F y
      = -((∫ y, (F y * laplaceTrace χ y) * u y)
          + (∫ y, inner ℝ (gradient χ y) (gradient F y) * u y)) := by
    have h := hDibp
    rw [hDlhs, hDrhs, hDsplit] at h
    exact h
  -- the left-hand sides of (A) and (B) agree
  have hcomm : ∫ y, χ y * inner ℝ (gradient F y) (gradient u y)
      = ∫ y, χ y * inner ℝ (gradient u y) (gradient F y) := by
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [real_inner_comm]
  set X : ℝ := ∫ y, χ y * inner ℝ (gradient F y) (gradient u y) with hX
  set Z : ℝ := ∫ y, inner ℝ (gradient χ y) (gradient u y) * F y with hZ
  set A1 : ℝ := ∫ y, (χ y * laplaceTrace F y) * u y with hA1
  set A2 : ℝ := ∫ y, inner ℝ (gradient χ y) (gradient F y) * u y with hA2
  set W1 : ℝ := ∫ y, (F y * laplaceTrace χ y) * u y with hW1
  have hA' : X = -(A1 + A2) := hAeq
  have hB' : X = -Z := by
    rw [hcomm]
    exact hBeq
  have hD' : Z = -(W1 + A2) := hDeq
  have key : A1 = -W1 - 2 * A2 := by linarith
  have e1 : A1 = ∫ y, χ y * u y * laplaceTrace F y := by
    rw [hA1]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    ring
  have e2 : W1 = ∫ y, u y * F y * laplaceTrace χ y := by
    rw [hW1]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    ring
  have e3 : A2 = ∫ y, u y * inner ℝ (gradient χ y) (gradient F y) := by
    rw [hA2]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    ring
  rw [← e1, ← e2, ← e3]
  linarith

end

end Work.FTS.PressureOn.Auxiliary
end
-- ===== merged: Submission.Work.FTS.PressureOn.Auxiliary.hasDerivAt_heatKernel_time =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The heat equation for the heat kernel: `∂_t γ_t(z) = Δ_z γ_t(z)`

`heatKernel t z = (4πt)^{-3/2} exp(-‖z‖²/(4t))` satisfies the heat equation in the strong
(derivative) form: for every `t > 0` and every `z : ℝ³`,

`HasDerivAt (fun s => heatKernel s z) (laplaceTrace (heatKernel t) z) t`,

where `laplaceTrace φ z = ∑ᵢ ∂ᵢ∂ᵢ φ(z)` is the Euclidean Laplacian in the *spatial* variable
(so the right-hand side is `Δ_z γ_t(z)`).

The two computations are:

* **spatial**, `Δ_z γ_t(z) = (4πt)^{-3/2} (‖z‖²/(4t²) - 3/(2t)) exp(-‖z‖²/(4t))`: split off the
  constant prefactor `A = (4πt)^{-3/2}` (`laplaceTrace` is `ℝ`-homogeneous, `laplaceTrace_const_mul`)
  and use `Green.laplaceTrace_exp_neg_mul_normSq`, the Laplacian of a Gaussian
  `Δ exp(-c‖y‖²) = (4c²‖y‖² - 6c) exp(-c‖y‖²)`;
* **temporal**, `∂_t γ_t(z) = (4πt)^{-3/2} (‖z‖²/(4t²) - 3/(2t)) exp(-‖z‖²/(4t))`: the product rule
  applied to `t ↦ (4πt)^{-3/2}` and `t ↦ exp(-‖z‖²/(4t))`
  (`hasDerivAt_heatPrefactor` and `hasDerivAt_heatGauss`).

The two values are equal by elementary algebra, which is the content of the theorem. -/

open Work.FTS.PressureOn (laplaceTrace)

namespace Work.FTS.PressureOn.Auxiliary

/-- `laplaceTrace` is homogeneous under multiplication by a constant: for `φ` of class `C²`,
`laplaceTrace (fun y => c * φ y) x = c * laplaceTrace φ x`.

(Unfolding the definition, both `fderiv`s in the chain are linear in the constant: the first
derivative of `c * φ` is `c • fderiv φ`, and then the second derivative of
`w ↦ c * (fderiv φ w (eᵢ))` is `c •` that of `w ↦ fderiv φ w (eᵢ)`.  Both applications of
`fderiv_const_mul` need the differentiability of the differentiated function, which is supplied by
`hφ` and by `hφ.fderiv_right`.) -/
lemma laplaceTrace_const_mul (c : ℝ) (φ : Work.FTS.PressureOn.R3 → ℝ)
    (hφ : ContDiff ℝ 2 φ) (x : Work.FTS.PressureOn.R3) :
    laplaceTrace (fun y => c * φ y) x = c * laplaceTrace φ x := by
  have hd1 : ∀ w, DifferentiableAt ℝ φ w := fun w => hφ.differentiable (by norm_num) w
  have hd2 : ∀ (i : Fin 3) (w : Work.FTS.PressureOn.R3),
      DifferentiableAt ℝ (fun w' : Work.FTS.PressureOn.R3 =>
        fderiv ℝ φ w' (FiniteTimeSingularity.e i)) w := by
    intro i w
    have h1 : ContDiff ℝ 1 (fderiv ℝ φ) := hφ.fderiv_right (m := 1) (by norm_num)
    have h2 : ContDiff ℝ 1 (fun w' : Work.FTS.PressureOn.R3 =>
        fderiv ℝ φ w' (FiniteTimeSingularity.e i)) :=
      (ContinuousLinearMap.apply ℝ ℝ (FiniteTimeSingularity.e i)).contDiff.comp h1
    exact h2.differentiable (by norm_num) w
  unfold laplaceTrace
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hA : (fun w : Work.FTS.PressureOn.R3 =>
        fderiv ℝ (fun y => c * φ y) w (FiniteTimeSingularity.e i))
      = (fun w : Work.FTS.PressureOn.R3 =>
          c * (fderiv ℝ φ w (FiniteTimeSingularity.e i))) := by
    funext w
    rw [fderiv_const_mul (hd1 w) c]
    simp
  rw [hA, fderiv_const_mul (hd2 i x) c]
  simp

/-- **The Laplacian of the heat kernel** in the spatial variable:
`Δ_z γ_t(z) = (4πt)^{-3/2} (4(4t)^{-2}‖z‖² - 6(4t)^{-1}) exp(-(4t)^{-1}‖z‖²)`.

The factor `(4t)^{-1}` is the Gaussian parameter `c` of `heatKernel t`, i.e.
`heatKernel t y = (4πt)^{-3/2} exp(-c‖y‖²)`; the statement is the homogeneity
`laplaceTrace_const_mul` applied to `Green.laplaceTrace_exp_neg_mul_normSq`. -/
lemma laplaceTrace_heatKernel (t : ℝ) (z : Work.FTS.PressureOn.R3) :
    laplaceTrace (Work.FTS.PressureOn.Auxiliary.heatKernel t) z
      = (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) *
          ((4 * (4 * t)⁻¹ ^ 2 * ‖z‖ ^ 2 - 6 * (4 * t)⁻¹) *
            Real.exp (-((4 * t)⁻¹ * ‖z‖ ^ 2))) := by
  have hc : ContDiff ℝ 2 (fun y : Work.FTS.PressureOn.R3 =>
      Real.exp (-((4 * t)⁻¹ * ‖y‖ ^ 2))) :=
    (((contDiff_const.mul (contDiff_norm_sq ℝ)).neg).exp)
  have hfun : Work.FTS.PressureOn.Auxiliary.heatKernel t
      = fun y : Work.FTS.PressureOn.R3 =>
          (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * Real.exp (-((4 * t)⁻¹ * ‖y‖ ^ 2)) := by
    funext y
    rw [Work.FTS.PressureOn.Auxiliary.heatKernel_apply]
    simp only [div_eq_inv_mul]
  rw [hfun, laplaceTrace_const_mul _ _ hc z,
    Work.FTS.PressureOn.Green.laplaceTrace_exp_neg_mul_normSq]

/-- **The heat equation for the heat kernel**: for `t > 0`, the time derivative at `t` of the
spatial profile `z ↦ γ_t(z)` is the Laplacian of the profile at time `t`, evaluated at `z`, i.e.
`∂_t γ_t(z) = Δ_z γ_t(z)`.

`HasDerivAt` is computed by the product rule (`hasDerivAt_heatPrefactor`,
`hasDerivAt_heatGauss`), the Laplacian by `laplaceTrace_heatKernel`; the two values coincide
because `4(4t)^{-2} = 1/(4t²)` and `6(4t)^{-1} = 3/(2t)`. -/
theorem hasDerivAt_heatKernel_time (t : ℝ) (ht : 0 < t) (z : Work.FTS.PressureOn.R3) :
    HasDerivAt (fun s : ℝ => Work.FTS.PressureOn.Auxiliary.heatKernel s z)
      (Work.FTS.PressureOn.laplaceTrace (Work.FTS.PressureOn.Auxiliary.heatKernel t) z) t := by
  -- The time derivative of the heat kernel, by the product rule.
  have h := (Work.FTS.PressureOn.Auxiliary.hasDerivAt_heatPrefactor t ht).mul
    (Work.FTS.PressureOn.Auxiliary.hasDerivAt_heatGauss t ht z)
  have h1 : (-(3 / (2 * t)) * (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) *
        Real.exp (-(‖z‖ ^ 2 / (4 * t))) +
        (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) *
          (Real.exp (-(‖z‖ ^ 2 / (4 * t))) * (‖z‖ ^ 2 / (4 * t ^ 2))))
      = ((4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * (‖z‖ ^ 2 / (4 * t ^ 2) - 3 / (2 * t)) *
          Real.exp (-(‖z‖ ^ 2 / (4 * t)))) := by
    ring
  have h2 := h.congr_deriv h1
  have hfun : ((fun s : ℝ => (4 * Real.pi * s) ^ (-(3 / 2 : ℝ))) *
        fun s : ℝ => Real.exp (-(‖z‖ ^ 2 / (4 * s))))
      = (fun s : ℝ => Work.FTS.PressureOn.Auxiliary.heatKernel s z) := by
    funext s
    simp only [Pi.mul_apply, Work.FTS.PressureOn.Auxiliary.heatKernel_apply]
  have hderiv : HasDerivAt (fun s : ℝ => Work.FTS.PressureOn.Auxiliary.heatKernel s z)
      ((4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * (‖z‖ ^ 2 / (4 * t ^ 2) - 3 / (2 * t)) *
        Real.exp (-(‖z‖ ^ 2 / (4 * t)))) t := by
    simpa only [hfun] using h2
  -- Replace the target value by the explicit Laplacian and compare the two expressions.
  rw [laplaceTrace_heatKernel t z]
  refine hderiv.congr_deriv ?_
  have hexp : Real.exp (-(‖z‖ ^ 2 / (4 * t))) = Real.exp (-((4 * t)⁻¹ * ‖z‖ ^ 2)) := by
    congr 1
    rw [div_eq_inv_mul, mul_comm]
  have hcoef : 4 * (4 * t)⁻¹ ^ 2 * ‖z‖ ^ 2 - 6 * (4 * t)⁻¹
      = ‖z‖ ^ 2 / (4 * t ^ 2) - 3 / (2 * t) := by
    field_simp
    ring
  rw [hexp, hcoef]
  ring

end Work.FTS.PressureOn.Auxiliary
end
-- ===== merged: Submission.Work.FTS.PressureOn.Auxiliary.heatKernel_integral_one =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The heat kernel on `ℝ³` is a probability density

`Work.FTS.PressureOn.Auxiliary.heatKernel t z = (4πt)^{-3/2} exp(-‖z‖²/(4t))` is integrable and
integrates to `1` (for `t > 0`).

The integral was already computed in the sibling module
`Submission.Work.FTS.PressureOn.Auxiliary.integral_heatKernel`
(`integral_heatKernel t ht : ∫ z, heatKernel t z = 1`); here we only add the integrability, which
is the observation that the heat kernel is a *constant* times the Gaussian
`z ↦ exp (-((4t)⁻¹ ‖z‖²))`, and Gaussians are integrable (`ihak_integrable_rexp_normSq`).
-/

open MeasureTheory

set_option autoImplicit false

namespace Work.FTS.PressureOn.Auxiliary

noncomputable section

/-- **Integrability of the heat kernel.**  For `t > 0` the kernel is the constant
`(4πt)^{-3/2}` times the Gaussian `z ↦ exp (-(4t)⁻¹‖z‖²)`, and the Gaussian is integrable on
`ℝ³`. -/
private lemma integrable_heatKernel_aux {t : ℝ} (ht : 0 < t) : Integrable (heatKernel t) := by
  have ha : (0 : ℝ) < (4 * t)⁻¹ := inv_pos.mpr (by linarith)
  have hbase : Integrable (fun z : R3 => Real.exp (-((4 * t)⁻¹ * ‖z‖ ^ 2))) :=
    ihak_integrable_rexp_normSq ((4 * t)⁻¹) ha
  refine (hbase.const_mul ((4 * Real.pi * t) ^ (-(3 / 2 : ℝ)))).congr
    (Filter.Eventually.of_forall fun z => ?_)
  exact (heatKernel_eq_const_mul_exp ht z).symm

theorem heatKernel_integral_one (t : ℝ) (ht : 0 < t) :
    MeasureTheory.Integrable (Work.FTS.PressureOn.Auxiliary.heatKernel t) ∧
      (∫ z : Work.FTS.PressureOn.R3, Work.FTS.PressureOn.Auxiliary.heatKernel t z) = 1 :=
  ⟨integrable_heatKernel_aux ht, integral_heatKernel t ht⟩

end

end Work.FTS.PressureOn.Auxiliary
end
-- ===== merged: Submission.Work.FTS.PressureOn.Auxiliary.ihak_interval_shift_mean =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The shear-average (interval mean) lemma

For a continuous, Gaussian-decaying function `g` on `ℝ³` and any shift vector `h`, the *sliding
average* `z ↦ ∫₀¹ g (z - s h) ds` is integrable and has the same total integral as `g`:

`∫_z ∫₀¹ g (z - s h) ds dz = ∫_z g z dz`.

This is the (very special case of the) `L¹`-invariance of Lebesgue measure under the shear
`z ↦ z - s h` averaged over `s ∈ [0,1]`.  It is the analytic input of the shear-averaging step in
the reconstruction of the Biot–Savart field (the averaged field is the Biot–Savart field of the
averaged vorticity, and the two have a common mean).

The proof is Fubini on the product `(0,1] × ℝ³` together with translation invariance of the
Lebesgue integral (`MeasureTheory.integral_sub_right_eq_self`).  The only analytic input is the
integrability of `(s, z) ↦ g (z - s h)` on `(0,1] × ℝ³`, which follows from the elementary
exponential bound

`exp (-(a ‖z - s h‖²)) ≤ exp (-(a/2 ‖z‖²)) · exp (a ‖h‖² s²)`

(`neg_sq_sub_smul_le` below) and the integrability of the Gaussian `exp (-(a/2 ‖z‖²))`
(`ihak_integrable_rexp_normSq`).
-/

open MeasureTheory Filter
open scoped Topology

set_option autoImplicit false

namespace Work.FTS.PressureOn.Auxiliary

noncomputable section

/-- **The elementary exponential bound for the shear.**  For `a > 0`, `z, h` in a real normed
space and `s : ℝ`,

`-(a ‖z - s • h‖²) ≤ -(a/2 ‖z‖²) + a ‖h‖² s²`,

i.e. sliding `z` by `s h` costs only a factor `exp (a ‖h‖² s²)` in the Gaussian weight.  It is the
arithmetic mean–geometric mean inequality applied to `‖z‖ ≤ ‖z - s•h‖ + ‖s•h‖`. -/
lemma neg_sq_sub_smul_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℝ) (ha : 0 < a) (z h : E) (s : ℝ) :
    -(a * ‖z - s • h‖ ^ 2) ≤ -(a / 2 * ‖z‖ ^ 2) + a * ‖h‖ ^ 2 * s ^ 2 := by
  have h1 : ‖z‖ ≤ ‖z - s • h‖ + ‖s • h‖ := by
    calc ‖z‖ = ‖(z - s • h) + s • h‖ := by rw [sub_add_cancel]
      _ ≤ ‖z - s • h‖ + ‖s • h‖ := norm_add_le _ _
  have h2 : ‖z‖ ^ 2 ≤ (‖z - s • h‖ + ‖s • h‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg z) h1 2
  have h3 : (‖z - s • h‖ + ‖s • h‖) ^ 2 ≤ 2 * ‖z - s • h‖ ^ 2 + 2 * ‖s • h‖ ^ 2 := by
    nlinarith [two_mul_le_add_sq ‖z - s • h‖ ‖s • h‖]
  have h4 : ‖s • h‖ ^ 2 = s ^ 2 * ‖h‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have h5 : ‖z‖ ^ 2 ≤ 2 * ‖z - s • h‖ ^ 2 + 2 * (s ^ 2 * ‖h‖ ^ 2) := by linarith
  have h6 : (a / 2) * ‖z‖ ^ 2 ≤ (a / 2) * (2 * ‖z - s • h‖ ^ 2 + 2 * (s ^ 2 * ‖h‖ ^ 2)) :=
    mul_le_mul_of_nonneg_left h5 (by linarith : (0 : ℝ) ≤ a / 2)
  nlinarith [h6]

/-- **The interval mean of the shear translates has the same integral as `g`.**

If `g : ℝ³ → ℝ` is continuous and Gaussian-decaying, `|g w| ≤ C exp (-(a ‖w‖²))` with `a > 0` and
`C ≥ 0`, then for every `h : ℝ³` the averaged translate `z ↦ ∫₀¹ g (z - s h) ds` is integrable and

`∫_z (∫₀¹ g (z - s h) ds) = ∫_z g z`.

(Equivalently: the shear `z ↦ z - s h`, averaged over `s ∈ [0,1]`, preserves the total mass.) -/
theorem ihak_interval_shift_mean {g : Work.FTS.PressureOn.R3 → ℝ} (hg : Continuous g) (C a : ℝ)
    (ha : 0 < a) (hC : 0 ≤ C) (hb : ∀ w, |g w| ≤ C * Real.exp (-(a * ‖w‖ ^ 2)))
    (h : Work.FTS.PressureOn.R3) :
    MeasureTheory.Integrable (fun z : Work.FTS.PressureOn.R3 => ∫ s in (0 : ℝ)..1, g (z - s • h))
        MeasureTheory.volume
      ∧ (∫ z : Work.FTS.PressureOn.R3, (∫ s in (0 : ℝ)..1, g (z - s • h))) =
          ∫ z : Work.FTS.PressureOn.R3, g z := by
  -- `(0,1]` (equivalently `[0,1]`) carries a finite measure.
  have hfin : volume (Set.uIoc (0 : ℝ) 1) ≠ ⊤ := by
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1), Real.volume_Ioc]
    simp
  have hI : IsFiniteMeasure (volume.restrict (Set.uIoc (0 : ℝ) 1)) :=
    isFiniteMeasure_restrict.mpr hfin
  -- the `s`-factor `exp (a ‖h‖² s²)` is integrable on `(0,1]` (it is bounded there).
  have hf : Integrable (fun s : ℝ => Real.exp (a * ‖h‖ ^ 2 * s ^ 2))
      (volume.restrict (Set.uIoc (0 : ℝ) 1)) := by
    refine Integrable.mono' (integrable_const (Real.exp (a * ‖h‖ ^ 2))) ?_ ?_
    · exact (by fun_prop : Continuous (fun s : ℝ => Real.exp (a * ‖h‖ ^ 2 * s ^ 2))).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
      rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      have hs2 : s ^ 2 ≤ 1 := by nlinarith [hs.1, hs.2]
      have hs3 : a * ‖h‖ ^ 2 * s ^ 2 ≤ a * ‖h‖ ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left hs2 (by positivity)
      simpa using hs3
  -- the Gaussian `z`-factor is integrable on `ℝ³`.
  have hgauss : Integrable (fun z : R3 => C * Real.exp (-(a / 2 * ‖z‖ ^ 2))) volume :=
    (ihak_integrable_rexp_normSq (a / 2) (by linarith)).const_mul C
  -- hence the dominating product function is integrable.
  have hBint : Integrable
      (fun p : ℝ × R3 =>
        Real.exp (a * ‖h‖ ^ 2 * p.1 ^ 2) * (C * Real.exp (-(a / 2 * ‖p.2‖ ^ 2))))
      ((volume.restrict (Set.uIoc (0 : ℝ) 1)).prod volume) :=
    Integrable.mul_prod hf hgauss
  -- and so is `(s,z) ↦ g (z - s h)`.
  have hInt : Integrable (fun p : ℝ × R3 => g (p.2 - p.1 • h))
      ((volume.restrict (Set.uIoc (0 : ℝ) 1)).prod volume) := by
    refine Integrable.mono' hBint ?_ ?_
    · exact (hg.comp (by fun_prop)).aestronglyMeasurable
    · filter_upwards with p
      rw [Real.norm_eq_abs]
      calc |g (p.2 - p.1 • h)| ≤ C * Real.exp (-(a * ‖p.2 - p.1 • h‖ ^ 2)) := hb _
        _ ≤ C * (Real.exp (-(a / 2 * ‖p.2‖ ^ 2)) * Real.exp (a * ‖h‖ ^ 2 * p.1 ^ 2)) := by
            apply mul_le_mul_of_nonneg_left _ hC
            rw [← Real.exp_add]
            exact Real.exp_le_exp.mpr (neg_sq_sub_smul_le a ha p.2 h p.1)
        _ = Real.exp (a * ‖h‖ ^ 2 * p.1 ^ 2) * (C * Real.exp (-(a / 2 * ‖p.2‖ ^ 2))) := by ring
  refine ⟨?_, ?_⟩
  · -- integrability of `z ↦ ∫₀¹ g (z - s h) ds`, by Fubini (`Integrable.integral_prod_right`).
    have h1 := hInt.integral_prod_right
    refine h1.congr (Eventually.of_forall fun z => ?_)
    simp only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  · -- the identity of integrals, by Fubini + translation invariance.
    have hswap := intervalIntegral_integral_swap (f := fun s z => g (z - s • h)) hInt
    calc ∫ z : R3, (∫ s in (0 : ℝ)..1, g (z - s • h))
        = ∫ s in (0 : ℝ)..1, ∫ z : R3, g (z - s • h) := hswap.symm
      _ = ∫ s in (0 : ℝ)..1, ∫ z : R3, g z := by
          apply intervalIntegral.integral_congr
          intro s _
          exact integral_sub_right_eq_self (fun w : R3 => g w) (s • h)
      _ = ∫ z : R3, g z := by
          rw [intervalIntegral.integral_const, sub_zero, one_smul]

end

end Work.FTS.PressureOn.Auxiliary
end
-- ===== merged: Submission.Work.FTS.PressureOn.Auxiliary.integrable_inner_laplaceTraceVec_coord =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Integrability of the coordinatewise pairing with the trace of the Hessian

`Work.FTS.PressureOn.Auxiliary.integrable_inner_laplaceTraceVec_coord`.

For a smooth vector field `V` on `ℝ³` and a smooth *compactly supported* vector field `W`, and for
every coordinate index `j`, the two coordinatewise pairings

  `x ↦ (V x) j * Δ((W ·) j)(x)`  and  `x ↦ Δ((V ·) j)(x) * (W x) j`

are integrable on `ℝ³`.

Both are immediate: the trace of the Hessian of a compactly supported smooth function is
continuous (`Green.continuous_laplaceTrace`) and supported in `tsupport` of that function
(`Green.laplaceTrace_eq_zero_of_notMem_tsupport`), hence bounded with compact support; multiplying
it by the continuous coordinate function `x ↦ (V x) j` (resp. `x ↦ (W x) j`) keeps it continuous
with compact support, and a continuous compactly supported function is integrable.

The only structural inputs are the two elementary facts that the coordinate functions of a smooth
vector field are smooth and compactly supported whenever the field is.
-/

namespace Work.FTS.PressureOn.Auxiliary

open MeasureTheory

/-- The coordinate functions `x ↦ (V x) j` of a smooth vector field are smooth: they are the
composites of `V` with the continuous linear projection `PiLp.proj`. -/
lemma contDiff_coord (V : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (hV : ∀ n : ℕ, ContDiff ℝ n V) (j : Fin 3) :
    ∀ n : ℕ, ContDiff ℝ n (fun x : EuclideanSpace ℝ (Fin 3) => (V x) j) := by
  intro n
  fun_prop

/-- The coordinate functions `x ↦ (V x) j` of a compactly supported vector field are compactly
supported (their support is contained in the support of the field). -/
lemma hasCompactSupport_coord (V : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (hVc : HasCompactSupport V) (j : Fin 3) :
    HasCompactSupport (fun x : EuclideanSpace ℝ (Fin 3) => (V x) j) := by
  refine hVc.mono' fun z hz => ?_
  by_contra h
  exact hz (by simp [image_eq_zero_of_notMem_tsupport h])

/-- The trace of the Hessian of a coordinate function of a compactly supported smooth vector field
is compactly supported. -/
lemma hasCompactSupport_laplaceTrace_coord
    (W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (hWc : HasCompactSupport W) (j : Fin 3) :
    HasCompactSupport
      (Work.FTS.PressureOn.laplaceTrace (fun y : EuclideanSpace ℝ (Fin 3) => (W y) j)) :=
  (hasCompactSupport_coord W hWc j).mono' fun _ hz => by
    by_contra h
    exact hz (Work.FTS.PressureOn.Green.laplaceTrace_eq_zero_of_notMem_tsupport h)

/-- The trace of the Hessian of a coordinate function of a smooth vector field is continuous. -/
lemma continuous_laplaceTrace_coord
    (W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (hW : ∀ n : ℕ, ContDiff ℝ n W) (j : Fin 3) :
    Continuous
      (Work.FTS.PressureOn.laplaceTrace (fun y : EuclideanSpace ℝ (Fin 3) => (W y) j)) :=
  Work.FTS.PressureOn.Green.continuous_laplaceTrace _ ((contDiff_coord W hW j) 2)

theorem integrable_inner_laplaceTraceVec_coord
    (V W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (hV : ∀ n : ℕ, ContDiff ℝ n V) (hW : ∀ n : ℕ, ContDiff ℝ n W)
    (hWc : HasCompactSupport W) (j : Fin 3) :
    MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin 3) =>
        (V x) j * Work.FTS.PressureOn.laplaceTrace (fun y => (W y) j) x) ∧
    MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin 3) =>
        Work.FTS.PressureOn.laplaceTrace (fun y => (V y) j) x * (W x) j) := by
  have hVj : Continuous (fun x : EuclideanSpace ℝ (Fin 3) => (V x) j) :=
    ((contDiff_coord V hV j) 0).continuous
  have hWjc : HasCompactSupport (fun x : EuclideanSpace ℝ (Fin 3) => (W x) j) :=
    hasCompactSupport_coord W hWc j
  have hWj : Continuous (fun x : EuclideanSpace ℝ (Fin 3) => (W x) j) :=
    ((contDiff_coord W hW j) 0).continuous
  have hΔWj : Continuous
      (Work.FTS.PressureOn.laplaceTrace (fun y : EuclideanSpace ℝ (Fin 3) => (W y) j)) :=
    continuous_laplaceTrace_coord W hW j
  have hΔWjc : HasCompactSupport
      (Work.FTS.PressureOn.laplaceTrace (fun y : EuclideanSpace ℝ (Fin 3) => (W y) j)) :=
    hasCompactSupport_laplaceTrace_coord W hWc j
  have hΔVj : Continuous
      (Work.FTS.PressureOn.laplaceTrace (fun y : EuclideanSpace ℝ (Fin 3) => (V y) j)) :=
    continuous_laplaceTrace_coord V hV j
  constructor
  · refine (hVj.mul hΔWj).integrable_of_hasCompactSupport ?_
    exact hΔWjc.mul_left (f := fun x : EuclideanSpace ℝ (Fin 3) => (V x) j)
  · refine (hΔVj.mul hWj).integrable_of_hasCompactSupport ?_
    exact hWjc.mul_left (f := fun x : EuclideanSpace ℝ (Fin 3) =>
      Work.FTS.PressureOn.laplaceTrace (fun y => (V y) j) x)

end Work.FTS.PressureOn.Auxiliary
end
-- ===== merged: Submission.Work.FTS.PressureOn.Auxiliary.tendsto_tail_heatKernel =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The heat kernel escapes every ball as `t → 0⁺`

For `δ > 0` the mass of the heat kernel `γ_t z = (4πt)^{-3/2} exp (-‖z‖²/(4t))` on `ℝ³` outside
the ball of radius `δ` tends to `0` as `t → 0⁺`: the kernel concentrates at the origin.

The pointwise input is the exact split of the exponent

  `γ_t z = 2^{3/2} γ_{2t} z · exp (-‖z‖²/(8t))`,

so for `‖z‖ ≥ δ`

  `γ_t z ≤ 2^{3/2} exp (-δ²/(8t)) · γ_{2t} z`.

Integrating over the tail and using the normalisation `∫ γ_{2t} = 1`
(`Work.FTS.PressureOn.Auxiliary.integral_heatKernel`) gives

  `∫_{‖z‖ ≥ δ} γ_t ≤ 2^{3/2} exp (-δ²/(8t))`,

and `exp (-δ²/(8t)) → 0` because `δ²/(8t) → +∞` as `t → 0⁺`.
-/

open MeasureTheory Set Filter Topology
open scoped Topology

namespace Work.FTS.PressureOn.Auxiliary

noncomputable section







/-- The heat kernel is integrable at positive times (its mass is `1`). -/
private lemma integrable_heatKernel_prv {t : ℝ} (ht : 0 < t) : Integrable (heatKernel t) := by
  by_contra hf
  have h := integral_heatKernel t ht
  rw [integral_undef hf] at h
  exact one_ne_zero h.symm


end

end Work.FTS.PressureOn.Auxiliary
end
-- ===== merged: Submission.Work.FTS.PressureOn.Connect.biotSavart_uniform_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.Connect

/-- **A uniform-in-time bound for the Biot–Savart field of a bounded, uniformly supported family
of vorticities.**  If all the slices `ω(·,s)`, `s ∈ [0,S]`, are bounded by `M ≥ 0` and vanish off
the closed ball of radius `R`, then there is a single constant `B ≥ 0` bounding
`‖biotSavart (ω(·,s)) x‖` for *all* `s ∈ [0,S]` and *all* `x ∈ ℝ³`.

The point is that the explicit estimate `Work.FTS.PressureOn.biotSavartDecayExplicit` supplies a
constant depending only on `M` and on the radius — never on the slice — so it can be used
simultaneously for every `s`.  Since the statement does not assume `0 ≤ R`, the radius is first
replaced by `R' = max R 0`, which only enlarges the support; the constant is then
`3 M R' (1 + 4R'²)`, and the weight `(1 + ‖x‖²)⁻¹` is dropped because it is `≤ 1`. -/
theorem biotSavart_uniform_bound {ω : Work.FTS.PressureOn.R3 → ℝ → Work.FTS.PressureOn.R3}
    {S M R : ℝ} (hM : 0 ≤ M) (hbdd : ∀ s ∈ Set.Icc 0 S, ∀ x, ‖ω x s‖ ≤ M)
    (hsupp : ∀ s ∈ Set.Icc 0 S, ∀ x, ω x s ≠ 0 → ‖x‖ ≤ R) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s ∈ Set.Icc 0 S, ∀ x,
      ‖Work.LWP.biotSavart (fun y => ω y s) x‖ ≤ B := by
  -- Step 0: replace the radius `R` by `R' = max R 0 ≥ 0`; this only enlarges the support.
  set R' : ℝ := max R 0 with hR'def
  have hR' : 0 ≤ R' := le_max_right R 0
  have hRR' : R ≤ R' := le_max_left R 0
  refine ⟨3 * M * R' * (1 + 4 * R' ^ 2), by positivity, ?_⟩
  intro s hs x
  have hg : ∀ y, ‖ω y s‖ ≤ M := fun y => hbdd s hs y
  have hsup' : ∀ y, ω y s ≠ 0 → y ∈ Metric.closedBall (0 : Work.LWP.R3) R' := by
    intro y hy
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    exact le_trans (hsupp s hs y hy) hRR'
  -- the explicit estimate, with a constant independent of the slice `s`
  have hb := biotSavartDecayExplicit hR' hM hg hsup' x
  refine hb.trans ?_
  have hden : (1 : ℝ) ≤ 1 + ‖x‖ ^ 2 := by nlinarith [sq_nonneg ‖x‖]
  have hC : (0 : ℝ) ≤ 3 * M * R' * (1 + 4 * R' ^ 2) := by positivity
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 1 + ‖x‖ ^ 2)]
  nlinarith [hC, hden, sq_nonneg ‖x‖]

end Work.FTS.PressureOn.Connect
end
-- ===== merged: Submission.Work.FTS.PressureOn.EulerAssembly =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set MeasureTheory Gradient InnerProductSpace
open Work.FTS.Physical (physVel)
open scoped Topology NNReal ENNReal Matrix

set_option autoImplicit false

namespace Work.FTS.PressureOn

/-- **The scalar potential of the reconstruction**, as a space-time field: the design's `q`,
`q x t = pressurePotential (lamb u ω · t) x` with `u = physVel ω`. -/
noncomputable def potOn (ω : R3 → ℝ → R3) : R3 → ℝ → ℝ :=
  fun x t => pressurePotential (lamb (physVel ω) ω · t) x

/-- `pressureOn ω = -‖u·‖²/2 - q`: the reconstructed pressure in terms of `potOn`. -/
theorem pressureOn_eq (ω : R3 → ℝ → R3) :
    pressureOn ω = fun x t => -(‖physVel ω x t‖ ^ 2 / 2) - potOn ω x t := by
  funext x t
  rw [pressureOn_apply, potOn]
  rfl

/-- The gradient of `-(a) - b`. -/
theorem gradient_neg_sub {a b : R3 → ℝ} {x : R3} (ha : DifferentiableAt ℝ a x)
    (hb : DifferentiableAt ℝ b x) :
    gradient (fun y => -(a y) - b y) x = -(gradient a x) - gradient b x := by
  apply (toDual ℝ R3).injective
  rw [toDual_gradient, map_sub, map_neg, toDual_gradient, toDual_gradient]
  rw [show (fun y : R3 => -(a y) - b y) = (-a) - b from rfl]
  rw [fderiv_sub ha.neg hb, fderiv_neg]

/-- **From the Weyl step to `spaceGrad`.**  If (`weyl_pair`'s output) the slice of `q` has
`HasFDerivAt` with functional `innerSL ℝ (∂_t u - u×ω)`, then the spatial gradient of `q` is
`∂_t u - u×ω`. -/
theorem spaceGrad_potOn {ω : R3 → ℝ → R3} {x : R3} {t : ℝ}
    (hgq : HasFDerivAt (potOn ω · t)
      (innerSL ℝ (timeDeriv (physVel ω) x t - crossVec (physVel ω x t) (ω x t))) x) :
    spaceGrad (potOn ω) x t = timeDeriv (physVel ω) x t - crossVec (physVel ω x t) (ω x t) := by
  refine Work.FTS.Physical.spaceGrad_eq_of_inner_eq (fun y => ?_)
  have h1 : inner ℝ (spaceGrad (potOn ω) x t) y = fderiv ℝ (potOn ω · t) x y := by
    rw [Work.FTS.Physical.fderiv_eq_innerSL_spaceGrad (potOn ω) x t]
    rfl
  rw [h1, hgq.fderiv]
  rfl

/-- **The spatial gradient of the reconstructed pressure.**  `∇p = -∇(‖u‖²/2) - ∇q`. -/
theorem spaceGrad_pressureOn {ω : R3 → ℝ → R3} {x : R3} {t : ℝ}
    (hsq : DifferentiableAt ℝ (fun y => ‖physVel ω y t‖ ^ 2 / 2) x)
    (hq : DifferentiableAt ℝ (potOn ω · t) x)
    (hgq : HasFDerivAt (potOn ω · t)
      (innerSL ℝ (timeDeriv (physVel ω) x t - crossVec (physVel ω x t) (ω x t))) x) :
    spaceGrad (pressureOn ω) x t
      = -(gradient (fun y => ‖physVel ω y t‖ ^ 2 / 2) x)
        - (timeDeriv (physVel ω) x t - crossVec (physVel ω x t) (ω x t)) := by
  have hslice : (fun y => pressureOn ω y t)
      = fun y => -(‖physVel ω y t‖ ^ 2 / 2) - potOn ω y t := by
    funext y
    rw [pressureOn_apply, potOn]
    rfl
  have hgrad := gradient_neg_sub (a := fun y => ‖physVel ω y t‖ ^ 2 / 2)
    (b := fun y => potOn ω y t) hsq hq
  have hpot : spaceGrad (potOn ω) x t = gradient (fun y => potOn ω y t) x := rfl
  rw [spaceGrad, hslice, hgrad, ← hpot]
  exact congrArg (fun v => -(gradient (fun y => ‖physVel ω y t‖ ^ 2 / 2) x) - v)
    (spaceGrad_potOn hgq)

/-- **Step 5: the Euler equation for the reconstructed pressure.**  Given the pointwise vector
identity for `u = physVel ω` (from `C¹` in space), the gradient identity `∇q = ∂_t u - u×ω`
(Step 4, i.e. `weyl_pair` for the pair `(q, ∂_t u - u×ω)`) and the differentiability of the two
pieces, the pressure `p = pressureOn ω` satisfies `∂_t u + (u·∇)u + ∇p = 0`. -/
theorem euler_eq_of_gradient {ω : R3 → ℝ → R3} {x : R3} {t : ℝ}
    (hu : HasFDerivAt (fun y => physVel ω y t)
      (fderiv ℝ (fun y => physVel ω y t) x) x)
    (hcurl : ∀ z, vorticity (fun y => physVel ω y t) z = ω z t)
    (hsq : DifferentiableAt ℝ (fun y => ‖physVel ω y t‖ ^ 2 / 2) x)
    (hq : DifferentiableAt ℝ (potOn ω · t) x)
    (hgq : HasFDerivAt (potOn ω · t)
      (innerSL ℝ (timeDeriv (physVel ω) x t - crossVec (physVel ω x t) (ω x t))) x) :
    timeDeriv (physVel ω) x t + directionalDeriv (physVel ω) (physVel ω) x t
      + spaceGrad (pressureOn ω) x t = 0 := by
  have hp := spaceGrad_pressureOn hsq hq hgq
  have hmv := materialDeriv_eq_gradient_sub_cross hu
  rw [hcurl x] at hmv
  -- hmv : fderiv u x (u x) = ∇(‖u‖²/2) x - u×ω
  have hsq' : gradient (fun y => ‖physVel ω y t‖ ^ 2 / 2) x
      = fderiv ℝ (fun y => physVel ω y t) x (physVel ω x t)
        + crossVec (physVel ω x t) (ω x t) := sub_eq_iff_eq_add.mp hmv.symm
  rw [hp, hsq']
  show timeDeriv (physVel ω) x t + fderiv ℝ (fun y => physVel ω y t) x (physVel ω x t)
      + (-(fderiv ℝ (fun y => physVel ω y t) x (physVel ω x t)
            + crossVec (physVel ω x t) (ω x t))
          - (timeDeriv (physVel ω) x t - crossVec (physVel ω x t) (ω x t))) = 0
  abel

end Work.FTS.PressureOn
end
-- ===== merged: Submission.Work.FTS.PressureOn.MollAux.Dpair_convolution =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.MollAux

open MeasureTheory

/-- The divergence of a compactly supported field is compactly supported: off `tsupport f` the
field is locally zero, hence so is its derivative, hence so is the trace. -/
lemma hasCompactSupport_div (f : R3 → R3) (hfc : HasCompactSupport f) :
    HasCompactSupport (fun y => FiniteTimeSingularity.div f y) := by
  refine hfc.mono' fun y hy => ?_
  by_contra hx
  rw [Function.mem_support] at hy
  exact hy (Auxiliary.div_eq_zero_of_notMem_tsupport hx)

theorem Dpair_convolution (q : EuclideanSpace ℝ (Fin 3) → ℝ)
    (Φ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (ρ : EuclideanSpace ℝ (Fin 3) → ℝ) (f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (hρ : ∀ n : ℕ, ContDiff ℝ n ρ) (hρc : HasCompactSupport ρ) (hρeven : ∀ z, ρ (-z) = ρ z)
    (hf : ∀ n : ℕ, ContDiff ℝ n f) (hfc : HasCompactSupport f)
    (hq : Continuous q) (hΦ : Continuous Φ) :
    Work.FTS.PressureOn.Dpair q Φ
        (MeasureTheory.convolution ρ f (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume)
      = Work.FTS.PressureOn.Dpair
          (MeasureTheory.convolution ρ q (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume)
          (MeasureTheory.convolution ρ Φ (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume) f := by
  have hρ' : Continuous ρ := (hρ 0).continuous
  have hf' : Continuous f := (hf 0).continuous
  have hdiv_cont : Continuous fun y => FiniteTimeSingularity.div f y :=
    Work.FTS.PressureOn.continuous_div_of_contDiff (hf 1)
  have hdiv_cs : HasCompactSupport fun y => FiniteTimeSingularity.div f y :=
    hasCompactSupport_div f hfc
  -- the four integrability side conditions for the Fubini steps
  have hα : MeasureTheory.Integrable (Function.uncurry fun (x t : R3) =>
      ρ t * inner ℝ (Φ x) (f (x - t))) (MeasureTheory.volume.prod MeasureTheory.volume) := by
    refine MeasureTheory.Integrable.mono'
      (Auxiliary.integrable_uncurry_mul_sub (fun x => ‖Φ x‖) (fun x => ‖f x‖) (fun t => |ρ t|)
        hΦ.norm hf'.norm hρ'.abs (hfc.comp_left (g := fun v : R3 => ‖v‖) (by simp))
        hρc.abs) ?_ ?_
    · have hcont : Continuous fun p : R3 × R3 =>
          ρ p.2 * inner ℝ (Φ p.1) (f (p.1 - p.2)) :=
        (hρ'.comp continuous_snd).mul
          ((hΦ.comp continuous_fst).inner (hf'.comp (continuous_fst.sub continuous_snd)))
      exact hcont.aestronglyMeasurable
    · filter_upwards with p
      calc ‖ρ p.2 * inner ℝ (Φ p.1) (f (p.1 - p.2))‖
          = |ρ p.2| * |inner ℝ (Φ p.1) (f (p.1 - p.2))| := by
            rw [Real.norm_eq_abs, abs_mul]
        _ ≤ |ρ p.2| * (‖Φ p.1‖ * ‖f (p.1 - p.2)‖) :=
            mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (abs_nonneg _)
        _ = |ρ p.2| * ‖Φ p.1‖ * ‖f (p.1 - p.2)‖ := by ring
  have hβ : MeasureTheory.Integrable (Function.uncurry fun (x t : R3) =>
      ρ t * inner ℝ (Φ (x - t)) (f x)) (MeasureTheory.volume.prod MeasureTheory.volume) := by
    refine MeasureTheory.Integrable.mono'
      (Auxiliary.integrable_uncurry_mul_sub_left (fun x => ‖f x‖) (fun x => ‖Φ x‖) (fun t => |ρ t|)
        hf'.norm hΦ.norm hρ'.abs (hfc.comp_left (g := fun v : R3 => ‖v‖) (by simp))
        hρc.abs) ?_ ?_
    · have hcont : Continuous fun p : R3 × R3 =>
          ρ p.2 * inner ℝ (Φ (p.1 - p.2)) (f p.1) :=
        (hρ'.comp continuous_snd).mul
          ((hΦ.comp (continuous_fst.sub continuous_snd)).inner (hf'.comp continuous_fst))
      exact hcont.aestronglyMeasurable
    · filter_upwards with p
      calc ‖ρ p.2 * inner ℝ (Φ (p.1 - p.2)) (f p.1)‖
          = |ρ p.2| * |inner ℝ (Φ (p.1 - p.2)) (f p.1)| := by
            rw [Real.norm_eq_abs, abs_mul]
        _ ≤ |ρ p.2| * (‖Φ (p.1 - p.2)‖ * ‖f p.1‖) :=
            mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (abs_nonneg _)
        _ = |ρ p.2| * ‖f p.1‖ * ‖Φ (p.1 - p.2)‖ := by ring
  have hγ : MeasureTheory.Integrable (Function.uncurry fun (x t : R3) =>
      q x * (ρ t * FiniteTimeSingularity.div f (x - t)))
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
    refine (Auxiliary.integrable_uncurry_mul_sub q (fun y => FiniteTimeSingularity.div f y) ρ
      hq hdiv_cont hρ' hdiv_cs hρc).congr ?_
    filter_upwards with p
    obtain ⟨x, t⟩ := p
    show ρ t * q x * FiniteTimeSingularity.div f (x - t)
        = q x * (ρ t * FiniteTimeSingularity.div f (x - t))
    ring
  have hδ : MeasureTheory.Integrable (Function.uncurry fun (x t : R3) =>
      (ρ t * q (x - t)) * FiniteTimeSingularity.div f x)
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
    refine (Auxiliary.integrable_uncurry_mul_sub_left (fun y => FiniteTimeSingularity.div f y) q ρ
      hdiv_cont hq hρ' hdiv_cs hρc).congr ?_
    filter_upwards with p
    obtain ⟨x, t⟩ := p
    show ρ t * FiniteTimeSingularity.div f x * q (x - t)
        = (ρ t * q (x - t)) * FiniteTimeSingularity.div f x
    ring
  rw [Work.FTS.PressureOn.Dpair, Work.FTS.PressureOn.Dpair]
  have h1 : ∫ x, inner ℝ (Φ x)
        (MeasureTheory.convolution ρ f (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume x)
      = ∫ x, inner ℝ
          (MeasureTheory.convolution ρ Φ (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume x)
          (f x) :=
    Auxiliary.integral_inner_convolution_eq Φ f ρ hΦ hf' hfc hρ' hρc hρeven hα hβ
  have h2 : ∫ x, q x * FiniteTimeSingularity.div
        (MeasureTheory.convolution ρ f (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume) x
      = ∫ x, (MeasureTheory.convolution ρ q (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume x)
          * FiniteTimeSingularity.div f x := by
    have hdiv := Auxiliary.div_convolution ρ f ((hρ 0).continuous.locallyIntegrable) (hf 1) hfc
    simp only [hdiv]
    exact Auxiliary.integral_mul_convolution_eq q (fun y => FiniteTimeSingularity.div f y) ρ
      hq hdiv_cont hdiv_cs hρ' hρc hρeven hγ hδ
  rw [h1, h2]

end Work.FTS.PressureOn.MollAux
end
-- ===== merged: Submission.Work.FTS.PressureOn.MollAux.Dpair_eq_integral_sub_gradient_of_smooth =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Dpair q Φ ψ = ∫ ⟪Φ − ∇q, ψ⟫` for smooth data

`Work.FTS.PressureOn.Dpair` is defined as

  `Dpair q Φ f = ∫ x, ⟪Φ x, f x⟫ + ∫ x, q x * div f x`,

i.e. the pairing `⟨Φ − ∇q, f⟩` of the distribution `D := Φ − ∇q` against `f` in the sense of
Schwartz distributions.  The present lemma identifies it, for `q` smooth and `ψ` a smooth
compactly supported test field, with the ordinary integral of `⟪Φ − ∇q, ψ⟫`.

The proof is one integration by parts, `∫ q · div ψ = −∫ ⟪∇q, ψ⟫`
(`Auxiliary.integral_mul_div_eq_neg_inner_gradient`, which is the divergence theorem applied to
`q • ψ`), combined with the linearity of the integral:

  `Dpair q Φ ψ = ∫ ⟪Φ, ψ⟫ + ∫ q · div ψ = ∫ ⟪Φ, ψ⟫ − ∫ ⟪∇q, ψ⟫ = ∫ ⟪Φ − ∇q, ψ⟫`.
-/

namespace Work.FTS.PressureOn.MollAux

open MeasureTheory Filter Set
open scoped Topology

theorem Dpair_eq_integral_sub_gradient_of_smooth
    (q : EuclideanSpace ℝ (Fin 3) → ℝ)
    (Φ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (hq : ∀ n : ℕ, ContDiff ℝ n q) (hΦ : Continuous Φ)
    (ψ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (hψ : ∀ n : ℕ, ContDiff ℝ n ψ) (hψc : HasCompactSupport ψ) :
    Work.FTS.PressureOn.Dpair q Φ ψ
      = ∫ x, inner ℝ (Φ x - gradient q x) (ψ x) := by
  -- `∇q` is continuous (indeed `C¹`)
  have hgrad : Continuous (fun x : EuclideanSpace ℝ (Fin 3) => gradient q x) :=
    (Work.FTS.PressureOn.Green.contDiff_gradient q (hq 2)).continuous
  -- anything paired with `ψ` against a field `G` is compactly supported
  have aux : ∀ (G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)),
      HasCompactSupport (fun x => inner ℝ (G x) (ψ x)) := by
    intro G
    apply HasCompactSupport.of_support_subset_isCompact hψc.isCompact
    intro x hx
    by_contra hx'
    exact hx (by simp only [image_eq_zero_of_notMem_tsupport hx', inner_zero_right])
  have hI1 : Integrable (fun x => inner ℝ (Φ x) (ψ x)) :=
    (hΦ.inner (hψ 0).continuous).integrable_of_hasCompactSupport (aux Φ)
  have hI2 : Integrable (fun x => inner ℝ (gradient q x) (ψ x)) :=
    (hgrad.inner (hψ 0).continuous).integrable_of_hasCompactSupport (aux (fun x => gradient q x))
  -- the integration by parts
  have hibp : ∫ x, q x * FiniteTimeSingularity.div ψ x
      = -∫ x, inner ℝ (gradient q x) (ψ x) :=
    Work.FTS.PressureOn.Auxiliary.integral_mul_div_eq_neg_inner_gradient q ψ hq hψ hψc
  -- linearity of the integral
  have key : (∫ x, inner ℝ (Φ x) (ψ x)) - ∫ x, inner ℝ (gradient q x) (ψ x)
      = ∫ x, inner ℝ (Φ x - gradient q x) (ψ x) := by
    rw [← integral_sub hI1 hI2]
    exact integral_congr_ae (Eventually.of_forall fun x => (inner_sub_left _ _ _).symm)
  rw [Work.FTS.PressureOn.Dpair_apply, hibp]
  linarith [key]

end Work.FTS.PressureOn.MollAux
end
-- ===== merged: Submission.Work.FTS.PressureOn.MollAux.laplaceTraceVec_smooth_compact =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.MollAux

theorem laplaceTraceVec_smooth_compact (W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (hW : ∀ n : ℕ, ContDiff ℝ n W) :
    (∀ n : ℕ, ContDiff ℝ n (Work.FTS.PressureOn.laplaceTraceVec W)) ∧
      (HasCompactSupport W → HasCompactSupport (Work.FTS.PressureOn.laplaceTraceVec W)) := by
  constructor
  · -- Smoothness: each coordinate of `laplaceTraceVec W` is `∂ᵢ∂ᵢ W · eᵢ`, the derivative of the
    -- `C^∞` slice `fun w => fderiv ℝ W w (e i)`, applied to the constant `e i`.
    intro m
    unfold Work.FTS.PressureOn.laplaceTraceVec
    refine ContDiff.sum fun i _ => ?_
    have h1 : ContDiff ℝ (m + 1)
        (fun w : EuclideanSpace ℝ (Fin 3) =>
          fderiv ℝ W w (FiniteTimeSingularity.e i)) :=
      ((hW (m + 2)).fderiv_right (m := m + 1)
        (by exact_mod_cast (show (m : ℕ) + 1 + 1 ≤ m + 2 by omega))).clm_apply contDiff_const
    have h3 : ContDiff ℝ m
        (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
          (fderiv ℝ (fun w : EuclideanSpace ℝ (Fin 3) =>
            fderiv ℝ W w (FiniteTimeSingularity.e i)) p.1) p.2) :=
      h1.contDiff_fderiv_apply (m := m)
        (by exact_mod_cast (show (m : ℕ) + 1 ≤ m + 1 by omega))
    exact h3.comp (contDiff_id.prodMk contDiff_const)
  · -- Compact support: the support of the Laplacian trace is contained in `tsupport W`.
    intro hWc
    exact HasCompactSupport.of_support_subset_isCompact hWc.isCompact
      (Work.FTS.PressureOn.Green.support_laplaceTraceVec_subset W)

end Work.FTS.PressureOn.MollAux
end
-- ===== merged: Submission.Work.FTS.PressureOn.MollAux.moll_tendsto =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Filter Set
open scoped Topology Pointwise

namespace Work.FTS.PressureOn.MollAux

theorem moll_tendsto (q : EuclideanSpace ℝ (Fin 3) → ℝ)
    (Φ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (hq : Continuous q) (hΦ : Continuous Φ)
    (ψ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (hψ : ∀ n : ℕ, ContDiff ℝ n ψ) (hψc : HasCompactSupport ψ) :
    Filter.Tendsto (fun n : ℕ => Work.FTS.PressureOn.Dpair q Φ (Work.FTS.PressureOn.mollV n ψ))
      Filter.atTop (nhds (Work.FTS.PressureOn.Dpair q Φ ψ)) := by
  -- ## 0. Elementary facts about the mollifier kernel `rho n`
  have hρ_cd : ∀ n : ℕ, ContDiff ℝ 1 (Work.FTS.PressureOn.rho n) := fun n => (rho_props n).1 1
  have hρ_cs : ∀ n : ℕ, HasCompactSupport (Work.FTS.PressureOn.rho n) := fun n => (rho_props n).2.1
  have hρ_one : ∀ n : ℕ, ∫ z, Work.FTS.PressureOn.rho n z = 1 := fun n => (rho_props n).2.2.1
  have hρ_nonneg : ∀ n z, 0 ≤ Work.FTS.PressureOn.rho n z := fun n => (rho_props n).2.2.2.1
  have hρ_int : ∀ n : ℕ,
      MeasureTheory.Integrable (Work.FTS.PressureOn.rho n) MeasureTheory.volume := fun n =>
    ContDiffBump.integrable_normed (Work.FTS.PressureOn.bump n) (μ := MeasureTheory.volume)
  have hρ_supp : ∀ n z, Work.FTS.PressureOn.rho n z ≠ 0 → ‖z‖ ≤ 1 := by
    intro n z hz
    have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have := Nat.cast_nonneg (α := ℝ) n
      linarith
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by linarith
    have hle : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
      calc (1 : ℝ) / ((n : ℝ) + 1) ≤ ((n : ℝ) + 1) / ((n : ℝ) + 1) :=
            div_le_div_of_nonneg_right hn (le_of_lt hpos)
        _ = 1 := div_self (ne_of_gt hpos)
    exact le_trans ((rho_props n).2.2.2.2.2.1 z hz) hle
  have hρ_rOut : Filter.Tendsto (fun n : ℕ => (Work.FTS.PressureOn.bump n).rOut)
      Filter.atTop (nhds 0) := (rho_props 0).2.2.2.2.2.2
  -- ## 1. The compact set containing all the relevant supports
  set K : Set (EuclideanSpace ℝ (Fin 3)) :=
    tsupport ψ + Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) (1 : ℝ) with hKdef
  have hKc : IsCompact K := by
    rw [hKdef]
    exact hψc.isCompact.add (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1)
  have htsuppK : tsupport ψ ⊆ K := by
    rw [hKdef]
    exact fun x hx => Set.mem_add.mpr ⟨x, hx, 0, by simp [Metric.mem_closedBall], by simp⟩
  -- ## 2. Bounds: `‖ψ‖`, `‖div ψ‖`, and the bounds of `q`, `Φ` on `K`
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ y, ‖ψ y‖ ≤ M := by
    obtain ⟨C, hC⟩ := hψc.isCompact.exists_bound_of_continuousOn (hψ 0).continuous.continuousOn
    refine ⟨max C 0, fun y => ?_⟩
    by_cases hy : y ∈ tsupport ψ
    · exact le_trans (hC y hy) (le_max_left _ _)
    · rw [image_eq_zero_of_notMem_tsupport hy, norm_zero]
      exact le_max_right _ _
  have hM0 : 0 ≤ M := le_trans (norm_nonneg (ψ 0)) (hM 0)
  have hdivψ_cont : Continuous (fun y => FiniteTimeSingularity.div ψ y) := by
    rw [funext (Work.FTS.PressureOn.div_eq_sum_single ψ)]
    fun_prop
  have hdivψ_cs : HasCompactSupport (fun y => FiniteTimeSingularity.div ψ y) := by
    refine HasCompactSupport.intro (K := tsupport ψ) hψc.isCompact ?_
    intro y hy
    exact Auxiliary.div_eq_zero_of_notMem_tsupport hy
  obtain ⟨Vd, hVd⟩ : ∃ Vd : ℝ, ∀ y, ‖FiniteTimeSingularity.div ψ y‖ ≤ Vd := by
    obtain ⟨C, hC⟩ := hψc.isCompact.exists_bound_of_continuousOn hdivψ_cont.continuousOn
    refine ⟨max C 0, fun y => ?_⟩
    by_cases hy : y ∈ tsupport ψ
    · exact le_trans (hC y hy) (le_max_left _ _)
    · rw [Auxiliary.div_eq_zero_of_notMem_tsupport hy, norm_zero]
      exact le_max_right _ _
  have hVd0 : 0 ≤ Vd := le_trans (norm_nonneg _) (hVd 0)
  obtain ⟨DΦ₀, hDΦ₀⟩ : ∃ D : ℝ, ∀ x ∈ K, ‖Φ x‖ ≤ D :=
    hKc.exists_bound_of_continuousOn hΦ.continuousOn
  have hDΦ : ∀ x ∈ K, ‖Φ x‖ ≤ max DΦ₀ 0 := fun x hx =>
    le_trans (hDΦ₀ x hx) (le_max_left _ _)
  have hDΦ0 : 0 ≤ max DΦ₀ 0 := le_max_right _ _
  obtain ⟨Dq₀, hDq₀⟩ : ∃ D : ℝ, ∀ x ∈ K, |q x| ≤ D := by
    obtain ⟨D, hD⟩ := hKc.exists_bound_of_continuousOn hq.continuousOn
    exact ⟨D, fun x hx => by rw [← Real.norm_eq_abs]; exact hD x hx⟩
  have hDq : ∀ x ∈ K, |q x| ≤ max Dq₀ 0 := fun x hx =>
    le_trans (hDq₀ x hx) (le_max_left _ _)
  have hDq0 : 0 ≤ max Dq₀ 0 := le_max_right _ _
  -- ## 3. Support and bound of `mollV n ψ`
  have hmollVsupp : ∀ n : ℕ, Function.support (Work.FTS.PressureOn.mollV n ψ) ⊆ K := by
    intro n x hx
    by_contra hxK
    refine hx ((MollAux.mollV_support_bound n ψ M hM).1 x (fun b hb => ?_))
    by_contra hle
    push_neg at hle
    exact hxK (Set.mem_add.mpr ⟨b, hb, x - b, by
      rw [Metric.mem_closedBall, dist_zero_right]
      rwa [dist_eq_norm] at hle, by rw [add_sub_cancel]⟩)
  have hmollVbound : ∀ n x, ‖Work.FTS.PressureOn.mollV n ψ x‖ ≤ M := by
    intro n x
    simpa [Work.FTS.PressureOn.mollV] using
      MollAux.convolution_norm_le (Work.FTS.PressureOn.rho n) ψ (hρ_nonneg n) (hρ_int n)
        (hρ_one n) (hψ 0).continuous hψc M hM x
  have hmollV_cont : ∀ n : ℕ, Continuous (Work.FTS.PressureOn.mollV n ψ) := fun n =>
    (hρ_cs n).continuous_convolution_left (L := ContinuousLinearMap.lsmul ℝ ℝ)
      ((hρ_cd n).continuous) ((hψ 0).continuous.locallyIntegrable)
  -- ## 4. `div (mollV n ψ) = rho n ⋆ div ψ`, its support and its bound
  have hdiv_mollV : ∀ n : ℕ, ∀ x : EuclideanSpace ℝ (Fin 3),
      FiniteTimeSingularity.div (Work.FTS.PressureOn.mollV n ψ) x =
        MeasureTheory.convolution (Work.FTS.PressureOn.rho n)
          (fun y => FiniteTimeSingularity.div ψ y) (ContinuousLinearMap.lsmul ℝ ℝ)
          MeasureTheory.volume x := by
    intro n x
    simpa [Work.FTS.PressureOn.mollV] using
      Auxiliary.div_convolution (Work.FTS.PressureOn.rho n) ψ
        ((hρ_cd n).continuous.locallyIntegrable) (hψ 1) hψc x
  have hdivmollVsupp : ∀ n : ℕ,
      Function.support (fun x => FiniteTimeSingularity.div (Work.FTS.PressureOn.mollV n ψ) x)
        ⊆ K := by
    intro n x hx
    rw [Function.mem_support] at hx
    have hx' : FiniteTimeSingularity.div (Work.FTS.PressureOn.mollV n ψ) x ≠ 0 := hx
    rw [hdiv_mollV n x] at hx'
    have hmem := support_convolution_subset (μ := MeasureTheory.volume)
      (L := ContinuousLinearMap.lsmul ℝ ℝ) (f := Work.FTS.PressureOn.rho n)
      (g := fun y => FiniteTimeSingularity.div ψ y) hx'
    obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_add.mp hmem
    rw [hKdef]
    refine Set.mem_add.mpr ⟨b, ?_, a, ?_, ?_⟩
    · by_contra hbt
      exact hb (Auxiliary.div_eq_zero_of_notMem_tsupport hbt)
    · rw [Metric.mem_closedBall, dist_zero_right]
      exact hρ_supp n a ha
    · rw [add_comm]
      exact hab
  have hdivmollVbound : ∀ n x,
      ‖FiniteTimeSingularity.div (Work.FTS.PressureOn.mollV n ψ) x‖ ≤ Vd := by
    intro n x
    rw [hdiv_mollV n x, MeasureTheory.convolution_def]
    calc ‖∫ t, (ContinuousLinearMap.lsmul ℝ ℝ) (Work.FTS.PressureOn.rho n t)
            (FiniteTimeSingularity.div ψ (x - t))‖
        ≤ ∫ t, ‖(ContinuousLinearMap.lsmul ℝ ℝ) (Work.FTS.PressureOn.rho n t)
            (FiniteTimeSingularity.div ψ (x - t))‖ :=
          MeasureTheory.norm_integral_le_integral_norm _
      _ = ∫ t, Work.FTS.PressureOn.rho n t * ‖FiniteTimeSingularity.div ψ (x - t)‖ := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards with t
          rw [ContinuousLinearMap.lsmul_apply, norm_smul, Real.norm_eq_abs,
            abs_of_nonneg (hρ_nonneg n t)]
      _ ≤ ∫ t, Work.FTS.PressureOn.rho n t * Vd := by
          refine MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun t => ?_)
            ((hρ_int n).mul_const Vd) (Filter.Eventually.of_forall fun t => ?_)
          · exact mul_nonneg (hρ_nonneg n t) (norm_nonneg _)
          · exact mul_le_mul_of_nonneg_left (hVd (x - t)) (hρ_nonneg n t)
      _ = (∫ t, Work.FTS.PressureOn.rho n t) * Vd := MeasureTheory.integral_mul_const Vd _
      _ = Vd := by rw [hρ_one n, one_mul]
  have hdivmollV_cont : ∀ n : ℕ,
      Continuous (fun x => FiniteTimeSingularity.div (Work.FTS.PressureOn.mollV n ψ) x) := by
    intro n
    refine Continuous.congr ?_ (fun x => (hdiv_mollV n x).symm)
    exact HasCompactSupport.continuous_convolution_right (L := ContinuousLinearMap.lsmul ℝ ℝ)
      hdivψ_cs ((hρ_cd n).continuous.locallyIntegrable) hdivψ_cont
  -- ## 5. The two integrals converge
  -- ### 5a. the inner-product term
  have hA : Filter.Tendsto
      (fun n : ℕ => ∫ x, inner ℝ (Φ x) (Work.FTS.PressureOn.mollV n ψ x))
      Filter.atTop (nhds (∫ x, inner ℝ (Φ x) (ψ x))) := by
    refine Auxiliary.tendsto_integral_of_compact_support
      (F := fun n x => inner ℝ (Φ x) (Work.FTS.PressureOn.mollV n ψ x))
      (f := fun x => inner ℝ (Φ x) (ψ x)) (K := K) (C := max DΦ₀ 0 * M) hKc
      ?_ ?_ ?_ ?_ ?_ ?_
    · exact mul_nonneg hDΦ0 hM0
    · intro n
      exact (hΦ.inner (hmollV_cont n)).aestronglyMeasurable
    · intro n x hx
      by_contra hxK
      refine hx ?_
      have hzero : Work.FTS.PressureOn.mollV n ψ x = 0 := by
        by_contra hne
        exact hxK (hmollVsupp n hne)
      simp [hzero]
    · intro x hx
      by_contra hxK
      refine hx ?_
      have hzero : ψ x = 0 := by
        by_contra hne
        exact hxK (htsuppK (subset_tsupport ψ hne))
      simp [hzero]
    · intro n x
      by_cases hxK : x ∈ K
      · exact le_trans (norm_inner_le_norm _ _)
          (mul_le_mul (hDΦ x hxK) (hmollVbound n x) (norm_nonneg _) hDΦ0)
      · have hzero : Work.FTS.PressureOn.mollV n ψ x = 0 := by
          by_contra hne
          exact hxK (hmollVsupp n hne)
        simp [hzero]
        exact mul_nonneg hDΦ0 hM0
    · intro x
      refine Tendsto.inner tendsto_const_nhds ?_
      have h := ContDiffBump.convolution_tendsto_right_of_continuous (μ := MeasureTheory.volume)
        hρ_rOut ((hψ 0).continuous) x
      simpa [Work.FTS.PressureOn.mollV, Work.FTS.PressureOn.rho] using h
  -- ### 5b. the divergence term
  have hB : Filter.Tendsto
      (fun n : ℕ => ∫ x, q x * FiniteTimeSingularity.div (Work.FTS.PressureOn.mollV n ψ) x)
      Filter.atTop (nhds (∫ x, q x * FiniteTimeSingularity.div ψ x)) := by
    refine Auxiliary.tendsto_integral_of_compact_support
      (F := fun n x => q x * FiniteTimeSingularity.div (Work.FTS.PressureOn.mollV n ψ) x)
      (f := fun x => q x * FiniteTimeSingularity.div ψ x) (K := K) (C := max Dq₀ 0 * Vd) hKc
      ?_ ?_ ?_ ?_ ?_ ?_
    · exact mul_nonneg hDq0 hVd0
    · intro n
      exact (hq.mul (hdivmollV_cont n)).aestronglyMeasurable
    · intro n x hx
      by_contra hxK
      refine hx ?_
      have hzero : FiniteTimeSingularity.div (Work.FTS.PressureOn.mollV n ψ) x = 0 := by
        by_contra hne
        exact hxK (hdivmollVsupp n hne)
      simp [hzero]
    · intro x hx
      by_contra hxK
      refine hx ?_
      have hzero : FiniteTimeSingularity.div ψ x = 0 := by
        by_contra hne
        exact hxK (htsuppK (by
          by_contra hb
          exact hne (Auxiliary.div_eq_zero_of_notMem_tsupport hb)))
      simp [hzero]
    · intro n x
      by_cases hxK : x ∈ K
      · rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hDq x hxK)
          (by rw [← Real.norm_eq_abs]; exact hdivmollVbound n x) (abs_nonneg _) hDq0
      · have hzero : FiniteTimeSingularity.div (Work.FTS.PressureOn.mollV n ψ) x = 0 := by
          by_contra hne
          exact hxK (hdivmollVsupp n hne)
        simp [hzero]
        exact mul_nonneg hDq0 hVd0
    · intro x
      refine Tendsto.const_mul (q x) ?_
      have h := ContDiffBump.convolution_tendsto_right_of_continuous (μ := MeasureTheory.volume)
        hρ_rOut hdivψ_cont x
      have heq : (fun n : ℕ => FiniteTimeSingularity.div (Work.FTS.PressureOn.mollV n ψ) x)
          = fun n : ℕ => MeasureTheory.convolution
              ((Work.FTS.PressureOn.bump n).normed MeasureTheory.volume)
              (fun y => FiniteTimeSingularity.div ψ y) (ContinuousLinearMap.lsmul ℝ ℝ)
              MeasureTheory.volume x := by
        funext n
        rw [hdiv_mollV n x]
        rfl
      rw [heq]
      exact h
  -- ## 6. Assembly
  have hsum := hA.add hB
  simpa [Work.FTS.PressureOn.Dpair] using hsum

end Work.FTS.PressureOn.MollAux
end
-- ===== merged: Submission.Work.FTS.PressureOn.PoissonAux.KI.massKernel_peak =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Topology

namespace Work.FTS.PressureOn.PoissonAux.KI

/-!
# Peaking of the mass kernel against a continuous test function

The mass kernel `massKernel 1` is (up to normalisation) the second radial derivative of the
cutoff profile `rhoProfile 1` divided by `4π‖x‖`; it vanishes off the *fixed* annulus
`1 ≤ ‖x‖ ≤ √2` (`massKernel_eq_zero_of_lt`) and is integrable (`integrable_massKernel`).
Consequently, for any *continuous* `Ψ`, the rescaled argument `ε • x` tends to `0` uniformly
on the (fixed, compact) support of `massKernel 1`, and

`∫ x, massKernel 1 x * Ψ (ε • x) → Ψ 0 * ∫ x, massKernel 1 x`  as `ε → 0`.

The proof below is the classical `ε`-`δ` estimate: write the difference of the two sides as
`∫ x, massKernel 1 x * (Ψ (ε • x) - Ψ 0)`, bound it by
`(∫ x, |massKernel 1 x|) · sup_{x ∈ supp} |Ψ (ε • x) - Ψ 0|`, and let `ε → 0`.
No `C¹`-regularity of `Ψ` is needed (compare `tendsto_integral_massKernel_mul`, where the
shrinking support forces a first-order Taylor bound), because the support of the kernel here
does not shrink with `ε`; this is exactly what makes `∫ massKernel 1 · Ψ (ε • ·)` peak at
`ε = 0`.
-/

/-- The two-sided (`ε → 0`) version of `massKernel_peak`: the mass kernel `massKernel 1`,
which lives on the fixed annulus `1 ≤ ‖x‖ ≤ √2`, peaks against every continuous `Ψ`. -/
theorem massKernel_peak_aux {Ψ : R3 → ℝ} (hΨ : Continuous Ψ) :
    Filter.Tendsto (fun ε : ℝ => ∫ x : R3, massKernel 1 x * Ψ (ε • x))
      (nhds (0 : ℝ)) (nhds (Ψ 0 * ∫ x : R3, massKernel 1 x)) := by
  have hgint : Integrable (fun x : R3 => massKernel 1 x) := integrable_massKernel 1 one_pos
  -- `massKernel 1` is supported in the fixed ball of radius `√2`
  have hsupp : ∀ x : R3, massKernel 1 x ≠ 0 → ‖x‖ ≤ Real.sqrt 2 := by
    intro x hx
    by_contra h
    rw [not_le] at h
    exact hx (massKernel_eq_zero_of_lt one_pos (by simpa using h))
  -- the total variation of the kernel
  set D : ℝ := ∫ x : R3, |massKernel 1 x| with hD
  have hDnn : 0 ≤ D := integral_nonneg fun x => abs_nonneg _
  have hD1 : 0 < D + 1 := by linarith
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  rw [Metric.tendsto_nhds]
  intro δ hδ
  -- continuity of `Ψ` at the origin, with the weight `(D + 1)⁻¹`
  have hcont : ContinuousAt Ψ 0 := hΨ.continuousAt
  obtain ⟨η, hηpos, hη⟩ :=
    Metric.continuousAt_iff.mp hcont (δ / (D + 1)) (by positivity)
  -- only `ε` with `|ε| √2 < η` matter
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (div_pos hηpos hsqrt)] with ε hε
  have hηε : |ε| * Real.sqrt 2 < η := by
    have h1 : |ε| < η / Real.sqrt 2 := by
      simpa [Metric.mem_ball, Real.dist_eq] using hε
    calc |ε| * Real.sqrt 2 < (η / Real.sqrt 2) * Real.sqrt 2 :=
          mul_lt_mul_of_pos_right h1 hsqrt
      _ = η := by rw [div_mul_cancel₀ _ (ne_of_gt hsqrt)]
  -- pointwise estimate: `|Ψ (ε • x) - Ψ 0|` is small wherever the kernel does not vanish
  have hpoint : ∀ x : R3,
      |massKernel 1 x * (Ψ (ε • x) - Ψ 0)| ≤ |massKernel 1 x| * (δ / (D + 1)) := by
    intro x
    by_cases hx : massKernel 1 x = 0
    · simp [hx]
    · have hxs : ‖x‖ ≤ Real.sqrt 2 := hsupp x hx
      have hnorm : ‖ε • x‖ < η := by
        rw [norm_smul, Real.norm_eq_abs]
        calc |ε| * ‖x‖ ≤ |ε| * Real.sqrt 2 := mul_le_mul_of_nonneg_left hxs (abs_nonneg ε)
          _ < η := hηε
      have hΨx : |Ψ (ε • x) - Ψ 0| ≤ δ / (D + 1) := le_of_lt (by
        have h := hη (x := ε • x) (by simpa [dist_eq_norm] using hnorm)
        rwa [Real.dist_eq] at h)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hΨx (abs_nonneg _)
  have hInt1 : Integrable (fun x : R3 => massKernel 1 x * Ψ (ε • x)) :=
    integrable_massKernel_mul 1 one_pos (hΨ.comp (continuous_const_smul ε))
  have hInt3 : Integrable (fun x : R3 => massKernel 1 x * (Ψ (ε • x) - Ψ 0)) :=
    integrable_massKernel_mul 1 one_pos
      ((hΨ.comp (continuous_const_smul ε)).sub continuous_const)
  -- split off the limit value `Ψ 0 * ∫ massKernel 1`
  have hsplit : ∫ x : R3, massKernel 1 x * (Ψ (ε • x) - Ψ 0)
      = (∫ x : R3, massKernel 1 x * Ψ (ε • x)) - Ψ 0 * ∫ x : R3, massKernel 1 x := by
    rw [show (∫ x : R3, massKernel 1 x * (Ψ (ε • x) - Ψ 0))
        = ∫ x : R3, (massKernel 1 x * Ψ (ε • x) - massKernel 1 x * Ψ 0) from
        integral_congr_ae (Eventually.of_forall fun x => by ring)]
    rw [integral_sub hInt1 (hgint.mul_const (Ψ 0)), integral_mul_const]
    ring
  have hbound : |∫ x : R3, massKernel 1 x * (Ψ (ε • x) - Ψ 0)| ≤ D * (δ / (D + 1)) := by
    have h1 : |∫ x : R3, massKernel 1 x * (Ψ (ε • x) - Ψ 0)|
        ≤ ∫ x : R3, |massKernel 1 x * (Ψ (ε • x) - Ψ 0)| := by
      simpa only [Real.norm_eq_abs] using
        norm_integral_le_integral_norm (fun x : R3 => massKernel 1 x * (Ψ (ε • x) - Ψ 0))
    have h2 : ∫ x : R3, |massKernel 1 x * (Ψ (ε • x) - Ψ 0)|
        ≤ ∫ x : R3, |massKernel 1 x| * (δ / (D + 1)) :=
      integral_mono_ae hInt3.abs (hgint.abs.mul_const _) (Eventually.of_forall hpoint)
    have h3 : ∫ x : R3, |massKernel 1 x| * (δ / (D + 1)) = D * (δ / (D + 1)) := by
      rw [integral_mul_const, ← hD]
    linarith [h1, h2, h3]
  have hlt : D * (δ / (D + 1)) < δ := by
    have hratio : D / (D + 1) < 1 := (div_lt_one hD1).mpr (by linarith)
    calc D * (δ / (D + 1)) = δ * (D / (D + 1)) := by ring
      _ < δ * 1 := mul_lt_mul_of_pos_left hratio hδ
      _ = δ := by ring
  rw [Real.dist_eq, ← hsplit]
  exact lt_of_le_of_lt hbound hlt

theorem massKernel_peak {Ψ : R3 → ℝ} (hΨ : Continuous Ψ) :
    Filter.Tendsto (fun ε : ℝ => ∫ x : R3, massKernel 1 x * Ψ (ε • x))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (Ψ 0 * ∫ x : R3, massKernel 1 x)) := by
  exact (massKernel_peak_aux hΨ).mono_left nhdsWithin_le_nhds

end Work.FTS.PressureOn.PoissonAux.KI
end
-- ===== merged: Submission.Work.FTS.PressureOn.PoissonAux.kernelGradAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter Topology
open scoped Topology

set_option autoImplicit false

namespace Work.FTS.PressureOn.PoissonAux

namespace kgiAux



/-! ## Regularity of `laplaceTrace` -/

/-- The first partial derivative of a `C³` function is `C²`. -/
theorem contDiff_two_fderiv_apply_e {u : R3 → ℝ} (hu : ContDiff ℝ 3 u) (i : Fin 3) :
    ContDiff ℝ 2 (fun x : R3 => fderiv ℝ u x (FiniteTimeSingularity.e i)) := by
  have h : ContDiff ℝ 2 (fun p : R3 × R3 => fderiv ℝ u p.1 p.2) :=
    ContDiff.contDiff_fderiv_apply hu (by norm_num)
  have h2 : ContDiff ℝ 2 (fun x : R3 => (x, FiniteTimeSingularity.e i)) := by
    have h3 : ContDiff ℝ 2 (fun x : R3 => ((x, (0 : R3)) : R3 × R3)) :=
      (ContinuousLinearMap.inl ℝ R3 R3).contDiff
    simpa using h3.add (contDiff_const (c := ((0 : R3), FiniteTimeSingularity.e i)))
  exact h.comp h2

/-- `laplaceTrace Ψ` is `C¹` when `Ψ` is smooth. -/
theorem contDiff_one_laplaceTrace {Ψ : R3 → ℝ} (hΨ : ∀ n : ℕ, ContDiff ℝ n Ψ) :
    ContDiff ℝ 1 (laplaceTrace Ψ) := by
  change ContDiff ℝ 1 (fun x : R3 => ∑ i : Fin 3, fderiv ℝ
    (fun w : R3 => fderiv ℝ Ψ w (FiniteTimeSingularity.e i)) x (FiniteTimeSingularity.e i))
  exact ContDiff.sum fun i _ =>
    contDiff_fderiv_apply_e (contDiff_two_fderiv_apply_e (hΨ 3) i) i

/-- The Laplacian of a compactly supported function is compactly supported. -/
theorem hasCompactSupport_laplaceTrace {Ψ : R3 → ℝ} (hcs : HasCompactSupport Ψ) :
    HasCompactSupport (laplaceTrace Ψ) := by
  refine hcs.mono' fun z hz => ?_
  by_contra hzt
  exact hz (Work.FTS.PressureOn.Green.laplaceTrace_eq_zero_of_notMem_tsupport hzt)

/-! ## Translation invariance of `laplaceTrace` -/

/-- `laplaceTrace` is invariant under translations of the argument. -/
theorem laplaceTrace_comp_add (g : R3 → ℝ) (a : R3) (z : R3) :
    laplaceTrace (fun z' : R3 => g (a + z')) z = laplaceTrace g (a + z) := by
  rw [laplaceTrace, laplaceTrace]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : (fun w : R3 => fderiv ℝ (fun z' : R3 => g (a + z')) w (FiniteTimeSingularity.e i))
      = fun w : R3 => fderiv ℝ g (a + w) (FiniteTimeSingularity.e i) := by
    funext w
    exact congrArg (fun L : R3 →L[ℝ] ℝ => L (FiniteTimeSingularity.e i))
      (fderiv_comp_add_left (𝕜 := ℝ) (f := g) (x := w) a)
  rw [h1]
  exact congrArg (fun L : R3 →L[ℝ] ℝ => L (FiniteTimeSingularity.e i))
    (fderiv_comp_add_left (𝕜 := ℝ)
      (f := fun u : R3 => fderiv ℝ g u (FiniteTimeSingularity.e i)) (x := z) a)

/-- The gradient of a translated function at the origin is the gradient at the centre. -/
theorem gradient_comp_add_const (g : R3 → ℝ) (a : R3) :
    gradient (fun z : R3 => g (a + z)) 0 = gradient g a := by
  rw [gradient, gradient, fderiv_comp_add_left (𝕜 := ℝ) (f := g) (x := 0) a, add_zero]

/-! ## Integrability of the Newtonian gradient -/

/-- `x ^ (-2) = (x ^ 2)⁻¹` for `x ≥ 0`. -/
theorem rpow_neg_two {x : ℝ} (hx : 0 ≤ x) : x ^ (-2 : ℝ) = (x ^ 2)⁻¹ := by
  rw [Real.rpow_neg hx (2 : ℝ), Real.rpow_two]

/-- The pointwise size of `newtonGrad`: `‖∇N(z)‖ = (4π)⁻¹‖z‖^{-2}`. -/
theorem norm_newtonGrad_rpow (z : R3) :
    ‖newtonGrad z‖ = (4 * Real.pi)⁻¹ * ‖z‖ ^ (-2 : ℝ) := by
  rw [norm_newtonGrad]
  rcases eq_or_lt_of_le (norm_nonneg z) with h | h
  · have hz0 : z = 0 := norm_eq_zero.mp h.symm
    subst hz0
    simp [Real.zero_rpow (by norm_num : (-2 : ℝ) ≠ 0)]
  · rw [rpow_neg_two (le_of_lt h)]
    have h2 : (‖z‖ ^ (3 : ℕ))⁻¹ * ‖z‖ = (‖z‖ ^ 2)⁻¹ := by
      have hne : ‖z‖ ≠ 0 := ne_of_gt h
      field_simp
    rw [show (4 * Real.pi)⁻¹ * (‖z‖ ^ (3 : ℕ))⁻¹ * ‖z‖
        = (4 * Real.pi)⁻¹ * ((‖z‖ ^ (3 : ℕ))⁻¹ * ‖z‖) by ring, h2]

/-- A compactly supported function is supported inside some open ball. -/
theorem exists_ball_tsupport_subset {f : R3 → ℝ} (hcs : HasCompactSupport f) :
    ∃ R : ℝ, tsupport f ⊆ Metric.ball 0 R := by
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : R3)).mp hcs.isBounded
  refine ⟨r + 1, fun z hz => ?_⟩
  have h1 := hr hz
  rw [Metric.mem_closedBall, dist_zero_right] at h1
  rw [Metric.mem_ball, dist_zero_right]
  linarith

/-- **The Newtonian gradient times a compactly supported continuous function is integrable.** -/
theorem integrable_smul_newtonGrad {f : R3 → ℝ} (hf : Continuous f)
    (hcs : HasCompactSupport f) :
    Integrable (fun z : R3 => f z • newtonGrad z) := by
  obtain ⟨C, hC⟩ := hcs.exists_bound_of_continuousOn hf.continuousOn
  have hCglob : ∀ z : R3, ‖f z‖ ≤ max C 0 := by
    intro z
    by_cases hz : z ∈ tsupport f
    · exact le_trans (hC z hz) (le_max_left _ _)
    · rw [image_eq_zero_of_notMem_tsupport hz, norm_zero]
      exact le_max_right _ _
  obtain ⟨R, hR⟩ := exists_ball_tsupport_subset hcs
  have hsubset : Function.support (fun z : R3 => f z • newtonGrad z) ⊆ Metric.ball 0 R := by
    intro z hz
    rw [Function.mem_support] at hz
    by_contra h
    exact hz (by
      rw [image_eq_zero_of_notMem_tsupport (fun hz' => h (hR hz')), zero_smul])
  have hmeas : AEStronglyMeasurable (fun z : R3 => f z • newtonGrad z) volume := by
    have hfun : (fun z : R3 => f z • newtonGrad z)
        = fun z : R3 => (-(f z * (4 * Real.pi * ‖z‖ ^ 3)⁻¹)) • z := by
      funext z
      rw [newtonGrad_apply, mul_inv]
      simp only [neg_smul, smul_neg, smul_smul]
      ring_nf
    rw [hfun]
    exact (((hf.measurable.mul
      (((continuous_norm.pow 3).const_mul (4 * Real.pi)).measurable.inv)).neg).smul
        measurable_id).aestronglyMeasurable
  refine (MeasureTheory.integrableOn_iff_integrable_of_support_subset hsubset).mp ?_
  refine MeasureTheory.integrableOn_ball_of_norm_le_rpow (μ := volume) (F := R3)
    (C := max C 0 * (4 * Real.pi)⁻¹) (α := 2) (r := R) ?_ ?_ ?_ hmeas
  · rw [show Module.finrank ℝ R3 = 3 from by simp]
    norm_num
  · rw [show Module.finrank ℝ R3 = 3 from by simp]
    norm_num
  · filter_upwards with z
    have hnn : (0 : ℝ) ≤ (4 * Real.pi)⁻¹ * ‖z‖ ^ (-2 : ℝ) :=
      mul_nonneg (by positivity) (Real.rpow_nonneg (norm_nonneg z) _)
    rw [norm_smul, norm_newtonGrad_rpow]
    calc ‖f z‖ * ((4 * Real.pi)⁻¹ * ‖z‖ ^ (-2 : ℝ))
        = (4 * Real.pi)⁻¹ * ‖z‖ ^ (-2 : ℝ) * ‖f z‖ := by ring
      _ ≤ (4 * Real.pi)⁻¹ * ‖z‖ ^ (-2 : ℝ) * max C 0 :=
            mul_le_mul_of_nonneg_left (hCglob z) hnn
      _ = max C 0 * (4 * Real.pi)⁻¹ * ‖z‖ ^ (-2 : ℝ) := by ring

/-! ## Integration by parts against the cut-off kernel -/

/-- The origin is a null set of `ℝ³`. -/
theorem ae_ne_zero_volume : ∀ᵐ z ∂(volume : Measure R3), z ≠ 0 := by
  rw [MeasureTheory.ae_iff]
  have h : {z : R3 | ¬ z ≠ 0} = {0} := by
    ext z
    simp
  rw [h]
  exact measure_singleton 0


end kgiAux

end Work.FTS.PressureOn.PoissonAux
end
-- ===== merged: Submission.Work.FTS.PressureOn.Weyl.dpair_laplaceTraceVec_eq_zero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS.PressureOn.Weyl

/-- Compact support of `div V` from that of `V` (the divergence only sees the first derivatives,
which are supported in `tsupport V`). -/
theorem hasCompactSupport_div (V : Work.FTS.PressureOn.R3 → Work.FTS.PressureOn.R3)
    (hV : HasCompactSupport V) : HasCompactSupport (FiniteTimeSingularity.div V) := by
  have hfun : FiniteTimeSingularity.div V
      = Work.FTS.PressureOn.Auxiliary.divTraceCLM ∘ (fderiv ℝ V) := by
    funext x
    exact Work.FTS.PressureOn.Auxiliary.div_eq_divTraceCLM V x
  rw [hfun]
  exact (hV.fderiv (𝕜 := ℝ)).comp_left (map_zero _)

/-- Compact support of `vorticity V` from that of `V`. -/
theorem hasCompactSupport_vorticity (V : Work.FTS.PressureOn.R3 → Work.FTS.PressureOn.R3)
    (hV : HasCompactSupport V) : HasCompactSupport (FiniteTimeSingularity.vorticity V) := by
  have hfun : FiniteTimeSingularity.vorticity V
      = Work.FTS.Physical.Pressure.curlCLM ∘ (fderiv ℝ V) := by
    funext x
    exact Work.FTS.Physical.Pressure.vorticity_eq_curlCLM V x
  rw [hfun]
  exact (hV.fderiv (𝕜 := ℝ)).comp_left (map_zero _)

/-- **Integrability of a pairing against a compactly supported continuous field.**
If `Φ` is locally integrable and `g` is continuous with compact support, then `x ↦ ⟨Φ x, g x⟩` is
integrable.  This is the absolute-convergence input that the requested statement is missing. -/
theorem integrable_inner_of_hasCompactSupport {Φ g : Work.FTS.PressureOn.R3 → Work.FTS.PressureOn.R3}
    (hΦ : LocallyIntegrable Φ) (hg : Continuous g) (hgc : HasCompactSupport g) :
    Integrable (fun x => inner ℝ (Φ x) (g x)) := by
  have hK : IsCompact (tsupport g) := hgc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hg.continuousOn
  have hCnn : (0 : ℝ) ≤ max C 1 := le_trans zero_le_one (le_max_right C 1)
  have hbound : ∀ x : Work.FTS.PressureOn.R3, ‖g x‖ ≤ max C 1 := by
    intro x
    by_cases hx : x ∈ tsupport g
    · exact le_trans (hC x hx) (le_max_left _ _)
    · rw [image_eq_zero_of_notMem_tsupport hx, norm_zero]
      exact hCnn
  have hint : Integrable (fun x => inner ℝ (Φ x) (g x)) (volume.restrict (tsupport g)) := by
    have h1 : Integrable (fun x => max C 1 * ‖Φ x‖) (volume.restrict (tsupport g)) :=
      (hΦ.integrableOn_isCompact hK).norm.const_mul _
    refine h1.mono' ((hΦ.aestronglyMeasurable.inner hg.aestronglyMeasurable).restrict) ?_
    filter_upwards with x
    calc ‖inner ℝ (Φ x) (g x)‖ ≤ ‖Φ x‖ * ‖g x‖ := norm_inner_le_norm _ _
      _ ≤ ‖Φ x‖ * max C 1 := by
          exact mul_le_mul_of_nonneg_left (hbound x) (norm_nonneg _)
      _ = max C 1 * ‖Φ x‖ := mul_comm _ _
  refine (integrableOn_iff_integrable_of_support_subset ?_).mp hint
  intro x hx
  by_contra hx'
  exact hx (by
    have hzero : g x = 0 := image_eq_zero_of_notMem_tsupport hx'
    simp [hzero])

/-- **The corrected M2 step**: the requested statement with the necessary hypothesis that `Φ` be
locally integrable (equivalently, that the pairings against smooth compactly supported fields be
absolutely convergent).  In the intended application `Φ = ∂_t u - u × ω` is continuous, so this
holds. -/
theorem dpair_laplaceTraceVec_eq_zero_of_locallyIntegrable
    (q : Work.FTS.PressureOn.R3 → ℝ)
    (Φ : Work.FTS.PressureOn.R3 → Work.FTS.PressureOn.R3)
    (hΦ : LocallyIntegrable Φ)
    (hdiv : ∀ φ : Work.FTS.PressureOn.R3 → ℝ, (∀ n : ℕ, ContDiff ℝ n φ) → HasCompactSupport φ →
      ∫ x, inner ℝ (Φ x) (gradient φ x)
        = -∫ x, q x * Work.FTS.PressureOn.laplaceTrace φ x)
    (hcurl : ∀ ψ : Work.FTS.PressureOn.R3 → Work.FTS.PressureOn.R3,
      (∀ n : ℕ, ContDiff ℝ n ψ) → HasCompactSupport ψ →
      ∫ x, inner ℝ (Φ x) (FiniteTimeSingularity.vorticity ψ x) = 0)
    (W : Work.FTS.PressureOn.R3 → Work.FTS.PressureOn.R3)
    (hW : ∀ n : ℕ, ContDiff ℝ n W) (hWc : HasCompactSupport W) :
    (∫ x, inner ℝ (Φ x) (Work.FTS.PressureOn.laplaceTraceVec W x))
      + ∫ x, q x * FiniteTimeSingularity.div (Work.FTS.PressureOn.laplaceTraceVec W) x = 0 := by
  have hWo : ∀ n : ℕ, ContDiff ℝ n (FiniteTimeSingularity.div W) :=
    Work.FTS.PressureOn.Auxiliary.contDiff_div W hW
  have hWoc : HasCompactSupport (FiniteTimeSingularity.div W) := hasCompactSupport_div W hWc
  have hvort : ∀ n : ℕ, ContDiff ℝ n (FiniteTimeSingularity.vorticity W) :=
    Work.FTS.PressureOn.Auxiliary.contDiff_vorticity W hW
  have hvc : HasCompactSupport (FiniteTimeSingularity.vorticity W) :=
    hasCompactSupport_vorticity W hWc
  -- the two weak identities at the relevant test objects
  have hA := hdiv (FiniteTimeSingularity.div W) hWo hWoc
  have hB := hcurl (FiniteTimeSingularity.vorticity W) hvort hvc
  -- absolute convergence of the two pairings
  have hAint : Integrable
      (fun x => inner ℝ (Φ x) (gradient (FiniteTimeSingularity.div W) x)) :=
    integrable_inner_of_hasCompactSupport hΦ
      ((Green.contDiff_gradient (FiniteTimeSingularity.div W) (hWo 2)).continuous)
      ((hWoc.fderiv (𝕜 := ℝ)).comp_left (map_zero _))
  have hBint : Integrable
      (fun x => inner ℝ (Φ x) (FiniteTimeSingularity.vorticity
        (FiniteTimeSingularity.vorticity W) x)) :=
    integrable_inner_of_hasCompactSupport hΦ
      ((Work.FTS.PressureOn.Auxiliary.contDiff_vorticity _ hvort 1).continuous)
      (hasCompactSupport_vorticity _ hvc)
  -- the two pointwise identities
  have hpt : ∀ x, inner ℝ (Φ x) (Work.FTS.PressureOn.laplaceTraceVec W x)
      = inner ℝ (Φ x) (gradient (FiniteTimeSingularity.div W) x)
        - inner ℝ (Φ x) (FiniteTimeSingularity.vorticity
            (FiniteTimeSingularity.vorticity W) x) := by
    intro x
    rw [Work.FTS.PressureOn.Auxiliary.laplaceTraceVec_identity W hW x, inner_sub_right]
  have hdiv_eq : ∀ x, FiniteTimeSingularity.div (Work.FTS.PressureOn.laplaceTraceVec W) x
      = Work.FTS.PressureOn.laplaceTrace (FiniteTimeSingularity.div W) x :=
    fun x => Work.FTS.PressureOn.Auxiliary.div_laplaceTraceVec W hW x
  have hfirst : (∫ x, inner ℝ (Φ x) (Work.FTS.PressureOn.laplaceTraceVec W x))
      = (∫ x, inner ℝ (Φ x) (gradient (FiniteTimeSingularity.div W) x))
        - ∫ x, inner ℝ (Φ x) (FiniteTimeSingularity.vorticity
            (FiniteTimeSingularity.vorticity W) x) := by
    rw [show (fun x => inner ℝ (Φ x) (Work.FTS.PressureOn.laplaceTraceVec W x))
        = fun x => inner ℝ (Φ x) (gradient (FiniteTimeSingularity.div W) x)
            - inner ℝ (Φ x) (FiniteTimeSingularity.vorticity
                (FiniteTimeSingularity.vorticity W) x) from funext hpt]
    exact integral_sub hAint hBint
  have hsecond : (∫ x, q x * FiniteTimeSingularity.div
        (Work.FTS.PressureOn.laplaceTraceVec W) x)
      = ∫ x, q x * Work.FTS.PressureOn.laplaceTrace (FiniteTimeSingularity.div W) x := by
    refine integral_congr_ae ?_
    filter_upwards with x
    rw [hdiv_eq x]
  rw [hfirst, hsecond, hA, hB]
  ring

/-- **M2, in the form consumed by the assembly.**  The version above with the local-integrability
hypothesis replaced by the *continuity* of `Φ` and `q` (which is what holds for the pair
`(q, Φ) = (pressurePotential (u × ω), ∂_t u - u × ω)` of `weyl_pair`).  Continuity implies local
integrability, so this is an immediate corollary of
`dpair_laplaceTraceVec_eq_zero_of_locallyIntegrable`. -/
theorem dpair_laplaceTraceVec_eq_zero
    (q : Work.FTS.PressureOn.R3 → ℝ)
    (Φ : Work.FTS.PressureOn.R3 → Work.FTS.PressureOn.R3)
    (hq : Continuous q) (hΦ : Continuous Φ)
    (hdiv : ∀ φ : Work.FTS.PressureOn.R3 → ℝ, (∀ n : ℕ, ContDiff ℝ n φ) → HasCompactSupport φ →
      ∫ x, inner ℝ (Φ x) (gradient φ x)
        = -∫ x, q x * Work.FTS.PressureOn.laplaceTrace φ x)
    (hcurl : ∀ ψ : Work.FTS.PressureOn.R3 → Work.FTS.PressureOn.R3,
      (∀ n : ℕ, ContDiff ℝ n ψ) → HasCompactSupport ψ →
      ∫ x, inner ℝ (Φ x) (FiniteTimeSingularity.vorticity ψ x) = 0)
    (W : Work.FTS.PressureOn.R3 → Work.FTS.PressureOn.R3)
    (hW : ∀ n : ℕ, ContDiff ℝ n W) (hWc : HasCompactSupport W) :
    (∫ x, inner ℝ (Φ x) (Work.FTS.PressureOn.laplaceTraceVec W x))
      + ∫ x, q x * FiniteTimeSingularity.div (Work.FTS.PressureOn.laplaceTraceVec W) x = 0 :=
  dpair_laplaceTraceVec_eq_zero_of_locallyIntegrable q Φ hΦ.locallyIntegrable hdiv hcurl W hW hWc

end Work.FTS.PressureOn.Weyl
end
-- ===== merged: Submission.Work.FTS.PressureOn.integral_div_eq_zero_of_offPlanes =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn

theorem integral_div_eq_zero_of_offPlanes {W : R3 → R3}
    (hWcont : Continuous W) (hWcs : HasCompactSupport W)
    (hWdiff : ∀ x, x 0 ≠ 0 → x 2 ≠ 0 → HasFDerivAt W (fderiv ℝ W x) x)
    (hWint : MeasureTheory.Integrable (fun x => FiniteTimeSingularity.div W x)) :
    ∫ x, FiniteTimeSingularity.div W x = 0 := by
  -- a ball containing the support, off which `W` and its divergence vanish
  obtain ⟨R, hRpos, hR⟩ := exists_norm_supp_bound W hWcs
  -- transport to the coordinate space `Fin 3 → ℝ`
  have hHcont : Continuous (transport W) := continuous_transport W hWcont
  have hHdiff : ∀ x : Fin 3 → ℝ, x 0 ≠ 0 → x 2 ≠ 0 →
      HasFDerivAt (transport W) (fderivTransport W x) x := by
    intro x hx0 hx2
    refine hasFDerivAt_transport ?_
    exact hWdiff (toLpCLM x) (by simpa using hx0) (by simpa using hx2)
  have hHint : MeasureTheory.Integrable
      (fun x : Fin 3 → ℝ => ∑ i, fderivTransport W x (Pi.single i (1 : ℝ)) i) := by
    refine (integrable_div_transport W hWint).congr ?_
    filter_upwards with x
    exact (sum_fderivTransport W x).symm
  have hHsupp : ∀ x : Fin 3 → ℝ, R ≤ ‖x‖ → transport W x = 0 := by
    intro x hx
    have h1 : R ≤ ‖toLpCLM x‖ := le_trans hx (norm_le_norm_toLp x)
    change WithLp.ofLp (W (toLpCLM x)) = 0
    rw [(hR (toLpCLM x) h1).1]
    exact WithLp.ofLp_zero 2
  have hH'supp : ∀ x : Fin 3 → ℝ, R ≤ ‖x‖ →
      (∑ i, fderivTransport W x (Pi.single i (1 : ℝ)) i) = 0 := by
    intro x hx
    have h1 : R ≤ ‖toLpCLM x‖ := le_trans hx (norm_le_norm_toLp x)
    rw [sum_fderivTransport]
    exact (hR (toLpCLM x) h1).2
  -- the divergence theorem on the coordinate space, off the two planes
  have hcore := integral_trace_eq_zero_of_diff_off_planes (transport W) (fderivTransport W)
    hHcont hHdiff hHint R hRpos hHsupp hH'supp
  -- transport back to `ℝ³`
  have hEq : (∫ x : Fin 3 → ℝ, FiniteTimeSingularity.div W (toLpCLM x))
      = ∫ x : Fin 3 → ℝ, ∑ i, fderivTransport W x (Pi.single i (1 : ℝ)) i :=
    MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun x => (sum_fderivTransport W x).symm)
  rw [← integral_div_transport W, hEq]
  exact hcore

end Work.FTS.PressureOn
end

/-
# `∫ ‖z‖⁻¹ Δψ = -4π ψ(0)`

The fundamental-solution identity for the Laplacian in `ℝ³`, on the class of smooth compactly
supported `ψ`:

  `∫ z, ‖z‖⁻¹ * Δψ z = -4π ψ 0`.

## Proof strategy

Let `χ_ε z = fcut (‖z‖/ε)` be the smooth cutoff which is `0` for `‖z‖ ≤ ε` and `1` for
`‖z‖ ≥ 2ε`, and put `φ_ε z = χ_ε z / ‖z‖`, a smooth function equal to `‖z‖⁻¹` outside the ball of
radius `2ε`.

* **Self-adjointness** (`laplacian_pairing_comm`): `∫ φ_ε Δψ = ∫ ψ Δφ_ε`.
* **The Laplacian of `φ_ε`** (`laplacian_phiCut`): `Δφ_ε z = ρ''(‖z‖/ε)/(ε²‖z‖)` where `ρ = fcut`.
* Substituting `z = ε w` turns the right-hand side into `∫ w, ψ (εw) ρ''(‖w‖)/‖w‖ dw`, whose
  limit as `ε → 0⁺` is `ψ 0 · ∫ w, ρ''(‖w‖)/‖w‖ dw = ψ 0 · (-4π)`.
* The left-hand side converges to `∫ z, ‖z‖⁻¹ Δψ z` by dominated convergence.

The value `∫ w, ρ''(‖w‖)/‖w‖ dw = -4π` and the dominated convergence for the left-hand side are
supplied by the companion modules `integral_deriv_deriv_fcut_over_norm` and
`tendsto_fcut_div_mul`.
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.FTS.BSSwirl.Defs
import Submission.Work.FTS.BSSwirl.inv_norm_cut
import Submission.Work.FTS.BSSwirl.laplacian_radial
import Submission.Work.FTS.BSSwirl.deriv_deriv_fcut_div_add
import Submission.Work.FTS.BSSwirl.integral_deriv_deriv_fcut_over_norm
import Submission.Work.FTS.BSSwirl.tendsto_fcut_div_mul

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

lemma phiCut_eq_inv_of_le {ε : ℝ} (hε : 0 < ε) {z : R3} (hz : 2 * ε ≤ ‖z‖) :
    phiCut ε z = ‖z‖⁻¹ := by
  have h : (2 : ℝ) ≤ ‖z‖ / ε := by rw [le_div_iff₀ hε]; linarith
  rw [phiCut, fcut_of_two_le h, one_div]

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

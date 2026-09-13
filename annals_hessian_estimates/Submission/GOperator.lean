/-
The operator `G(M) = tr M − √(2 + ‖M‖²)` and its relation to the `σ₂`-equation on the positive
branch.

For a symmetric operator `T` one has `G(T) = 0 ↔ σ₂(T) = 1 ∧ tr T > 0`; moreover `G` is monotone
with respect to the Loewner (quadratic form) order, so that a classical solution of
`σ₂(D²u) = 1` with `Δu > 0` is a viscosity solution of `-G(D²u) = 0`.  This is the form of the
equation in which Savin's small perturbation theorem applies.
-/
import ChallengeDeps
import Submission.Viscosity
import Submission.DoublingMovingCenter
import Submission.Commons.Analysis.Calculus.FDeriv.trace_adjoint_comp_eq_coord_sq_sum
import Submission.Commons.Analysis.Calculus.FDeriv.fderiv_fderiv_nonpos_of_localMax
import Submission.Commons.Analysis.Calculus.FDeriv.fderiv_fderiv_nonneg_of_localMin
import Submission.Commons.Analysis.Calculus.FDeriv.hessianWithin_eq_hessian
import Submission.Commons.Analysis.Calculus.FDeriv.hessianWithin_sub_of_mem_nhds
import Submission.Commons.Analysis.Calculus.FDeriv.isSymmetric_hessianWithin
import Submission.Commons.Analysis.Calculus.FDeriv.laplacian_eq_trace_hessian
import Submission.Commons.Analysis.Sigma2.trace_sq_eq_two_add_trace_comp
import Submission.Commons.Analysis.Sigma2.trace_adjoint_sq_eq_trace_sq
import Submission.Commons.Analysis.Sigma2.sigma2_eigen_eq_trace_invariants
import Submission.Commons.Analysis.Trace.trace_sub_sqrt_mono

open HessianEstimates
open Commons.Analysis.Sigma2
open Commons.Analysis.Calculus.FDeriv
open Commons.Analysis.Trace
open Laplacian Metric MeasureTheory Filter
open scoped BigOperators InnerProductSpace RealInnerProductSpace Topology ENNReal

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Submission

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

/-- The operator `G(M) = tr M − √(2 + ‖M‖²)`, where `‖M‖² = tr (M* ∘ M)` is the square of the
Frobenius norm.  On the positive branch this is the equation satisfied by smooth solutions of
`σ₂(D²u) = 1` with `Δu > 0`. -/
noncomputable def Gop (M : ℝ⁴ →L[ℝ] ℝ⁴) : ℝ :=
  LinearMap.trace ℝ ℝ⁴ (M.toLinearMap)
    - Real.sqrt (2 + LinearMap.trace ℝ ℝ⁴ (M.toLinearMap.adjoint ∘ₗ M))

theorem Gop_eq_coord (M : ℝ⁴ →L[ℝ] ℝ⁴) :
    Gop M = (∑ i : Fin 4, ⟪stdB i, M (stdB i)⟫)
      - Real.sqrt (2 + ∑ i : Fin 4, ∑ j : Fin 4, ⟪M (stdB i), stdB j⟫ ^ 2) := by
  unfold Gop
  rw [LinearMap.trace_eq_sum_inner M.toLinearMap stdB,
    trace_adjoint_comp_eq_coord_sq_sum stdB]
  simp

theorem continuous_Gop : Continuous Gop := by
  rw [show Gop = fun M : ℝ⁴ →L[ℝ] ℝ⁴ => (∑ i : Fin 4, ⟪stdB i, M (stdB i)⟫)
      - Real.sqrt (2 + ∑ i : Fin 4, ∑ j : Fin 4, ⟪M (stdB i), stdB j⟫ ^ 2) from
    funext Gop_eq_coord]
  refine Continuous.sub ?_ ?_
  · exact continuous_finsetSum _ (fun i _ =>
      continuous_const.inner ((ContinuousLinearMap.apply ℝ ℝ⁴ (stdB i)).continuous))
  · refine Real.continuous_sqrt.comp (continuous_const.add ?_)
    exact continuous_finsetSum _ (fun i _ => continuous_finsetSum _ (fun j _ =>
      ((((ContinuousLinearMap.apply ℝ ℝ⁴ (stdB i)).continuous).inner
        continuous_const).pow 2)))

private theorem sum_lt_eq_sum_ite {n : ℕ} (f : Fin n → ℝ) (j : Fin n) :
    (∑ i < j, f i) = ∑ i : Fin n, (if i < j then f i else 0) := by
  show ∑ i ∈ Finset.Iio j, f i = _
  rw [show Finset.Iio j = Finset.univ.filter (fun x => x < j) from by
        ext x; simp [Finset.mem_Iio], Finset.sum_filter]

/-- `G(T) = 0` for a symmetric operator `T` is equivalent to `σ₂(T) = 1` together with the
positivity of the trace. -/
theorem Gop_eq_zero_iff {T : ℝ⁴ →L[ℝ] ℝ⁴} (hT : T.IsSymmetric) :
    Gop T = 0 ↔ σ₂ T = 1 ∧ 0 < LinearMap.trace ℝ ℝ⁴ (T.toLinearMap) := by
  have hpair_sigma : σ₂ T = ∑ j : Fin (Module.finrank ℝ ℝ⁴), ∑ i : Fin (Module.finrank ℝ ℝ⁴),
      if i < j then hT.eigenvalues rfl i * hT.eigenvalues rfl j else 0 := by
    rw [HessianEstimates.σ₂, dif_pos hT]
    exact Finset.sum_congr rfl (fun j _ => sum_lt_eq_sum_ite _ j)
  have htrT_nonneg : 0 ≤ LinearMap.trace ℝ ℝ⁴ (T.toLinearMap.adjoint ∘ₗ T.toLinearMap) := by
    rw [trace_adjoint_comp_eq_coord_sq_sum stdB]
    positivity
  constructor
  · intro h
    have htr : LinearMap.trace ℝ ℝ⁴ (T.toLinearMap)
        = Real.sqrt (2 + LinearMap.trace ℝ ℝ⁴ (T.toLinearMap.adjoint ∘ₗ T.toLinearMap)) := by
      have := h; unfold Gop at this; linarith
    have hpos : (0 : ℝ) ≤ 2 + LinearMap.trace ℝ ℝ⁴ (T.toLinearMap.adjoint ∘ₗ T.toLinearMap) := by
      linarith [htrT_nonneg]
    have hsq : (LinearMap.trace ℝ ℝ⁴ (T.toLinearMap)) ^ 2
        = 2 + LinearMap.trace ℝ ℝ⁴ (T.toLinearMap ∘ₗ T.toLinearMap) := by
      calc (LinearMap.trace ℝ ℝ⁴ (T.toLinearMap)) ^ 2
          = (Real.sqrt (2 + LinearMap.trace ℝ ℝ⁴
              (T.toLinearMap.adjoint ∘ₗ T.toLinearMap))) ^ 2 := by rw [htr]
        _ = 2 + LinearMap.trace ℝ ℝ⁴ (T.toLinearMap.adjoint ∘ₗ T.toLinearMap) :=
              Real.sq_sqrt hpos
        _ = 2 + LinearMap.trace ℝ ℝ⁴ (T.toLinearMap ∘ₗ T.toLinearMap) := by
              rw [trace_adjoint_sq_eq_trace_sq hT]
    have hinv := sigma2_eigen_eq_trace_invariants hT
    constructor
    · rw [hpair_sigma, hinv, hsq]
      ring
    · have h2 : (2 : ℝ) ≤ (LinearMap.trace ℝ ℝ⁴ (T.toLinearMap)) ^ 2 := by
        rw [hsq]
        have hnn := htrT_nonneg
        rw [trace_adjoint_sq_eq_trace_sq hT] at hnn
        linarith
      have h3 : 0 ≤ LinearMap.trace ℝ ℝ⁴ (T.toLinearMap) := by
        rw [htr]; exact Real.sqrt_nonneg _
      nlinarith
  · rintro ⟨hσ, htrpos⟩
    have hpair : (∑ j : Fin (Module.finrank ℝ ℝ⁴), ∑ i : Fin (Module.finrank ℝ ℝ⁴),
        if i < j then hT.eigenvalues rfl i * hT.eigenvalues rfl j else 0) = 1 := by
      rw [← hpair_sigma]; exact hσ
    have hsq := trace_sq_eq_two_add_trace_comp hT hpair
    rw [← trace_adjoint_sq_eq_trace_sq hT] at hsq
    have hsqrt : Real.sqrt (2 + LinearMap.trace ℝ ℝ⁴ (T.toLinearMap.adjoint ∘ₗ T.toLinearMap))
        = LinearMap.trace ℝ ℝ⁴ (T.toLinearMap) := by
      rw [← hsq, Real.sqrt_sq (le_of_lt htrpos)]
    unfold Gop
    rw [hsqrt, sub_self]

/-- For a smooth solution of `σ₂(D²u) = 1` with `Δu > 0`, the operator `G` vanishes on the
Hessian. -/
theorem Gop_hessian_eq_zero {u : ℝ⁴ → ℝ} {s : Set ℝ⁴} (hs : IsOpen s) {x : ℝ⁴} (hx : x ∈ s)
    (hu : ContDiffOn ℝ 2 u s) (hσ : σ₂ (H u s x) = 1) (hΔ : 0 < (Δ u) x) :
    Gop (H u s x) = 0 := by
  have hiff := Gop_eq_zero_iff (T := H u s x) (isSymmetric_hessianWithin hs hx hu)
  refine hiff.mpr ⟨hσ, ?_⟩
  have htr : (Δ u) x = LinearMap.trace ℝ ℝ⁴ ((H u s x).toLinearMap) :=
    laplacian_eq_trace_hessian hs hx hu (stdOrthonormalBasis ℝ ℝ⁴)
  linarith

/-- A classical (`C²`) solution of `σ₂(D²u) = 1` with `Δu > 0` on an open set is a viscosity
solution of `-G(D²u) = 0`.  This is the direction in which `σ₂`-solutions enter the viscosity
framework (used to apply the stability theorem to a converging sequence of classical
solutions). -/
theorem isViscSolution_negGop_of_classical {u : ℝ⁴ → ℝ} {s : Set ℝ⁴} (hs : IsOpen s)
    (hu : ContDiffOn ℝ 2 u s) (hσ : ∀ x ∈ s, σ₂ (H u s x) = 1) (hΔ : ∀ x ∈ s, 0 < (Δ u) x) :
    IsViscSolution (fun M => -Gop M) u s := by
  have hsym_u : ∀ x ∈ s, (HessOp u s x).IsSymmetric := fun x hx =>
    isSymmetric_hessianWithin hs hx hu
  have hsym_φ : ∀ (φ : ℝ⁴ → ℝ) (x : ℝ⁴), ContDiffOn ℝ 2 φ s → x ∈ s →
      (HessOp φ s x).IsSymmetric := fun φ x hφ hx => isSymmetric_hessianWithin hs hx hφ
  have hzero : ∀ x ∈ s, Gop (HessOp u s x) = 0 := fun x hx =>
    Gop_hessian_eq_zero hs hx hu (hσ x hx) (hΔ x hx)
  constructor
  · intro φ hφ x hx hloc
    have hmax : IsLocalMax (fun y => u y - φ y) x := by
      rw [IsLocalMax]
      rw [eventually_nhdsWithin_iff] at hloc
      filter_upwards [hloc, hs.mem_nhds hx] with y hy hys
      exact hy hys
    have hcd : ContDiffAt ℝ 2 (fun y => u y - φ y) x :=
      ((hu.contDiffWithinAt hx).sub (hφ.contDiffWithinAt hx)).contDiffAt (hs.mem_nhds hx)
    have hnonpos : ∀ v, (fderiv ℝ (fderiv ℝ (fun y => u y - φ y)) x) v v ≤ 0 :=
      fun v => fderiv_fderiv_nonpos_of_localMax hcd hmax v
    have hq : ∀ v, ⟪HessOp (fun y => u y - φ y) s x v, v⟫ ≤ 0 := by
      intro v
      have h1 : HessOp (fun y => u y - φ y) s x =
          InnerProductSpace.continuousLinearMapOfBilin
            (fderiv ℝ (fderiv ℝ (fun y => u y - φ y)) x) :=
        hessianWithin_eq_hessian (hs.mem_nhds hx)
      rw [h1, InnerProductSpace.continuousLinearMapOfBilin_apply]
      exact hnonpos v
    have hsubeq : HessOp (fun y => u y - φ y) s x = HessOp u s x - HessOp φ s x :=
      hessianWithin_sub_of_mem_nhds (hs.mem_nhds hx) (hu.contDiffWithinAt hx)
        (hφ.contDiffWithinAt hx)
    have hle : ∀ v, ⟪HessOp u s x v, v⟫ ≤ ⟪HessOp φ s x v, v⟫ := by
      intro v
      have h := hq v
      rw [hsubeq] at h
      simp only [sub_apply, inner_sub_left] at h
      linarith
    have hmono : Gop (HessOp u s x) ≤ Gop (HessOp φ s x) :=
      trace_sub_sqrt_mono (hsym_u x hx) (hsym_φ φ x hφ hx) hle
    have hz := hzero x hx
    change -(Gop (HessOp φ s x)) ≤ 0
    linarith
  · intro φ hφ x hx hloc
    have hmin : IsLocalMin (fun y => u y - φ y) x := by
      rw [IsLocalMin]
      rw [eventually_nhdsWithin_iff] at hloc
      filter_upwards [hloc, hs.mem_nhds hx] with y hy hys
      exact hy hys
    have hcd : ContDiffAt ℝ 2 (fun y => u y - φ y) x :=
      ((hu.contDiffWithinAt hx).sub (hφ.contDiffWithinAt hx)).contDiffAt (hs.mem_nhds hx)
    have hnonneg : ∀ v, 0 ≤ (fderiv ℝ (fderiv ℝ (fun y => u y - φ y)) x) v v :=
      fun v => fderiv_fderiv_nonneg_of_localMin hcd hmin v
    have hq : ∀ v, 0 ≤ ⟪HessOp (fun y => u y - φ y) s x v, v⟫ := by
      intro v
      have h1 : HessOp (fun y => u y - φ y) s x =
          InnerProductSpace.continuousLinearMapOfBilin
            (fderiv ℝ (fderiv ℝ (fun y => u y - φ y)) x) :=
        hessianWithin_eq_hessian (hs.mem_nhds hx)
      rw [h1, InnerProductSpace.continuousLinearMapOfBilin_apply]
      exact hnonneg v
    have hsubeq : HessOp (fun y => u y - φ y) s x = HessOp u s x - HessOp φ s x :=
      hessianWithin_sub_of_mem_nhds (hs.mem_nhds hx) (hu.contDiffWithinAt hx)
        (hφ.contDiffWithinAt hx)
    have hle : ∀ v, ⟪HessOp φ s x v, v⟫ ≤ ⟪HessOp u s x v, v⟫ := by
      intro v
      have h := hq v
      rw [hsubeq] at h
      simp only [sub_apply, inner_sub_left] at h
      linarith
    have hmono : Gop (HessOp φ s x) ≤ Gop (HessOp u s x) :=
      trace_sub_sqrt_mono (hsym_φ φ x hφ hx) (hsym_u x hx) hle
    have hz := hzero x hx
    change 0 ≤ -(Gop (HessOp φ s x))
    linarith


end Submission

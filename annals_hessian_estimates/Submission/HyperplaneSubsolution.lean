/-
A 2-convex function is a viscosity subsolution of the *degenerate* Laplacian
`L_e = tr((1 - e⊗e)D²) = Δ - D_ee` (i.e. of the Laplacian in the hyperplane `e^⊥`).

This is the algebraic step `Σ_{j≠i}D_jj u ≥ Δu - λ_max ≥ 0` of the appendix of Shankar--Yuan: at a
local maximum of `u - φ` the Hessian `M = D²φ(x)` satisfies `tr M ≥ 0` and `σ₂(M) ≥ 0`
(i.e. `M ∈ Γ₂`), and for `M ∈ Γ₂` in dimension four one has `⟨M e, e⟩ ≤ tr M` for every unit `e`.
-/
import Mathlib
import Submission.MasterEstimate
import Submission.AlexandrovInputs
import Submission.Viscosity
import Submission.Commons.Analysis.Sigma2.weighted_sum_le_sum
import Submission.Commons.Analysis.Sigma2.sigma2_nonneg_linearized_nonneg
import Submission.Commons.Analysis.Sigma2.trace_eq_sum_eigenvalues
import Submission.Commons.Analysis.Calculus.FDeriv.isSymmetric_hessianWithin
import Submission.Commons.Analysis.InnerProductSpace.eigen_basis_inner_apply

open HessianEstimates
open MeasureTheory Metric Set Filter Function
open scoped BigOperators ENNReal Topology RealInnerProductSpace InnerProductSpace

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Submission

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

/-- **A `2`-convex function is a viscosity subsolution of `L_e = tr((1 - e⊗e)D²)`.** -/
theorem isViscSubsolution_hyperplane {u : ℝ⁴ → ℝ} {s : Set ℝ⁴} (hs : IsOpen s)
    (h2 : IsTwoConvexOn u s) (e : ℝ⁴) (he : ‖e‖ = 1) :
    IsViscSubsolution (fun M => -(LinearMap.trace ℝ ℝ⁴ M.toLinearMap - ⟪M e, e⟫)) u s := by
  intro φ hφ x hx hmax
  obtain ⟨hΔ, hσ⟩ := h2
  have htr : 0 ≤ LinearMap.trace ℝ ℝ⁴ (HessOp φ s x).toLinearMap := by
    have h := hΔ φ hφ x hx hmax
    simp only [negTrace] at h
    linarith
  have hsig : 0 ≤ σ₂ (HessOp φ s x) := by
    have h := hσ φ hφ x hx hmax
    simpa using h
  have hsym : (HessOp φ s x).IsSymmetric :=
    Commons.Analysis.Calculus.FDeriv.isSymmetric_hessianWithin hs hx hφ
  rw [show (fun M => -((LinearMap.trace ℝ ℝ⁴) M.toLinearMap - ⟪M e, e⟫)) (HessOp φ s x)
      = -((LinearMap.trace ℝ ℝ⁴) (HessOp φ s x).toLinearMap - ⟪(HessOp φ s x) e, e⟫) from rfl, neg_nonpos, sub_nonneg]
  show ⟪HessOp φ s x e, e⟫ ≤ LinearMap.trace ℝ ℝ⁴ (HessOp φ s x).toLinearMap
  -- eigenvalues
  set v := hsym.eigenvectorBasis rfl with hv
  set lam := hsym.eigenvalues rfl with hlam
  have htrace : LinearMap.trace ℝ ℝ⁴ (HessOp φ s x).toLinearMap = ∑ i, lam i :=
    Commons.Analysis.Sigma2.trace_eq_sum_eigenvalues hsym
  have hsum2 : 0 ≤ ∑ j, ∑ i : Fin (Module.finrank ℝ ℝ⁴),
      (if i < j then lam i * lam j else 0) := by
    have h1 : σ₂ (HessOp φ s x) = ∑ j, ∑ i : Fin (Module.finrank ℝ ℝ⁴),
        (if i < j then lam i * lam j else 0) := by
      unfold HessianEstimates.σ₂
      rw [dif_pos hsym]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Finset.filter_gt_eq_Iio, Finset.sum_filter]
    rwa [h1] at hsig
  have hlin : ∀ i, lam i ≤ ∑ j, lam j :=
    Commons.Analysis.Sigma2.sigma2_nonneg_linearized_nonneg (by rw [← htrace]; exact htr) hsum2
  -- coefficients of `e` in the eigenbasis
  set c : Fin (Module.finrank ℝ ℝ⁴) → ℝ := fun i => (v.repr e).ofLp i with hc
  have hexp : e = ∑ i, c i • v i := by
    rw [hc]; exact (v.sum_repr e).symm
  have hcsq : ∑ i, c i ^ 2 = 1 := by
    have h1 : ‖e‖ = ‖v.repr e‖ := (LinearIsometryEquiv.norm_map v.repr e).symm
    have h2 : ‖v.repr e‖ ^ 2 = ∑ i, (v.repr e).ofLp i ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp only [Real.norm_eq_abs, sq_abs]
    rw [← h2, ← h1, he, one_pow]
  have hinner : ⟪HessOp φ s x e, e⟫ = ∑ i, lam i * c i ^ 2 := by
    have h1 : ⟪HessOp φ s x e, e⟫
        = ∑ i, ∑ j, c i * c j * (if i = j then lam i else 0) := by
      rw [hexp, map_sum, sum_inner]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [inner_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, inner_smul_left, inner_smul_right,
        Commons.Analysis.InnerProductSpace.eigen_basis_inner_apply hsym i j]
      rw [show (starRingEnd ℝ) (c i) = c i from rfl]
      ring
    rw [h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · simp only [if_true]; ring
    · intro j _ hj
      rw [if_neg (Ne.symm hj)]; ring
    · intro hi; exact absurd (Finset.mem_univ i) hi
  rw [hinner, htrace]
  exact Commons.Analysis.Sigma2.weighted_sum_le_sum (by rw [← htrace]; exact htr) hsum2 hcsq

end Submission

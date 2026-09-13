/-
Infrastructure for Proposition 2.4 of Shankar--Yuan (the doubling inequality): the test
function `P_{alpha beta gamma}`, the maximum principle for the linearized operator
`F = Delta u I - D^2u`, and the resulting inequality at an interior maximum.
-/
import ChallengeDeps
import Submission.Prop21
import Submission.Commons.Analysis.Calculus.FDeriv.fderiv_fderiv_nonpos_of_localMax
import Submission.Commons.Analysis.Calculus.FDeriv.isSymmetric_hessian
import Submission.Commons.Analysis.Calculus.FDeriv.iteratedFDeriv_two_log_rho_diag
import Submission.Commons.Analysis.Calculus.FDeriv.fderiv_affine_directional
import Submission.Commons.Analysis.Calculus.FDeriv.fderiv_grad_sq_directional
import Submission.Commons.Analysis.Calculus.FDeriv.fderiv_rho_eq
import Submission.Commons.Analysis.Calculus.FDeriv.fderiv_log_laplacian
import Submission.Commons.Analysis.Calculus.FDeriv.second_fderiv_log_laplacian_diag
import Submission.Commons.Analysis.Calculus.FDeriv.fderiv_fderiv_apply_directional
import Submission.Commons.Analysis.InnerProductSpace.trace_comp_nonpos_of_nonneg_nonpos
import Submission.Commons.Analysis.InnerProductSpace.trace_comp_eq_sum_inner_coord
import Submission.Commons.Analysis.InnerProductSpace.inner_smul_one_sub_eq_sum
import Submission.Commons.Analysis.InnerProductSpace.eigen_basis_inner_apply
import Submission.Commons.Analysis.Sigma2.diagonal_first_deriv_sigma2
import Submission.Commons.Analysis.Sigma2.sum_linearized_mul_self
import Submission.Commons.Analysis.Sigma2.linearized_pos_four
import Submission.Commons.Analysis.Sigma2.max_ineq_algebra
import Submission.Commons.Analysis.InnerProductSpace.norm_sq_eq_sum_sq_apply
import Submission.Commons.Analysis.Sigma2.trace_sq_ge_two_of_pair_sum
import Submission.Commons.Analysis.Calculus.FDeriv.laplacian_eq_trace_hessian
import Submission.Commons.Analysis.Sigma2.jacobi_log_algebra
import Submission.Commons.Analysis.Calculus.FDeriv.iteratedFDeriv_two_apply_const_mul
import Submission.Commons.Analysis.Calculus.FDeriv.iteratedFDeriv_two_affine_diag
import Submission.Commons.Analysis.Calculus.FDeriv.iteratedFDeriv_two_grad_sq_diag

open HessianEstimates
open Commons.Analysis.Calculus.FDeriv
open Commons.Analysis.Sigma2
open Commons.Analysis.InnerProductSpace
open Laplacian Metric
open scoped BigOperators RealInnerProductSpace Topology

set_option autoImplicit false

namespace Submission

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

variable {v : OrthonormalBasis (Fin 4) ℝ ℝ⁴}


theorem contDiffAt_iteratedFDeriv_apply_local {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] {u : E → F} {x : E} {n m : ℕ} (hu : ContDiffAt 𝕜 (n + m) u x)
    (t : Fin n → E) : ContDiffAt 𝕜 m (fun z => (iteratedFDeriv 𝕜 n u z) t) x := by
  have h : ContDiffAt 𝕜 m (iteratedFDeriv 𝕜 n u) x := by
    apply ContDiffAt.iteratedFDeriv_right (f := u) (i := n) (m := m) (n := (n + m : ℕ)) hu
    show ((m : WithTop ℕ∞) + (n : WithTop ℕ∞)) ≤ ((n + m : ℕ) : WithTop ℕ∞)
    exact_mod_cast (show m + n ≤ n + m by omega)
  have hh := h.continuousLinearMap_comp
    (ContinuousMultilinearMap.apply 𝕜 (fun _ : Fin n => E) F t)
  simpa [Function.comp_def] using hh

/-- The distance-squared test function `rho(x) = 9 - |x|^2` (the paper's `rho` with `R = 3`). -/
noncomputable def rhoF (z : ℝ⁴) : ℝ := 9 - ‖z‖ ^ 2

/-- The `x · Du - u` term of the test function. -/
noncomputable def WF (u : ℝ⁴ → ℝ) (z : ℝ⁴) : ℝ := (fderiv ℝ u z) z - u z

/-- The `|Du|^2` term of the test function, written in coordinates in the orthonormal basis. -/
noncomputable def QF (v : OrthonormalBasis (Fin 4) ℝ ℝ⁴) (u : ℝ⁴ → ℝ) (z : ℝ⁴) : ℝ :=
  ∑ k : Fin 4, ((fderiv ℝ u z) (v k)) ^ 2

/-- `b = log (Delta u)`. -/
noncomputable def bF (u : ℝ⁴ → ℝ) (z : ℝ⁴) : ℝ := Real.log ((Δ u) z)

/-- `bar b = b - c`, the normalisation of `b` by a reference value. -/
noncomputable def barF (u : ℝ⁴ → ℝ) (c : ℝ) (z : ℝ⁴) : ℝ := bF u z - c

/-- The unclamped test function `2 log rho + alpha (x·Du - u) + (beta/2)|Du|^2 + log bar b`. -/
noncomputable def P0 (v : OrthonormalBasis (Fin 4) ℝ ℝ⁴) (u : ℝ⁴ → ℝ) (c α β : ℝ)
    (z : ℝ⁴) : ℝ :=
  2 * Real.log (rhoF z) + α * WF u z + (β / 2) * QF v u z + Real.log (barF u c z)

/-- The test function `P_{alpha beta gamma} = 2 log rho + alpha (x·Du - u) + (beta/2)|Du|^2
+ log max(bar b, gamma^{-1})`. -/
noncomputable def Pfun (v : OrthonormalBasis (Fin 4) ℝ ℝ⁴) (u : ℝ⁴ → ℝ) (c α β γ : ℝ)
    (z : ℝ⁴) : ℝ :=
  2 * Real.log (rhoF z) + α * WF u z + (β / 2) * QF v u z
    + Real.log (max (barF u c z) γ⁻¹)

/-- **Maximum principle pairing.**  If `F` is a symmetric positive semidefinite operator,
`A` has non-positive quadratic form, and `F` is diagonal in the orthonormal basis `v` with
eigenvalues `f i`, then `sum_i f i * <A v_i, v_i> <= 0`. -/
theorem sum_mul_diag_nonpos_of_trace {F A : ℝ⁴ →L[ℝ] ℝ⁴} (hFsym : F.IsSymmetric)
    (hFnn : ∀ z : ℝ⁴, 0 ≤ ⟪F z, z⟫) (hAnn : ∀ z : ℝ⁴, ⟪A z, z⟫ ≤ 0)
    (f : Fin 4 → ℝ) (hFdiag : ∀ i : Fin 4, F (v i) = f i • v i) :
    (∑ i : Fin 4, f i * ⟪A (v i), v i⟫) ≤ 0 := by
  have htrace := trace_comp_nonpos_of_nonneg_nonpos (F := F) (A := A) hFsym hFnn hAnn
  have hcoord := trace_comp_eq_sum_inner_coord (F := F) (A := A) v
  rw [hcoord] at htrace
  have hinner : ∀ i j : Fin 4, ⟪v i, v j⟫ = if i = j then (1 : ℝ) else 0 := by
    intro i j
    rw [v.inner_eq_ite]
  have hdiag : (∑ i : Fin 4, ∑ j : Fin 4, ⟪F (v i), v j⟫ * ⟪A (v j), v i⟫)
      = ∑ i : Fin 4, f i * ⟪A (v i), v i⟫ := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_eq_single i]
    · rw [hFdiag i, inner_smul_left, hinner i i]
      simp
    · intro j _ hj
      rw [hFdiag i, inner_smul_left, hinner i j, if_neg (fun h => hj h.symm)]
      simp
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  rw [← hdiag]
  exact htrace

/-- Proposition 2.1 (almost-Jacobi inequality) in the form used by the maximum principle:
`Delta_F b >= eps |grad_F b|^2` for `b = log (Delta u)`, where `F` is the linearized operator
(in the basis diagonalizing `D^2 u x`) and `eps = (2/9)(1/2 + lam_3/S)`. -/
theorem jacobi_log {u : ℝ⁴ → ℝ} {s : Set ℝ⁴} {x : ℝ⁴}
    (hs : IsOpen s) (hu : ContDiffOn ℝ 4 u s) (hx : x ∈ s)
    (hσ2 : ∀ y ∈ s, σ₂ (H u s y) = 1) (hΔ : ∀ y ∈ s, 0 < (Δ u) y) :
    ∃ (v : OrthonormalBasis (Fin 4) ℝ ℝ⁴) (lam : Fin 4 → ℝ),
      (∀ i j : Fin 4, (iteratedFDeriv ℝ 2 u x) ![v i, v j] = if i = j then lam i else 0) ∧
      (∀ i j : Fin 4, i ≤ j → lam j ≤ lam i) ∧
      (let S : ℝ := ∑ t : Fin 4, lam t
       let eps : ℝ := (2 / 9 : ℝ) * (1 / 2 + lam 3 / S)
       eps * (∑ i : Fin 4, (S - lam i) * (fderiv ℝ (bF u) x (v i)) ^ 2)
        ≤ ∑ i : Fin 4, (S - lam i) * ((iteratedFDeriv ℝ 2 (bF u) x) ![v i, v i])) := by
  obtain ⟨v, lam, hdiag, hmono, hineq⟩ := jacobi_inequality_of_sigma2_smooth hs hu hx hσ2 hΔ
  refine ⟨v, lam, hdiag, hmono, ?_⟩
  dsimp only
  have hSpos : 0 < ∑ t : Fin 4, lam t := by
    rw [← laplacian_eq_sum_lam hdiag]; exact hΔ x hx
  have hL : ∀ z ∈ s, (Δ u) z ≠ 0 := fun z hz => ne_of_gt (hΔ z hz)
  have hLx : (Δ u) x = ∑ t : Fin 4, lam t := laplacian_eq_sum_lam hdiag
  have hD1 : ∀ i : Fin 4, fderiv ℝ (bF u) x (v i) =
      (∑ j : Fin 4, (iteratedFDeriv ℝ 3 u x) ![v j, v j, v i]) / (∑ t : Fin 4, lam t) := by
    intro i
    have h := fderiv_log_laplacian v hs hx (hu.of_le (by norm_num)) hL i
    rw [hLx] at h
    exact h
  have hD2 : ∀ i : Fin 4, (iteratedFDeriv ℝ 2 (bF u) x) ![v i, v i] =
      (∑ k : Fin 4, (iteratedFDeriv ℝ 4 u x) ![v i, v i, v k, v k]) / (∑ t : Fin 4, lam t)
        - ((∑ j : Fin 4, (iteratedFDeriv ℝ 3 u x) ![v j, v j, v i])
            / (∑ t : Fin 4, lam t)) ^ 2 := by
    intro i
    have h := second_fderiv_log_laplacian_diag (u := u) (s := s) (x := x) v hs hx hu hL i
    rw [hLx] at h
    exact h
  exact jacobi_log_algebra lam
    (fun i : Fin 4 => ∑ k : Fin 4, (iteratedFDeriv ℝ 4 u x) ![v i, v i, v k, v k])
    (fun i : Fin 4 => ∑ j : Fin 4, (iteratedFDeriv ℝ 3 u x) ![v j, v j, v i])
    (fun i : Fin 4 => fderiv ℝ (bF u) x (v i))
    (fun i : Fin 4 => (iteratedFDeriv ℝ 2 (bF u) x) ![v i, v i])
    (∑ t : Fin 4, lam t) ((2 / 9 : ℝ) * (1 / 2 + lam 3 / (∑ t : Fin 4, lam t)))
    (1 + (2 / 9 : ℝ) * (1 / 2 + lam 3 / (∑ t : Fin 4, lam t)))
    rfl rfl hSpos hD1 hD2 hineq

/-- The second directional derivative of the unclamped test function `P0` at `x` in the
direction `v i`, expanded into its four components. -/
theorem iteratedFDeriv_two_P0_diag {v : OrthonormalBasis (Fin 4) ℝ ℝ⁴} {u : ℝ⁴ → ℝ} {s : Set ℝ⁴} {x : ℝ⁴}
    {c α β : ℝ} (hs : IsOpen s) (hx : x ∈ s) (hu : ContDiffOn ℝ 4 u s)
    (hL : ∀ z ∈ s, (Δ u) z ≠ 0) (h3 : ‖x‖ < 3) (hbc : barF u c x ≠ 0) (i : Fin 4) :
    (iteratedFDeriv ℝ 2 (P0 v u c α β) x) ![v i, v i]
      = (-4 / (9 - ‖x‖ ^ 2) - 8 * (⟪x, v i⟫) ^ 2 / (9 - ‖x‖ ^ 2) ^ 2)
        + α * ((iteratedFDeriv ℝ 2 u x) ![v i, v i]
            + ∑ k : Fin 4, ⟪x, v k⟫ * (iteratedFDeriv ℝ 3 u x) ![v k, v i, v i])
        + (β / 2) * (2 * (∑ k : Fin 4, ((iteratedFDeriv ℝ 2 u x) ![v k, v i]) ^ 2)
            + 2 * ∑ k : Fin 4, (fderiv ℝ u x) (v k) * (iteratedFDeriv ℝ 3 u x) ![v k, v i, v i])
        + ((((∑ k : Fin 4, (iteratedFDeriv ℝ 4 u x) ![v i, v i, v k, v k]) / (Δ u) x
              - ((∑ j : Fin 4, (iteratedFDeriv ℝ 3 u x) ![v j, v j, v i]) / (Δ u) x) ^ 2)
            / (barF u c x)
          - ((∑ j : Fin 4, (iteratedFDeriv ℝ 3 u x) ![v j, v j, v i]) / (Δ u) x) ^ 2
            / (barF u c x) ^ 2)) := by
  have huAt : ContDiffAt ℝ 4 u x := hu.contDiffAt (hs.mem_nhds hx)
  have hcu : ContDiffAt ℝ 2 (fderiv ℝ u) x := huAt.fderiv_right (m := 2) (by norm_num)
  have hu2 : ContDiffAt ℝ 2 u x := huAt.of_le (by norm_num)
  have hΔne : (Δ u) x ≠ 0 := hL x hx
  have hWc : ContDiffAt ℝ 2 (fun z : ℝ⁴ => (fderiv ℝ u z) z - u z) x :=
    (hcu.clm_apply contDiffAt_id).sub hu2
  have hQc : ContDiffAt ℝ 2 (fun z : ℝ⁴ => ∑ k : Fin 4, ((fderiv ℝ u z) (v k)) ^ 2) x :=
    ContDiffAt.sum (fun k _ => (hcu.clm_apply (contDiffAt_const (c := v k))).pow 2)
  have hρc : ContDiffAt ℝ 2 (fun z : ℝ⁴ => (9 : ℝ) - ‖z‖ ^ 2) x :=
    contDiffAt_const.sub (contDiffAt_id.norm_sq ℝ)
  have hΔuc : ContDiffAt ℝ 2 (fun z : ℝ⁴ => (Δ u) z) x := by
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis u v]
    exact ContDiffAt.sum (fun k _ => contDiffAt_iteratedFDeriv_apply_local huAt ![v k, v k])
  have hbc' : ContDiffAt ℝ 2 (barF u c) x := by
    have h1 : ContDiffAt ℝ 2 (fun z : ℝ⁴ => Real.log ((Δ u) z)) x := hΔuc.log hΔne
    have h2 : ContDiffAt ℝ 2 (fun z : ℝ⁴ => Real.log ((Δ u) z) - c) x :=
      h1.sub (contDiffAt_const (c := c))
    exact h2
  have hne9 : (9 : ℝ) - ‖x‖ ^ 2 ≠ 0 := by
    have : ‖x‖ ^ 2 < 9 := by nlinarith [norm_nonneg x]
    linarith
  have hc1 : ContDiffAt ℝ 2 (fun z : ℝ⁴ => 2 * Real.log (rhoF z)) x := by
    have h := (hρc.log hne9).const_smul (2 : ℝ)
    simpa [rhoF, smul_eq_mul] using h
  have hc2 : ContDiffAt ℝ 2 (fun z : ℝ⁴ => α * WF u z) x := by
    have h := hWc.const_smul α
    simpa [WF, smul_eq_mul] using h
  have hc3 : ContDiffAt ℝ 2 (fun z : ℝ⁴ => (β / 2) * QF v u z) x := by
    have h := hQc.const_smul (β / 2)
    simpa [QF, smul_eq_mul] using h
  have hc4 : ContDiffAt ℝ 2 (fun z : ℝ⁴ => Real.log (barF u c z)) x := hbc'.log hbc
  -- derivatives of the four components
  have e1 : (iteratedFDeriv ℝ 2 (fun z : ℝ⁴ => 2 * Real.log (rhoF z)) x) ![v i, v i]
      = -4 / (9 - ‖x‖ ^ 2) - 8 * (⟪x, v i⟫) ^ 2 / (9 - ‖x‖ ^ 2) ^ 2 :=
    iteratedFDeriv_two_log_rho_diag v x h3 i
  have dW1 : DifferentiableAt ℝ (fun z : ℝ⁴ => (fderiv ℝ u z) z - u z) x :=
    hWc.differentiableAt (by norm_num)
  have dW2 : DifferentiableAt ℝ (fderiv ℝ (fun z : ℝ⁴ => (fderiv ℝ u z) z - u z)) x :=
    (hWc.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have e2 : (iteratedFDeriv ℝ 2 (fun z : ℝ⁴ => α * WF u z) x) ![v i, v i]
      = α * ((iteratedFDeriv ℝ 2 u x) ![v i, v i]
          + ∑ k : Fin 4, ⟪x, v k⟫ * (iteratedFDeriv ℝ 3 u x) ![v k, v i, v i]) := by
    have h := iteratedFDeriv_two_apply_const_mul (f := WF u) (a := v i) (b := v i) α dW1 dW2
    have h2 := iteratedFDeriv_two_affine_diag (u := u) (s := s) (x := x) v hs hx
      (hu.of_le (by norm_num)) i
    simpa [WF] using h.trans (congrArg (fun t => α * t) h2)
  have dQ1 : DifferentiableAt ℝ (fun z : ℝ⁴ => ∑ k : Fin 4, ((fderiv ℝ u z) (v k)) ^ 2) x :=
    hQc.differentiableAt (by norm_num)
  have dQ2 : DifferentiableAt ℝ
      (fderiv ℝ (fun z : ℝ⁴ => ∑ k : Fin 4, ((fderiv ℝ u z) (v k)) ^ 2)) x :=
    (hQc.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have e3 : (iteratedFDeriv ℝ 2 (fun z : ℝ⁴ => (β / 2) * QF v u z) x) ![v i, v i]
      = (β / 2) * (2 * (∑ k : Fin 4, ((iteratedFDeriv ℝ 2 u x) ![v k, v i]) ^ 2)
          + 2 * ∑ k : Fin 4, (fderiv ℝ u x) (v k) * (iteratedFDeriv ℝ 3 u x) ![v k, v i, v i]) := by
    have h := iteratedFDeriv_two_apply_const_mul (f := QF v u) (a := v i) (b := v i) (β / 2) dQ1 dQ2
    have h2 := iteratedFDeriv_two_grad_sq_diag (u := u) (s := s) (x := x) v hs hx
      (hu.of_le (by norm_num)) i
    simpa [QF] using h.trans (congrArg (fun t => (β / 2) * t) h2)
  have e4 : (iteratedFDeriv ℝ 2 (fun z : ℝ⁴ => Real.log (barF u c z)) x) ![v i, v i]
      = (((∑ k : Fin 4, (iteratedFDeriv ℝ 4 u x) ![v i, v i, v k, v k]) / (Δ u) x
              - ((∑ j : Fin 4, (iteratedFDeriv ℝ 3 u x) ![v j, v j, v i]) / (Δ u) x) ^ 2)
            / (barF u c x)
          - ((∑ j : Fin 4, (iteratedFDeriv ℝ 3 u x) ![v j, v j, v i]) / (Δ u) x) ^ 2
            / (barF u c x) ^ 2) := by
    rw [iteratedFDeriv_two_log_comp hbc' hbc (v i) (v i)]
    have hfde : fderiv ℝ (barF u c) x = fderiv ℝ (fun z : ℝ⁴ => Real.log ((Δ u) z)) x := by
      show fderiv ℝ (fun z : ℝ⁴ => bF u z - c) x = fderiv ℝ (fun z : ℝ⁴ => Real.log ((Δ u) z)) x
      rw [fderiv_sub_const]
      rfl
    have h2nd : (iteratedFDeriv ℝ 2 (barF u c) x) ![v i, v i]
        = (iteratedFDeriv ℝ 2 (fun z : ℝ⁴ => Real.log ((Δ u) z)) x) ![v i, v i] := by
      have hev : fderiv ℝ (barF u c) =ᶠ[𝓝 x] fderiv ℝ (fun z : ℝ⁴ => Real.log ((Δ u) z)) := by
        filter_upwards with y
        exact fderiv_sub_const c
      rw [iteratedFDeriv_two_apply, iteratedFDeriv_two_apply, Filter.EventuallyEq.fderiv_eq hev]
    rw [h2nd, hfde]
    rw [second_fderiv_log_laplacian_diag (u := u) (s := s) (x := x) v hs hx hu hL i,
        fderiv_log_laplacian (u := u) (s := s) (x := x) v hs hx (hu.of_le (by norm_num)) hL i]
    ring
  -- assemble
  have hAB : ContDiffAt ℝ 2 ((fun z : ℝ⁴ => 2 * Real.log (rhoF z))
      + (fun z : ℝ⁴ => α * WF u z)) x := hc1.add hc2
  have hABC : ContDiffAt ℝ 2 ((fun z : ℝ⁴ => 2 * Real.log (rhoF z))
      + (fun z : ℝ⁴ => α * WF u z) + (fun z : ℝ⁴ => (β / 2) * QF v u z)) x := hAB.add hc3
  have hsplit : P0 v u c α β
      = (fun z : ℝ⁴ => 2 * Real.log (rhoF z)) + (fun z : ℝ⁴ => α * WF u z)
        + (fun z : ℝ⁴ => (β / 2) * QF v u z) + (fun z : ℝ⁴ => Real.log (barF u c z)) := rfl
  rw [hsplit, iteratedFDeriv_add_apply hABC hc4, iteratedFDeriv_add_apply hAB hc3,
      iteratedFDeriv_add_apply hc1 hc2]
  simp only [ContinuousMultilinearMap.add_apply]
  rw [e1, e2, e3, e4]


/-- The first directional derivative of the unclamped test function `P0` at `x` in the direction
`v i`. -/
theorem fderiv_P0_diag {v : OrthonormalBasis (Fin 4) ℝ ℝ⁴} {u : ℝ⁴ → ℝ} {s : Set ℝ⁴} {x : ℝ⁴}
    {c α β : ℝ} (hs : IsOpen s) (hx : x ∈ s) (hu : ContDiffOn ℝ 3 u s)
    (hL : ∀ z ∈ s, (Δ u) z ≠ 0) (h3 : ‖x‖ < 3) (hbc : barF u c x ≠ 0) (i : Fin 4) :
    fderiv ℝ (P0 v u c α β) x (v i)
      = 2 * (fderiv ℝ rhoF x (v i)) / rhoF x
        + α * (∑ k : Fin 4, ⟪x, v k⟫ * (iteratedFDeriv ℝ 2 u x) ![v i, v k])
        + (β / 2) * (2 * ∑ k : Fin 4, (fderiv ℝ u x) (v k) * (iteratedFDeriv ℝ 2 u x) ![v i, v k])
        + (fderiv ℝ (bF u) x (v i)) / barF u c x := by
  have huAt : ContDiffAt ℝ 3 u x := hu.contDiffAt (hs.mem_nhds hx)
  have hcu : ContDiffAt ℝ 1 (fderiv ℝ u) x := huAt.fderiv_right (m := 1) (by norm_num)
  have hu1 : ContDiffAt ℝ 1 u x := huAt.of_le (by norm_num)
  have hu2 : ContDiffAt ℝ 2 u x := huAt.of_le (by norm_num)
  have hΔne : (Δ u) x ≠ 0 := hL x hx
  have hW1 : ContDiffAt ℝ 1 (fun z : ℝ⁴ => (fderiv ℝ u z) z - u z) x :=
    (hcu.clm_apply contDiffAt_id).sub hu1
  have hQ1 : ContDiffAt ℝ 1 (fun z : ℝ⁴ => ∑ k : Fin 4, ((fderiv ℝ u z) (v k)) ^ 2) x :=
    ContDiffAt.sum (fun k _ => (hcu.clm_apply (contDiffAt_const (c := v k))).pow 2)
  have hρ1 : ContDiffAt ℝ 1 (fun z : ℝ⁴ => (9 : ℝ) - ‖z‖ ^ 2) x :=
    contDiffAt_const.sub (contDiffAt_id.norm_sq ℝ)
  have hΔu1 : ContDiffAt ℝ 1 (fun z : ℝ⁴ => (Δ u) z) x := by
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis u v]
    exact ContDiffAt.sum (fun k _ => contDiffAt_iteratedFDeriv_apply_local huAt ![v k, v k])
  have hb1 : ContDiffAt ℝ 1 (fun z : ℝ⁴ => Real.log ((Δ u) z) - c) x :=
    (hΔu1.log hΔne).sub (contDiffAt_const (c := c))
  have hne9 : (9 : ℝ) - ‖x‖ ^ 2 ≠ 0 := by
    have : ‖x‖ ^ 2 < 9 := by nlinarith [norm_nonneg x]
    linarith
  -- the four HasFDerivAt facts
  have H1 : HasFDerivAt (fun z : ℝ⁴ => 2 * Real.log (rhoF z))
      ((2 : ℝ) • ((rhoF x)⁻¹ • fderiv ℝ rhoF x)) x :=
    (((hρ1.differentiableAt (by norm_num)).hasFDerivAt).log hne9).const_mul 2
  have H2 : HasFDerivAt (fun z : ℝ⁴ => α * WF u z) (α • fderiv ℝ (WF u) x) x :=
    ((hW1.differentiableAt (by norm_num)).hasFDerivAt).const_mul α
  have H3 : HasFDerivAt (fun z : ℝ⁴ => (β / 2) * QF v u z) ((β / 2) • fderiv ℝ (QF v u) x) x :=
    ((hQ1.differentiableAt (by norm_num)).hasFDerivAt).const_mul (β / 2)
  have H4 : HasFDerivAt (fun z : ℝ⁴ => Real.log (barF u c z))
      ((barF u c x)⁻¹ • fderiv ℝ (barF u c) x) x :=
    ((hb1.differentiableAt (by norm_num)).hasFDerivAt).log hbc
  have HAB := H1.add H2
  have HABC := HAB.add H3
  have HABCD := HABC.add H4
  have hsplit : P0 v u c α β
      = (fun z : ℝ⁴ => 2 * Real.log (rhoF z)) + (fun z : ℝ⁴ => α * WF u z)
        + (fun z : ℝ⁴ => (β / 2) * QF v u z) + (fun z : ℝ⁴ => Real.log (barF u c z)) := rfl
  rw [hsplit, HABCD.fderiv]
  simp only [ContinuousLinearMap.add_apply]
  -- evaluate the four pieces
  have e1 : ((2 : ℝ) • (rhoF x)⁻¹ • fderiv ℝ rhoF x) (v i)
      = 2 * (fderiv ℝ rhoF x (v i)) / rhoF x := by
    simp only [smul_apply, smul_eq_mul]
    ring
  have e2 : (α • fderiv ℝ (WF u) x) (v i)
      = α * (∑ k : Fin 4, ⟪x, v k⟫ * (iteratedFDeriv ℝ 2 u x) ![v i, v k]) := by
    rw [smul_apply, smul_eq_mul]
    congr 1
    exact fderiv_affine_directional v hs hx (hu.of_le (by norm_num)) (v i)
  have e3 : ((β / 2) • fderiv ℝ (QF v u) x) (v i)
      = (β / 2) * (2 * ∑ k : Fin 4, (fderiv ℝ u x) (v k) * (iteratedFDeriv ℝ 2 u x) ![v i, v k]) := by
    rw [smul_apply, smul_eq_mul]
    congr 1
    exact fderiv_grad_sq_directional v hs hx (hu.of_le (by norm_num)) (v i)
  have e4 : ((barF u c x)⁻¹ • fderiv ℝ (barF u c) x) (v i)
      = (fderiv ℝ (bF u) x (v i)) / barF u c x := by
    have hfde : fderiv ℝ (barF u c) x = fderiv ℝ (bF u) x := by
      show fderiv ℝ (fun z : ℝ⁴ => bF u z - c) x = fderiv ℝ (bF u) x
      rw [fderiv_sub_const]
    rw [hfde]
    simp only [smul_apply, smul_eq_mul, div_eq_mul_inv]
    ring
  rw [e1, e2, e3, e4]


theorem contDiffAt_two_P0 {v : OrthonormalBasis (Fin 4) ℝ ℝ⁴} {u : ℝ⁴ → ℝ} {s : Set ℝ⁴}
    {x : ℝ⁴} {c α β : ℝ} (hs : IsOpen s) (hx : x ∈ s) (hu : ContDiffOn ℝ 4 u s)
    (hL : ∀ z ∈ s, (Δ u) z ≠ 0) (h3 : ‖x‖ < 3) (hbc : barF u c x ≠ 0) :
    ContDiffAt ℝ 2 (P0 v u c α β) x := by
  have huAt : ContDiffAt ℝ 4 u x := hu.contDiffAt (hs.mem_nhds hx)
  have hcu : ContDiffAt ℝ 2 (fderiv ℝ u) x := huAt.fderiv_right (m := 2) (by norm_num)
  have hu2 : ContDiffAt ℝ 2 u x := huAt.of_le (by norm_num)
  have hΔne : (Δ u) x ≠ 0 := hL x hx
  have hWc : ContDiffAt ℝ 2 (fun z : ℝ⁴ => (fderiv ℝ u z) z - u z) x :=
    (hcu.clm_apply contDiffAt_id).sub hu2
  have hQc : ContDiffAt ℝ 2 (fun z : ℝ⁴ => ∑ k : Fin 4, ((fderiv ℝ u z) (v k)) ^ 2) x :=
    ContDiffAt.sum (fun k _ => (hcu.clm_apply (contDiffAt_const (c := v k))).pow 2)
  have hρc : ContDiffAt ℝ 2 (fun z : ℝ⁴ => (9 : ℝ) - ‖z‖ ^ 2) x :=
    contDiffAt_const.sub (contDiffAt_id.norm_sq ℝ)
  have hΔuc : ContDiffAt ℝ 2 (fun z : ℝ⁴ => (Δ u) z) x := by
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis u v]
    exact ContDiffAt.sum (fun k _ => contDiffAt_iteratedFDeriv_apply_local huAt ![v k, v k])
  have hbc' : ContDiffAt ℝ 2 (barF u c) x := by
    have h1 : ContDiffAt ℝ 2 (fun z : ℝ⁴ => Real.log ((Δ u) z)) x := hΔuc.log hΔne
    have h2 : ContDiffAt ℝ 2 (fun z : ℝ⁴ => Real.log ((Δ u) z) - c) x :=
      h1.sub (contDiffAt_const (c := c))
    exact h2
  have hne9 : (9 : ℝ) - ‖x‖ ^ 2 ≠ 0 := by
    have : ‖x‖ ^ 2 < 9 := by nlinarith [norm_nonneg x]
    linarith
  have hc1 : ContDiffAt ℝ 2 (fun z : ℝ⁴ => 2 * Real.log (rhoF z)) x := by
    have h := (hρc.log hne9).const_smul (2 : ℝ)
    simpa [rhoF, smul_eq_mul] using h
  have hc2 : ContDiffAt ℝ 2 (fun z : ℝ⁴ => α * WF u z) x := by
    have h := hWc.const_smul α
    simpa [WF, smul_eq_mul] using h
  have hc3 : ContDiffAt ℝ 2 (fun z : ℝ⁴ => (β / 2) * QF v u z) x := by
    have h := hQc.const_smul (β / 2)
    simpa [QF, smul_eq_mul] using h
  have hc4 : ContDiffAt ℝ 2 (fun z : ℝ⁴ => Real.log (barF u c z)) x := hbc'.log hbc
  have hAB : ContDiffAt ℝ 2 ((fun z : ℝ⁴ => 2 * Real.log (rhoF z))
      + (fun z : ℝ⁴ => α * WF u z)) x := hc1.add hc2
  have hABC : ContDiffAt ℝ 2 ((fun z : ℝ⁴ => 2 * Real.log (rhoF z))
      + (fun z : ℝ⁴ => α * WF u z) + (fun z : ℝ⁴ => (β / 2) * QF v u z)) x := hAB.add hc3
  have hABCD : ContDiffAt ℝ 2 ((fun z : ℝ⁴ => 2 * Real.log (rhoF z))
      + (fun z : ℝ⁴ => α * WF u z) + (fun z : ℝ⁴ => (β / 2) * QF v u z)
      + (fun z : ℝ⁴ => Real.log (barF u c z))) x := hABC.add hc4
  exact hABCD

theorem max_ineq {v : OrthonormalBasis (Fin 4) ℝ ℝ⁴} {u : ℝ⁴ → ℝ} {s : Set ℝ⁴} {x : ℝ⁴}
    {lam : Fin 4 → ℝ} {c α β : ℝ}
    (hs : IsOpen s) (hx : x ∈ s) (hu : ContDiffOn ℝ 4 u s)
    (hσ2 : ∀ y ∈ s, σ₂ (H u s y) = 1) (hΔ : ∀ y ∈ s, 0 < (Δ u) y)
    (hdiag : ∀ i j : Fin 4, (iteratedFDeriv ℝ 2 u x) ![v i, v j] = if i = j then lam i else 0)
    (hmono : ∀ i j : Fin 4, i ≤ j → lam j ≤ lam i)
    (hmax : IsLocalMax (P0 v u c α β) x)
    (h3 : ‖x‖ < 3) (hbpos : 0 < barF u c x) :
    -12 * (∑ t : Fin 4, lam t) / (9 - ‖x‖ ^ 2)
      - 8 * (∑ i : Fin 4, ((∑ t : Fin 4, lam t) - lam i) * (⟪x, v i⟫) ^ 2)
        / (9 - ‖x‖ ^ 2) ^ 2
      + 2 * α
      + β * (∑ i : Fin 4, ((∑ t : Fin 4, lam t) - lam i) * (lam i) ^ 2)
      + (1 / barF u c x) * (∑ i : Fin 4, ((∑ t : Fin 4, lam t) - lam i)
          * ((iteratedFDeriv ℝ 2 (bF u) x) ![v i, v i]))
      - (1 / (barF u c x) ^ 2) * (∑ i : Fin 4, ((∑ t : Fin 4, lam t) - lam i)
          * (fderiv ℝ (bF u) x (v i)) ^ 2) ≤ 0 := by
  have hu2 : ContDiffOn ℝ 2 u s := hu.of_le (by norm_num)
  have hu3 : ContDiffOn ℝ 3 u s := hu.of_le (by norm_num)
  have hΔne : ∀ z ∈ s, (Δ u) z ≠ 0 := fun z hz => ne_of_gt (hΔ z hz)
  have hbcne : barF u c x ≠ 0 := ne_of_gt hbpos
  have hSpos : 0 < ∑ t : Fin 4, lam t := by
    rw [← laplacian_eq_sum_lam hdiag]; exact hΔ x hx
  have hpair : (∑ j : Fin 4, ∑ i : Fin 4, if i < j then lam i * lam j else 0) = 1 :=
    pair_sum_lam_eq_one hs hu2 hσ2 hx hdiag
  have hfs : ∀ i : Fin 4, 0 < (∑ t : Fin 4, lam t) - lam i :=
    linearized_pos_four lam hmono hpair hSpos
  have hTdiag : ∀ i : Fin 4, H u s x (v i) = lam i • v i := hessian_apply_eq_smul hs hx hu2 hdiag
  have hTsym : (H u s x).IsSymmetric := isSymmetric_hessianWithin hs hx hu2
  have hFdiag : ∀ i : Fin 4,
      ((∑ t : Fin 4, lam t) • (1 : ℝ⁴ →L[ℝ] ℝ⁴) - H u s x) (v i)
        = ((∑ t : Fin 4, lam t) - lam i) • v i := by
    intro i
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply, hTdiag i, sub_smul]
  have hFsym : ((∑ t : Fin 4, lam t) • (1 : ℝ⁴ →L[ℝ] ℝ⁴) - H u s x).IsSymmetric := by
    have hone : ((∑ t : Fin 4, lam t) • (1 : ℝ⁴ →L[ℝ] ℝ⁴)).IsSymmetric := by
      intro a b
      simp [ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply,
        real_inner_smul_left, real_inner_smul_right]
    exact hone.sub hTsym
  have hFnn : ∀ z : ℝ⁴, 0 ≤ ⟪((∑ t : Fin 4, lam t) • (1 : ℝ⁴ →L[ℝ] ℝ⁴) - H u s x) z, z⟫ := by
    intro z
    rw [inner_smul_one_sub_eq_sum v lam hTdiag (∑ t : Fin 4, lam t) z]
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (le_of_lt (hfs i)) (sq_nonneg _))
  have hC2 : ContDiffAt ℝ 2 (P0 v u c α β) x := contDiffAt_two_P0 hs hx hu hΔne h3 hbcne
  have hAnn : ∀ z : ℝ⁴, ⟪InnerProductSpace.continuousLinearMapOfBilin
      (fderiv ℝ (fderiv ℝ (P0 v u c α β)) x) z, z⟫ ≤ 0 := by
    intro z
    have h := fderiv_fderiv_nonpos_of_localMax (f := P0 v u c α β) hC2 hmax z
    rw [InnerProductSpace.continuousLinearMapOfBilin_apply]
    exact h
  have hcontr := sum_mul_diag_nonpos_of_trace (v := v) hFsym hFnn hAnn
    (fun i : Fin 4 => (∑ t : Fin 4, lam t) - lam i) hFdiag
  have hconv : ∀ i : Fin 4, ⟪InnerProductSpace.continuousLinearMapOfBilin
      (fderiv ℝ (fderiv ℝ (P0 v u c α β)) x) (v i), v i⟫
      = (iteratedFDeriv ℝ 2 (P0 v u c α β) x) ![v i, v i] := by
    intro i
    rw [hessianMatrix_apply_second_partial v (P0 v u c α β) x i i,
      bilinearIteratedFDerivTwo_eq_iteratedFDeriv]
  simp only [hconv] at hcontr
  have hexp : ∀ i : Fin 4, (iteratedFDeriv ℝ 2 (P0 v u c α β) x) ![v i, v i]
      = (-4 / (9 - ‖x‖ ^ 2) - 8 * (⟪x, v i⟫) ^ 2 / (9 - ‖x‖ ^ 2) ^ 2)
        + α * ((iteratedFDeriv ℝ 2 u x) ![v i, v i]
            + ∑ k : Fin 4, ⟪x, v k⟫ * (iteratedFDeriv ℝ 3 u x) ![v k, v i, v i])
        + (β / 2) * (2 * (∑ k : Fin 4, ((iteratedFDeriv ℝ 2 u x) ![v k, v i]) ^ 2)
            + 2 * ∑ k : Fin 4, (fderiv ℝ u x) (v k)
              * (iteratedFDeriv ℝ 3 u x) ![v k, v i, v i])
        + (((∑ k : Fin 4, (iteratedFDeriv ℝ 4 u x) ![v i, v i, v k, v k]) / (Δ u) x
              - ((∑ j : Fin 4, (iteratedFDeriv ℝ 3 u x) ![v j, v j, v i]) / (Δ u) x) ^ 2)
            / (barF u c x)
          - ((∑ j : Fin 4, (iteratedFDeriv ℝ 3 u x) ![v j, v j, v i]) / (Δ u) x) ^ 2
            / (barF u c x) ^ 2) :=
    fun i => iteratedFDeriv_two_P0_diag (v := v) hs hx hu hΔne h3 hbcne i
  have hDterm : ∀ i : Fin 4,
      (((∑ k : Fin 4, (iteratedFDeriv ℝ 4 u x) ![v i, v i, v k, v k]) / (Δ u) x
            - ((∑ j : Fin 4, (iteratedFDeriv ℝ 3 u x) ![v j, v j, v i]) / (Δ u) x) ^ 2)
          / (barF u c x)
        - ((∑ j : Fin 4, (iteratedFDeriv ℝ 3 u x) ![v j, v j, v i]) / (Δ u) x) ^ 2
          / (barF u c x) ^ 2)
      = ((iteratedFDeriv ℝ 2 (bF u) x) ![v i, v i]) / (barF u c x)
        - (fderiv ℝ (bF u) x (v i)) ^ 2 / (barF u c x) ^ 2 := by
    intro i
    rw [← second_fderiv_log_laplacian_diag (u := u) (s := s) (x := x) v hs hx hu hΔne i,
      ← fderiv_log_laplacian (u := u) (s := s) (x := x) v hs hx hu3 hΔne i]
    rfl
  simp only [hexp, hDterm] at hcontr
  have hS3 : (∑ i : Fin 4, ((∑ t : Fin 4, lam t) - lam i)) = 3 * (∑ t : Fin 4, lam t) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    simp only [nsmul_eq_mul]
    ring
  have hlam : ∀ i : Fin 4, (iteratedFDeriv ℝ 2 u x) ![v i, v i] = lam i := by
    intro i; rw [hdiag i i]; simp
  have huki2 : ∀ i : Fin 4,
      (∑ k : Fin 4, ((iteratedFDeriv ℝ 2 u x) ![v k, v i]) ^ 2) = (lam i) ^ 2 := by
    intro i
    rw [Finset.sum_eq_single i]
    · rw [hdiag i i, if_pos rfl]
    · intro k _ hk
      rw [hdiag k i, if_neg hk]; simp
    · intro hi; exact absurd (Finset.mem_univ i) hi
  have h2 : (∑ i : Fin 4, ((∑ t : Fin 4, lam t) - lam i) * lam i) = 2 := by
    rw [sum_linearized_mul_self lam, hpair]; ring
  have hzero : ∀ k : Fin 4, (∑ i : Fin 4, ((∑ t : Fin 4, lam t) - lam i)
      * (iteratedFDeriv ℝ 3 u x) ![v k, v i, v i]) = 0 :=
    fun k => linearized_first_eq hs hu hx hσ2 hdiag k
  have halg := max_ineq_algebra lam (fun i => (iteratedFDeriv ℝ 2 u x) ![v i, v i])
    (fun i => ⟪x, v i⟫) (fun k => (fderiv ℝ u x) (v k))
    (fun i => fderiv ℝ (bF u) x (v i)) (fun i => (iteratedFDeriv ℝ 2 (bF u) x) ![v i, v i])
    (fun k i => (iteratedFDeriv ℝ 2 u x) ![v k, v i])
    (fun k i => (iteratedFDeriv ℝ 3 u x) ![v k, v i, v i])
    (∑ t : Fin 4, lam t) (9 - ‖x‖ ^ 2) (barF u c x) α β hS3 hlam huki2 h2 hzero
  rw [halg] at hcontr
  exact hcontr


/-- Proposition 2.1 (almost-Jacobi inequality) in the parametric diagonal form: for the given
orthonormal basis `v` diagonalising the Hessian at `x` with eigenvalues `lam`, the weighted second
derivative of `b = log (Delta u)` dominates `eps` times the weighted square of its gradient. -/
theorem jacobi_log_diag {v : OrthonormalBasis (Fin 4) ℝ ℝ⁴} {u : ℝ⁴ → ℝ} {s : Set ℝ⁴} {x : ℝ⁴}
    {lam : Fin 4 → ℝ} (hs : IsOpen s) (hu : ContDiffOn ℝ 4 u s) (hx : x ∈ s)
    (hσ2 : ∀ y ∈ s, σ₂ (H u s y) = 1) (hΔ : ∀ y ∈ s, 0 < (Δ u) y)
    (hdiag : ∀ i j : Fin 4, (iteratedFDeriv ℝ 2 u x) ![v i, v j] = if i = j then lam i else 0)
    (hmono : ∀ i j : Fin 4, i ≤ j → lam j ≤ lam i)
    (hσ2lam : (∑ j : Fin 4, ∑ i : Fin 4, if i < j then lam i * lam j else 0) = 1)
    (hσ1 : 0 < ∑ t : Fin 4, lam t) :
    (2 / 9 : ℝ) * (1 / 2 + lam 3 / (∑ t : Fin 4, lam t))
        * (∑ i : Fin 4, ((∑ t : Fin 4, lam t) - lam i) * (fderiv ℝ (bF u) x (v i)) ^ 2)
      ≤ ∑ i : Fin 4, ((∑ t : Fin 4, lam t) - lam i)
          * ((iteratedFDeriv ℝ 2 (bF u) x) ![v i, v i]) := by
  have hconst := coord_minor_sum_eq_one hs (hu.of_le (by norm_num)) hσ2 v
  have hineq := jacobi_inequality_of_sigma2_coord hs hu hx hconst lam hdiag hmono hσ2lam hσ1
  dsimp only at hineq
  have hSpos : 0 < ∑ t : Fin 4, lam t := hσ1
  have hL : ∀ z ∈ s, (Δ u) z ≠ 0 := fun z hz => ne_of_gt (hΔ z hz)
  have hLx : (Δ u) x = ∑ t : Fin 4, lam t := laplacian_eq_sum_lam hdiag
  have hD1 : ∀ i : Fin 4, fderiv ℝ (bF u) x (v i) =
      (∑ j : Fin 4, (iteratedFDeriv ℝ 3 u x) ![v j, v j, v i]) / (∑ t : Fin 4, lam t) := by
    intro i
    have h := fderiv_log_laplacian v hs hx (hu.of_le (by norm_num)) hL i
    rw [hLx] at h
    exact h
  have hD2 : ∀ i : Fin 4, (iteratedFDeriv ℝ 2 (bF u) x) ![v i, v i] =
      (∑ k : Fin 4, (iteratedFDeriv ℝ 4 u x) ![v i, v i, v k, v k]) / (∑ t : Fin 4, lam t)
        - ((∑ j : Fin 4, (iteratedFDeriv ℝ 3 u x) ![v j, v j, v i])
            / (∑ t : Fin 4, lam t)) ^ 2 := by
    intro i
    have h := second_fderiv_log_laplacian_diag (u := u) (s := s) (x := x) v hs hx hu hL i
    rw [hLx] at h
    exact h
  exact jacobi_log_algebra lam
    (fun i : Fin 4 => ∑ k : Fin 4, (iteratedFDeriv ℝ 4 u x) ![v i, v i, v k, v k])
    (fun i : Fin 4 => ∑ j : Fin 4, (iteratedFDeriv ℝ 3 u x) ![v j, v j, v i])
    (fun i : Fin 4 => fderiv ℝ (bF u) x (v i))
    (fun i : Fin 4 => (iteratedFDeriv ℝ 2 (bF u) x) ![v i, v i])
    (∑ t : Fin 4, lam t) ((2 / 9 : ℝ) * (1 / 2 + lam 3 / (∑ t : Fin 4, lam t)))
    (1 + (2 / 9 : ℝ) * (1 / 2 + lam 3 / (∑ t : Fin 4, lam t)))
    rfl rfl hSpos hD1 hD2 hineq

/-- The paper's (maxP) inequality with the almost-Jacobi term used in its sharp form:
the term `(1/bar b) sum_i f_i (b)_{ii}` is replaced by `(eps/bar b) sum_i f_i ((b)_i)^2`. -/
theorem max_ineq_eps {v : OrthonormalBasis (Fin 4) ℝ ℝ⁴} {u : ℝ⁴ → ℝ} {s : Set ℝ⁴} {x : ℝ⁴}
    {lam : Fin 4 → ℝ} {c α β : ℝ}
    (hs : IsOpen s) (hx : x ∈ s) (hu : ContDiffOn ℝ 4 u s)
    (hσ2 : ∀ y ∈ s, σ₂ (H u s y) = 1) (hΔ : ∀ y ∈ s, 0 < (Δ u) y)
    (hdiag : ∀ i j : Fin 4, (iteratedFDeriv ℝ 2 u x) ![v i, v j] = if i = j then lam i else 0)
    (hmono : ∀ i j : Fin 4, i ≤ j → lam j ≤ lam i)
    (hmax : IsLocalMax (P0 v u c α β) x)
    (h3 : ‖x‖ < 3) (hbpos : 0 < barF u c x) :
    -12 * (∑ t : Fin 4, lam t) / (9 - ‖x‖ ^ 2)
      - 8 * (∑ i : Fin 4, ((∑ t : Fin 4, lam t) - lam i) * (⟪x, v i⟫) ^ 2)
        / (9 - ‖x‖ ^ 2) ^ 2
      + 2 * α
      + β * (∑ i : Fin 4, ((∑ t : Fin 4, lam t) - lam i) * (lam i) ^ 2)
      + (((2 / 9 : ℝ) * (1 / 2 + lam 3 / (∑ t : Fin 4, lam t))) / barF u c x)
          * (∑ i : Fin 4, ((∑ t : Fin 4, lam t) - lam i) * (fderiv ℝ (bF u) x (v i)) ^ 2)
      - (1 / (barF u c x) ^ 2) * (∑ i : Fin 4, ((∑ t : Fin 4, lam t) - lam i)
          * (fderiv ℝ (bF u) x (v i)) ^ 2) ≤ 0 := by
  have hΔne : ∀ z ∈ s, (Δ u) z ≠ 0 := fun z hz => ne_of_gt (hΔ z hz)
  have hbcne : barF u c x ≠ 0 := ne_of_gt hbpos
  have hSpos : 0 < ∑ t : Fin 4, lam t := by
    rw [← laplacian_eq_sum_lam hdiag]; exact hΔ x hx
  have hpair : (∑ j : Fin 4, ∑ i : Fin 4, if i < j then lam i * lam j else 0) = 1 :=
    pair_sum_lam_eq_one hs (hu.of_le (by norm_num)) hσ2 hx hdiag
  have hm := max_ineq hs hx hu hσ2 hΔ hdiag hmono hmax h3 hbpos
  have hj := jacobi_log_diag hs hu hx hσ2 hΔ hdiag hmono hpair hSpos
  have step : (((2 / 9 : ℝ) * (1 / 2 + lam 3 / (∑ t : Fin 4, lam t))) / barF u c x)
        * (∑ i : Fin 4, ((∑ t : Fin 4, lam t) - lam i) * (fderiv ℝ (bF u) x (v i)) ^ 2)
      ≤ (1 / barF u c x) * (∑ i : Fin 4, ((∑ t : Fin 4, lam t) - lam i)
          * ((iteratedFDeriv ℝ 2 (bF u) x) ![v i, v i])) := by
    have hpos : (0 : ℝ) ≤ 1 / barF u c x := le_of_lt (by positivity)
    have h1 := mul_le_mul_of_nonneg_left hj hpos
    have h2 : 1 / barF u c x * ((2 / 9 : ℝ) * (1 / 2 + lam 3 / (∑ t : Fin 4, lam t))
          * (∑ i : Fin 4, ((∑ t : Fin 4, lam t) - lam i) * (fderiv ℝ (bF u) x (v i)) ^ 2))
        = (((2 / 9 : ℝ) * (1 / 2 + lam 3 / (∑ t : Fin 4, lam t))) / barF u c x)
          * (∑ i : Fin 4, ((∑ t : Fin 4, lam t) - lam i) * (fderiv ℝ (bF u) x (v i)) ^ 2) := by
      ring
    rw [h2] at h1
    exact h1
  linarith [hm, step]

/-- At an interior maximum of the test function `Pfun`, in the case `bar b (x) > gamma^{-1}` where
`Pfun` and `P0` agree near `x`, the first derivative of `P0` vanishes.  Diagonalising the Hessian
at `x` this is the relation
`(b)_i / bar b = 4 x_i/rho - alpha x_i lam_i - beta u_i lam_i`,  `rho = 9 - |x|^2`. -/
theorem first_deriv_relation_at_max {v : OrthonormalBasis (Fin 4) ℝ ℝ⁴} {u : ℝ⁴ → ℝ}
    {s : Set ℝ⁴} {x : ℝ⁴} {lam : Fin 4 → ℝ} {c α β γ : ℝ}
    (hs : IsOpen s) (hx : x ∈ s) (hu : ContDiffOn ℝ 4 u s)
    (hΔ : ∀ y ∈ s, 0 < (Δ u) y)
    (hdiag : ∀ i j : Fin 4, (iteratedFDeriv ℝ 2 u x) ![v i, v j] = if i = j then lam i else 0)
    (hmax : IsLocalMax (Pfun v u c α β γ) x) (h3 : ‖x‖ < 3)
    (hγ : γ⁻¹ < barF u c x) (hbpos : 0 < barF u c x) (i : Fin 4) :
    fderiv ℝ (bF u) x (v i) / barF u c x
      = 4 * ⟪x, v i⟫ / (9 - ‖x‖ ^ 2) - α * ⟪x, v i⟫ * lam i
        - β * (fderiv ℝ u x) (v i) * lam i := by
  have huAt : ContDiffAt ℝ 4 u x := hu.contDiffAt (hs.mem_nhds hx)
  have hΔne : ∀ z ∈ s, (Δ u) z ≠ 0 := fun z hz => ne_of_gt (hΔ z hz)
  have hbcne : barF u c x ≠ 0 := ne_of_gt hbpos
  have hne9 : (9 : ℝ) - ‖x‖ ^ 2 ≠ 0 := by
    have : ‖x‖ ^ 2 < 9 := by nlinarith [norm_nonneg x]
    linarith
  -- `P0` and `Pfun` agree near `x`
  have hΔuc : ContDiffAt ℝ 1 (fun z : ℝ⁴ => (Δ u) z) x := by
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis u v]
    exact ContDiffAt.sum (fun k _ =>
      contDiffAt_iteratedFDeriv_apply_local (n := 2) (m := 1)
        (huAt.of_le (by norm_num)) ![v k, v k])
  have hb1 : ContDiffAt ℝ 1 (fun z : ℝ⁴ => Real.log ((Δ u) z)) x := hΔuc.log (hΔne x hx)
  have hbar : ContDiffAt ℝ 1 (barF u c) x := by
    have h2 : ContDiffAt ℝ 1 (fun z : ℝ⁴ => Real.log ((Δ u) z) - c) x :=
      hb1.sub (contDiffAt_const (c := c))
    exact h2
  have hev : P0 v u c α β =ᶠ[𝓝 x] Pfun v u c α β γ := by
    filter_upwards [hbar.continuousAt.eventually (isOpen_Ioi.mem_nhds hγ)] with y hy
    simp only [P0, Pfun]
    rw [max_eq_left (le_of_lt hy)]
  have h0 : fderiv ℝ (P0 v u c α β) x = 0 := by
    rw [Filter.EventuallyEq.fderiv_eq hev]
    exact hmax.fderiv_eq_zero
  have h := congrArg (fun L : ℝ⁴ →L[ℝ] ℝ => L (v i)) h0
  rw [fderiv_P0_diag (v := v) hs hx (hu.of_le (by norm_num)) hΔne h3 hbcne i] at h
  have hs1 : (∑ k : Fin 4, ⟪x, v k⟫ * (iteratedFDeriv ℝ 2 u x) ![v i, v k])
      = ⟪x, v i⟫ * lam i := by
    rw [Finset.sum_eq_single i]
    · rw [hdiag i i, if_pos rfl]
    · intro k _ hk
      rw [hdiag i k, if_neg (fun h : i = k => hk h.symm)]; simp
    · intro hi; exact absurd (Finset.mem_univ i) hi
  have hs2 : (∑ k : Fin 4, (fderiv ℝ u x) (v k) * (iteratedFDeriv ℝ 2 u x) ![v i, v k])
      = (fderiv ℝ u x) (v i) * lam i := by
    rw [Finset.sum_eq_single i]
    · rw [hdiag i i, if_pos rfl]
    · intro k _ hk
      rw [hdiag i k, if_neg (fun h : i = k => hk h.symm)]; simp
    · intro hi; exact absurd (Finset.mem_univ i) hi
  have hrho : (fderiv ℝ rhoF x) (v i) = -2 * ⟪x, v i⟫ := by
    show fderiv ℝ (fun z : ℝ⁴ => 9 - ‖z‖ ^ 2) x (v i) = -2 * ⟪x, v i⟫
    exact fderiv_rho_eq x (v i)
  rw [hrho, hs1, hs2] at h
  change 2 * (-2 * ⟪x, v i⟫) / (9 - ‖x‖ ^ 2)
      + α * (⟪x, v i⟫ * lam i)
      + (β / 2) * (2 * ((fderiv ℝ u x) (v i) * lam i))
      + fderiv ℝ (bF u) x (v i) / barF u c x = 0 at h
  field_simp at h ⊢
  linarith [h]

/-- Near a point where `bar b > gamma^{-1}` the test function `Pfun` agrees with the unclamped
function `P0`. -/
theorem P0_eventuallyEq_Pfun {v : OrthonormalBasis (Fin 4) ℝ ℝ⁴} {u : ℝ⁴ → ℝ} {x : ℝ⁴}
    {c α β γ : ℝ} (hcont : ContinuousAt (barF u c) x) (hγ : γ⁻¹ < barF u c x) :
    P0 v u c α β =ᶠ[𝓝 x] Pfun v u c α β γ := by
  filter_upwards [hcont.eventually (isOpen_Ioi.mem_nhds hγ)] with y hy
  simp only [P0, Pfun]
  rw [max_eq_left (le_of_lt hy)]

/-- A local maximum of `Pfun` at a point where `bar b > gamma^{-1}` is a local maximum of `P0`. -/
theorem isLocalMax_P0_of_Pfun {v : OrthonormalBasis (Fin 4) ℝ ℝ⁴} {u : ℝ⁴ → ℝ} {x : ℝ⁴}
    {c α β γ : ℝ} (hcont : ContinuousAt (barF u c) x) (hγ : γ⁻¹ < barF u c x)
    (hmax : IsLocalMax (Pfun v u c α β γ) x) : IsLocalMax (P0 v u c α β) x := by
  have hev : P0 v u c α β =ᶠ[𝓝 x] Pfun v u c α β γ :=
    P0_eventuallyEq_Pfun (v := v) (c := c) hcont hγ
  have h1 : ∀ᶠ y in 𝓝 x, P0 v u c α β y = Pfun v u c α β γ y := hev
  have h2 : ∀ᶠ y in 𝓝 x, Pfun v u c α β γ y ≤ Pfun v u c α β γ x := hmax
  have h3 : P0 v u c α β x = Pfun v u c α β γ x := hev.self_of_nhds
  filter_upwards [h1, h2] with y hy1 hy2
  rw [hy1, h3]
  exact hy2

/-- The weighted sum of the linearised coefficients: `∑ (S - lam i) = 3 S` in dimension four. -/
theorem sum_S_sub_lam {lam : Fin 4 → ℝ} :
    (∑ i : Fin 4, ((∑ t : Fin 4, lam t) - lam i)) = 3 * ∑ t : Fin 4, lam t := by
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp only [nsmul_eq_mul]
  ring

/-- The coordinates of a point of `ball 0 3` along an orthonormal basis are bounded by `3`. -/
theorem abs_coord_le_three {v : OrthonormalBasis (Fin 4) ℝ ℝ⁴} {x : ℝ⁴} (h3 : ‖x‖ < 3)
    (i : Fin 4) : |⟪x, v i⟫| ≤ 3 := by
  have h := abs_real_inner_le_norm x (v i)
  rw [v.norm_eq_one i, mul_one] at h
  linarith

/-- The partial derivatives of a function whose derivative is bounded by `Γ - 4` are bounded
by `Γ` once `Γ ≥ 4`. -/
theorem abs_fderiv_le {v : OrthonormalBasis (Fin 4) ℝ ℝ⁴} {u : ℝ⁴ → ℝ} {x : ℝ⁴} {Γ : ℝ}
    (hΓ : 4 ≤ Γ) (h : ‖fderiv ℝ u x‖ ≤ Γ - 4) (i : Fin 4) :
    |(fderiv ℝ u x) (v i)| ≤ Γ := by
  have h1 : ‖(fderiv ℝ u x) (v i)‖ ≤ ‖fderiv ℝ u x‖ * ‖v i‖ :=
    ContinuousLinearMap.le_opNorm _ _
  rw [v.norm_eq_one i, mul_one] at h1
  rw [Real.norm_eq_abs] at h1
  linarith

/-- The squared gradient bound, in coordinates. -/
theorem sum_sq_fderiv_le {v : OrthonormalBasis (Fin 4) ℝ ℝ⁴} {u : ℝ⁴ → ℝ} {x : ℝ⁴} {Γ : ℝ}
    (hΓ : 4 ≤ Γ) (h : ‖fderiv ℝ u x‖ ≤ Γ - 4) :
    (∑ i : Fin 4, ((fderiv ℝ u x) (v i)) ^ 2) ≤ Γ ^ 2 := by
  rw [← norm_sq_eq_sum_sq_apply v (fderiv ℝ u x)]
  have h4 : (0 : ℝ) ≤ Γ - 4 := by linarith
  nlinarith [norm_nonneg (fderiv ℝ u x), h, h4]

/-- The pointwise lower bound `2 ≤ (Δu)²` for solutions: `sigma_1 = Δu` is the trace of the
Hessian and `sigma_2 = 1` gives `(σ₁)² = 2 + |λ|² ≥ 2`.  In particular `√2 ≤ Δu`. -/
theorem laplacian_sq_ge_two {u : ℝ⁴ → ℝ} {s : Set ℝ⁴} {x : ℝ⁴} (hs : IsOpen s) (hx : x ∈ s)
    (hu : ContDiffOn ℝ 2 u s) (hσ2 : ∀ y ∈ s, σ₂ (H u s y) = 1) :
    2 ≤ ((Δ u) x) ^ 2 := by
  have hT : (H u s x).IsSymmetric := isSymmetric_hessianWithin hs hx hu
  have hpair : (∑ j : Fin (Module.finrank ℝ ℝ⁴), ∑ i : Fin (Module.finrank ℝ ℝ⁴),
      if i < j then hT.eigenvalues rfl i * hT.eigenvalues rfl j else 0) = 1 := by
    have h := hσ2 x hx
    rw [HessianEstimates.σ₂, dif_pos hT] at h
    rw [show (∑ j : Fin (Module.finrank ℝ ℝ⁴), ∑ i < j,
          hT.eigenvalues rfl i * hT.eigenvalues rfl j)
        = (∑ j : Fin (Module.finrank ℝ ℝ⁴), ∑ i : Fin (Module.finrank ℝ ℝ⁴),
            if i < j then hT.eigenvalues rfl i * hT.eigenvalues rfl j else 0) from
        Finset.sum_congr rfl (fun j _ => by
          show (∑ i ∈ Finset.Iio j, _) = _
          rw [show Finset.Iio j = Finset.univ.filter (fun x => x < j) from by
                ext x; simp [Finset.mem_Iio], Finset.sum_filter])] at h
    exact h
  have htr := trace_sq_ge_two_of_pair_sum hT hpair
  have hlap := laplacian_eq_trace_hessian (u := u) (s := s) (x := x) hs hx hu
    (stdOrthonormalBasis ℝ ℝ⁴)
  rw [hlap]
  exact htr

end Submission

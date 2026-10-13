/-
  Work.WilE2 — area E2.  The Jacobian determinant of the graph map.

  `graphMap S F : ℝⁿ⁺¹ → ℝⁿ⁺¹` is the map `z ↦ (liftSystem S F z, rolleg S z)`; its `j`-th
  component is the function `liftFun S F j` (the `j`-th lifted equation for `j < n`, and the
  graph function `g = rolleg S` for `j = n`).  The statement below says that the determinant of
  the Fréchet derivative of `graphMap S F` at `z` is the determinant of the matrix of the
  directional derivatives of the components in the standard basis — i.e. that the Jacobian really
  is the matrix `∂(graphMap)ⱼ/∂xᵢ`.

  The contents are:

  * `det_eq_det_coord` — for a continuous linear endomorphism `L` of `ℝᵏ`, `det L` equals the
    determinant of the matrix `L (Pi.single i 1) j` (the transpose of `LinearMap.toMatrix'`).
  * `fderiv_det_coord` — the same for `L = fderiv ℝ g z`, where `g : ℝᵏ → ℝᵏ` is differentiable:
    this is `fderiv_pi` plus `det_eq_det_coord`.
  * `liftFun_eq_graphMap` — the `j`-th component of `graphMap` is `liftFun S F j`.
  * `differentiableAt_liftFun` — each component is differentiable.
-/
import Mathlib
import Submission.Work.WilE2.KhoGood
import Submission.Work.WilE2.RegSol
import Submission.Work.WilE2.RolleDetAnalytic

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace Work.WilE2

open Classical

variable {n s : ℕ}

/-! ## §1. The determinant of a linear map and the matrix of its values on the basis -/

/-- The determinant of a continuous linear endomorphism of `ℝᵏ` is the determinant of its matrix
of values on the standard basis vectors `Pi.single i 1`, indexed as in the theorem below. -/
theorem det_eq_det_coord {k : ℕ} (L : (Fin k → ℝ) →L[ℝ] (Fin k → ℝ)) :
    L.det = (Matrix.of fun (i j : Fin k) => L (Pi.single i 1) j).det := by
  have h : Matrix.of (fun (i j : Fin k) => L (Pi.single i 1) j)
      = Matrix.transpose (LinearMap.toMatrix' (L : (Fin k → ℝ) →ₗ[ℝ] (Fin k → ℝ))) := by
    ext i j
    rw [Matrix.transpose_apply, LinearMap.toMatrix'_apply, Matrix.of_apply]
    rfl
  rw [h, Matrix.det_transpose, LinearMap.det_toMatrix', ContinuousLinearMap.det]

/-- For a differentiable map `g : ℝᵏ → ℝᵏ`, the determinant of its Fréchet derivative at `z` is
the determinant of the matrix of the directional derivatives of its components. -/
theorem fderiv_det_coord {k : ℕ} (g : (Fin k → ℝ) → (Fin k → ℝ)) (z : Fin k → ℝ)
    (hg : DifferentiableAt ℝ g z) :
    (fderiv ℝ g z).det =
      (Matrix.of fun (i j : Fin k) => fderiv ℝ (fun w => g w j) z (Pi.single i 1)).det := by
  have hpi : fderiv ℝ g z = ContinuousLinearMap.pi (fun j => fderiv ℝ (fun w => g w j) z) := by
    have h := fderiv_pi (𝕜 := ℝ) (x := z) (φ := fun (j : Fin k) (w : Fin k → ℝ) => g w j)
      (fun j => (differentiableAt_pi.mp hg) j)
    simpa using h
  rw [hpi, det_eq_det_coord]
  congr 1

/-! ## §2. The components of the graph map -/

/-- The `j`-th component of `graphMap S F` is `liftFun S F j`. -/
theorem liftFun_eq_graphMap (S : ESys n (s + 1)) (F : Fin n → EPoly n (s + 1))
    (j : Fin (n + 1)) :
    liftFun S F j = fun w => graphMap S F w j := by
  refine Fin.lastCases ?_ ?_ j
  · funext w
    simp only [liftFun_of_not_lt S F (Fin.last n) (by simp), graphMap, Fin.snoc_last]
  · intro i
    funext w
    simp only [liftFun_of_lt S F (Fin.castSucc i) (by simp), graphMap, Fin.snoc_castSucc, liftSystem,
      Fin.val_castSucc, Fin.eta]

/-- Each component of the graph map is differentiable: the lifted equations are evaluated EA
polynomials along the lifted chain, and the graph function is `ψ_{s+1} - x_{n+1}`. -/
theorem differentiableAt_liftFun (S : ESys n (s + 1)) (F : Fin n → EPoly n (s + 1))
    (j : Fin (n + 1)) (z : Fin (n + 1) → ℝ) : DifferentiableAt ℝ (liftFun S F j) z := by
  by_cases h : (j : ℕ) < n
  · rw [liftFun_of_lt S F j h]
    exact (ev_hasFDerivAt S.liftChain (liftP (F ⟨j, h⟩)) z).differentiableAt
  · rw [liftFun_of_not_lt S F j h, rolleg_eq_ravel]
    have h1 : HasFDerivAt (fun w : Fin (n + 1) → ℝ => (S.ravel).psi (Fin.last s) w)
        ((S.ravel).psi (Fin.last s) z • (S.ravel).ellGrad (Fin.last s)) z :=
      ESys.hasFDerivAt_psi S.ravel (Fin.last s) z
    have h2 : HasFDerivAt (fun w : Fin (n + 1) → ℝ => w (Fin.last n))
        (ContinuousLinearMap.proj (Fin.last n) : (Fin (n + 1) → ℝ) →L[ℝ] ℝ) z :=
      ContinuousLinearMap.hasFDerivAt
        (ContinuousLinearMap.proj (Fin.last n) : (Fin (n + 1) → ℝ) →L[ℝ] ℝ) (x := z)
    exact (h1.sub h2).differentiableAt

/-! ## §3. The Jacobian determinant of the graph map -/

theorem fderiv_graphMap_det {n s : ℕ} (S : ESys n (s + 1)) (F : Fin n → EPoly n (s + 1))
    (z : Fin (n + 1) → ℝ) :
    (fderiv ℝ (graphMap S F) z).det =
      (Matrix.of fun (i j : Fin (n + 1)) => fderiv ℝ (liftFun S F j) z (Pi.single i (1 : ℝ))).det := by
  have hd : DifferentiableAt ℝ (graphMap S F) z :=
    differentiableAt_pi.mpr fun j => by
      rw [show (fun w => graphMap S F w j) = liftFun S F j from (liftFun_eq_graphMap S F j).symm]
      exact differentiableAt_liftFun S F j z
  rw [fderiv_det_coord (graphMap S F) z hd]
  refine congrArg Matrix.det ?_
  ext a b
  simp only [Matrix.of_apply]
  rw [← liftFun_eq_graphMap S F b]

end Work.WilE2

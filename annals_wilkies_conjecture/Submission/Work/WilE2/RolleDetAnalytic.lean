/-
  Work.WilE2 — area E2.  The paper's Claim `regular-solutions`.

  The evaluated Rolle determinant of the lift is the determinant of the analytic Rolle matrix
  `[∂g_1/∂z_i | … | ∂g_n/∂z_i | ∂g/∂z_i]` of the lifted system, and consequently the old Jacobian
  determinant is minus that determinant: a root of the old system is non-degenerate exactly when
  the lifted root is a transversal crossing of the graph `N = {g = 0}`.
-/
import Mathlib
import Submission.Work.WilE2.RollegDeriv
import Submission.Work.WilE2.KhoCount

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.WilE2

open Classical
open WilkiesDesign WilkiesDesign.E WilkiesConjecture

variable {n s : ℕ}

/-- The analytic Rolle matrix of the lifted system is the `tangMatrix` of the cross-product
construction. -/
theorem analyticRolleMat_eq (S : ESys n (s + 1)) (F : Fin n → EPoly n (s + 1))
    (z : Fin (n + 1) → ℝ) :
    (Matrix.of fun (i j : Fin (n + 1)) => fderiv ℝ (liftFun S F j) z (Pi.single i 1))
      = tangMatrix (liftSystem S F) z (rollGrad S z) := by
  ext i j
  rw [Matrix.of_apply, tangMatrix, Matrix.of_apply]
  by_cases hj : (j : ℕ) < n
  · rw [dif_pos hj, liftFun_of_lt S F j hj]
    rfl
  · rw [dif_neg hj, liftFun_of_not_lt S F j hj]
    rfl

/-- **The evaluated Rolle determinant is the determinant of the analytic Rolle matrix.** -/
theorem ev_rolleDet_analytic (S : ESys n (s + 1)) (F : Fin n → EPoly n (s + 1))
    (x : Fin n → ℝ) :
    (S.liftChain).ev (S.rolleDet F) (Fin.snoc x (S.lastPsi x)) =
      (Matrix.of fun (i j : Fin (n + 1)) =>
        fderiv ℝ (liftFun S F j) (Fin.snoc x (S.lastPsi x)) (Pi.single i 1)).det := by
  have hentry : ∀ i j : Fin (n + 1),
      (S.liftChain).ev (S.rolleMat F i j) (Fin.snoc x (S.lastPsi x))
        = fderiv ℝ (liftFun S F j) (Fin.snoc x (S.lastPsi x)) (Pi.single i 1) := by
    intro i j
    by_cases hj : (j : ℕ) < n
    · rw [ESys.rolleMat, Matrix.of_apply, dif_pos hj, liftFun_of_lt S F j hj, fderiv_ev_single]
    · rw [ESys.rolleMat, Matrix.of_apply, dif_neg hj, liftFun_of_not_lt S F j hj]
      rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
      · rw [ESys.liftChain_ev_eta_castSucc, (fderiv_rolleg_apply S (Fin.snoc x (S.lastPsi x))).1 i',
          Fin.init_snoc]
      · rw [ESys.liftChain_ev_eta_last, (fderiv_rolleg_apply S (Fin.snoc x (S.lastPsi x))).2]
  have hdet : (S.liftChain).ev (S.rolleDet F) (Fin.snoc x (S.lastPsi x))
      = (Matrix.of fun i j =>
          (S.liftChain).ev (S.rolleMat F i j) (Fin.snoc x (S.lastPsi x))).det := by
    have hmat : (Matrix.of fun i j =>
          (S.liftChain).ev (S.rolleMat F i j) (Fin.snoc x (S.lastPsi x)))
        = (S.rolleMat F).map (fun P => (S.liftChain).ev P (Fin.snoc x (S.lastPsi x))) := by
      ext i j
      rw [Matrix.map_apply, Matrix.of_apply]
    rw [hmat, ESys.rolleDet]
    have h := RingHom.map_det
      (MvPolynomial.eval (Sum.elim (Fin.snoc x (S.lastPsi x))
        (fun j => (S.liftChain).psi j (Fin.snoc x (S.lastPsi x)))))
      (S.rolleMat F)
    rw [RingHom.mapMatrix_apply] at h
    simpa only [ESys.ev] using h
  rw [hdet]
  refine congrArg Matrix.det ?_
  ext i j
  exact hentry i j

/-- **Claim `regular-solutions`.**  The old Jacobian determinant is minus the determinant of the
analytic Rolle matrix of the lifted system. -/
theorem det_lift_analytic (S : ESys n (s + 1)) (F : Fin n → EPoly n (s + 1)) (x : Fin n → ℝ) :
    (Matrix.of fun i j => S.ev (S.d j (F i)) x).det =
      -(Matrix.of fun (i j : Fin (n + 1)) =>
        fderiv ℝ (liftFun S F j) (Fin.snoc x (S.lastPsi x)) (Pi.single i 1)).det := by
  rw [det_lift_eq S F x, ev_rolleDet_analytic S F x]

/-- The same identity with the analytic determinant on the left. -/
theorem det_analytic_eq (S : ESys n (s + 1)) (F : Fin n → EPoly n (s + 1)) (x : Fin n → ℝ) :
    (Matrix.of fun (i j : Fin (n + 1)) =>
        fderiv ℝ (liftFun S F j) (Fin.snoc x (S.lastPsi x)) (Pi.single i 1)).det =
      -(Matrix.of fun i j => S.ev (S.d j (F i)) x).det := by
  rw [det_lift_analytic S F x, neg_neg]

/-- A point is a non-degenerate zero of the old system if and only if the corresponding lifted
point is a non-degenerate zero of the lifted system (a transversal crossing of the graph). -/
theorem nondegen_iff_lift (S : ESys n (s + 1)) (F : Fin n → EPoly n (s + 1)) (x : Fin n → ℝ) :
    S.Nondegen F x ↔
      (∀ i, (S.liftChain).ev (liftP (F i)) (Fin.snoc x (S.lastPsi x)) = 0) ∧
        (Matrix.of fun (i j : Fin (n + 1)) =>
          fderiv ℝ (liftFun S F j) (Fin.snoc x (S.lastPsi x)) (Pi.single i 1)).det ≠ 0 := by
  constructor
  · rintro ⟨hz, hdet⟩
    refine ⟨fun i => ?_, fun h => hdet ?_⟩
    · rw [ESys.ev_liftP_lastPsi]; exact hz i
    · rw [det_lift_analytic S F x, h, neg_zero]
  · rintro ⟨hz, hdet⟩
    refine ⟨fun i => ?_, fun h => hdet ?_⟩
    · rw [← ESys.ev_liftP_lastPsi S (F i) x]; exact hz i
    · rw [det_analytic_eq S F x, h, neg_zero]

/-- The evaluated Rolle determinant is the derivative of the graph function along the
cross-product field of the lifted system: the hypothesis `ψ = dg(X)` of the Rolle counting. -/
theorem ev_rolleDet_eq_crossField (S : ESys n (s + 1)) (F : Fin n → EPoly n (s + 1))
    (x : Fin n → ℝ) :
    (S.liftChain).ev (S.rolleDet F) (Fin.snoc x (S.lastPsi x)) =
      fderiv ℝ (rolleg S) (Fin.snoc x (S.lastPsi x))
        (crossField (liftSystem S F) (Fin.snoc x (S.lastPsi x))) := by
  rw [fderiv_crossField]
  rw [show (fun i => fderiv ℝ (rolleg S) (Fin.snoc x (S.lastPsi x)) (Pi.single i 1))
      = rollGrad S (Fin.snoc x (S.lastPsi x)) from rfl,
    ← analyticRolleMat_eq S F (Fin.snoc x (S.lastPsi x)), ← ev_rolleDet_analytic S F x]

end Work.WilE2

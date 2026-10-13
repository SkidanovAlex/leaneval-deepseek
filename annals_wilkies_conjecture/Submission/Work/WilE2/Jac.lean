/-
  Work.WilE2 — area E2.  The differential of the system map.

  `ev_hasFDerivAt` (proved elsewhere in this directory) gives the derivative of one evaluated
  EA polynomial.  Differentiating componentwise gives the differential of the system map
  `x ↦ (S.ev (F i) x)_i`, and evaluating that differential on the standard basis vector `e_j`
  recovers the `j`-th column of the symbolic Jacobian `S.ev (S.d j (F i)) x`.  This is the
  bridge needed to speak about nondegenerate zeros geometrically.
-/
import Submission.Work.WilE2.ev_hasFDerivAt
import Mathlib.Analysis.Calculus.FDeriv.Pi

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section
open Classical
namespace Work.WilE2

open WilkiesDesign WilkiesDesign.E WilkiesConjecture

variable {n r : ℕ}

/-- The system map of an EA system is differentiable, with differential the tuple of gradients
(the rows of the symbolic Jacobian). -/
theorem system_hasFDerivAt (S : ESys n r) (F : Fin n → EPoly n r) (x : Fin n → ℝ) :
    HasFDerivAt (fun y : Fin n → ℝ => fun i => S.ev (F i) y)
      (ContinuousLinearMap.pi fun i => S.grad (F i) x) x :=
  hasFDerivAt_pi.mpr fun i => ev_hasFDerivAt S (F i) x

theorem fderiv_system (S : ESys n r) (F : Fin n → EPoly n r) (x : Fin n → ℝ) :
    fderiv ℝ (fun y : Fin n → ℝ => fun i => S.ev (F i) y) x =
      ContinuousLinearMap.pi fun i => S.grad (F i) x :=
  (system_hasFDerivAt S F x).fderiv

/-- The `j`-th column of the differential of the system map is the column of symbolic
derivatives `S.ev (S.d j (F i)) x`. -/
theorem fderiv_system_apply (S : ESys n r) (F : Fin n → EPoly n r) (x : Fin n → ℝ)
    (j : Fin n) :
    fderiv ℝ (fun y : Fin n → ℝ => fun i => S.ev (F i) y) x (Pi.single j 1) =
      fun i => S.ev (S.d j (F i)) x := by
  rw [fderiv_system]
  funext i
  rw [ContinuousLinearMap.pi_apply, ESys.grad_apply, Finset.sum_eq_single j]
  · rw [Pi.single_eq_same, mul_one]
  · intro a _ ha
    rw [Pi.single_eq_of_ne ha, mul_zero]
  · intro h; exact absurd (Finset.mem_univ j) h

end Work.WilE2

/-
  annals_wilkies_conjecture, AREA E3K (`Submission.Work.WilE3K`): the Rolle step's value
  bookkeeping.

  For `E : ETData N (rt+1) n re` and the level `y` of the remaining system:

  * `E.rolleDetFun z = (E.jac z).det` (the evaluated scaled Rolle determinant divided by the
    positive scaling factor `E.prodEval z`);
  * the equations of the new system `E.newData y δ` are the old ones shifted by the level value,
    plus the Rolle equation `E.rolleDetP - δ · E.prodPoly`;
  * on the crossings of the level set `{psiMap = y}` with the eliminated equation, all the
    equations of the new system vanish.
-/
import Mathlib
import Submission.Work.WilE3K.ET
import Submission.Work.WilE3K.Elim
import Submission.Work.WilE3K.ContAux
import Submission.Work.WilE3K.evalPoly_rolleDetP
import Submission.Work.WilE3K.ETRolle.IndexBook

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
namespace Work.WilE3K
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

variable {N rt n re : ℕ}

namespace ETData

variable (E : ETData N (rt + 1) n re)

/-! ## §1. The Rolle determinant and the evaluations of `EA`-polynomials -/

/-- The product of the scaling factors is positive. -/
theorem prodEval_pos (z : Fin (N + 1) → ℝ) : 0 < E.prodEval z :=
  Finset.prod_pos fun j _ => ETData.one_add_sq_pos z (E.tanCoord j)

/-- **The analytic Rolle determinant is the Jacobian determinant.** -/
theorem rolleDetFun_eq_jac_det (z : Fin (N + 1) → ℝ) :
    E.rolleDetFun z = (E.jac z).det := by
  rw [ETData.rolleDetFun, evalPoly_rolleDetP E z, div_eq_iff (ne_of_gt (E.prodEval_pos z))]
  ring

/-- Evaluation of the constant polynomial `1`. -/
theorem evalPoly_one (z : Fin (N + 1) → ℝ) :
    E.evalPoly (1 : EAPoly (N + 1) re) z = 1 := by
  change E.evalPoly (MvPolynomial.C (1 : ℝ)) z = 1
  rw [E.evalPoly_C]

/-- Evaluation of a subtraction. -/
theorem evalPoly_sub (P Q : EAPoly (N + 1) re) (z : Fin (N + 1) → ℝ) :
    E.evalPoly (P - Q) z = E.evalPoly P z - E.evalPoly Q z := by
  simp only [ETData.evalPoly, map_sub]

/-- Evaluation of a square. -/
theorem evalPoly_sq (P : EAPoly (N + 1) re) (z : Fin (N + 1) → ℝ) :
    E.evalPoly (P ^ 2) z = E.evalPoly P z ^ 2 := by
  rw [sq, E.evalPoly_mul, sq]

/-- Evaluation of a product of `EA`-polynomials. -/
theorem evalPoly_finset_prod {ι : Type*} (s : Finset ι) (g : ι → EAPoly (N + 1) re)
    (z : Fin (N + 1) → ℝ) :
    E.evalPoly (∏ i ∈ s, g i) z = ∏ i ∈ s, E.evalPoly (g i) z := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.prod_empty, Finset.prod_empty]
    exact E.evalPoly_one z
  · intro a s ha ih
    rw [Finset.prod_insert ha, Finset.prod_insert ha, E.evalPoly_mul, ih]

/-- Evaluation of the product of the scaling factors. -/
theorem evalPoly_prodPoly (z : Fin (N + 1) → ℝ) :
    E.evalPoly E.prodPoly z = E.prodEval z := by
  rw [ETData.prodPoly, ETData.prodEval, E.evalPoly_finset_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [E.evalPoly_add, E.evalPoly_one, E.evalPoly_sq, E.evalPoly_X_tan]

/-- **The new Rolle equation vanishes at a point of the level set `{rolleDetFun = δ}`.** -/
theorem evalPoly_rolleDetP_sub (y : Fin N → ℝ) (δ : ℝ) (z : Fin (N + 1) → ℝ)
    (h : E.rolleDetFun z = δ) :
    E.evalPoly (E.rolleDetP - MvPolynomial.C δ * E.prodPoly) z = 0 := by
  rw [E.evalPoly_sub, E.evalPoly_mul, E.evalPoly_C, E.evalPoly_prodPoly,
    evalPoly_rolleDetP E z, ← E.rolleDetFun_eq_jac_det z, h]
  ring

/-! ## §2. The equations of the new system -/

/-- The arctan coefficients of the new system vanish on the new (eliminated) coordinate. -/
@[simp] theorem newLam_zero (y : Fin N → ℝ) (δ : ℝ) (j : Fin rt) :
    (E.newData y δ).lam j 0 = 0 := by
  simp only [ETData.newData, ETData.newLam]
  simp

/-- The arctan coefficients of the new system are the old ones (shifted by one). -/
theorem newLam_succ (y : Fin N → ℝ) (δ : ℝ) (j : Fin rt) (i : Fin n) :
    (E.newData y δ).lam j i.succ = E.lam (Fin.castSucc j) i := by
  have hne : ¬ ((i.succ : Fin (n + 1)) : ℕ) = 0 := by
    simp only [Fin.val_succ]
    omega
  simp only [ETData.newData, ETData.newLam]
  rw [dif_neg hne]
  exact congrArg (E.lam (Fin.castSucc j)) (Fin.ext (by simp only [Fin.val_succ]; omega))

/-- The constants of the new arctan equations. -/
theorem newMu_apply (y : Fin N → ℝ) (δ : ℝ) (j : Fin rt) (hj : (j : ℕ) < N) :
    (E.newData y δ).mu j = E.mu (Fin.castSucc j) + y ⟨j, hj⟩ := by
  show E.newMu y j = E.mu (Fin.castSucc j) + y ⟨j, hj⟩
  unfold ETData.newMu
  exact congrArg₂ (fun a b => a + b) rfl (congrArg y (Fin.ext rfl))

/-- **The arctan equations of the new system.** -/
theorem newData_lin (y : Fin N → ℝ) (δ : ℝ) (j : Fin rt) (hj : (j : ℕ) < N)
    (z : Fin (N + 1) → ℝ) :
    (E.newData y δ).lin j z = E.lin (Fin.castSucc j) z + y ⟨j, hj⟩ := by
  rw [ETData.lin, ETData.lin, Fin.sum_univ_succ]
  have hzero : (E.newData y δ).lam j 0 * z ((E.newData y δ).freeCoord 0) = 0 := by
    rw [E.newLam_zero, zero_mul]
  have hsucc : ∀ i : Fin n,
      (E.newData y δ).lam j i.succ * z ((E.newData y δ).freeCoord i.succ)
        = E.lam (Fin.castSucc j) i * z (E.freeCoord i) := by
    intro i
    rw [E.newLam_succ y δ j i, E.newData_freeCoord_succ y δ i]
  rw [hzero, zero_add, Finset.sum_congr rfl (fun i _ => hsucc i), E.newMu_apply y δ j hj]
  ring

/-- **The arctan equations of the new system.**  They are the old ones, shifted by the level
value. -/
theorem newData_tanFun (y : Fin N → ℝ) (δ : ℝ) (j : Fin rt) (hj : (j : ℕ) < N)
    (z : Fin (N + 1) → ℝ) :
    (E.newData y δ).tanFun j z = E.tanFun (Fin.castSucc j) z - y ⟨j, hj⟩ := by
  rw [ETData.tanFun, ETData.tanFun, E.newData_tanCoord y δ j, E.newData_lin y δ j hj z]
  ring

/-- **The new polynomial equation `0` is the Rolle equation.** -/
theorem newData_evP_zero (y : Fin N → ℝ) (δ : ℝ) (z : Fin (N + 1) → ℝ) :
    (E.newData y δ).evP 0 z
      = E.evalPoly (E.rolleDetP - MvPolynomial.C δ * E.prodPoly) z := by
  rw [ETData.evP, E.newData_evalPoly]
  congr 1

/-- **The new polynomial equations `i + 1` are the old ones, shifted by the level value.** -/
theorem newData_evP_succ (y : Fin N → ℝ) (δ : ℝ) (i : Fin n) (z : Fin (N + 1) → ℝ) :
    (E.newData y δ).evP i.succ z
      = E.evP i z - y ⟨rt + (i : ℕ), by have h := E.h; omega⟩ := by
  have hidx : ((i.succ : Fin (n + 1)) : ℕ) - 1 = (i : ℕ) := by
    simp only [Fin.val_succ]
    omega
  have hG : (E.newData y δ).G i.succ
      = E.G i - MvPolynomial.C (y ⟨rt + (i : ℕ), by have h := E.h; omega⟩) := by
    show E.newG y δ i.succ = _
    unfold ETData.newG
    rw [dif_neg (by simp only [Fin.val_succ]; omega)]
    congr 1
  rw [ETData.evP, hG, E.newData_evalPoly, E.evalPoly_sub, E.evalPoly_C, ← ETData.evP]

/-! ## §3. The new system vanishes on the crossings of the level set -/

/-- At a point of the level set `{psiMap = y}`, the arctan equations of the new system vanish. -/
theorem newData_tanFun_eq_zero (y : Fin N → ℝ) (δ : ℝ) (z : Fin (N + 1) → ℝ)
    (h1 : E.psiMap z = y) :
    ∀ j : Fin rt, (E.newData y δ).tanFun j z = 0 := by
  intro j
  have hj : (j : ℕ) < N := by have h := E.h; omega
  rw [E.newData_tanFun y δ j hj z]
  have hc : E.tanFun (Fin.castSucc j) z = y ⟨(j : ℕ), hj⟩ := by
    have h := congrFun h1 (Fin.castLE (by have h := E.h; omega) j)
    rw [E.psiMap_apply_tan z j] at h
    rwa [show (Fin.castLE (by have h := E.h; omega) j : Fin N) = ⟨(j : ℕ), hj⟩
      from Fin.ext rfl] at h
  rw [hc, sub_self]

/-- At a point of the level set `{psiMap = y}` with `rolleDetFun = δ`, the polynomial equations of
the new system vanish. -/
theorem newData_evP_eq_zero (y : Fin N → ℝ) (δ : ℝ) (z : Fin (N + 1) → ℝ)
    (h1 : E.psiMap z = y) (h2 : E.rolleDetFun z = δ) :
    ∀ i : Fin (n + 1), (E.newData y δ).evP i z = 0 := by
  intro i
  rcases Fin.eq_zero_or_eq_succ i with h | ⟨k, rfl⟩
  · subst h
    rw [E.newData_evP_zero y δ z, E.evalPoly_rolleDetP_sub y δ z h2]
  · rw [E.newData_evP_succ y δ k z]
    have hk : rt + (k : ℕ) < N := by have h := E.h; omega
    have h := congrFun h1 (Fin.castLE (by have h := E.h; omega) (Fin.natAdd rt k))
    rw [E.psiMap_apply_free z k] at h
    have hcast : (Fin.castLE (by have h := E.h; omega) (Fin.natAdd rt k) : Fin N)
        = (⟨rt + (k : ℕ), hk⟩ : Fin N) :=
      Fin.ext (by simp only [Fin.val_castLE, Fin.val_natAdd])
    rw [hcast] at h
    rw [← h]
    exact sub_self _

end ETData

end Work.WilE3K

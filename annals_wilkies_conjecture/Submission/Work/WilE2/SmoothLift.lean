/-
  Work.WilE2 — area E2.  Smoothness of evaluated EA polynomials.

  `S.ev P` is a polynomial in the coordinates and the chain functions `exp (ℓ_j x)`, hence `C^∞`;
  we only need `C²`, for the Sard input `regular_values_dense` (a `C²` rectangular map) and `C¹`
  for the inverse function theorem.  This module is self-contained (it does not import
  `contDiff_ev`) so that the final assembly does not depend on another agent's file.
-/
import Mathlib
import Submission.Work.WilE2.KhoGood

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.WilE2

open Classical
open WilkiesDesign WilkiesDesign.E WilkiesConjecture

variable {n r : ℕ}

/-- The affine exponent is `C^∞`. -/
theorem ESys.contDiff_ell' (S : ESys n r) (j : Fin r) (N : WithTop ℕ∞) : ContDiff ℝ N (S.ell j) := by
  have h : S.ell j = fun x : Fin n → ℝ => (∑ i, S.a j i * x i) + S.b j := by
    funext x; rw [ESys.ell]
  rw [h]
  fun_prop

/-- The chain function is `C^∞`. -/
theorem ESys.contDiff_psi' (S : ESys n r) (j : Fin r) (N : WithTop ℕ∞) : ContDiff ℝ N (S.psi j) := by
  exact (Real.contDiff_exp.of_le le_top).comp (S.contDiff_ell' j N)

/-- A single variable of the chain is `C²` along the evaluation. -/
theorem ESys.contDiff_ev_X' (S : ESys n r) (s : Fin n ⊕ Fin r) (N : WithTop ℕ∞) :
    ContDiff ℝ N (S.ev (MvPolynomial.X s)) := by
  rcases s with i | j
  · have h : S.ev (MvPolynomial.X (Sum.inl i)) = fun x : Fin n → ℝ => x i := by
      funext x; simp [ESys.ev]
    rw [h]
    fun_prop
  · rw [ESys.ev_X_inr]; exact S.contDiff_psi' j N

/-- Every evaluated EA polynomial is `C^∞`. -/
theorem ESys.contDiff_ev' (S : ESys n r) (N : WithTop ℕ∞) (P : EPoly n r) : ContDiff ℝ N (S.ev P) := by
  induction P using MvPolynomial.induction_on with
  | C c => rw [ESys.ev_C]; exact contDiff_const
  | add P Q hP hQ => rw [ESys.ev_add]; exact hP.add hQ
  | mul_X P s hP =>
      have hX := S.contDiff_ev_X' s N
      rw [ESys.ev_mul]
      exact hP.mul hX

/-- The lifted system map is `C²`. -/
theorem contDiff_liftSystem {n s : ℕ} (S : ESys n (s + 1)) (F : Fin n → EPoly n (s + 1)) :
    ContDiff ℝ 2 (liftSystem S F) := by
  rw [contDiff_pi]
  intro i
  exact S.liftChain.contDiff_ev' 2 (liftP (F i))

/-- The graph map (lifted system together with the graph function) is `C²`. -/
theorem contDiff_graphMap {n s : ℕ} (S : ESys n (s + 1)) (F : Fin n → EPoly n (s + 1)) :
    ContDiff ℝ 2 (graphMap S F) := by
  rw [contDiff_pi]
  intro i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · rw [show (fun z => graphMap S F z (Fin.castSucc j))
        = fun z => (S.liftChain).ev (liftP (F j)) z from by
      funext z; simp only [graphMap_apply_castSucc, liftSystem]]
    exact S.liftChain.contDiff_ev' 2 (liftP (F j))
  · rw [show (fun z => graphMap S F z (Fin.last n)) = rolleg S from by
      funext z; rw [graphMap_apply_last]]
    rw [rolleg_eq_ravel]
    refine (S.ravel.contDiff_psi' (Fin.last s) 2).sub ?_
    fun_prop

/-- The Rolle map (lifted system together with the Rolle determinant) is `C²`. -/
theorem contDiff_rolleMap {n s : ℕ} (S : ESys n (s + 1)) (F : Fin n → EPoly n (s + 1)) :
    ContDiff ℝ 2 (rolleMap S F) := by
  rw [contDiff_pi]
  intro i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · rw [show (fun z => rolleMap S F z (Fin.castSucc j))
        = fun z => (S.liftChain).ev (liftP (F j)) z from by
      funext z; simp only [rolleMap_apply_castSucc, liftSystem]]
    exact S.liftChain.contDiff_ev' 2 (liftP (F j))
  · rw [show (fun z => rolleMap S F z (Fin.last n)) = fun z => (S.liftChain).ev (S.rolleDet F) z
        from by funext z; simp only [rolleMap_apply_last, rolleDetFun]]
    exact S.liftChain.contDiff_ev' 2 (S.rolleDet F)

end Work.WilE2

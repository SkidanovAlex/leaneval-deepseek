/-
  Work.WilE2 — area E2.  The algebraic hinge of the Khovanskii–Rolle elimination.

  On the graph `N = {x_{n+1} = ψ_{s+1}(x)}` the differential of the system map
  `x ↦ (S.ev (F i) x)_i` and the Rolle matrix `[∇g_1, …, ∇g_n, η]` are related by a Schur
  complement, so

    det (S.ev (S.d j (F i)) x) = - (S.liftChain).ev (S.rolleDet F) (Fin.snoc x (S.lastPsi x)).

  The proof: evaluate the Rolle determinant entrywise (`RingHom.map_det`), observe that the
  evaluated Rolle matrix has the block shape `[[Q, c], [b, -1]]`, and that the evaluated
  Jacobian is its Schur complement; then apply `det_fromBlocks_eq`.

  The two ingredients that the area's parallel development supplies separately are imported
  from `Submission.Work.WilE2.liftP_d` and `Submission.Work.WilE2.det_block_last`.
-/
import Mathlib
import Submission.Work.WilE2.Lift
import Submission.Work.WilE2.det_fromBlocks_eq
import Submission.Work.WilE2.liftP_d
import Submission.Work.WilE2.det_block_last

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
open Classical
namespace Work.WilE2

open WilkiesDesign WilkiesDesign.E WilkiesConjecture

variable {n s : ℕ}

/-! ## §1. Entry lemmas for the lift -/

/-- The new coordinate of the lift carries no chain function, so the symbolic derivative in
that direction is the plain partial derivative in the new variable. -/
theorem ESys.liftChain_d_last (S : ESys n (s + 1)) (Q : EPoly (n + 1) s) :
    (S.liftChain).d (Fin.last n) Q = MvPolynomial.pderiv (Sum.inl (Fin.last n)) Q := by
  rw [ESys.d]
  simp

/-- The `η` entry of the Rolle matrix at a non-last row is the coefficient of the last chain
function, times the new coordinate. -/
theorem ESys.liftChain_ev_eta_castSucc (S : ESys n (s + 1)) (j : Fin n) (x : Fin n → ℝ)
    (t : ℝ) :
    (S.liftChain).ev (S.eta (Fin.castSucc j)) (Fin.snoc x t) = S.a (Fin.last s) j * t := by
  have h : S.eta (Fin.castSucc j) =
      MvPolynomial.C (S.a (Fin.last s) j) *
        (MvPolynomial.X (Sum.inl (Fin.last n)) : EPoly (n + 1) s) := by
    have hk : (↑(Fin.castSucc j) : ℕ) < n := j.isLt
    rw [ESys.eta, dif_pos hk]
    refine congrArg (fun z : Fin n => MvPolynomial.C (S.a (Fin.last s) z) *
      (MvPolynomial.X (Sum.inl (Fin.last n)) : EPoly (n + 1) s)) ?_
    exact Fin.ext (by simp)
  rw [h]
  simp only [ESys.ev, MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
    Sum.elim_inl, Fin.snoc_last]

/-- The last entry of the Rolle matrix is `-1`. -/
theorem ESys.liftChain_ev_eta_last (S : ESys n (s + 1)) (x : Fin n → ℝ) (t : ℝ) :
    (S.liftChain).ev (S.eta (Fin.last n)) (Fin.snoc x t) = -1 := by
  have h : S.eta (Fin.last n) = (-1 : EPoly (n + 1) s) := by
    have hk : ¬ (↑(Fin.last n) : ℕ) < n := by
      rw [Fin.val_last]
      exact Nat.lt_irrefl n
    rw [ESys.eta, dif_neg hk]
  rw [h, ESys.ev, MvPolynomial.eval_neg, map_one]

/-- The derivative of the `j`-th component of the old system, in terms of the lift: the
symbolic derivative in the direction `j` splits into the derivative of the lifted polynomial
plus the correction coming from the last chain function. -/
theorem ESys.ev_d_eq (S : ESys n (s + 1)) (j : Fin n) (Q : EPoly n (s + 1)) (x : Fin n → ℝ) :
    S.ev (S.d j Q) x =
      (S.liftChain).ev ((S.liftChain).d (Fin.castSucc j) (liftP Q))
          (Fin.snoc x (S.lastPsi x)) +
        (S.liftChain).ev (S.eta (Fin.castSucc j)) (Fin.snoc x (S.lastPsi x)) *
          (S.liftChain).ev ((S.liftChain).d (Fin.last n) (liftP Q))
            (Fin.snoc x (S.lastPsi x)) := by
  rw [← ESys.ev_liftP_lastPsi S (S.d j Q) x, liftP_d S j Q,
    ESys.liftChain_ev_eta_castSucc S j x (S.lastPsi x)]
  simp only [ESys.ev, MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_C,
    MvPolynomial.eval_X, Sum.elim_inl, Fin.snoc_last]
  rw [← ESys.liftChain_d_last S (liftP Q)]

/-! ## §2. Evaluation of the Rolle determinant -/

/-- Evaluating the Rolle determinant in the lifted chain is the same as evaluating the Rolle
matrix entrywise. -/
private theorem ev_rolleDet_eq (S : ESys n (s + 1)) (F : Fin n → EPoly n (s + 1))
    (x : Fin n → ℝ) :
    (S.liftChain).ev (S.rolleDet F) (Fin.snoc x (S.lastPsi x)) =
      ((S.rolleMat F).map
        (fun P => (S.liftChain).ev P (Fin.snoc x (S.lastPsi x)))).det := by
  have h := RingHom.map_det
    (MvPolynomial.eval (Sum.elim (Fin.snoc x (S.lastPsi x))
      (fun j => (S.liftChain).psi j (Fin.snoc x (S.lastPsi x)))))
    (S.rolleMat F)
  rw [RingHom.mapMatrix_apply] at h
  rw [ESys.rolleDet]
  simpa only [ESys.ev] using h

/-! ## §3. The determinant identity -/

theorem det_lift_eq {n s : ℕ} (S : ESys n (s + 1)) (F : Fin n → EPoly n (s + 1))
    (x : Fin n → ℝ) :
    (Matrix.of fun i j => S.ev (S.d j (F i)) x).det =
      -(S.liftChain).ev (S.rolleDet F) (Fin.snoc x (S.lastPsi x)) := by
  obtain ⟨R, hR⟩ : ∃ R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ,
      R = (S.rolleMat F).map (fun P => (S.liftChain).ev P (Fin.snoc x (S.lastPsi x))) := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : Matrix (Fin n) (Fin n) ℝ,
      Q = Matrix.of (fun j k => (S.liftChain).ev
        ((S.liftChain).d (Fin.castSucc j) (liftP (F k))) (Fin.snoc x (S.lastPsi x))) := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : Fin n → ℝ,
      c = fun j => (S.liftChain).ev (S.eta (Fin.castSucc j)) (Fin.snoc x (S.lastPsi x)) :=
    ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : Fin n → ℝ,
      b = fun k => (S.liftChain).ev ((S.liftChain).d (Fin.last n) (liftP (F k)))
        (Fin.snoc x (S.lastPsi x)) := ⟨_, rfl⟩
  have hEv : (S.liftChain).ev (S.rolleDet F) (Fin.snoc x (S.lastPsi x)) = R.det := by
    rw [hR]
    exact ev_rolleDet_eq S F x
  have h11 : ∀ j k : Fin n, R (Fin.castSucc j) (Fin.castSucc k) = Q j k := by
    intro j k
    have hk : (↑(Fin.castSucc k) : ℕ) < n := k.isLt
    have hfin : (⟨(Fin.castSucc k : Fin (n + 1)).val, hk⟩ : Fin n) = k := Fin.ext (by simp)
    simp only [hR, Matrix.map_apply, ESys.rolleMat, Matrix.of_apply, dif_pos hk, hfin, hQ]
  have h12 : ∀ j : Fin n, R (Fin.castSucc j) (Fin.last n) = c j := by
    intro j
    have hk : ¬ (↑(Fin.last n) : ℕ) < n := by
      rw [Fin.val_last]
      exact Nat.lt_irrefl n
    simp only [hR, Matrix.map_apply, ESys.rolleMat, Matrix.of_apply, dif_neg hk, hc]
  have h21 : ∀ k : Fin n, R (Fin.last n) (Fin.castSucc k) = b k := by
    intro k
    have hk : (↑(Fin.castSucc k) : ℕ) < n := k.isLt
    have hfin : (⟨(Fin.castSucc k : Fin (n + 1)).val, hk⟩ : Fin n) = k := Fin.ext (by simp)
    simp only [hR, Matrix.map_apply, ESys.rolleMat, Matrix.of_apply, dif_pos hk, hfin, hb]
  have h22 : R (Fin.last n) (Fin.last n) = -1 := by
    have hk : ¬ (↑(Fin.last n) : ℕ) < n := by
      rw [Fin.val_last]
      exact Nat.lt_irrefl n
    simp only [hR, Matrix.map_apply, ESys.rolleMat, Matrix.of_apply, dif_neg hk]
    exact ESys.liftChain_ev_eta_last S x (S.lastPsi x)
  have hA : (Matrix.of fun i j => S.ev (S.d j (F i)) x).transpose =
      Q + Matrix.vecMulVec c b := by
    ext k i
    simp only [Matrix.transpose_apply, Matrix.add_apply, Matrix.vecMulVec_apply, Matrix.of_apply]
    rw [hQ, hc, hb]
    simp only [Matrix.of_apply]
    rw [ESys.ev_d_eq S k (F i) x]
  have hAt : (Matrix.of fun i j => S.ev (S.d j (F i)) x).det =
      (Q + Matrix.vecMulVec c b).det := by
    calc (Matrix.of fun i j => S.ev (S.d j (F i)) x).det
        = ((Matrix.of fun i j => S.ev (S.d j (F i)) x).transpose).det :=
          (Matrix.det_transpose _).symm
      _ = (Q + Matrix.vecMulVec c b).det := by rw [hA]
  have hRdet : R.det = -(Q + Matrix.vecMulVec c b).det :=
    det_block_last R Q c b h11 h12 h21 h22
  rw [hEv, hAt, hRdet, neg_neg]

end Work.WilE2

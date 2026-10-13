/-
  Work.WilE2 — area E2.  The Khovanskii–Rolle lift.

  Given a system with a chain of `s+1` functions, the lift replaces the last chain function
  `ψ_{s+1}(x) = exp(ℓ_{s+1}(x))` by a new coordinate `x_{n+1}`.  The lifted system has `s`
  chain functions in `n+1` variables.  The Rolle determinant `rolleDet` is the determinant of
  the matrix `[∇g_1, …, ∇g_n, η]` of the paper ("Rolle determinant degree"), and it is again a
  polynomial in the *shortened* chain: this is the mechanism by which the number of chain
  functions decreases by one at each elimination step.
-/
import Submission.Work.WilE2.Grad
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
open Classical
namespace Work.WilE2

open WilkiesDesign WilkiesDesign.E WilkiesConjecture

variable {n s : ℕ} {σ : Type*}

/-! ## §1. Degree of a determinant -/

/-- An integer cast into the polynomial ring is a constant, hence of total degree `0`. -/
theorem totalDegree_intCast (z : ℤ) : (z : MvPolynomial σ ℝ).totalDegree = 0 := by
  have h : (z : MvPolynomial σ ℝ) = MvPolynomial.C (z : ℝ) := by
    rw [MvPolynomial.C_eq_algebraMap]
    exact (map_intCast (algebraMap ℝ (MvPolynomial σ ℝ)) z).symm
  rw [h, MvPolynomial.totalDegree_C]

/-- If every entry of `M` in column `j` has total degree `≤ b j`, then so does `det M`. -/
theorem Matrix.det_totalDegree_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (MvPolynomial σ ℝ)) (b : ι → ℕ) (hb : ∀ i j, (M i j).totalDegree ≤ b j) :
    (M.det).totalDegree ≤ ∑ j, b j := by
  classical
  rw [Matrix.det_apply']
  refine (MvPolynomial.totalDegree_finsetSum_le fun σ' _ => ?_).trans (le_refl _)
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [totalDegree_intCast, Nat.zero_add]
  refine (MvPolynomial.totalDegree_finsetProd Finset.univ (fun i => M (σ' i) i)).trans ?_
  exact Finset.sum_le_sum fun i _ => hb (σ' i) i

/-! ## §2. The lifted chain -/

/-- The lift of a chain with `s+1` functions: the first `s` chain functions, regarded as
functions on `ℝ^{n+1}` (the last coefficient is zero, so they do not depend on the new
coordinate). -/
def ESys.liftChain (S : ESys n (s + 1)) : ESys (n + 1) s where
  a j i := if h : (i : ℕ) < n then S.a (Fin.castSucc j) ⟨i, h⟩ else 0
  b j := S.b (Fin.castSucc j)

@[simp] theorem ESys.liftChain_a_lt (S : ESys n (s + 1)) (j : Fin s) (i : Fin n) :
    (S.liftChain).a j (Fin.castSucc i) = S.a (Fin.castSucc j) i := by
  simp [ESys.liftChain, i.isLt]

@[simp] theorem ESys.liftChain_a_last (S : ESys n (s + 1)) (j : Fin s) :
    (S.liftChain).a j (Fin.last n) = 0 := by
  simp [ESys.liftChain]

@[simp] theorem ESys.liftChain_b (S : ESys n (s + 1)) (j : Fin s) :
    (S.liftChain).b j = S.b (Fin.castSucc j) := rfl

/-- The chain functions of the lifted chain agree with the first `s` chain functions of `S`,
evaluated at the first `n` coordinates. -/
theorem ESys.liftChain_ell (S : ESys n (s + 1)) (j : Fin s) (x : Fin n → ℝ) (t : ℝ) :
    (S.liftChain).ell j (Fin.snoc x t) = S.ell (Fin.castSucc j) x := by
  rw [ESys.ell, ESys.ell, Fin.sum_univ_castSucc]
  simp [Fin.snoc_castSucc]

theorem ESys.liftChain_psi (S : ESys n (s + 1)) (j : Fin s) (x : Fin n → ℝ) (t : ℝ) :
    (S.liftChain).psi j (Fin.snoc x t) = S.psi (Fin.castSucc j) x := by
  simp only [ESys.psi]
  rw [ESys.liftChain_ell]

/-- The last chain function of `S`, as a function of `x`. -/
def ESys.lastPsi (S : ESys n (s + 1)) (x : Fin n → ℝ) : ℝ := S.psi (Fin.last s) x

/-- `g(x,t) = ψ_{s+1}(x) - t`.  The graph `N = {g = 0}` is where the lifted system meets the
original one. -/
def rolleg (S : ESys n (s + 1)) (z : Fin (n + 1) → ℝ) : ℝ :=
  S.lastPsi (Fin.init z) - z (Fin.last n)

/-! ## §3. The variable substitution `ψ_{s+1}(x) ↦ x_{n+1}` -/

/-- `Fin.lastCases` evaluated at an index below `last`. -/
theorem Fin.lastCases_of_lt {β : Type*} {s : ℕ} {j : Fin (s + 1)} (hj : (j : ℕ) < s)
    (a : β) (f : Fin s → β) : Fin.lastCases a f j = f ⟨(j : ℕ), hj⟩ := by
  conv_lhs => rw [show j = Fin.castSucc ⟨(j : ℕ), hj⟩ from Fin.ext rfl]
  rw [Fin.lastCases_castSucc]

/-- `Fin.lastCases` evaluated at `Fin.last`. -/
theorem Fin.lastCases_of_not_lt {β : Type*} {s : ℕ} {j : Fin (s + 1)}
    (hj : ¬ (j : ℕ) < s) (a : β) (f : Fin s → β) : Fin.lastCases a f j = a := by
  have h : j = Fin.last s := Fin.ext (by simp at hj ⊢; omega)
  rw [h, Fin.lastCases_last]

/-- The change of variables: `x i ↦ x i`, `ψ_j ↦ ψ_j` (`j ≤ s`), `ψ_{s+1} ↦ x_{n+1}`. -/
def liftVar (n s : ℕ) : (Fin n ⊕ Fin (s + 1)) → (Fin (n + 1) ⊕ Fin s)
  | Sum.inl i => Sum.inl (Fin.castSucc i)
  | Sum.inr j => Fin.lastCases (Sum.inl (Fin.last n)) (fun k => Sum.inr k) j

/-- The corresponding substitution of EA polynomials. -/
def liftP {n s : ℕ} (P : EPoly n (s + 1)) : EPoly (n + 1) s :=
  MvPolynomial.rename (liftVar n s) P

theorem liftP_totalDegree_le (P : EPoly n (s + 1)) :
    (liftP P).totalDegree ≤ P.totalDegree :=
  MvPolynomial.totalDegree_rename_le _ _

/-- The evaluation point of the lifted polynomial: the first `s` chain functions of `S` and the
new coordinate `t` in place of the last one. -/
def ESys.liftEval (S : ESys n (s + 1)) (x : Fin n → ℝ) (t : ℝ) : (Fin n ⊕ Fin (s + 1)) → ℝ
  | Sum.inl i => x i
  | Sum.inr j => Fin.lastCases t (fun k => S.psi (Fin.castSucc k) x) j

/-- Evaluating the substituted polynomial along the lifted chain. -/
theorem ESys.ev_liftP (S : ESys n (s + 1)) (P : EPoly n (s + 1)) (x : Fin n → ℝ) (t : ℝ) :
    (S.liftChain).ev (liftP P) (Fin.snoc x t) = MvPolynomial.eval (S.liftEval x t) P := by
  rw [ESys.ev, liftP, MvPolynomial.eval_rename]
  refine congrArg (fun f => MvPolynomial.eval f P) ?_
  funext v
  rcases v with i | j
  · simp [liftVar, ESys.liftEval]
  · by_cases hj : (j : ℕ) < s
    · simp only [Function.comp_apply, liftVar, Fin.lastCases_of_lt hj, Sum.elim_inr,
        ESys.liftChain_psi, ESys.liftEval]
    · simp only [Function.comp_apply, liftVar, Fin.lastCases_of_not_lt hj, Sum.elim_inl,
        Fin.snoc_last, ESys.liftEval]

/-- On the graph `N = {t = ψ_{s+1}(x)}` the lifted evaluation is the original evaluation. -/
theorem ESys.liftEval_lastPsi (S : ESys n (s + 1)) (x : Fin n → ℝ) :
    S.liftEval x (S.lastPsi x) = Sum.elim x (fun j => S.psi j x) := by
  funext v
  rcases v with i | j
  · simp [ESys.liftEval]
  · by_cases hj : (j : ℕ) < s
    · simp only [ESys.liftEval, Fin.lastCases_of_lt hj, Sum.elim_inr]
      rw [show (⟨(j : ℕ), hj⟩ : Fin s).castSucc = j from Fin.ext rfl]
    · simp only [ESys.liftEval, Fin.lastCases_of_not_lt hj, Sum.elim_inr, ESys.lastPsi]
      rw [show j = Fin.last s from Fin.ext (by simp at hj ⊢; omega)]

/-- On the graph `N`, the lifted system reproduces the original system. -/
theorem ESys.ev_liftP_lastPsi (S : ESys n (s + 1)) (P : EPoly n (s + 1)) (x : Fin n → ℝ) :
    (S.liftChain).ev (liftP P) (Fin.snoc x (S.lastPsi x)) = S.ev P x := by
  rw [ESys.ev_liftP, ESys.liftEval_lastPsi]
  rfl

/-! ## §4. The Rolle determinant -/

/-- The vector `η = (a_{s+1,j} · t, …, -1)`: on the graph `N` it equals `∇g`. -/
def ESys.eta (S : ESys n (s + 1)) (i : Fin (n + 1)) : EPoly (n + 1) s :=
  if h : (i : ℕ) < n then
    MvPolynomial.C (S.a (Fin.last s) ⟨i, h⟩) * MvPolynomial.X (Sum.inl (Fin.last n))
  else -1

/-- The matrix `[∇g_1, …, ∇g_n, η]` of the paper. -/
def ESys.rolleMat (S : ESys n (s + 1)) (F : Fin n → EPoly n (s + 1)) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) (EPoly (n + 1) s) :=
  Matrix.of fun i j =>
    if h : (j : ℕ) < n then (S.liftChain).d i (liftP (F ⟨j, h⟩)) else S.eta i

/-- The Khovanskii–Rolle determinant: a polynomial in the *shortened* chain (`s` functions). -/
def ESys.rolleDet (S : ESys n (s + 1)) (F : Fin n → EPoly n (s + 1)) : EPoly (n + 1) s :=
  (S.rolleMat F).det

/-- The lifted system: the `n` lifted equations together with the Rolle determinant. -/
def ESys.liftedSystem (S : ESys n (s + 1)) (F : Fin n → EPoly n (s + 1)) :
    Fin (n + 1) → EPoly (n + 1) s :=
  Fin.lastCases (S.rolleDet F) (fun i => liftP (F i))

@[simp] theorem ESys.liftedSystem_castSucc (S : ESys n (s + 1)) (F : Fin n → EPoly n (s + 1))
    (i : Fin n) : S.liftedSystem F (Fin.castSucc i) = liftP (F i) := by
  simp [ESys.liftedSystem]

@[simp] theorem ESys.liftedSystem_last (S : ESys n (s + 1)) (F : Fin n → EPoly n (s + 1)) :
    S.liftedSystem F (Fin.last n) = S.rolleDet F := by
  simp [ESys.liftedSystem]

/-! ## §5. Degree of the Rolle determinant -/

theorem ESys.eta_totalDegree_le (S : ESys n (s + 1)) (i : Fin (n + 1)) :
    (S.eta i).totalDegree ≤ 1 := by
  rw [ESys.eta]
  split_ifs with h
  · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, Nat.zero_add, MvPolynomial.totalDegree_X]
  · rw [MvPolynomial.totalDegree_neg, MvPolynomial.totalDegree_one]
    exact Nat.zero_le 1

theorem ESys.rolleDet_totalDegree_le (S : ESys n (s + 1)) (F : Fin n → EPoly n (s + 1)) :
    (S.rolleDet F).totalDegree ≤ ∑ i, (F i).totalDegree + 1 := by
  have key : ∀ i j : Fin (n + 1), (S.rolleMat F i j).totalDegree ≤
      (if h : (j : ℕ) < n then (F ⟨j, h⟩).totalDegree else 1) := by
    intro i j
    rw [ESys.rolleMat]
    simp only [Matrix.of_apply]
    split_ifs with h
    · exact (ESys.d_totalDegree_le _ _ _).trans (liftP_totalDegree_le _)
    · exact S.eta_totalDegree_le i
  refine (Matrix.det_totalDegree_le _ _ key).trans ?_
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc]
  have hlast : (if h : (Fin.last n : Fin (n + 1)) < n then
      (F ⟨Fin.last n, h⟩).totalDegree else 1) = 1 := by
    rw [dif_neg (by simp)]
  rw [hlast]
  have hsum : (∑ i : Fin n, (if h : (i : ℕ) < n then (F ⟨i, h⟩).totalDegree else 1)) =
      ∑ i, (F i).totalDegree := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [dif_pos i.isLt]
  rw [hsum]

end Work.WilE2

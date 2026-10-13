/-
  Work.WilE2 — area E2.  Vocabulary for the lift / regular-solutions bridge.

  Setting: `S : ESys n (s+1)` is a chain of `s+1` functions, `F : Fin n → EPoly n (s+1)` a
  system, `S.liftChain : ESys (n+1) s` the lifted chain (the last chain function becoming the
  free coordinate `z (Fin.last n)`), `S.lastPsi` the last chain function and
  `g := rolleg S z = S.lastPsi (Fin.init z) - z (Fin.last n)` the graph equation, so that the
  roots of the old system correspond to the points of `N = {g = 0}`.

  This module contains the definitions used by the bridge lemmas (proved in the delegated
  modules under `WilE2/`):

  * `ESys.ravel` — the chain `S : ESys n s` regarded as a chain on `ℝⁿ⁺¹` not depending on the
    new coordinate (this is how the derivative of `g` in the `x`-directions is computed);
  * `liftFun` — the `j`-th function of the lifted system: the `j`-th lifted equation, or `g` for
    the last index;
  * `liftSystem` — the lifted system as a map `ℝⁿ⁺¹ → ℝⁿ`;
  * `rollGrad` — the gradient of `g`, the last column of the analytic Rolle matrix.
-/
import Mathlib
import Submission.Work.WilE2.Lift
import Submission.Work.WilE2.det_lift_eq
import Submission.Work.WilE2.ev_hasFDerivAt
import Submission.Work.WilE2.tangentField_exists
import Submission.Work.WilE2.KhoCount

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.WilE2

open Classical
open WilkiesDesign WilkiesDesign.E WilkiesConjecture

variable {n s : ℕ}

/-! ## §1. The chain extended to one more coordinate -/

/-- The chain `S` on `ℝⁿ`, regarded as a chain on `ℝⁿ⁺¹` not depending on the new coordinate. -/
def ESys.ravel (S : ESys n s) : ESys (n + 1) s where
  a j i := if h : (i : ℕ) < n then S.a j ⟨i, h⟩ else 0
  b j := S.b j

theorem ESys.ravel_a_castSucc (S : ESys n s) (j : Fin s) (i : Fin n) :
    (S.ravel).a j (Fin.castSucc i) = S.a j i := by
  show (if h : ((Fin.castSucc i : Fin (n + 1)) : ℕ) < n then
      S.a j ⟨((Fin.castSucc i : Fin (n + 1)) : ℕ), h⟩ else 0) = S.a j i
  rw [Fin.val_castSucc, dif_pos i.isLt]

theorem ESys.ravel_a_last (S : ESys n s) (j : Fin s) :
    (S.ravel).a j (Fin.last n) = 0 := by
  show (if h : ((Fin.last n : Fin (n + 1)) : ℕ) < n then
      S.a j ⟨((Fin.last n : Fin (n + 1)) : ℕ), h⟩ else 0) = 0
  rw [Fin.val_last, dif_neg (Nat.lt_irrefl n)]

theorem ESys.ravel_b (S : ESys n s) (j : Fin s) : (S.ravel).b j = S.b j := rfl

theorem ESys.ravel_ell (S : ESys n s) (j : Fin s) (z : Fin (n + 1) → ℝ) :
    (S.ravel).ell j z = S.ell j (Fin.init z) := by
  simp only [ESys.ell, Fin.sum_univ_castSucc, ESys.ravel_a_castSucc, ESys.ravel_a_last,
    ESys.ravel_b, Fin.init, zero_mul, add_zero]

theorem ESys.ravel_psi (S : ESys n s) (j : Fin s) (z : Fin (n + 1) → ℝ) :
    (S.ravel).psi j z = S.psi j (Fin.init z) := by
  rw [ESys.psi, ESys.psi, ESys.ravel_ell]

/-- The graph function as a difference of the extended chain and the new coordinate. -/
theorem rolleg_eq_ravel (S : ESys n (s + 1)) :
    rolleg S = fun z : Fin (n + 1) → ℝ => (S.ravel).psi (Fin.last s) z - z (Fin.last n) := by
  funext z
  rw [rolleg, ESys.lastPsi, ESys.ravel_psi]

/-! ## §2. The lifted system and its Rolle matrix -/

/-- The `j`-th function of the lifted system: the `j`-th lifted equation, or the graph function
`rolleg` for the last index. -/
def liftFun (S : ESys n (s + 1)) (F : Fin n → EPoly n (s + 1)) (j : Fin (n + 1)) :
    (Fin (n + 1) → ℝ) → ℝ :=
  if h : (j : ℕ) < n then fun w => (S.liftChain).ev (liftP (F ⟨j, h⟩)) w else rolleg S

/-- The system map of the lifted system, as a map `ℝⁿ⁺¹ → ℝⁿ`. -/
def liftSystem (S : ESys n (s + 1)) (F : Fin n → EPoly n (s + 1)) :
    (Fin (n + 1) → ℝ) → (Fin n → ℝ) :=
  fun w i => (S.liftChain).ev (liftP (F i)) w

/-- The gradient vector of the graph function `g`, used as the last column of the Rolle
matrix. -/
def rollGrad (S : ESys n (s + 1)) (z : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  fun i => fderiv ℝ (rolleg S) z (Pi.single i 1)

@[simp] theorem liftFun_of_lt (S : ESys n (s + 1)) (F : Fin n → EPoly n (s + 1))
    (j : Fin (n + 1)) (h : (j : ℕ) < n) :
    liftFun S F j = fun w => (S.liftChain).ev (liftP (F ⟨j, h⟩)) w := by
  rw [liftFun, dif_pos h]

@[simp] theorem liftFun_of_not_lt (S : ESys n (s + 1)) (F : Fin n → EPoly n (s + 1))
    (j : Fin (n + 1)) (h : ¬ (j : ℕ) < n) : liftFun S F j = rolleg S := by
  rw [liftFun, dif_neg h]

end Work.WilE2

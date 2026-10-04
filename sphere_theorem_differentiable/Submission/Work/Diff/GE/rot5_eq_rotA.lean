import Mathlib
import Submission.Work.Diff.GE.frobSq5_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `rot5` is the `5`-fold change of frame `rotA 5`

`rot5 A S` (`Work.Diff.GE.rot5`) changes the frame of a `(0,5)`-tensor array by contracting every
slot with `A`, i.e. it is the *uncurried* form of `rotA 5 A` applied to the curried tensor
`fun x : Fin 5 → Fin n => S (x 0) (x 1) (x 2) (x 3) (x 4)`.  This file proves the identification.

The content is the re-indexing of a sum over the function type `Fin 5 → Fin n` as a five-fold
iterated sum over `Fin n` (`sum_pi_five`, via the `5`-tuple equivalence `tupleEquiv`), together
with `Fin.prod_univ_five` for the product of the five change-of-frame factors.
-/

namespace Work.Diff.GE

open Finset LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg

/-- Re-indexing a function `Fin 5 → Fin n` as a nested `5`-tuple of its five coordinates. -/
def tupleEquiv (n : ℕ) : (Fin 5 → Fin n) ≃ Fin n × Fin n × Fin n × Fin n × Fin n where
  toFun y := (y 0, y 1, y 2, y 3, y 4)
  invFun p := ![p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2]
  left_inv y := by funext i; fin_cases i <;> rfl
  right_inv p := by rfl

/-- Every element of `Fin 5 → Fin n` is the vector of its five coordinates. -/
theorem fun_eq_vec5 {n : ℕ} (y : Fin 5 → Fin n) : y = ![y 0, y 1, y 2, y 3, y 4] := by
  funext i; fin_cases i <;> rfl

/-- A sum over the function type `Fin 5 → Fin n` is the corresponding five-fold iterated sum. -/
theorem sum_pi_five {n : ℕ} {β : Type*} [AddCommMonoid β] (F : (Fin 5 → Fin n) → β) :
    ∑ y : Fin 5 → Fin n, F y = ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, F ![a,b,c,d,e] := by
  refine (Fintype.sum_equiv (tupleEquiv n) F
      (fun p : Fin n × Fin n × Fin n × Fin n × Fin n =>
        F ![p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2]) ?_).trans ?_
  · intro y
    rw [fun_eq_vec5 y]
    rfl
  · simp only [Fintype.sum_prod_type]

theorem rot5_eq_rotA {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (S : Fin n → Curv4 n) : (fun x : Fin 5 → Fin n => rot5 A S (x 0) (x 1) (x 2) (x 3) (x 4)) = rotA 5 A (fun x : Fin 5 → Fin n => S (x 0) (x 1) (x 2) (x 3) (x 4)) := by
  funext x
  show rot5 A S (x 0) (x 1) (x 2) (x 3) (x 4)
      = rotA 5 A (fun y : Fin 5 → Fin n => S (y 0) (y 1) (y 2) (y 3) (y 4)) x
  rw [rotA]
  rw [sum_pi_five (F := fun y : Fin 5 → Fin n =>
        (∏ d : Fin 5, A (x d) (y d)) * S (y 0) (y 1) (y 2) (y 3) (y 4))]
  rw [rot5]
  simp only [Fin.prod_univ_five]
  rfl

end Work.Diff.GE

/-
  WilE4 — polynomial vocabulary for the effective CAD of area E4:
  specialization of a polynomial in `(m+1)` variables to a polynomial in the last variable,
  the derivative tower, the projection family (leading coefficients and pairwise resultants),
  sign conditions, atoms of a DNF, and the cylinder (padding) operation.

  Note on conventions. `MvPolynomial.finSuccEquiv ℝ m` splits off the FIRST variable as the
  polynomial variable. `spec` therefore first renames the last variable to the first position
  (via `Equiv.swap 0 (Fin.last m)`); the remaining coordinates are indexed by `Fin m` in the
  permuted order. All statements about the CAD only use this labelling consistently.
-/
import Submission.Work.WilE4.Basic
import Mathlib.Algebra.Polynomial.RuleOfSigns
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Algebra.MvPolynomial.Polynomial

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical
namespace Work.WilE4
open MvPolynomial

/-- The cyclic shift `i ↦ i + 1` of `Fin (m+1)`: it moves the last coordinate to the first place.
`finSuccEquiv` splits off the *first* variable, so specialising along `rot` splits off the *last*
one, while `pderiv` in the last variable becomes `pderiv 0`. -/
def rot (m : ℕ) : Fin (m+1) ≃ Fin (m+1) := finRotate (m+1)

@[simp] theorem rot_apply (m : ℕ) (i : Fin (m+1)) : rot m i = i + 1 := finRotate_apply i

@[simp] theorem rot_last (m : ℕ) : rot m (Fin.last m) = 0 := by
  rw [rot_apply]
  exact Fin.ext (by simp [Fin.val_add, Fin.last])

/-! ## Specialization to the last variable -/

/-- `spec P x`: view `P ∈ ℝ[X_0,…,X_m]` (last variable `X_m`) as a polynomial in `X_m` with the
other variables evaluated at `x`. -/
def spec {m : ℕ} (P : MvPolynomial (Fin (m+1)) ℝ) (x : Fin m → ℝ) : Polynomial ℝ :=
  ((MvPolynomial.finSuccEquiv ℝ m) (MvPolynomial.rename (rot m) P)).map
    (MvPolynomial.eval x)

@[simp] theorem spec_add {m : ℕ} (P Q : MvPolynomial (Fin (m+1)) ℝ) (x : Fin m → ℝ) :
    spec (P + Q) x = spec P x + spec Q x := by simp [spec]

@[simp] theorem spec_mul {m : ℕ} (P Q : MvPolynomial (Fin (m+1)) ℝ) (x : Fin m → ℝ) :
    spec (P * Q) x = spec P x * spec Q x := by simp [spec]

/-- The specialisation is evaluation at the point `Fin.snoc x t` obtained by appending `t` to `x`. -/
theorem spec_eval_snoc {m : ℕ} (P : MvPolynomial (Fin (m+1)) ℝ) (x : Fin m → ℝ) (t : ℝ) :
    (spec P x).eval t = MvPolynomial.eval (Fin.snoc x t) P := by
  have key : Polynomial.eval₂ (MvPolynomial.eval x) t
      (MvPolynomial.finSuccEquiv ℝ m (MvPolynomial.rename (rot m) P)) =
      MvPolynomial.eval x (Polynomial.eval (MvPolynomial.C t)
        (MvPolynomial.finSuccEquiv ℝ m (MvPolynomial.rename (rot m) P))) := by
    conv_lhs => rw [show t = (MvPolynomial.eval x) (MvPolynomial.C t) from by simp]
    rw [Polynomial.eval₂_hom]
  have hfun : (fun i : Fin (m + 1) => Fin.cases t x (rot m i)) = Fin.snoc x t := by
    funext i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · rw [rot_apply,
        show (j.castSucc : Fin (m + 1)) + 1 = j.succ from Fin.ext (by simp)]
      rw [Fin.cases_succ, Fin.snoc_castSucc]
    · rw [rot_last, Fin.cases_zero, Fin.snoc_last]
  rw [spec, Polynomial.eval_map, key, MvPolynomial.eval_polynomial_eval_finSuccEquiv,
    MvPolynomial.eval_rename]
  simp only [MvPolynomial.eval_C]
  rw [show ((fun i : Fin (m + 1) => Fin.cases t x i) ∘ (rot m)) = Fin.snoc x t from hfun]

/-! ## Sign conditions -/

/-- The sign conditions of a list of polynomials: `v` picks a sign for each member. -/
def signCond {m : ℕ} (G : List (MvPolynomial (Fin m) ℝ)) (v : Fin G.length → SignType) :
    Set (Fin m → ℝ) :=
  {x | ∀ i, SignType.sign (MvPolynomial.eval x (G.get i)) = v i}

/-! ## Atoms of a DNF -/

namespace BasicD

/-- The list of all atoms of a basic set. -/
def atoms {m : ℕ} (B : BasicD m) : List (MvPolynomial (Fin m) ℝ) := B.eqs ++ B.pos

end BasicD

namespace SAd

/-- The list of all atoms of a DNF. -/
def atoms {m : ℕ} (X : SAd m) : List (MvPolynomial (Fin m) ℝ) :=
  X.basics.flatMap BasicD.atoms

end SAd

/-! ## The cylinder (padding) operation -/

namespace SAd

/-- Regard a subset of `ℝ^m` as a subset of `ℝ^{m+1}` by ignoring the last coordinate. -/
def pad {m : ℕ} (X : SAd m) : SAd (m+1) :=
  ⟨X.basics.map fun B =>
    ⟨B.eqs.map (MvPolynomial.rename Fin.castSucc), B.pos.map (MvPolynomial.rename Fin.castSucc)⟩⟩

end SAd

end Work.WilE4

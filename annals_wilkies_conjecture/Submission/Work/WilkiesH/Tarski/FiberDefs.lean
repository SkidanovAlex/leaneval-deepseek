import Mathlib
import Submission.Work.WilkiesH.Tarski.definable_iff_polynomialSignSet

/-!
# Fibre polynomials of a polynomial in `n+1` variables

This file provides the vocabulary for the induction step of
`Work.WilkiesH.Tarski.exists_finite_connected_cover`: a polynomial
`G ∈ ℝ[x_1,…,x_n,Y]` (family index `Fin (n+1)` with `Fin.last n` the fibre direction)
is viewed as a *family* of one-variable polynomials parametrised by the base point
`u : Fin n → ℝ`, namely `u ↦ G(u,·)`.

The two numerical invariants of the fibre that the induction step uses are
* `#distinct real roots` = `(fiberPoly G u).roots.toFinset.card`, and
* `#real roots counted with multiplicity` = `(fiberPoly G u).roots.card`
  (for a *real* polynomial, `Polynomial.roots` is the multiset of roots *in ℝ* with
  multiplicity).
-/

set_option autoImplicit false
noncomputable section

open Polynomial

namespace Work.WilkiesH.Tarski

/-- Reindexing `Fin (n+1)` as `Option (Fin n)` with the *last* coordinate going to `none`. -/
def lastOption {n : ℕ} : Fin (n + 1) → Option (Fin n) := Fin.lastCases none (fun i => some i)

/-- The base point together with a value of the last coordinate. -/
def consPoint {n : ℕ} (u : Fin n → ℝ) (y : ℝ) : Fin (n + 1) → ℝ := Fin.snoc u y

/-- The fibre of `G ∈ ℝ[x_1,…,x_n,Y]` at `u`: the one-variable polynomial `G(u,·) ∈ ℝ[Y]`. -/
def fiberPoly {n : ℕ} (G : MvPolynomial (Fin (n + 1)) ℝ) (u : Fin n → ℝ) : Polynomial ℝ :=
  ((MvPolynomial.optionEquivLeft ℝ (Fin n)) (MvPolynomial.rename (lastOption (n := n)) G)).map
    (MvPolynomial.eval u)

theorem eval_consPoint {n : ℕ} (G : MvPolynomial (Fin (n + 1)) ℝ) (u : Fin n → ℝ) (y : ℝ) :
    MvPolynomial.eval (consPoint u y) G = (fiberPoly G u).eval y := by
  have hcomp : (fun o : Option (Fin n) => Option.elim o y u) ∘ (lastOption (n := n)) = consPoint u y := by
    funext i
    cases i using Fin.lastCases with
    | last => simp [lastOption, consPoint]
    | cast j => simp [lastOption, consPoint]
  calc MvPolynomial.eval (consPoint u y) G
      = MvPolynomial.eval ((fun o : Option (Fin n) => Option.elim o y u) ∘ (lastOption (n := n))) G := by
        rw [hcomp]
    _ = MvPolynomial.eval (fun o : Option (Fin n) => Option.elim o y u)
          (MvPolynomial.rename (lastOption (n := n)) G) := by
        rw [MvPolynomial.eval_rename]
    _ = (fiberPoly G u).eval y := by
        rw [fiberPoly]
        exact (Work.WilLibTS.TS.SignElimination.eval_optionEquivLeft _ u y).symm

/-- `y` is a root of the fibre `G(u,·)` iff the corresponding evaluation of `G` vanishes. -/
theorem eval_consPoint_eq_zero {n : ℕ} (G : MvPolynomial (Fin (n + 1)) ℝ) (u : Fin n → ℝ)
    (y : ℝ) : MvPolynomial.eval (consPoint u y) G = 0 ↔ (fiberPoly G u).eval y = 0 := by
  rw [eval_consPoint]

/-- `y` is a root of the fibre polynomial iff the corresponding evaluation of `G` vanishes. -/
theorem isRoot_fiberPoly_iff {n : ℕ} (G : MvPolynomial (Fin (n + 1)) ℝ) (u : Fin n → ℝ)
    (y : ℝ) : (fiberPoly G u).IsRoot y ↔ MvPolynomial.eval (consPoint u y) G = 0 := by
  rw [Polynomial.IsRoot.def, eval_consPoint]

@[simp]
theorem consPoint_init {n : ℕ} (u : Fin n → ℝ) (y : ℝ) : Fin.init (consPoint u y) = u := by
  simp [consPoint]

@[simp]
theorem consPoint_last {n : ℕ} (u : Fin n → ℝ) (y : ℝ) : consPoint u y (Fin.last n) = y := by
  simp [consPoint]

/-- Every point of `Fin (n+1) → ℝ` is `consPoint` of its init and last coordinate. -/
theorem snoc_init_last {n : ℕ} (z : Fin (n + 1) → ℝ) : consPoint (Fin.init z) (z (Fin.last n)) = z := by
  simp [consPoint]

end Work.WilkiesH.Tarski

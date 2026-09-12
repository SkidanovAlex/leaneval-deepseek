/-
The binary quadratic form attached to a Descartes quadruple at a circle
(route A toward χ₂ constancy; paper Proposition "quadformbij").

For the Descartes quadruple w with the circle w i in first position and the
cyclic neighbours (a,b,c,d) = (w i, w(i+1), w(i+2), w(i+3)), the paper's map
is f(x,y) = (a+b)x² + (a+b+c-d)xy + (a+c)y².  Here qfA/qfB/qfC are the three
coefficients, qfEval evaluates the form, and qf_discriminant proves the
defining identity B²-4AC = -4a² from the Descartes equation.

χ₂ of the circle at (w,i) is the Kronecker symbol of the leading coefficient
against the curvature; Prop1step (χ₂ equal for coprime tangent circles) is
stated in Work/Prop1step.lean and reduces, inside one Descartes quadruple, to
the reciprocity lemmas of ChiCross via χ₂(w,i) = pairChi (w i) (w j) for a
coprime tangent partner w j.
-/
import Submission.Apollo.Chi2
import Mathlib.Tactic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.Basic
set_option autoImplicit false
open scoped Pointwise
open LocalGlobalApollonianCirclePackings

namespace Apollo

/-- the ordered quadruple with first curvature at index i (cyclic successors). -/
def cycQuad (w : Fin 4 → ℤ) (i : Fin 4) : Fin 4 → ℤ
| 0 => w i
| 1 => w (i + 1)
| 2 => w (i + 2)
| 3 => w (i + 3)

/-- coefficients (A,B,C) of the binary quadratic form attached to the
Descartes quadruple w at the circle w i, in the cyclic ordering
(a,b,c,d) = (w i, w(i+1), w(i+2), w(i+3)): the paper's map
f(x,y) = (a+b)x² + (a+b+c-d)xy + (a+c)y². -/
def qfA (w : Fin 4 → ℤ) (i : Fin 4) : ℤ := w i + w (i + 1)
def qfB (w : Fin 4 → ℤ) (i : Fin 4) : ℤ := w i + w (i + 1) + w (i + 2) - w (i + 3)
def qfC (w : Fin 4 → ℤ) (i : Fin 4) : ℤ := w i + w (i + 2)

/-- the quadratic form f(x,y) attached to (w, i). -/
def qfEval (w : Fin 4 → ℤ) (i : Fin 4) (x y : ℤ) : ℤ :=
  qfA w i * x ^ 2 + qfB w i * x * y + qfC w i * y ^ 2

/-- the leading coefficient of the form at (w,i): ρ = a + b. -/
def qfRho (w : Fin 4 → ℤ) (i : Fin 4) : ℤ := qfA w i

/-- distinctness of the cyclic successors. -/
lemma fin_ne_succ {i : Fin 4} : i ≠ i + 1 := by fin_cases i <;> decide
lemma fin_ne_succ2 {i : Fin 4} : i ≠ i + 2 := by fin_cases i <;> decide
lemma fin_ne_succ3 {i : Fin 4} : i ≠ i + 3 := by fin_cases i <;> decide
lemma fin_succ_ne {i : Fin 4} : i + 1 ≠ i + 2 := by fin_cases i <;> decide
lemma fin_succ2_ne {i : Fin 4} : i + 1 ≠ i + 3 := by fin_cases i <;> decide
lemma fin_succ3_ne {i : Fin 4} : i + 2 ≠ i + 3 := by fin_cases i <;> decide

/-- the discriminant of the attached form is -4a² (a = w i), from the
Descartes equation in exact form. -/
theorem qf_discriminant (w : Fin 4 → ℤ) (hw : w ∈ apOrbit) (i : Fin 4) :
    (qfB w i) ^ 2 - 4 * (qfA w i) * (qfC w i) = -4 * (w i) ^ 2 := by
  let a := w i
  let b := w (i + 1)
  let c := w (i + 2)
  let d := w (i + 3)
  have hD := descartes_fourterm w hw
    (i := i) (j := i + 1) (k := i + 2) (l := i + 3)
    fin_ne_succ fin_ne_succ2 fin_ne_succ3 fin_succ_ne fin_succ2_ne fin_succ3_ne
  have hD' : (a + b + c + d) ^ 2 = 2 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
    simpa [a, b, c, d, add_assoc, add_comm, add_left_comm] using hD
  dsimp [qfA, qfB, qfC]
  change (a + b + c - d) ^ 2 - 4 * (a + b) * (a + c) = -4 * a ^ 2
  nlinarith [hD']

end Apollo

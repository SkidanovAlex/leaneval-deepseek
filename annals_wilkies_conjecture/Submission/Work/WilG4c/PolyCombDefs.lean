import Mathlib
import Submission.Work.WilG4c.GraphOfComp

set_option autoImplicit false
noncomputable section

namespace Work.WilG4c

open WilkiesDesign
open Work.WilG0 Work.WilG1

/-! ## Vocabulary for the polynomial-combination lemma `FamGraphPolyComb`

Given functions `H i : ℝ^m → ℝ` (`i : Fin k`) and `P : MvPolynomial (Fin k) ℝ` we want to
express the graph of `x ↦ P.eval (fun i => H i x)` in `ℝ^{m+1}` using the pullbacks of the
graphs of the `H i` inside `ℝ^{(m+1)+k}` with coordinates `(x, value, y)`.

The set built below is

`(⋂ i, {z | z ∘ sigY i ∈ graphOf (H i)}) ∩ {z | eval z (combPoly P) = 0}`

and its projection along the trailing `k` (`y`)-coordinates is the desired graph. -/

namespace PolyComb

/-- The coordinate substitution selecting the `x`-coordinates together with the `i`-th
auxiliary coordinate `y_i`: a map `Fin (m+1) → Fin ((m+1)+k)`. -/
def sigY (m k : ℕ) (i : Fin k) : Fin (m + 1) → Fin (m + 1 + k) :=
  Fin.snoc (fun j : Fin m => Fin.castAdd k (Fin.castSucc j)) (Fin.natAdd (m + 1) i)

/-- The index of the "value" coordinate in `ℝ^{(m+1)+k}`, i.e. the coordinate that should
equal the polynomial combination of the `y`'s. -/
def valIdx (m k : ℕ) : Fin (m + 1 + k) := Fin.castAdd k (Fin.last m)

/-- The index of the `i`-th auxiliary coordinate `y_i` in `ℝ^{(m+1)+k}`. -/
def yIdx (m k : ℕ) (i : Fin k) : Fin (m + 1 + k) := Fin.natAdd (m + 1) i

/-- The polynomial `value - P(y_0, …, y_{k-1})` whose zero set is the "polynomial
combination" hypersurface. -/
def combPoly (m k : ℕ) (P : MvPolynomial (Fin k) ℝ) : MvPolynomial (Fin (m + 1 + k)) ℝ :=
  MvPolynomial.X (valIdx m k) - MvPolynomial.rename (yIdx m k) P

end PolyComb

end Work.WilG4c

end
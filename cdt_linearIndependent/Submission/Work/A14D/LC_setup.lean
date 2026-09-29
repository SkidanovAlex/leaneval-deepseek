import Mathlib
import Submission.Work.A14.defs

/-!
# A14D — the "jump" objects of the `(LC)` transfer

Route (design §4, `REFS/design/a14/A14_design.lean.txt`): the relation
`Σᵢ Pᵢ(y)·fᵢ(y) = 0` among the fourteen functions of Theorem A is pulled back along `y = y(z)`,
and the *jump* `J(F) = F|SU − F|SL` is taken.  Since
`(Sym⁺ H)(y(z)) = H(z) + H(w z)`, the jump of the pulled-back `G` is `D − D∘w`, where
`D = HU − HL` is the jump of `H` (a hypothesis of the target lemma).  This gives a relation
among the jumps of the fourteen pulled-back functions; its coefficient of `log (z − 1/9)`
(graded by the truncated `y`-derivative / `y`-integral operations) is the `(LC)` identity.

This file only *defines* the objects; the analytic content lives in the delegated lemmas.
-/

open Complex Metric

noncomputable section
namespace Work.A14D

/-- `J(H) = D − D∘w`: the jump of the continued `H` across the cut `(−∞,1]`. -/
def jumpH (D : ℂ → ℂ) : ℂ → ℂ := fun z => D z - D (wC z)

/-- The jump of the pulled-back `k`-th `y`-derivative of `G`:
`J((∂_y^k G)∘y) = ∂_y^k (D − D∘w)`. -/
def jumpG (D : ℂ → ℂ) (k : ℕ) : ℂ → ℂ := DyIter k (jumpH D)

/-- The primitive along the segment from the centre `c`, vanishing at `c`. -/
def primSeg (f : ℂ → ℂ) (c : ℂ) : ℂ → ℂ :=
  fun z => ∫ t in (0 : ℝ)..1, f (c + (t : ℂ) * (z - c)) * (z - c)

/-- The derivative-of-the-integral jump for the `j`-th integral-type entry:
`J(∫ (G − jet) / y^j) ' = y'·y^{−j}·(D − D∘w)`. -/
def jumpI (D : ℂ → ℂ) (j : ℕ) : ℂ → ℂ :=
  primSeg (fun z => dyC z * (yC z)⁻¹ ^ j * jumpH D z) ninth

/-- The `j`-th primitive of `y^{−j}·y'·y9` (the `J_i` of the target lemma), with value `0`
at the ninth; it is the coefficient of `log (z − 1/9)` of `jumpI D j`. -/
def jPrim (y9 : ℂ → ℂ) (j : ℕ) : ℂ → ℂ :=
  primSeg (fun z => (yC z)⁻¹ ^ j * dyC z * y9 z) ninth

/-- The explicit coefficient of `log (z − 1/9)` in the jump of the fourteen pulled-back
functions, in the design's indexing: `κ·∂_y^k y9` for the four `G`-entries, `κ·J_j` for the
three integral entries, `0` for the seven pure entries. -/
def jumpCoeff (κ : ℂ) (y9 : ℂ → ℂ) : Fin 14 → ℂ → ℂ := fun i z =>
  if h : 5 ≤ (i : ℕ) ∧ (i : ℕ) ≤ 8 then κ * DyIter ((i : ℕ) - 5) y9 z
  else if h : 11 ≤ (i : ℕ) then κ * jPrim y9 ((i : ℕ) - 11) z
  else 0

end Work.A14D

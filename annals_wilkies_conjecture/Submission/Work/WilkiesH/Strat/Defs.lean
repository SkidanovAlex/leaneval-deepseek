import Mathlib
import Submission.Work.WilkiesH.Defs
import Submission.Work.WilkiesH.Count.Defs

/-!
# Area H (counting) — the stratification input (BNZ §2.3)

BNZ §6 proves the counting theorem by an induction on `μ = dim X`.  The step calls the
interpolation step (area (I), `Work.WilkiesH.ChartCover`) on the set `X`, obtaining a family
`V_1, …, V_m` of *semialgebraic* `Ω`-sets of dimension `≤ μ` covering the points of
`X.trans` of bounded degree and height.  The remaining geometric content is BNZ §2.3's
*stratification* metatheorem:

> a definable set is a disjoint union of finitely many connected *regular* strata (with
> controlled format and degree), and the complement of a stratum inside the closure has
> strictly smaller dimension.

Applied to the pair `(X, V)` this says: the points of `X ∩ V` which do not lie in a
positive-dimensional semialgebraic piece of `X` (i.e. which are not in `X.alg`) are contained
in boundedly many `Ω`-sets of dimension `≤ μ - 1`.  Such points are then counted by the
induction hypothesis.  Conversely, a point of `X ∩ V` which *is* a `μ`-regular point of `V`
and at which `V` is locally contained in `X` lies in `X.alg`
(`Work.WilkiesH.Mfd.mem_alg_of_isGraphAt`, and
`Work.WilkiesH.Mfd.mem_alg_of_semialg_limitPt` in the non-regular case), so it cannot occur in
`X.trans`.

This file states the stratification input in exactly the form the induction step consumes it,
with constants as in BNZ: for each `(F, n)` a format `a_{F,n}` (the `O_{F,n}(1)`), a number
of pieces `poly_{F,n}(D + D_V)` and a degree index `poly_{F,n}(D + D_V)`.

It is the single geometric input of the counting area; the interpolation step and the
assembly are independent of it.  It is *not* an axiom: it is a named hypothesis of the
assembly, to be proved from `SharpCD` via BNZ §2.3 (first-order closure of `Ω`, the
regular-part formula, and the dimension drop for the frontier of a definable set).
-/

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkiesH

open WilkiesDesign WilkiesConjecture

/-- **The stratification input.**  For a definable set `X ∈ Ω_{F,D}` and a semialgebraic
`Ω`-set `V ∈ Ω_{F,D_V}` with `dim V ≤ μ`, the transcendental part of `X ∩ V` is covered by at
most `poly_F(D + D_V)` `Ω`-sets of format `a_F` and degree index `poly_F(D + D_V)`, each of
dimension `≤ μ - 1` and each contained in `X`.

The pieces are contained in `X`, so that a point of `X.trans` lying in a piece is
automatically in the `.trans` of the piece: `(W j).alg ⊆ X.alg`. -/
def StratInput (S : SOMin) : Prop :=
  ∀ F n : ℕ, ∃ (a : ℕ) (pm : MvPolynomial (Fin 2) ℕ) (c : Polynomial ℕ),
    ∀ (μ : ℕ) (D Dv : ℕ) (X V : Set (Fin n → ℝ)),
      X ∈ S.Ω F D n → V ∈ S.Ω F Dv n → IsSemialgebraic V → DimLE V μ →
      ∃ (m : ℕ) (W : Fin m → Set (Fin n → ℝ)),
        m ≤ MvPolynomial.eval ![(D + Dv : ℕ), (n + 1 : ℕ)] pm ∧
        (∀ j, W j ∈ S.Ω a (c.eval (D + Dv)) n) ∧
        (∀ j, DimLE (W j) (μ - 1)) ∧
        (∀ j, W j ⊆ X) ∧
        ((X ∩ V) \ X.alg) ⊆ ⋃ j, W j

end Work.WilkiesH

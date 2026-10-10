import Mathlib
import Submission.Work.MotC2.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Polynomial

namespace Work.MotC2.TransAux

/-- Two `L`-algebra homomorphisms out of the affine coordinate ring `L[X,Y]/(W_E)` of a
Weierstrass curve are equal as soon as they agree on the two coordinates `x = coordX` and
`y = coordY`: those two classes generate `Coord E` as an `L`-algebra.

The proof goes through the universal property of `AdjoinRoot`.  Writing
`Coord E = AdjoinRoot (polynomial E)` with base ring `L[X]`, the homomorphisms `f` and `g`
agree on the adjoined root `root (polynomial E) = coordY E` (hypothesis `hy`) and, since
`(polynomial E).of X = coordX E` (hypothesis `hx`), they also agree after precomposition with
the structure map `L[X] → Coord E`.  `AdjoinRoot.algHom_ext'` then yields `f = g`. -/
theorem CoordExt {L : Type*} [Field L] (E : WeierstrassCurve L) {F : Type*} [Field F]
    [Algebra L F] (f g : Work.MotC2.Coord E →ₐ[L] F)
    (hx : f (Work.MotC2.coordX E) = g (Work.MotC2.coordX E))
    (hy : f (Work.MotC2.coordY E) = g (Work.MotC2.coordY E)) : f = g := by
  apply AdjoinRoot.algHom_ext' (p := WeierstrassCurve.Affine.polynomial E)
  · apply Polynomial.algHom_ext
    rw [AlgHom.comp_apply, AlgHom.comp_apply, AdjoinRoot.coe_ofAlgHom]
    change f (Work.MotC2.coordX E) = g (Work.MotC2.coordX E)
    exact hx
  · change f (Work.MotC2.coordY E) = g (Work.MotC2.coordY E)
    exact hy

end Work.MotC2.TransAux

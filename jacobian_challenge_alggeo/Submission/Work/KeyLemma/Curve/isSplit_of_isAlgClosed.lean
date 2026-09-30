import Mathlib
import Submission.Work.KeyLemma.SymPow

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-!
# Over an algebraically closed field every divisor is split

Let `C` be a smooth, proper, geometrically irreducible curve over a field `k`, let `L/k` be a
field extension with `L` algebraically closed, and let `D` be an effective divisor on the base
change `C_L`.  This file proves

> `D` is split over `L`: every closed point of the support of `D` is the image of an `L`-point
> of `C_L`.

Equivalently, every closed point of a curve over an algebraically closed field is the image of
a rational point.  This is the base case of the reduction of the key lemma to the split case:
over an algebraically closed field no Galois descent is needed.

## Proof

Let `X = C_L`, with structure morphism `f : X ⟶ Spec L`.  `X` is locally of finite type over
the algebraically closed field `L`, so Mathlib's `AlgebraicGeometry.pointEquivClosedPoint`

`{p : Spec L ⟶ X // p ≫ f = 𝟙 _} ≃ closedPoints X`

puts the closed points of `X` in bijection with the `L`-points of `X`; the corresponding
`L`-point of a closed point `Q` is `pointOfClosedPoint f Q.1 Q.2`, whose value at the closed
point of `Spec L` is `Q.1`.  Transporting this section of `f` across the definitional equality
`Pt L X = {p : Spec L ⟶ X // p ≫ f = 𝟙 _}` gives the required point, and `placeOfPoint` is by
definition the value of a point at the closed point of `Spec L`.
-/

set_option autoImplicit false

namespace Work.KeyLemma.Curve

universe u

open CategoryTheory AlgebraicGeometry

open Work.CurveBasics

/-- **Over an algebraically closed field, every closed point of a curve is the image of a
rational point.**

If `X` is a curve over an algebraically closed field `L` and `Q` is a closed point of `X`,
then `Q = placeOfPoint X p` for some `L`-point `p` of `X`.  Indeed, `X` is locally of finite
type over `L` and `L` is algebraically closed, so the residue field of the closed point `Q` is
`L` (`AlgebraicGeometry.residueFieldIsoBase`); the corresponding section of the structure
morphism of `X` is Mathlib's `AlgebraicGeometry.pointOfClosedPoint`. -/
theorem exists_point_placeOfPoint_eq {L : Type u} [Field L] [IsAlgClosed L]
    (X : Curve L) (Q : X.Place) :
    ∃ p : Point X, placeOfPoint X p = Q := by
  -- The section of the structure morphism of `X` corresponding to `Q`.
  let q := (AlgebraicGeometry.pointEquivClosedPoint (X := X.left) (K := L) X.hom).symm Q
  -- `q` is an `L`-point of `X`, i.e. an element of `Pt L X.toOver`.
  let p : Point X := Over.homMk q.1 q.2
  refine ⟨p, ?_⟩
  have hl : Pt.leftHom p = q.1 := rfl
  have hq : q.1 = AlgebraicGeometry.pointOfClosedPoint (X := X.left) (K := L) X.hom Q.1 Q.2 := rfl
  apply Subtype.ext
  show (placeOfPoint X p).point = Q.1
  rw [placeOfPoint_point, hl, hq]
  exact AlgebraicGeometry.pointOfClosedPoint_apply (X := X.left) (K := L) X.hom Q.1 Q.2
    (IsLocalRing.closedPoint L)

theorem isSplit_of_isAlgClosed {k : Type u} [Field k] {C : Work.CurveBasics.Curve k}
    {L : Type u} [Field L] [Algebra k L] [IsAlgClosed L] (D : (C.baseChange L).Div)
    (hD : D.IsEffective) : Work.KeyLemma.Curve.IsSplit (C.baseChange L) D := by
  intro Q _
  obtain ⟨p, hp⟩ := exists_point_placeOfPoint_eq (C.baseChange L) Q
  exact ⟨p, hp⟩

end Work.KeyLemma.Curve

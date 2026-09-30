import Mathlib
import Submission.Work.BcDiv.Basic
import Submission.Work.SymQuot.DivOf.divMap_injective

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.BcDiv

universe u

/-- **B3, the ramification index of the comparison square.** For two cartesian squares
`S₁ : BCSquare C C₁`, `S₂ : BCSquare C C₂` with the same cospan (`C` a curve over `k`, `C₁`, `C₂`
curves over `F`), the comparison square `Work.BcDiv.BCSquare.cmp S₁ S₂` is an isomorphism, so the
ramification index at every place of `C₂` is one.

Proof route: apply the pasting lemma `Work.CurveBasics.Curve.BCSquare.ramIdx_comp`
(`Submission/Work/CurveBasics/Curve/BCSquare/divMap_comp.lean`) to the composite
`(cmp S₂ S₁).comp (cmp S₁ S₂)` (whose projection is `𝟙` by
`Work.BcDiv.BCSquare.cmp_comp_cmp_π`, so its `ramIdx` is `1` by
`Work.SymQuot.DivOf.Work.SymQuot.DivOf.ramIdx_self`): this gives
`1 = (cmp S₁ S₂).ramIdx Q * (cmp S₂ S₁).ramIdx _` for every `Q : C₂.Place`, and the second factor
is `≥ 1` by `one_le_ramIdx`
(`Submission/Work/SymQuot/DivOf/divMap_injective.lean`). The closedness hypothesis of
`ramIdx_comp` holds because the projection of `cmp S₁ S₂` is an isomorphism of schemes (hence a
homeomorphism, so it maps the closed point `Q.point` to a closed point). -/
theorem ramIdx_cmp {k : Type u} [Field k] {F : Type u} [Field F] [Algebra k F]
    {C : Work.CurveBasics.Curve k} {C₁ C₂ : Work.CurveBasics.Curve F}
    (S₁ : Work.CurveBasics.Curve.BCSquare C C₁)
    (S₂ : Work.CurveBasics.Curve.BCSquare C C₂) (Q : C₂.Place) :
    (Work.BcDiv.BCSquare.cmp S₁ S₂).ramIdx Q = 1 := by
  -- The projection of `cmp S₁ S₂` is an isomorphism, hence a homeomorphism; so it carries the
  -- closed point `Q.point` to a closed point.
  have hT : IsClosed ({(BCSquare.cmp S₁ S₂).π Q.point} : Set C₁.left) := by
    have h := ((BCSquare.cmp S₁ S₂).π.homeomorph).isClosedMap ({Q.point} : Set C₂.left) Q.isClosed
    simpa using h
  -- The analogous closedness for the projection of `cmp S₂ S₁`, at the place below: here the
  -- closed point is the image of `Q.point` under the composite projection, which is `𝟙`.
  have hS : IsClosed ((singleton ((BCSquare.cmp S₂ S₁).π
      ((BCSquare.cmp S₁ S₂).under Q hT).point)) : Set C₂.left) := by
    have hpt : (BCSquare.cmp S₂ S₁).π ((BCSquare.cmp S₁ S₂).under Q hT).point = Q.point := by
      have h1 : ((Work.CurveBasics.Curve.BCSquare.comp (BCSquare.cmp S₂ S₁) (BCSquare.cmp S₁ S₂)).π Q.point)
          = (BCSquare.cmp S₂ S₁).π ((BCSquare.cmp S₁ S₂).under Q hT).point := rfl
      rw [← h1, BCSquare.cmp_comp_cmp_π S₂ S₁]
      rfl
    rw [hpt]
    exact Q.isClosed
  -- The pasting lemma for the composite, whose projection is the identity.
  have hcomp := Work.CurveBasics.Curve.BCSquare.ramIdx_comp (BCSquare.cmp S₂ S₁) (BCSquare.cmp S₁ S₂) Q hT
  have hself : ((BCSquare.cmp S₂ S₁).comp (BCSquare.cmp S₁ S₂)).ramIdx Q = 1 :=
    Work.SymQuot.DivOf.Work.SymQuot.DivOf.ramIdx_self _ (BCSquare.cmp_comp_cmp_π S₂ S₁) Q
  -- Both factors are at least one, and their product is one.
  have ha : 1 ≤ (BCSquare.cmp S₁ S₂).ramIdx Q := Work.SymQuot.DivOf.one_le_ramIdx _ Q hT
  have hb : 1 ≤ (BCSquare.cmp S₂ S₁).ramIdx ((BCSquare.cmp S₁ S₂).under Q hT) :=
    Work.SymQuot.DivOf.one_le_ramIdx _ _ hS
  have hab : (BCSquare.cmp S₁ S₂).ramIdx Q *
      (BCSquare.cmp S₂ S₁).ramIdx ((BCSquare.cmp S₁ S₂).under Q hT) = 1 := by
    rw [← hcomp, hself]
  have ha0 : (0 : ℤ) ≤ (BCSquare.cmp S₁ S₂).ramIdx Q := le_trans zero_le_one ha
  have h1 : (BCSquare.cmp S₁ S₂).ramIdx Q * 1 ≤ (BCSquare.cmp S₁ S₂).ramIdx Q *
      (BCSquare.cmp S₂ S₁).ramIdx ((BCSquare.cmp S₁ S₂).under Q hT) :=
    mul_le_mul_of_nonneg_left hb ha0
  rw [mul_one, hab] at h1
  exact le_antisymm h1 ha

end Work.BcDiv

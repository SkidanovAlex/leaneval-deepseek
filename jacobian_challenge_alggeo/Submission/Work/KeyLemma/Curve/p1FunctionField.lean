/-
# The function field of `ℙ¹` as a `k`-algebra

This file provides the `k`-algebra instance on the function field `K(ℙ¹)` of the projective
line `Work.AbVar.P1 k` (mirroring `Work.CurveBasics.Curve.instAlgebraFunctionField`), so that
statements such as `Nonempty (K(ℙ¹) ≃ₐ[k] k(h))` make sense.
-/
import Mathlib
import Submission.Work.AbVar.ProjectiveLine
import Submission.Work.AbVar.ProjectiveLine.isIntegral_P1
import Submission.Work.KeyLemma.Curve.genericSum

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.KeyLemma.Curve

/-- `ℙ¹` is integral, hence irreducible and reduced. -/
instance instIsIntegralP1 (k : Type u) [Field k] : IsIntegral (Work.AbVar.P1 k).left :=
  Work.AbVar.ProjectiveLine.isIntegral_P1 k

/-- The structure morphism `ℙ¹ ⟶ Spec k` makes the function field of `ℙ¹` into a `k`-algebra. -/
noncomputable instance instAlgebraP1FunctionField (k : Type u) [Field k] :
    Algebra k ↥((Work.AbVar.P1 k).left.functionField) :=
  haveI : Nonempty (⊤ : (Work.AbVar.P1 k).left.Opens) :=
    ⟨⟨genericPoint (Work.AbVar.P1 k).left, trivial⟩⟩
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (Work.AbVar.P1 k).hom.appTop ≫
    (Work.AbVar.P1 k).left.germToFunctionField ⊤).hom.toAlgebra

/-- The generic point of `ℙ¹`, as a morphism out of `Spec K(ℙ¹)`. -/
noncomputable abbrev genericPtP1 (k : Type u) [Field k] :
    Spec (CommRingCat.of ↥((Work.AbVar.P1 k).left.functionField)) ⟶ (Work.AbVar.P1 k).left :=
  (Work.AbVar.P1 k).left.fromSpecStalk (genericPoint (Work.AbVar.P1 k).left)

end Work.KeyLemma.Curve

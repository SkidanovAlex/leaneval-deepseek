/-
Area AV (abelian-variety toolkit) for the Jacobian challenge: equalities of morphisms.
-/
import Submission.Work.AbVar.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Two morphisms agreeing on a dominant locus

If `J` is reduced and `A` is separated over `k`, then two morphisms `J ⟶ A` which agree
after precomposition with a dominant morphism `W ⟶ J` are equal.

This is the `GEN` item of the `AV` contract: two homomorphisms out of a reduced group
scheme (for instance the Jacobian of a curve) which agree on a subvariety whose image is
dense coincide.

It is a wrapper around `AlgebraicGeometry.ext_of_isDominant_of_isSeparated'`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open AlgebraicGeometry

namespace Work.AbVar

variable {k : Type u} [Field k]
variable {J A W : Sch k}

/-- Two `k`-morphisms from a reduced `k`-scheme to a separated `k`-scheme which agree
after precomposition with a dominant morphism are equal. -/
theorem eq_of_isDominant [IsReduced J.left] [IsSeparated A.hom] {f g : J ⟶ A} (u : W ⟶ J)
    [IsDominant u.left] (h : u ≫ f = u ≫ g) : f = g := by
  have hsep : (A.left ↘ Spec (.of k)) = A.hom := rfl
  have : IsSeparated (A.left ↘ Spec (.of k)) := hsep.symm ▸ inferInstance
  ext1
  exact ext_of_isDominant_of_isSeparated' (Spec (.of k)) u.left (congrArg Over.Hom.left h)

/-- Two `k`-morphisms from a reduced `k`-scheme to a separated `k`-scheme which agree
after precomposition with a surjective morphism are equal. -/
theorem eq_of_surjective [IsReduced J.left] [IsSeparated A.hom] {f g : J ⟶ A} (u : W ⟶ J)
    (hu : Surjective u.left) (h : u ≫ f = u ≫ g) : f = g :=
  eq_of_isDominant (A := A) u h

end Work.AbVar

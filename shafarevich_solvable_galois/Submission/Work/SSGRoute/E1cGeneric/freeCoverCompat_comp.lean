import Mathlib
import Submission.Work.SSGRoute.PT.freeCoverCompat
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# (i) `PhiE`-compat: the comparison map of the two canonical covers is compatible

`freeCoverCompat φ X : Rep.free Coeff H X.V ⟶ Rep.res φ (Rep.free Coeff G X.V)` is the canonical
map of complexes relating the two canonical presentations of `X` (the canonical cover over `H`, and
the restriction of the canonical cover over `G`), and it is the identity on the generators.  Its
compatibility with the two covers,

    freeCoverCompat φ X ≫ (Rep.resFunctor φ).map (freeCover X) = freeCover (Rep.res φ X),

is proved here by hand: both sides are morphisms out of the free representation on `X.V`
(the generators), so it suffices to compare them on the generators `single x (single 1 1)`
(`Rep.free_ext`), where both are `x`.  The value of `freeCoverCompat` on a generator is the
computation rule of `Rep.freeLift` (`Representation.freeLift_single_single`); the value of
`freeCover` is the same rule with `f = id`.
-/

namespace Work.SSGRoute.E1cGeneric

open CategoryTheory

-- instance priorities: as in `Submission.Work.SSGRoute.ext_level_lift`, so that the `Module` action
-- on the carrier of a representation (rather than the `ULift`-inherited one) is used when rewriting
-- `1 • x` in the `freeLift` computation rule.
attribute [local instance 10000] Rep.hV2 Rep.hV1 Submodule.module
attribute [local instance 1] ULift.module ULift.smulLeft ULift.mulAction ULift.smulZeroClass
attribute [local instance 1] ULift.distribSMul ULift.distribMulAction ULift.smulWithZero
attribute [local instance 1] ULift.mulActionWithZero

/-- The value of the comparison map `freeCoverCompat φ X` on a free generator: it fixes the
generators (the `H`-generator of a fixed `x` maps to the `G`-generator of the same `x`). -/
private lemma freeCoverCompat_apply_single {G H : Type} [Group G] [Group H] (φ : H →* G)
    (X : Rep.{0} SSGRoute.PTExt.Coeff G) (x : X.V) :
    (ConcreteCategory.hom (Work.SSGRoute.PT.freeCoverCompat φ X))
      (Finsupp.single x (MonoidAlgebra.single (1 : H) (1 : SSGRoute.PTExt.Coeff)))
    = Finsupp.single x (MonoidAlgebra.single (1 : G) (1 : SSGRoute.PTExt.Coeff)) := by
  rw [Work.SSGRoute.PT.freeCoverCompat]
  simp only [Rep.freeLift, ConcreteCategory.hom_ofHom, Representation.freeLift_single_single]
  simp

/-- The value of the canonical cover `freeCover X` on a free generator (`freeCover` is `freeLift id`).
Stated without a `Fintype` hypothesis (unlike `Work.SSGRoute.freeCover_apply_single`). -/
private lemma freeCover_apply_single_of_freeLift {G : Type} [Group G]
    (X : Rep.{0} SSGRoute.PTExt.Coeff G) (x : X.V) :
    (ConcreteCategory.hom (Work.SSGRoute.freeCover X))
      (Finsupp.single x (MonoidAlgebra.single (1 : G) (1 : SSGRoute.PTExt.Coeff))) = x := by
  rw [Work.SSGRoute.freeCover]
  simp only [Rep.freeLift, ConcreteCategory.hom_ofHom, Representation.freeLift_single_single,
    map_one, Module.End.one_apply, one_smul, id_eq]

/-- **The comparison map of covers is compatible with the two canonical covers**:
`freeCoverCompat φ X ≫ (Rep.resFunctor φ).map (freeCover X) = freeCover (Rep.res φ X)`. -/
theorem freeCoverCompat_comp {G H : Type} [Group G] [Group H] (φ : H →* G)
    (X : Rep.{0} SSGRoute.PTExt.Coeff G) :
    CategoryTheory.CategoryStruct.comp (Work.SSGRoute.PT.freeCoverCompat φ X)
        ((Rep.resFunctor φ).map (Work.SSGRoute.freeCover X))
      = Work.SSGRoute.freeCover (Rep.res φ X) := by
  -- both sides are morphisms out of the free representation on the generators
  refine Rep.free_ext (k := SSGRoute.PTExt.Coeff) (G := H) (α := X.V)
    (A := Rep.res φ X) _ _ ?_
  intro x
  rw [Rep.comp_apply]
  rw [freeCoverCompat_apply_single]
  rw [Rep.resMap_hom_apply]
  rw [freeCover_apply_single_of_freeLift, freeCover_apply_single_of_freeLift]

end Work.SSGRoute.E1cGeneric

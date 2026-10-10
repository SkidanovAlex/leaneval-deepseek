import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
import Submission.NK.NUV2.RouteC.LevelInf
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The level inflation between two levels of `F^{ab}`, as an additive homomorphism

For two finite Galois levels `L ≤ E` of an abelian extension `F^{ab}/F`, this file packages the level
inflation `NK.NUV2.RouteC.levelInfMap` between them as an additive homomorphism of the cohomology
groups,

`levelInfHom L E h : H²(Gal(L/F), Lˣ) →+ H²(Gal(E/F), Eˣ)`,

with the `Algebra ↥L ↥E` structure provided locally from the inclusion.  This is the transition map
of the inverse system of fundamental classes (König's construction of a compatible family): the
point of giving it a name is that it can be mentioned without the local instances.
-/

open scoped BigOperators
open CategoryTheory

namespace NK.NUV2.RouteE

noncomputable def levelInfHom {F A : Type} [Field F] [Field A] [Algebra F A]
    (L E : FiniteGaloisIntermediateField F A) (h : L ≤ E) :
    (groupCohomology (Rep.ofAlgebraAutOnUnits F ↥L) 2) →+
      (groupCohomology (Rep.ofAlgebraAutOnUnits F ↥E) 2) :=
  letI : Algebra ↥L ↥E :=
    RingHom.toAlgebra (Subsemiring.inclusion ((FiniteGaloisIntermediateField.le_iff L E).mp h));
  letI : IsScalarTower F ↥L ↥E := IsScalarTower.of_algebraMap_eq (congrFun rfl);
  (NK.NUV2.RouteC.levelInfMap (F := F) (M := ↥L) (L := ↥E)).hom.toAddMonoidHom

end NK.NUV2.RouteE

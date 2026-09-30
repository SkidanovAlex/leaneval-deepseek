import Mathlib
import Submission.Work.Charts.FinBC

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Work.Charts

open CategoryTheory Limits AlgebraicGeometry

universe u

/-- The residue field of a closed point of a `K`-scheme locally of finite type over a field `K`
is a finite extension of `K`.

Indeed, the canonical morphism `Spec κ(x) ⟶ X` is a closed immersion (as `{x}` is closed), hence
locally of finite type, and so is `X ⟶ Spec K`; their composite — which is
`Spec (algebraMap K κ(x))` — is therefore locally of finite type, i.e. `κ(x)` is a finitely
generated `K`-algebra. Zariski's lemma (`finite_of_finite_type_of_isJacobsonRing`) then upgrades
this to finiteness over the field `K`. -/
theorem finiteDimensional_resField_of_isClosed {K : Type u} [Field K] {X : Work.GCBasics.Sch K}
    [AlgebraicGeometry.LocallyOfFiniteType X.hom] (x : X.left)
    (hx : IsClosed ({x} : Set X.left)) :
    FiniteDimensional K (Work.GCBasics.resField X x) := by
  -- `{x}` closed means the canonical point `Spec κ(x) ⟶ X` is a closed immersion.
  have hci : IsClosedImmersion (X.left.fromSpecResidueField x) :=
    (isClosed_singleton_iff_isClosedImmersion (X := X.left) (x := x)).mp hx
  -- A closed immersion is locally of finite type.
  haveI : LocallyOfFiniteType (X.left.fromSpecResidueField x) := inferInstance
  -- So is the composite `Spec κ(x) ⟶ X ⟶ Spec K`.
  have hcomp : LocallyOfFiniteType (X.left.fromSpecResidueField x ≫ X.hom) := inferInstance
  -- Rewrite the composite as `Spec (algebraMap K κ(x))`.
  have hmap : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (algebraMap K (Work.GCBasics.resField X x)))) := by
    change LocallyOfFiniteType (Work.GCBasics.specOf K (Work.GCBasics.resField X x)).hom
    rw [Work.GCBasics.specOf_resField_hom X x]
    exact hcomp
  -- Locally of finite type for `Spec.map` is finite type for the ring homomorphism.
  have hft : Algebra.FiniteType K (Work.GCBasics.resField X x) :=
    (AlgebraicGeometry.HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.LocallyOfFiniteType)
      (Q := RingHom.FiniteType)).mp hmap
  -- Zariski's lemma: a finitely generated field extension of a Jacobson ring is finite.
  exact finite_of_finite_type_of_isJacobsonRing K (Work.GCBasics.resField X x)

end Work.Charts

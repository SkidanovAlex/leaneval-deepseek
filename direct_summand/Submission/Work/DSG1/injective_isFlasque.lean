import Mathlib
import Submission.Work.DSMap.Map
import Submission.Work.DSG1.FlasqueAux

/-!
# Injective sheaves of modules are flasque

On a scheme `X`, an injective sheaf of `𝒪_X`-modules has flasque (flabby) underlying sheaf of
abelian groups.  This is the standard first step in the comparison of resolutions used in area G1
of the direct-summand proof map: an injective resolution of the structure sheaf can therefore be
replaced by a flasque one.

The proof is in two steps.

1. The forgetful functor `SheafOfModules.toSheaf` has a left adjoint (the `𝒪_X`-linearization of a
   sheaf of abelian groups), which is *left exact* — `PresheafOfModules.sheafification` is
   `PreservesFiniteLimits` in Mathlib.  By `Adjunction.map_injective` an injective sheaf of modules
   is therefore injective as a presheaf of modules, i.e. `Injective M'` for
   `M' = (restrictScalars (𝟙 R.obj)).obj M.val`.
2. An injective presheaf of modules is "flasque" in the sense that all restriction maps are
   surjective: this is `Work.DSG1.surjective_restrict_of_injective`, proved in
   `Submission/Work/DSG1/FlasqueAux.lean`.  (There the free module on the representable at `V` is
   shown to be a subobject of the unit presheaf of modules, and injectivity extends a section over
   `V` to an element of the unit.)

Flasqueness of the underlying presheaf of abelian groups of `M` is then exactly the surjectivity
of the components of `M'.map` on objects.
-/

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite
open scoped CategoryTheory

universe u

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Work.DSG1

theorem injective_isFlasque {X : AlgebraicGeometry.Scheme.{u}} (M : X.Modules)
    [CategoryTheory.Injective M] :
    TopCat.Presheaf.IsFlasque ((SheafOfModules.toSheaf X.ringCatSheaf).obj M).obj := by
  -- Step 1: an injective sheaf of modules is an injective presheaf of modules.
  haveI : Injective ((PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj
      ((SheafOfModules.forget X.ringCatSheaf).obj M)) :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).map_injective _
      ‹Injective M›
  -- Step 2: flasqueness of an injective presheaf of modules.
  refine ⟨fun {U V} i => ?_⟩
  rw [AddCommGrpCat.epi_iff_surjective]
  intro s
  obtain ⟨t, ht⟩ := surjective_restrict_of_injective (C := X.Opens)
    (J := Opens.grothendieckTopology ↥X) (R := X.ringCatSheaf)
    ((PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj
      ((SheafOfModules.forget X.ringCatSheaf).obj M)) i s
  exact ⟨t, ht⟩

end Work.DSG1

import Mathlib
import Submission.Work.DSMap.Map
import Submission.Work.DSG4a.BaseChangeComplex

/-!
# DSG4a: the Čech comparison and its coaugmentation

This file packages the two canonical coaugmentations of the Čech complexes of `X` and of the
base change `X_{A'}` (degree `0`), and the predicate saying that an isomorphism of complexes
`baseChangeComplex (cechZ A X f U) ≅ cechZ A' X' f' U'` carries one to the other.  The
existence of such an isomorphism is the remaining geometric input for the hypothesis `hbc` of
`area_G4a_localGlobal_of_models` (see `NOTES.md`); the mathematics behind it is
`sectionBaseChange_bijective` plus `sectionBaseChange_naturality`.

The coaugmentations are the canonical ones: `coaug0 A X f U` (from `Map.lean`) composed with
the degree-`0` identification of the extension `cechZ = (cech).extend _` on the `A`-side, and
the corresponding element of the base-changed complex `A' ⊗[A] (cechZ A X f U).X 0`.
-/

open CategoryTheory AlgebraicGeometry Limits
open scoped ChangeOfRings

universe u

namespace Work.DSG4a

/-- The canonical coaugmentation of `cechZ A X f U` in degree `0`. -/
noncomputable def coaugZ (A : Type u) [CommRing A] (X : Scheme.{u}) (f : X ⟶ Spec (.of A))
    {ι : Type u} (U : ι → X.Opens) : ModuleCat.of A A ⟶ (DSMap.cechZ A X f U).X 0 :=
  DSMap.coaug0 A X f U ≫
    ((DSMap.cech A X f U).extendXIso ComplexShape.embeddingUpNat (i := 0) rfl).inv

/-- The element of `(cechZ A X f U).X 0` given by the canonical coaugmentation. -/
noncomputable def coaugZElem (A : Type u) [CommRing A] (X : Scheme.{u}) (f : X ⟶ Spec (.of A))
    {ι : Type u} (U : ι → X.Opens) : (DSMap.cechZ A X f U).X 0 :=
  coaugZ A X f U 1

/-!
## Status

`coaugZ` is the canonical coaugmentation of `cechZ A X f U` in degree `0`
(`coaug0` composed with the inverse of the degree-`0` identification of the extension), and
`coaugZElem` is its value at `1`.

What is *not* yet here is the base-changed side, `a' ↦ a' ⊗ (coaugZElem A X f U)` as a map
`A' ⟶ (baseChangeComplex (cechZ A X f U)).X 0`: the carrier of
`(baseChangeComplex (cechZ A X f U)).X 0` is `TensorProduct A ((restrictScalars ψ).obj A') (…).X 0`
and Lean does not synthesize its `A'`-module structure from the unfolded type (the instance is
registered for `ExtendScalars.obj'`, not for the raw tensor).  The fix is local
(`inferInstanceAs`/an explicit `letI`, or phrasing the map through
`ExtendScalars.map'`/`LinearMap.toSpanSingleton` with the type ascription placed on the element
rather than on the map), and it is the first thing to do before stating the Čech comparison
`∃ Φ : baseChangeComplex (cechZ A X f U) ≅ cechZ A' X' f' U', IsIso Φ ∧ (Φ carries coaugZ to
coaugZ)`.
-/

end Work.DSG4a

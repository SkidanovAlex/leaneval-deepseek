import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.PTDefsOmega
import Submission.Work.SSGRoute.PT.pt_pairing_ext
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Level inflation between intermediate fields of `Ω/k`

`PTDefsOmega.inflCIn` is the level inflation `H²(Gal(L/k), C_L) → H²(Gal(L'/k), C_{L'})` for
`L L' : IntermediateField K Ω`, i.e. for levels of `Ω` *containing* a fixed field `K`, and the
inflation machinery of `PTDefs` (`inflC`) is indexed by arbitrary types.

The `G1⁺` construction (`Work.SSGRoute.PT.canonical_localPairing_reciprocity_converse`) chooses its
levels through `Work.SSGRoute.PT.exists_level_factors_locConstOnTwo`, which produces levels
`L : IntermediateField k Ω` (containing `K`), not `L : IntermediateField K Ω`.  This file provides
the level inflation in that vocabulary, so that the coherent invariant `χ` (`S1` of the design)
can be stated at levels `IntermediateField k Ω` — the vocabulary in which the level choice, the
place glue `Work.SSGRoute.PT.exists_place_under_isFinPlace` and `PT.iota` all live, avoiding the
(costly, and in this Mathlib version awkward) coercion between `IntermediateField k Ω` and
`IntermediateField K Ω`.

Nothing here is new mathematics: `inflLevel` is `PTExt.inflC` with the scalar tower coming from
`IntermediateField.inclusion`, exactly as `PTDefsOmega.inflCIn` does for its own vocabulary.
-/

open CategoryTheory

noncomputable section

namespace Work.SSGRoute.PT

open SSGRoute.PTExt

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]

/-- **Level inflation in the `IntermediateField k Ω` vocabulary.**  For levels
`L ≤ L'` of `Ω/k` which are finite Galois over `k`, the inflation
`H^n(Gal(L/k), C_L) → H^n(Gal(L'/k), C_{L'})` of the class formation, along the scalar tower
`k → L → L'` obtained from the inclusion. -/
def inflLevel (L L' : IntermediateField k Ω) [NumberField L] [NumberField L']
    [FiniteDimensional k L] [IsGalois k L] (h : L ≤ L') {n : ℕ}
    (y : extH (classesK k L) n) : extH (classesK k L') n :=
  letI : Algebra L L' := (IntermediateField.inclusion h).toAlgebra
  haveI : IsScalarTower k L L' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  inflC (k := k) (K := L) (L := L') y

/-- `inflLevel` is additive. -/
theorem inflLevel_add (L L' : IntermediateField k Ω) [NumberField L] [NumberField L']
    [FiniteDimensional k L] [IsGalois k L] (h : L ≤ L') {n : ℕ}
    (y y' : extH (classesK k L) n) :
    inflLevel L L' h (y + y') = inflLevel L L' h y + inflLevel L L' h y' := by
  unfold inflLevel inflC
  exact extHMap_add _ _ _ _

/-- `inflLevel` is definitionally the level inflation of `PTDefs`. -/
theorem inflLevel_def (L L' : IntermediateField k Ω) [NumberField L] [NumberField L']
    [FiniteDimensional k L] [IsGalois k L] (h : L ≤ L') {n : ℕ}
    (y : extH (classesK k L) n) :
    inflLevel L L' h y =
      letI : Algebra L L' := (IntermediateField.inclusion h).toAlgebra
      haveI : IsScalarTower k L L' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
      inflC (k := k) (K := L) (L := L') y := rfl

end Work.SSGRoute.PT

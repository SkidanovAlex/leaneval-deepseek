import Mathlib
import Submission.NK.NUV2.LC.RouteB.locUnits_tower_eq_zero
import Submission.NK.NUV2.ABHN.unitsLevelMap_injective

/-!
# The local units level system `M ↦ M_wˣ` and its injectivity (the missing `(G2)`)

`Submission/Work/NUV2/LC/LocalLevelSystem.lean` builds the *global* units level map
(`unitsLevelMapTower : H²(Gal(L/F), Lˣ) → H²(Gal(M/F), Mˣ)`) and its compatibility with the
localisation `locUnits` (`locUnits F M w' (unitsLevelMapTower b) = v (locUnits F L w b)`), and
names the missing half of the local layer:

> `(G2)`: *the injectivity of the local level map*
> `v : H²(Γ_w(L), L_wˣ) → H²(Γ_{w'}(M), M_{w'}ˣ)` (coefficient inclusion + inflation, via
> `H¹(Gal(M_{w'}/L_w), M_{w'}ˣ) = 0`, Hilbert 90 for local fields).

This file supplies the *definition* of that map — it is `groupCohomology.map` of the restriction of
the decomposition groups (`NK.NUV2.LC.RouteB.localStabilizerMapTower`) along the coefficient
inclusion of the local units (`NK.NUV2.LC.RouteB.localUnitsMapTowerCoeff`, whose equivariance is
proved in `locUnits_tower_eq_zero.lean`) — and *states* its injectivity (the `(G2)` gap).

## Why the injectivity is the right statement

The criterion is `NK.NUV2.ABHN.groupCohomology_map_two_injective` (the standard
"inflation with coefficients" injectivity criterion), applied with

* `f := localStabilizerMapTower h : Γ_{w'}(M) →* Γ_w(L)` (surjective: restriction of Galois
  groups; its kernel is `Gal(M_{w'}/L_w)`);
* `φ := localUnitsMapTowerCoeff h : L_wˣ → M_{w'}ˣ` (injective: the completion map is),
  whose image is exactly the invariants under the kernel (Galois theory for the local extension
  `M_{w'}/L_w`) and which satisfies Hilbert 90 on the kernel (`H¹(Gal(M_{w'}/L_w), M_{w'}ˣ) = 0`).

These are the same three inputs that make the *global* units level maps injective
(`NK.NUV2.ABHN.unitsLevelMap_injective`), transported to the completions.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace NK.NUV2.LC.RouteB

open CategoryTheory Representation

variable {F L M : Type} [Field F] [NumberField F] [Field L] [NumberField L] [Field M] [NumberField M]
  [Algebra F L] [Algebra F M] [Algebra L M] [IsScalarTower F L M]
  [FiniteDimensional F L] [IsGalois F L] [FiniteDimensional F M] [IsGalois F M]

/-- **The local units level map** `v : H²(Γ_w(L), L_wˣ) → H²(Γ_{w'}(M), M_{w'}ˣ)` of the tower
`F ⊆ L ⊆ M` at places `w' | w`: the restriction of the decomposition groups
(`localStabilizerMapTower`) together with the inclusion of the local units
(`localUnitsMapTowerCoeff`).  This is the `(G2)` map of `NUV2/LC/LocalLevelSystem.lean`. -/
noncomputable def localUnitsLevelMap {w : NK.GlobalCFT.Place L} {w' : NK.GlobalCFT.Place M}
    (h : NK.GlobalCFT.Place.LiesOver w' w) :
    groupCohomology (NK.HassePrinciple.localUnitsRep F L w) 2 ⟶
      groupCohomology (NK.HassePrinciple.localUnitsRep F M w') 2 :=
  groupCohomology.map (localStabilizerMapTower (F := F) (L := L) (M := M) h)
    (localUnitsMapTowerCoeff (F := F) (L := L) (M := M) h) 2

/-- Computation rule for `localUnitsLevelMap`. -/
theorem localUnitsLevelMap_apply {w : NK.GlobalCFT.Place L} {w' : NK.GlobalCFT.Place M}
    (h : NK.GlobalCFT.Place.LiesOver w' w)
    (x : groupCohomology (NK.HassePrinciple.localUnitsRep F L w) 2) :
    (localUnitsLevelMap (F := F) (L := L) (M := M) h).hom x =
      (groupCohomology.map (localStabilizerMapTower (F := F) (L := L) (M := M) h)
        (localUnitsMapTowerCoeff (F := F) (L := L) (M := M) h) 2).hom x := rfl

/-! ## The `(G2)` statement

The injectivity of `localUnitsLevelMap` — the local-field analogue of
`NK.NUV2.ABHN.unitsLevelMap_injective`, and the missing `(G2)` of
`NUV2/LC/LocalLevelSystem.lean` — is stated and proved in the separate module
`Submission/Work/NUV2/LC/RouteB/localUnitsLevelMap_injective.lean` (so that the statement can be
delegated without duplicating its name):

> `NK.NUV2.LC.RouteB.localUnitsLevelMap_injective` : the map
> `v : H²(Γ_w(L), L_wˣ) → H²(Γ_{w'}(M), M_{w'}ˣ)` of `localUnitsLevelMap` is injective.

Its three ingredients are: (a) `localUnitsMapTowerCoeff` is injective (the completion map is);
(b) its image is exactly the invariants under `Gal(M_{w'}/L_w)` (Galois theory for the local
extension); (c) `H¹(Gal(M_{w'}/L_w), M_{w'}ˣ) = 0` (Hilbert 90 for local fields).  With
`NK.NUV2.ABHN.groupCohomology_map_two_injective` these give the injectivity.
-/

end NK.NUV2.LC.RouteB

import Submission.NK.NUV2.LC.RouteB.localUnitsLevelMap_injective
import Submission.NK.NUV2.LC.RouteB.locUnits_tower_eq_zero
import Submission.NK.NUV2.ABHN.muColimEquivH2ProfiniteOfIsPrimitiveRoot
import Submission.NK.HassePrinciple.KummerLevel
import Submission.NK.HassePrinciple.OfLevelZero
import Submission.NK.NUV2.ABHN.LocalBrauerAux
import Submission.NK.NUV2.LC.nonempty_addEquiv_unitsLevelH2_level

/-!
# The setup of the one-place survival step

This module collects the *bookkeeping* that the survival step of the one-place construction
(`NK.NUV2.LC.RouteB.localH2_survival`) needs, together with the fundamental

* `locUnits_eq_zero_iff_unitsLevelMapTower` — **level independence of the vanishing of the
  localisation** (the conjunction (G1) + (G2) of `Submission/Work/NUV2/LC/LocalLevelSystem.lean`):
  for a tower `F ⊆ L ⊆ M` of number fields and places `w' | w`, the vanishing of
  `locUnits F L w b` is equivalent to the vanishing of `locUnits F M w'` of the inflation of `b`.

Note that the *name* `NK.NUV2.LC.RouteB.localLevelMap` (`locUnits_tower_eq_zero.lean`) and
`NK.NUV2.LC.RouteB.localUnitsLevelMap` (`localUnitsLevelSystem.lean`) denote the same map; the
injectivity of that map is `NK.NUV2.LC.RouteB.localUnitsLevelMap_injective` (Hilbert 90 for the
local extension `M_{w'}/L_w`).

## Why the transports below are re-stated

`Submission/Work/NUV2/LC/RouteB/level_kills_aux.lean` defines the same transports (`levelBase`,
`levelGroupEquiv`, `unitsLift`, `locL`), but it imports `Submission.NK.NUV2.ABHN.h2Twist_muColim_equiv`,
which *redefines* `NK.NUV2.ABHN.levelCompareRoot`; the version of that name used by
`NK.NUV2.ABHN.ofLevel_ne_zero_of_kummerLevel_ne_zero` (and hence by the survival step) lives in
`Submission.NK.NUV2.ABHN.muColimEquivH2ProfiniteOfIsPrimitiveRoot`.  The two modules cannot be
imported together, so the transports are re-stated here under new names.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NK.NUV2.LC.RouteB

open CategoryTheory

section LevelIndependence

variable {F L M : Type} [Field F] [NumberField F] [Field L] [NumberField L] [Field M] [NumberField M]
  [Algebra F L] [Algebra F M] [Algebra L M] [IsScalarTower F L M]
  [FiniteDimensional F L] [IsGalois F L] [FiniteDimensional F M] [IsGalois F M]

/-- The two names for the local level map agree. -/
lemma localLevelMap_eq_localUnitsLevelMap {w : NK.GlobalCFT.Place L}
    {w' : NK.GlobalCFT.Place M} (h : NK.GlobalCFT.Place.LiesOver w' w) :
    localLevelMap (F := F) (L := L) (M := M) h
      = localUnitsLevelMap (F := F) (L := L) (M := M) h := by
  rw [localLevelMap, localUnitsLevelMap, ← map_f_comp_id]
  simp only [Category.id_comp]

/-- **Level independence of the vanishing of `locUnits`.**

For a tower `F ⊆ L ⊆ M` of number fields and places `w' | w` of `M | L`, a class
`b ∈ H²(Gal(L/F), Lˣ)` has vanishing localisation at `w` if and only if its image under the units
level map `H²(Gal(L/F), Lˣ) → H²(Gal(M/F), Mˣ)` has vanishing localisation at `w'`.

This is the conjunction of the level square (G1) (`unitsLevelMapTower_comp_locUnits`) with the
injectivity of the local units level map (G2) (`localUnitsLevelMap_injective`): it is exactly the
statement that "local triviality at a place is a level-independent notion", the missing half of the
Hasse-principle argument of `Submission/Work/NUV2/LC/LocalLevelSystem.lean`. -/
theorem locUnits_eq_zero_iff_unitsLevelMapTower
    (b : ↥(groupCohomology (NK.HassePrinciple.unitsRep F L) 2))
    {w : NK.GlobalCFT.Place L} {w' : NK.GlobalCFT.Place M}
    (h : NK.GlobalCFT.Place.LiesOver w' w) :
    (NK.HassePrinciple.locUnits F L w).hom b = 0 ↔
      (NK.HassePrinciple.locUnits F M w').hom
        ((NK.NUV2.LC.unitsLevelMapTower (F := F) (L := L) (M := M)) b) = 0 := by
  have hsq := unitsLevelMapTower_comp_locUnits (F := F) (L := L) (M := M) h
  have h2 : (NK.HassePrinciple.locUnits F M w').hom
        ((NK.NUV2.LC.unitsLevelMapTower (F := F) (L := L) (M := M)) b)
      = (localLevelMap (F := F) (L := L) (M := M) h).hom
          ((NK.HassePrinciple.locUnits F L w).hom b) := by
    have hh := congrArg (fun f : groupCohomology (NK.HassePrinciple.unitsRep F L) 2
        ⟶ groupCohomology (NK.HassePrinciple.localUnitsRep F M w') 2 => f.hom b) hsq
    simpa using hh
  constructor
  · intro hb
    rw [h2, hb]
    exact map_zero _
  · intro hb
    rw [h2, localLevelMap_eq_localUnitsLevelMap (F := F) (L := L) (M := M) h] at hb
    exact localUnitsLevelMap_injective (F := F) (L := L) (M := M) h
      (hb.trans (map_zero _).symm)

end LevelIndependence

section Transport

variable {K K' : Type} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- **The base field of a level**: the fixed field of the image of `V` in `Gal(L/K)`. -/
noncomputable abbrev levelBaseOf (V : Subgroup Gal(K'/K)) (L : FiniteGaloisIntermediateField K K') :
    IntermediateField K (↥L) :=
  IntermediateField.fixedField (V.map (NK.HassePrinciple.levelRestrict L))

/-- The level-group dictionary: `LevelGroup V L` is the Galois group of `L` over `levelBaseOf V L`. -/
noncomputable def levelGroupEquivOf (V : Subgroup Gal(K'/K))
    (L : FiniteGaloisIntermediateField K K') :
    NK.BrauerHasse.LevelGroup V L ≃* Gal(↥L/↥(levelBaseOf (K := K) (K' := K') V L)) :=
  NK.HassePrinciple.levelGroupMulEquivLevelGalois V L

theorem levelGroupEquivOf_apply (V : Subgroup Gal(K'/K))
    (L : FiniteGaloisIntermediateField K K') (g : NK.BrauerHasse.LevelGroup V L) (x : ↥L) :
    (((levelGroupEquivOf (K := K) (K' := K') V L) g :
        ↥L ≃ₐ[↥(levelBaseOf (K := K) (K' := K') V L)] ↥L) x) =
      (((NK.HassePrinciple.levelGroupRestrictHom V L g) : ↥L ≃ₐ[K] ↥L) x) := by
  induction g using QuotientGroup.induction_on with
  | H v => simp only [levelGroupEquivOf, NK.HassePrinciple.levelGroupRestrictHom_mk]; rfl

/-- **The definite transport** from the `LevelGroup`-based units level cohomology to the
number-field Galois-group cohomology: the map on `H²` induced by the level-group dictionary and the
identity on the coefficients. -/
noncomputable def unitsLiftOf (V : Subgroup Gal(K'/K)) (L : FiniteGaloisIntermediateField K K') :
    NK.HassePrinciple.UnitsLevelH2 (K := K) (K' := K') V L ≃+
      (groupCohomology (NK.HassePrinciple.unitsRep
        (↥(levelBaseOf (K := K) (K' := K') V L)) (↥L)) 2) := by
  refine ((groupCohomology.mapIso
    (A := NK.HassePrinciple.unitsRep (↥(levelBaseOf (K := K) (K' := K') V L)) (↥L))
    (B := NK.HassePrinciple.unitsLevelRep V L)
    (levelGroupEquivOf (K := K) (K' := K') V L)
    (LinearEquiv.refl NK.HassePrinciple.CoeffInt (Additive (↥L)ˣ)) ?_ 2).toLinearEquiv).toAddEquiv
  intro g
  induction g using QuotientGroup.induction_on with
  | H v => simp only [NK.HassePrinciple.levelGroupRestrictHom_mk]; rfl

/-- **The localisation in the level-group vocabulary**: `locL` of `level_kills_aux.lean`, restated
here so as to avoid the `levelCompareRoot` name clash. -/
noncomputable abbrev locLOf (V : Subgroup Gal(K'/K)) (L : FiniteGaloisIntermediateField K K')
    (w : NK.GlobalCFT.Place ↥L)
    (b : NK.HassePrinciple.UnitsLevelH2 (K := K) (K' := K') V L) :=
  (NK.HassePrinciple.locUnits (↥(levelBaseOf (K := K) (K' := K') V L)) (↥L) w).hom
    ((unitsLiftOf (K := K) (K' := K') V L) b)

end Transport

end NK.NUV2.LC.RouteB

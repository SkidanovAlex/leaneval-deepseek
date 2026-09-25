import Mathlib
import Submission.NK.HassePrinciple.LocalUnits
import Submission.NK.GlobalCFT.Place
import Submission.Commons.RingTheory.Henselian.adicCompletionMap_liesOver

/-!
# The *local* level system: the local level map `v` and the level square `(G1)`

This file starts the missing layer identified in `Submission/Work/NUV2/LC/NOTES_hasse_open_level.md`:
the passage from a class of `H²(Gal(L/F), Lˣ)` to a class of `H²(Gal(M/F), Mˣ)` for a tower
`F ⊆ L ⊆ M` of number fields, *at the local level*, i.e. the map

`v : H²(Γ_w(L), L_wˣ) ⟶ H²(Γ_{w'}(M), M_{w'}ˣ)`

for places `w' | w`, together with the **level square `(G1)`**: the coarse localisation at the
deeper level is the image of the shallower one under `v`,

`locUnits F M w' (unitsLevelMapTower b) = v (locUnits F L w b)`   for `b ∈ H²(Gal(L/F), Lˣ)`,

and its companion `(G2)`: **`v` is injective** (coefficient inclusion followed by the inflation
`H²(Γ_w(L), M_{w'}ˣ) → H²(Γ_{w'}(M), M_{w'}ˣ)`, which is injective by the transgression/Hilbert 90
argument: `H¹(Gal(M_{w'}/L_w), M_{w'}ˣ) = 0` for the units of a local field).

Together `(G1)` and `(G2)` say precisely that a localisation at a place `w` of a level class vanishes
if and only if the localisation of its image at every place `w' | w` of a deeper level vanishes --
the "level independence" of the localisation vanishing.  This is the only gap between

* the finite-case Hasse–Brauer–Noether theorem `NK.GlobalCFTdeep.hbnUnits` (Milne CFT VII.7.1,
  unconditional) together with the finite support `NK.NUV2.LC.units_finite_support` and the Kummer
  injection `NK.HassePrinciple.kummerColim_injective` (all on disk),

and

* the Hasse principle at an open level `NK.NUV2.LC.hasse_open_level` (and its `fixingMu` special
  case, see `NK.NUV2.LC.hasse_open_level_of_fixingMu_crux`).

## The infrastructure statement (delegated)

The first ingredient is the **local units map**: for a tower `L ⊆ M` of number fields and finite
places `q' | q`, the canonical monoid homomorphism of local unit groups

`(Place.localField L (Place.ofFinite q))ˣ →* (Place.localField M (Place.ofFinite q'))ˣ`

coming from the embedding of the completion of `L` at `q` into the completion of `M` at `q'`, and
its compatibility with the global coefficient maps `Lˣ → L_qˣ` and `Mˣ → M_{q'}ˣ`.
-/

open CategoryTheory

namespace NK.NUV2.LC

variable {L M : Type} [Field L] [NumberField L] [Field M] [NumberField M] [Algebra L M]
  [FiniteDimensional L M] [IsGalois L M]

/-- **The local units map.**  For a tower `L ⊆ M` of number fields (with `M/L` finite Galois) and
finite places `q'` of `M` above the finite place `q` of `L`, there is a canonical monoid
homomorphism of local unit groups

`(Place.localField L (Place.ofFinite q))ˣ →* (Place.localField M (Place.ofFinite q'))ˣ`

induced by the embedding of the completion of `L` at `q` into the completion of `M` at `q'`
(`q.adicCompletion L → q'.adicCompletion M`), and it is compatible with the global coefficient maps
`Lˣ → L_qˣ` and `Mˣ → M_{q'}ˣ` carried by `algebraMap L M`.

This is the coefficient layer of the local level system; it is the input of the local level map `v`
of the level square `(G1)`. -/
theorem exists_localUnitsMap
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers M))
    (hq : q.asIdeal = q'.asIdeal.comap
      (algebraMap (NumberField.RingOfIntegers L) (NumberField.RingOfIntegers M))) :
    ∃ φ : (NK.GlobalCFT.Place.localField L (NK.GlobalCFT.Place.ofFinite q))ˣ →*
        (NK.GlobalCFT.Place.localField M (NK.GlobalCFT.Place.ofFinite q'))ˣ,
      ∀ x : Lˣ,
        φ (NK.HassePrinciple.unitsToLocalUnitsHom
            (NK.GlobalCFT.Place.ofFinite q) x) =
          NK.HassePrinciple.unitsToLocalUnitsHom
            (NK.GlobalCFT.Place.ofFinite q')
            (Units.map (algebraMap L M).toMonoidHom x) := by
  obtain ⟨f, hf⟩ := Commons.RingTheory.Henselian.adicCompletionMap_liesOver
    (K := L) (L := M) q q' ⟨hq⟩
  refine ⟨Units.map f.toMonoidHom, ?_⟩
  intro x
  apply Units.ext
  rw [Units.coe_map]
  show f ((x : Lˣ) : q.adicCompletion L) = _
  rw [hf]
  rfl

/-! ## The tower level map: `H²(Gal(L/F), Lˣ) → H²(Gal(M/F), Mˣ)` -/

section Tower

variable {F L M : Type} [Field F] [NumberField F] [Field L] [NumberField L] [Field M]
  [NumberField M] [Algebra F L] [Algebra F M] [Algebra L M] [IsScalarTower F L M]
  [FiniteDimensional F L] [IsGalois F L] [FiniteDimensional F M] [IsGalois F M]

/-- **Equivariance of the units inclusion along a tower.**  The inclusion `Lˣ → Mˣ` commutes with
the action of `Gal(M/F)` on `Mˣ` and, through the restriction
`AlgEquiv.restrictNormalHom : Gal(M/F) →* Gal(L/F)`, with the action on `Lˣ`. -/
theorem unitsInclTowerEquivariance (σ : Gal(M/F)) (y : Lˣ) :
    Units.map (algebraMap L M).toMonoidHom
        (((AlgEquiv.restrictNormalHom (K₁ := M) (E := L)) σ) • y) =
      σ • (Units.map (algebraMap L M).toMonoidHom y) := by
  ext
  simp only [AlgEquiv.smul_units_def, Units.coe_map]
  rw [show (AlgEquiv.restrictNormalHom (K₁ := M) (E := L)) σ = σ.restrictNormal L from rfl]
  exact AlgEquiv.restrictNormal_commutes (E := L) σ (y : L)

/-- The units inclusion `Lˣ → Mˣ` along `algebraMap L M`, as a `CoeffInt`-linear map. -/
noncomputable def unitsInclTowerLinearMap :
    Additive Lˣ →ₗ[NK.HassePrinciple.CoeffInt] Additive Mˣ :=
  { toFun := ⇑(Units.map (algebraMap L M).toMonoidHom).toAdditive
    map_add' := fun x y => map_add (Units.map (algebraMap L M).toMonoidHom).toAdditive x y
    map_smul' := fun n x => by
      obtain ⟨z⟩ := n
      exact AddMonoidHom.map_zsmul (Units.map (algebraMap L M).toMonoidHom).toAdditive z x }

/-- The coefficient morphism of the tower level map: the units inclusion `Lˣ → Mˣ`, as a morphism
of representations along the restriction `Gal(M/F) →* Gal(L/F)`. -/
noncomputable def unitsInclTowerCoeff :
    Rep.res (AlgEquiv.restrictNormalHom (K₁ := M) (E := L))
        (NK.HassePrinciple.unitsRep F L) ⟶
      NK.HassePrinciple.unitsRep F M :=
  Rep.ofHom
    { toFun := fun x => unitsInclTowerLinearMap x
      map_add' := fun x y => unitsInclTowerLinearMap.map_add x y
      map_smul' := fun n x => unitsInclTowerLinearMap.map_smul n x
      isIntertwining' := fun σ => by
        apply LinearMap.ext
        intro x
        set y : Lˣ := Additive.toMul x with hy
        show Additive.ofMul (Units.map (algebraMap L M).toMonoidHom
            (Units.map (((AlgEquiv.restrictNormalHom (K₁ := M) (E := L)) σ)).toMonoidHom y))
          = Additive.ofMul ((σ : M ≃ₐ[F] M) • Units.map (algebraMap L M).toMonoidHom y)
        rw [AlgEquiv.smul_units_def]
        congr 1
        apply Units.ext
        simp only [Units.coe_map]
        rw [show (AlgEquiv.restrictNormalHom (K₁ := M) (E := L)) σ = σ.restrictNormal L from rfl]
        exact AlgEquiv.restrictNormal_commutes (E := L) σ y }

/-- **The tower level map** `H²(Gal(L/F), Lˣ) → H²(Gal(M/F), Mˣ)`: the inclusion of the level
cohomology of `L` into that of the deeper tower level `M`, induced by the restriction of the Galois
groups and the coefficient inclusion `Lˣ → Mˣ`.  It is the field-theoretic analogue of
`NK.HassePrinciple.unitsLevelMap` (there for the `LevelGroup`-systems at `V = ⊤`). -/
noncomputable def unitsLevelMapTower :
    groupCohomology (NK.HassePrinciple.unitsRep F L) 2 ⟶
      groupCohomology (NK.HassePrinciple.unitsRep F M) 2 :=
  groupCohomology.map (AlgEquiv.restrictNormalHom (K₁ := M) (E := L))
    unitsInclTowerCoeff 2

end Tower

end NK.NUV2.LC

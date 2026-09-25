import Mathlib
import Submission.NK.NUV2.LC.RouteB.locUnits_tower_eq_zero
import Submission.NK.HassePrinciple.exists_units_div_of_isMulCocycle_ringEquiv
import Submission.NK.HassePrinciple.subsingleton_classGroupRep_one
import Submission.NK.GlobalCFT.Inclusion.globalCFT_exists_smul_eq_of_liesOver
import Submission.NK.GlobalCFT.Inclusion.globalCFT_liesOver_unique
import Submission.NK.HassePrinciple.liesOver_smul_of_restrict

/-!
# Auxiliaries for the tower `F ⊆ L ⊆ M`: surjectivity on decomposition groups and Hilbert 90

For a tower `F ⊆ L ⊆ M` of number fields with `L/F`, `M/F` (and `M/L`) finite Galois, places
`w` of `L` and `w'` of `M` above it, this file provides

* `localStabilizerMapTower_surjective`: the decomposition group of `w'` surjects onto the
  decomposition group of `w` under `NK.NUV2.LC.RouteB.localStabilizerMapTower`;
* `subsingleton_h1_ker_localStabilizerMapTower`: Hilbert 90 for the kernel `S` of that map acting
  on the local units `M_{w'}ˣ`;
* the two elementary facts about `AlgEquiv.restrictScalars` used in both.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open CategoryTheory

namespace NK.CFTLib.HR.TransferAux.TowerAux

variable {F L M : Type} [Field F] [NumberField F] [Field L] [NumberField L]
  [Field M] [NumberField M] [Algebra F L] [Algebra F M] [Algebra L M] [IsScalarTower F L M]
  [FiniteDimensional F L] [IsGalois F L] [FiniteDimensional F M] [IsGalois F M]

/-- **The two Galois actions of `M ≃ₐ[L] M` on the places of `M` (viewed as a place of the
`F`-algebra `M` and as a place of the `L`-algebra `M`) coincide.** -/
theorem restrictScalars_smul_place (τ : M ≃ₐ[L] M) (v : NK.GlobalCFT.Place M) :
    AlgEquiv.restrictScalars F τ • v = τ • v := by
  cases v with
  | inl w => rfl
  | inr q => rfl

/-- The restriction of an `L`-automorphism of `M` (regarded as an `F`-automorphism) restricts
trivially to `L`. -/
theorem restrictNormal_restrictScalars_eq_one (τ : M ≃ₐ[L] M) :
    (AlgEquiv.restrictNormalHom (K₁ := M) (E := L)) (AlgEquiv.restrictScalars F τ) = 1 := by
  apply AlgEquiv.ext
  intro y
  apply (algebraMap L M).injective
  have h1 : (AlgEquiv.restrictNormalHom (K₁ := M) (E := L)) (AlgEquiv.restrictScalars F τ)
      = (AlgEquiv.restrictScalars F τ).restrictNormal L := rfl
  rw [h1, AlgEquiv.restrictNormal_commutes, AlgEquiv.restrictScalars_apply, AlgEquiv.commutes,
    AlgEquiv.one_apply]

/-- **Surjectivity of the tower map of decomposition groups**: a `σ` fixing the place `w` of `L`
lifts to an element of `Gal(M/F)` fixing a place `w'` of `M` above `w`. -/
theorem localStabilizerMapTower_surjective {w : NK.GlobalCFT.Place L}
    {w' : NK.GlobalCFT.Place M} (h : NK.GlobalCFT.Place.LiesOver w' w) :
    Function.Surjective
      (NK.NUV2.LC.RouteB.localStabilizerMapTower (F := F) (L := L) (M := M) h) := by
  haveI : FiniteDimensional L M := Module.Finite.of_restrictScalars_finite F L M
  haveI : IsGalois L M := IsGalois.tower_top_of_isGalois F L M
  intro σ
  obtain ⟨σl, hσl⟩ := AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := L) (E := M) σ.1
  have h1 : (σl • w').LiesOver
      (((AlgEquiv.restrictNormalHom (K₁ := M) (E := L)) σl) • w) :=
    NK.HassePrinciple.liesOver_smul_of_restrict (K := F) (F := L) (L := M) σl
      ((AlgEquiv.restrictNormalHom (K₁ := M) (E := L)) σl)
      (fun y => AlgEquiv.restrictNormal_commutes (E := L) σl y) h
  rw [hσl, MulAction.mem_stabilizer_iff.mp σ.2] at h1
  obtain ⟨τ, hτ⟩ :=
    NK.GlobalCFT.Inclusion.globalCFT_exists_smul_eq_of_liesOver (K := L) (L := M) h1 h
  refine ⟨⟨AlgEquiv.restrictScalars F τ * σl, ?_⟩, ?_⟩
  · rw [MulAction.mem_stabilizer_iff]
    show (AlgEquiv.restrictScalars F τ * σl) • w' = w'
    rw [mul_smul, restrictScalars_smul_place (F := F) τ (σl • w'), hτ]
  · apply Subtype.ext
    show (AlgEquiv.restrictNormalHom (K₁ := M) (E := L))
      (AlgEquiv.restrictScalars F τ * σl) = σ.1
    rw [map_mul, restrictNormal_restrictScalars_eq_one, one_mul, hσl]

variable {w : NK.GlobalCFT.Place L} {w' : NK.GlobalCFT.Place M}

/-- **Hilbert 90 for the kernel of the tower map.**  The first group cohomology of the local units
`M_{w'}ˣ` with the action of the kernel `S = ker (localStabilizerMapTower h)` vanishes: this is
Noether's form of Hilbert 90 for the faithful action of `S` on the field `M_{w'}` by ring
automorphisms (`NK.HassePrinciple.exists_units_div_of_isMulCocycle_ringEquiv`). -/
theorem subsingleton_h1_ker_localStabilizerMapTower (h : NK.GlobalCFT.Place.LiesOver w' w) :
    Subsingleton (groupCohomology
      (Rep.res ((NK.NUV2.LC.RouteB.localStabilizerMapTower (F := F) (L := L) (M := M) h).ker).subtype
        (NK.HassePrinciple.localUnitsRep F M w')) 1) := by
  classical
  letI : MulDistribMulAction
      ↥((NK.NUV2.LC.RouteB.localStabilizerMapTower (F := F) (L := L) (M := M) h).ker)
      ((NK.GlobalCFT.Place.localField M w')ˣ) :=
    { smul := fun σ u =>
        (((NK.NUV2.LC.RouteB.localStabilizerMapTower (F := F) (L := L) (M := M) h).ker).subtype σ) • u
      one_smul := fun u => by
        change (((NK.NUV2.LC.RouteB.localStabilizerMapTower (F := F) (L := L) (M := M) h).ker).subtype 1) • u = u
        rw [map_one]
        exact one_smul _ u
      mul_smul := fun σ τ u => by
        change (((NK.NUV2.LC.RouteB.localStabilizerMapTower (F := F) (L := L) (M := M) h).ker).subtype (σ * τ)) • u
          = (((NK.NUV2.LC.RouteB.localStabilizerMapTower (F := F) (L := L) (M := M) h).ker).subtype σ) •
            ((((NK.NUV2.LC.RouteB.localStabilizerMapTower (F := F) (L := L) (M := M) h).ker).subtype τ) • u)
        rw [map_mul]
        exact mul_smul _ _ _
      smul_mul := fun σ u v => by
        change (((NK.NUV2.LC.RouteB.localStabilizerMapTower (F := F) (L := L) (M := M) h).ker).subtype σ) • (u * v)
          = (((NK.NUV2.LC.RouteB.localStabilizerMapTower (F := F) (L := L) (M := M) h).ker).subtype σ) • u *
            (((NK.NUV2.LC.RouteB.localStabilizerMapTower (F := F) (L := L) (M := M) h).ker).subtype σ) • v
        exact smul_mul' _ _ _
      smul_one := fun σ => by
        change (((NK.NUV2.LC.RouteB.localStabilizerMapTower (F := F) (L := L) (M := M) h).ker).subtype σ) •
          (1 : (NK.GlobalCFT.Place.localField M w')ˣ) = 1
        exact smul_one _ }
  rw [show Rep.res
        ((NK.NUV2.LC.RouteB.localStabilizerMapTower (F := F) (L := L) (M := M) h).ker).subtype
        (NK.HassePrinciple.localUnitsRep F M w')
      = Rep.ofDistribMulAction NK.HassePrinciple.CoeffInt
          ↥((NK.NUV2.LC.RouteB.localStabilizerMapTower (F := F) (L := L) (M := M) h).ker)
          (Additive ((NK.GlobalCFT.Place.localField M w')ˣ)) from rfl]
  refine NK.HassePrinciple.subsingleton_groupCohomology_one_of_mulCoboundary
    NK.HassePrinciple.CoeffInt (fun c hc => ?_)
  set φ : ↥((NK.NUV2.LC.RouteB.localStabilizerMapTower (F := F) (L := L) (M := M) h).ker) →*
      (NK.GlobalCFT.Place.localField M w' ≃+* NK.GlobalCFT.Place.localField M w') :=
    (NK.HassePrinciple.localAutHom (K := F) (L := M) w').comp
      ((NK.NUV2.LC.RouteB.localStabilizerMapTower (F := F) (L := L) (M := M) h).ker).subtype
  have hφ : Function.Injective φ := fun a b hab => by
    have h2 : (NK.HassePrinciple.localAutHom (K := F) (L := M) w') a.1
        = (NK.HassePrinciple.localAutHom (K := F) (L := M) w') b.1 := hab
    exact Subtype.ext ((NK.HassePrinciple.localAutHom_injective (K := F) (L := M) w') h2)
  have hact : ∀ (g : ↥((NK.NUV2.LC.RouteB.localStabilizerMapTower (F := F) (L := L)
        (M := M) h).ker))
      (u : (NK.GlobalCFT.Place.localField M w')ˣ), g • u = Units.map (φ g).toMonoidHom u :=
    fun g u => rfl
  haveI hF : Fintype Gal(M/F) := AlgEquiv.fintype F M
  haveI hS : Fintype
      ↥((NK.NUV2.LC.RouteB.localStabilizerMapTower (F := F) (L := L) (M := M) h).ker) :=
    Fintype.ofFinite _
  have hcoc : ∀ g h' : ↥((NK.NUV2.LC.RouteB.localStabilizerMapTower (F := F) (L := L)
      (M := M) h).ker), c (g * h') = Units.map (φ g).toMonoidHom (c h') * c g := by
    intro g h'
    have h1 : c (g * h') = g • c h' * c g := hc g h'
    rw [h1]
    exact congrArg (fun z : (NK.GlobalCFT.Place.localField M w')ˣ => z * c g) (hact g (c h'))
  obtain ⟨β, hβ⟩ := NK.HassePrinciple.exists_units_div_of_isMulCocycle_ringEquiv φ hφ c hcoc
  exact ⟨β, fun g => (congrArg (fun z : (NK.GlobalCFT.Place.localField M w')ˣ => z / β)
    (hact g β)).trans (hβ g).symm⟩

end NK.CFTLib.HR.TransferAux.TowerAux

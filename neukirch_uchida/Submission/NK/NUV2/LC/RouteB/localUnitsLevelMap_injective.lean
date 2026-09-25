import Mathlib
import Submission.NK.NUV2.LC.RouteB.localUnitsLevelSystem
import Submission.NK.NUV2.LC.RouteB.locUnits_tower_eq_zero
import Submission.NK.NUV2.ABHN.unitsLevelMap_injective
import Submission.NK.HassePrinciple.LocalUnits
import Submission.NK.CFTLib.HR.TransferAux.invariantsAux
import Submission.NK.GlobalCFT.Inclusion.globalCFT_ideleClassGroup_inclusion_injective
import Submission.Commons.RepresentationTheory.GroupCohomology.H2_inflation_injective_of_subsingleton_H1

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

open CategoryTheory

namespace NK.NUV2.LC.RouteB

/-- `NK.HassePrinciple.localUnitsRep` with all universes pinned to `0`. -/
noncomputable abbrev lurep (K N : Type) [Field K] [NumberField K] [Field N] [NumberField N]
    [Algebra K N] [FiniteDimensional K N] [IsGalois K N] (v : NK.GlobalCFT.Place N) :
    Rep.{0,0,0} NK.HassePrinciple.CoeffInt ↥(MulAction.stabilizer (N ≃ₐ[K] N) v) :=
  NK.HassePrinciple.localUnitsRep K N v

variable {F L M : Type} [Field F] [NumberField F] [Field L] [NumberField L] [Field M] [NumberField M]
  [Algebra F L] [Algebra F M] [Algebra L M] [IsScalarTower F L M]
  [FiniteDimensional F L] [IsGalois F L] [FiniteDimensional F M] [IsGalois F M]
  {w : NK.GlobalCFT.Place L} {w' : NK.GlobalCFT.Place M}

/-- **Injectivity of the local coefficient map `L_wˣ → M_{w'}ˣ`.**  It is the completion map on
units, hence the image of the injective ring map `L_w → M_{w'}`. -/
theorem localUnitsMapTowerCoeff_injective (h : NK.GlobalCFT.Place.LiesOver w' w) :
    Function.Injective ⇑(localUnitsMapTowerCoeff (F := F) (L := L) (M := M) h).hom := by
  intro a b hab
  have key : ∀ x : (lurep F L w).V,
      Additive.toMul ((localUnitsMapTowerCoeff (F := F) (L := L) (M := M) h).hom x)
        = NK.GlobalCFT.Place.localAlgebraMapUnits w' w h (Additive.toMul x) := fun _ => rfl
  have h2 : NK.GlobalCFT.Place.localAlgebraMapUnits w' w h (Additive.toMul a)
      = NK.GlobalCFT.Place.localAlgebraMapUnits w' w h (Additive.toMul b) := by
    rw [← key a, ← key b]
    exact congrArg (fun z => Additive.toMul z) hab
  exact congrArg Additive.ofMul
    (NK.GlobalCFT.Inclusion.globalCFT_localAlgebraMapUnits_injective h h2)

/-- **Every `1`-cocycle on the kernel of the tower map is a coboundary** (Hilbert 90 for the local
extension `M_{w'}/L_w`).  This is the `H¹ = 0` input of the inflation criterion
`NK.NUV2.ABHN.groupCohomology_map_two_injective`, derived from the vanishing of the first group
cohomology of `M_{w'}ˣ` along the kernel. -/
theorem kerCocycle_isCoboundary (h : NK.GlobalCFT.Place.LiesOver w' w)
    (α : ↥((localStabilizerMapTower (F := F) (L := L) (M := M) h).ker) → (lurep F M w').V)
    (hα : ∀ a b, α (a * b) = (NK.HassePrinciple.localUnitsRep F M w').ρ
      (a : ↥(MulAction.stabilizer Gal(M/F) w')) (α b) + α a) :
    ∃ y, ∀ a, α a = (NK.HassePrinciple.localUnitsRep F M w').ρ
      (a : ↥(MulAction.stabilizer Gal(M/F) w')) y - y := by
  have hmem : α ∈ groupCohomology.cocycles₁
      (Rep.res ((localStabilizerMapTower (F := F) (L := L) (M := M) h).ker).subtype
        (lurep F M w')) :=
    (groupCohomology.mem_cocycles₁_def
      (A := Rep.res ((localStabilizerMapTower (F := F) (L := L) (M := M) h).ker).subtype
        (lurep F M w')) α).2 (by
      intro g hh
      show (NK.HassePrinciple.localUnitsRep F M w').ρ
          (g : ↥(MulAction.stabilizer Gal(M/F) w')) (α hh) - α (g * hh) + α g = 0
      rw [hα g hh]
      abel)
  obtain ⟨y, hy⟩ := Commons.RepresentationTheory.GroupCohomology.exists_sub_eq_of_subsingleton_H1
    ((localStabilizerMapTower (F := F) (L := L) (M := M) h).ker)
    (lurep F M w')
    (NK.CFTLib.HR.TransferAux.TowerAux.subsingleton_h1_ker_localStabilizerMapTower h) α hmem
  exact ⟨y, fun a => (hy a).symm⟩

theorem localUnitsLevelMap_injective {F L M : Type} [Field F] [NumberField F] [Field L]
    [NumberField L] [Field M] [NumberField M]
    [Algebra F L] [Algebra F M] [Algebra L M] [IsScalarTower F L M]
    [FiniteDimensional F L] [IsGalois F L] [FiniteDimensional F M] [IsGalois F M]
    {w : NK.GlobalCFT.Place L} {w' : NK.GlobalCFT.Place M}
    (h : NK.GlobalCFT.Place.LiesOver w' w) :
    Function.Injective (fun x : groupCohomology (NK.HassePrinciple.localUnitsRep F L w) 2 =>
      (NK.NUV2.LC.RouteB.localUnitsLevelMap (F := F) (L := L) (M := M) h).hom x) := by
  letI : FiniteDimensional L M := Module.Finite.of_restrictScalars_finite F L M
  letI : IsGalois L M := IsGalois.tower_top_of_isGalois F L M
  have hcrit := NK.NUV2.ABHN.groupCohomology_map_two_injective
      (f := localStabilizerMapTower (F := F) (L := L) (M := M) h)
      (hf := NK.CFTLib.HR.TransferAux.TowerAux.localStabilizerMapTower_surjective h)
      (A := lurep F L w)
      (B := lurep F M w')
      (φ := localUnitsMapTowerCoeff (F := F) (L := L) (M := M) h)
      (hφ := localUnitsMapTowerCoeff_injective (F := F) (L := L) (M := M) h)
      (hφsurj := fun b hb => by
        obtain ⟨u, hu⟩ := NK.CFTLib.HR.TransferAux.unitsMapTowerCoeff_surj_invariants
          (F := F) (L := L) (M := M) h b hb
        exact ⟨Additive.ofMul u, hu⟩)
      (hH90 := kerCocycle_isCoboundary (F := F) (L := L) (M := M) h)
  exact hcrit

end NK.NUV2.LC.RouteB

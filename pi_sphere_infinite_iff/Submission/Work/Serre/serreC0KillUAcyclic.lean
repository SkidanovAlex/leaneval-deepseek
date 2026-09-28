import Submission.Work.Serre.serreC0KillHomologySets
import Submission.Work.Cohomology.MVSequence
import Submission.Work.Serre.CellStep.compressRel_cellU

set_option synthInstance.maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.Serre

noncomputable section

open Work.RatHurewicz

variable {n : ℕ} {Y : Type} [TopologicalSpace Y] {ι : Type}

/-- The relative homology of the pair `(KillU, KillA)` vanishes (the outer part strongly
deformation retracts onto the old part). -/
theorem isZero_relChains_KillU (f : ι → C(cellSphere n, Y)) (m : ℕ) :
    CategoryTheory.Limits.IsZero
      ((Work.Cohomology.relChains (TopCat.of ↥(KillU f))
        {x : ↥(KillU f) | (x : KillX f) ∈ KillA f}).homology m) := by
  refine Work.Serre.isZero_relChains_of_compress (X := ↥(KillU f))
    (A := {x : ↥(KillU f) | (x : KillX f) ∈ KillA f}) (fun d => ?_) m
  exact Work.Serre.CellStep.compressRel_cellU n Y ι f (ρ := 1 / 4) (by norm_num) (by norm_num) d

/-- The inclusion of the old part in the outer part induces an isomorphism on homology. -/
theorem isIso_inclChains_KillU (f : ι → C(cellSphere n, Y)) (k : ℕ) :
    IsIso (HomologicalComplex.homologyMap (Work.Cohomology.inclChains (TopCat.of ↥(KillU f))
      {x : ↥(KillU f) | (x : KillX f) ∈ KillA f}) k) := by
  set X' : TopCat := TopCat.of ↥(KillU f) with hX'
  set A' : Set X' := {x : ↥(KillU f) | (x : KillX f) ∈ KillA f} with hA'
  have hzero : ∀ m : ℕ, CategoryTheory.Limits.IsZero
      ((Work.Cohomology.relChains X' A').homology m) := by
    intro m
    have h := isZero_relChains_KillU f m
    simpa only [hX', hA'] using h
  haveI hk : Subsingleton ↥(HomologicalComplex.homology
      (cokernel (Work.Cohomology.inclChains X' A')) k) :=
    ModuleCat.subsingleton_of_isZero (hzero k)
  haveI hk1 : Subsingleton ↥(HomologicalComplex.homology
      (cokernel (Work.Cohomology.inclChains X' A')) (k + 1)) :=
    ModuleCat.subsingleton_of_isZero (hzero (k + 1))
  haveI hk' : Subsingleton ↥((Work.Cohomology.relChains X' A').homology k) :=
    ModuleCat.subsingleton_of_isZero (hzero k)
  haveI hk1' : Subsingleton ↥((Work.Cohomology.relChains X' A').homology (k + 1)) :=
    ModuleCat.subsingleton_of_isZero (hzero (k + 1))
  have hsurj : Function.Surjective
      (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (Work.Cohomology.inclChains X' A') k)) := by
    intro y
    have hex := Work.Cohomology.hPair_exact₂ X' A' k
    rw [ShortComplex.moduleCat_exact_iff] at hex
    have hg : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (cokernel.π (Work.Cohomology.inclChains X' A')) k)) y = 0 :=
      Subsingleton.elim _ _
    obtain ⟨x, hx⟩ := hex y hg
    exact ⟨x, hx⟩
  have hinj : Function.Injective
      (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (Work.Cohomology.inclChains X' A') k)) := by
    intro a b hab
    have hex := Work.Cohomology.hPair_exact₁ X' A' k
    rw [ShortComplex.moduleCat_exact_iff] at hex
    have hker : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (Work.Cohomology.inclChains X' A') k)) (a - b) = 0 := by
      rw [map_sub, hab, sub_self]
    obtain ⟨z, hz⟩ := hex (a - b) hker
    have hz0 : z = 0 := Subsingleton.elim _ _
    rw [hz0, map_zero] at hz
    exact sub_eq_zero.mp hz.symm
  haveI : Mono (HomologicalComplex.homologyMap (Work.Cohomology.inclChains X' A') k) :=
    (ModuleCat.mono_iff_injective _).mpr hinj
  haveI : Epi (HomologicalComplex.homologyMap (Work.Cohomology.inclChains X' A') k) :=
    (ModuleCat.epi_iff_surjective _).mpr hsurj
  exact isIso_of_mono_of_epi _

end

end Work.Serre

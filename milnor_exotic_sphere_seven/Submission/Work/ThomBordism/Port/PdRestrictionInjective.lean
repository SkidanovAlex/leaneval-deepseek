-- Copied verbatim from `Submission.Work.Cohomology.pd_restriction_injective`, with imports re-routed to the
-- clash-free chain (`Work.Thom.Relocate.*` / the local copies in this directory), exactly as
-- `Submission/Work/Thom/README.md` ADDENDUM 16 did for the Thom area: the workspace contains
-- two *identical* duplicate modules `Work.Cohomology.Crux.ovlRestrictionSurjective` and
-- `Work.Cohomology.Crux.vkCruxRestr`, so a module importing one cannot be combined with a
-- module importing the other.  The `Work.ThomBordism` chapter imports
-- `ovlRestrictionSurjective` (via `Interface.lean`), hence these copies.  All declarations
-- keep their original names and proofs.
import Mathlib
import Submission.Work.Cohomology.pd_good
-- Re-pointed to the original chain (Islands subproject, 2026): the `Thom/Relocate` copies of
-- the Poincaré-duality chain declared the same names as the `Cohomology/` originals.  The
-- originals are now re-routed (`Crux/vk_transgression_cap_weak.lean` imports the `ovl` copies),
-- so the copies are no longer needed here and the two modules can be imported together.
import Submission.Work.Cohomology.capRelAux

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

theorem pd_restriction_injective {M : TopCat} [T2Space M] {W U : Set M} (hW : IsOpen W)
    (hUW : U ⊆ W) (hU : IsOpen U) {K : Set M} (hKU : K ⊆ U) (hKc : IsCompact K) (k : ℕ) :
    Function.Injective ((HomologicalComplex.homologyMap (Work.Cohomology.relComplexMap ℤ
      (Work.Cohomology.pdRelSub U K) (Work.Cohomology.pdRelSub W K)
      (Work.Cohomology.pdIncl W U hUW) (fun x hx => hx)) k).hom) := by
  have hA : IsOpen (Kᶜ : Set M) := hKc.isClosed.isOpen_compl
  have hcovW : W ∪ Kᶜ = Set.univ := by
    rw [Set.eq_univ_iff_forall]; intro x
    by_cases hx : x ∈ K
    · exact Or.inl (hUW (hKU hx))
    · exact Or.inr hx
  have hcovU : U ∪ Kᶜ = Set.univ := by
    rw [Set.eq_univ_iff_forall]; intro x
    by_cases hx : x ∈ K
    · exact Or.inl (hKU hx)
    · exact Or.inr hx
  haveI hEW : IsIso (HomologicalComplex.homologyMap
      (relComplexMap ℤ (pdRelSub W K) Kᶜ (subtypeIncl M W) (fun y hy => hy)) k) :=
    capRel_excision_isIso M W Kᶜ hW hA hcovW k (fun y hy => hy)
  haveI hEU : IsIso (HomologicalComplex.homologyMap
      (relComplexMap ℤ (pdRelSub U K) Kᶜ (subtypeIncl M U) (fun x hx => hx)) k) :=
    capRel_excision_isIso M U Kᶜ hU hA hcovU k (fun x hx => hx)
  have hcomp := capRel_relComplexMap_comp (R := ℤ) (pdRelSub U K) (pdRelSub W K) Kᶜ
      (pdIncl W U hUW) (subtypeIncl M W) (fun x hx => hx) (fun y hy => hy)
  have hcongr := capRel_relComplexMap_congr (R := ℤ) (X₁ := TopCat.of U) (X₂ := M)
      (pdRelSub U K) Kᶜ
      (show pdIncl W U hUW ≫ subtypeIncl M W = subtypeIncl M U from by ext x; rfl)
      (fun x hx => hx) (fun x hx => hx)
  have hkey := hcomp.symm.trans hcongr
  have hhom := congrArg (fun φ => HomologicalComplex.homologyMap φ k) hkey
  rw [HomologicalComplex.homologyMap_comp] at hhom
  have hB : HomologicalComplex.homologyMap (relComplexMap ℤ (pdRelSub U K) (pdRelSub W K)
        (pdIncl W U hUW) (fun x hx => hx)) k
      = inv (HomologicalComplex.homologyMap
          (relComplexMap ℤ (pdRelSub W K) Kᶜ (subtypeIncl M W) (fun y hy => hy)) k)
        ≫ HomologicalComplex.homologyMap
          (relComplexMap ℤ (pdRelSub U K) Kᶜ (subtypeIncl M U) (fun x hx => hx)) k := by
    rw [← hhom, CategoryTheory.IsIso.inv_hom_id_assoc]
  haveI hBU : IsIso (HomologicalComplex.homologyMap (relComplexMap ℤ (pdRelSub U K)
        (pdRelSub W K) (pdIncl W U hUW) (fun x hx => hx)) k) := by
    rw [hB]; infer_instance
  haveI : CategoryTheory.Mono (HomologicalComplex.homologyMap (relComplexMap ℤ (pdRelSub U K)
        (pdRelSub W K) (pdIncl W U hUW) (fun x hx => hx)) k) :=
    CategoryTheory.IsIso.mono_of_iso _
  exact (ModuleCat.mono_iff_injective _).mp inferInstance

end
end Work.Cohomology


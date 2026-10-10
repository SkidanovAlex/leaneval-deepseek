import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
import Submission.NK.CFTLib.HR.isCyclotomic_onePlace_real
import Submission.NK.HR2.transferStepOnePlace
import Submission.Work.SSGRoute.eb_arch_crux
import Submission.Work.SSGRoute.eb_locUnits_resToGal
import Submission.Work.SSGRoute.phi1_level_naturality
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The cyclic case of `brauer_single_place` (Hilbert reciprocity)

For a cyclic extension `M/k` of number fields, a class of `H²(Gal(M/k), Mˣ)` whose localisation
vanishes at every place outside one place `v₀` is zero.

This is the statement of `Work.SSGRoute.brauer_single_place_cyclic` (proved in
`Submission/Work/SSGRoute/brauer_single_place.lean`, which is not yet complete); it is copied here
so that the archimedean assembly imports only fully verified modules.

The class is the cyclic class of some `b ∈ kˣ` (`NK.HR2.exists_cycClassOf_eq_period`), the
hypothesis says that `b` is a local norm at every place `≠ v₀` (the localisation dictionary
`NK.HR2.localNormSubgroup_iff_cycClass_place`), Hilbert reciprocity
`NK.CFTLib.hilbertReciprocity_onePlace_aux` supplies it at `v₀`, and the Hasse principle for units
`NK.GlobalCFTdeep.hbnUnits` finishes.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory

namespace Work.SSGRoute

/-- **The cyclic case of `brauer_single_place`.** -/
theorem eb_arch_cyclic (k M : Type) [Field k] [NumberField k] [Field M] [NumberField M]
    [Algebra k M] [FiniteDimensional k M] [IsGalois k M] [IsCyclic (M ≃ₐ[k] M)]
    (β : groupCohomology (NK.HassePrinciple.unitsRep k M) 2) (v₀ : NK.GlobalCFT.Place k)
    (h : ∀ w : NK.GlobalCFT.Place M, ¬ NK.GlobalCFT.Place.LiesOver w v₀ →
      (NK.HassePrinciple.locUnits k M w).hom β = 0) : β = 0 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := M ≃ₐ[k] M)
  obtain ⟨b, hb⟩ := NK.HR2.exists_cycClassOf_eq_period (K := k) (M := M) g hg β
  have hloc : ∀ v : NK.GlobalCFT.Place k, v ≠ v₀ →
      NK.CFTLib.IdeleHasse.localImageAt v b ∈
        NK.CFTLib.IdeleHasse.localNormSubgroup (K := k) (L := M) v := by
    intro v hv
    obtain ⟨w, hw⟩ := NK.GlobalCFTdeep.NormIndex.exists_place_liesOver (K := k) (L := M) v
    have hw₀ : ¬ NK.GlobalCFT.Place.LiesOver w v₀ := fun hh =>
      hv (NK.GlobalCFT.Inclusion.globalCFT_liesOver_unique hw hh)
    have h0 : (NK.HassePrinciple.locUnits k M w).hom β = 0 := h w hw₀
    rw [← hb] at h0
    exact (NK.HR2.localNormSubgroup_iff_cycClass_place (K := k) (F := M) g hg w v hw b).mp h0
  have h₀ : NK.CFTLib.IdeleHasse.localImageAt v₀ b ∈
      NK.CFTLib.IdeleHasse.localNormSubgroup (K := k) (L := M) v₀ := by
    refine NK.CFTLib.hilbertReciprocity_onePlace_aux b v₀ (fun v hv => ?_)
    simpa only [NK.CFTLib.IdeleHasse.localImageAt, NK.CFTLib.localImageHom_apply] using hloc v hv
  have hall : ∀ w : NK.GlobalCFT.Place M, (NK.HassePrinciple.locUnits k M w).hom β = 0 := by
    intro w
    by_cases hw : NK.GlobalCFT.Place.LiesOver w v₀
    · rw [← hb]
      exact (NK.HR2.localNormSubgroup_iff_cycClass_place (K := k) (F := M) g hg w v₀ hw b).mpr h₀
    · exact h w hw
  exact (NK.GlobalCFTdeep.hbnUnits (F := k) (E := M)) β hall

end Work.SSGRoute

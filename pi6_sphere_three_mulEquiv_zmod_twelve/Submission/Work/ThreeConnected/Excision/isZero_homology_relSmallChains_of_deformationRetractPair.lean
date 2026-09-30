import Mathlib
import Submission.Work.ThreeConnected.Excision.PairVanish
import Submission.Work.ThreeConnected.Excision.smallInToSingA_subInclChain
import Submission.Work.ThreeConnected.Excision.isZero_homology_three_of_isIso_homology_one
import Submission.Work.Cohomology.Endgame.relCohMV_elim

namespace Work.ThreeConnected.Excision

open CategoryTheory Limits

/-- **The relative small chains of `(U, U ∩ A)` vanish in positive degrees when `A` is a
deformation retract of `U`.**  The small chains of `(U, U ∩ A)` agree with the genuine relative
chains of the pair `(U, A)`, and those vanish in positive degrees over a deformation retract
(`Work.ThreeConnected.Excision.isZero_relChains_of_deformationRetractPair_succ`). -/
theorem isZero_homology_relSmallChains_of_deformationRetractPair
    {X : TopCat.{0}} {U A V : Set X} (h : Work.ThreeConnected.IsDeformationRetractPair (X := X) U A)
    (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ) (n : ℕ) (hn : 1 ≤ n) :
    CategoryTheory.Limits.IsZero ((Work.Cohomology.relSmallChains U V U (U ∩ A)
      Set.inter_subset_left).homology n) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  obtain ⟨e⟩ := Work.Cohomology.Endgame.relSmallChains_iso_relChains U V U (U ∩ A)
    Set.inter_subset_left (Or.inl subset_rfl)
  have hST : ((Subtype.val : ↥U → X) ⁻¹' (U ∩ A)) = Work.Cohomology.interAU A U := by
    ext x
    exact ⟨fun hx => hx.2, fun hx => ⟨x.2, hx⟩⟩
  have e' : Work.Cohomology.relSmallChains U V U (U ∩ A) Set.inter_subset_left
      ≅ Work.Cohomology.relChains (TopCat.of ↥U) (Work.Cohomology.interAU A U) :=
    hST ▸ e
  have hh := isZero_relChains_of_deformationRetractPair_succ h j
  refine CategoryTheory.Limits.IsZero.of_iso hh ?_
  exact
    { hom := HomologicalComplex.homologyMap e'.hom (j + 1)
      inv := HomologicalComplex.homologyMap e'.inv (j + 1)
      hom_inv_id := by
        rw [← HomologicalComplex.homologyMap_comp, e'.hom_inv_id,
          HomologicalComplex.homologyMap_id]
      inv_hom_id := by
        rw [← HomologicalComplex.homologyMap_comp, e'.inv_hom_id,
          HomologicalComplex.homologyMap_id] }

end Work.ThreeConnected.Excision

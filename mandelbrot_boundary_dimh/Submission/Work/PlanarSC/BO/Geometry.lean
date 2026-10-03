import Mathlib
import Submission.Work.PlanarSC.BO.Defs

/-!
# Elementary geometry of unit grid steps

Two lemmas about the unit steps of the integer lattice (`Work.HornSC.CellBoundaryJordan`):

* `eq_of_unitStep_same_ends` — unit steps are east/north oriented, so a unit step is determined by
  its unordered pair of endpoints;

* `unitStep_seg_inter_subset` — two *distinct* unit steps have segments meeting only in common
  endpoints.
-/

open Set

namespace Work.HornSC.CellBoundaryJordan.BO

noncomputable section

/-- A unit step is determined by its unordered pair of endpoints. -/
theorem eq_of_unitStep_same_ends {e e' : (ℤ × ℤ) × (ℤ × ℤ)} (he : IsUnitStep e)
    (he' : IsUnitStep e') (h : ({e.1, e.2} : Finset (ℤ × ℤ)) = {e'.1, e'.2}) : e = e' := by
  have h1 : e'.1 = e.1 ∨ e'.1 = e.2 := by
    have hm : e'.1 ∈ ({e'.1, e'.2} : Finset (ℤ × ℤ)) := by simp
    rw [← h] at hm
    simpa using hm
  have h2 : e'.2 = e.1 ∨ e'.2 = e.2 := by
    have hm : e'.2 ∈ ({e'.1, e'.2} : Finset (ℤ × ℤ)) := by simp
    rw [← h] at hm
    simpa using hm
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact absurd (h1.trans h2.symm) (isStep_ne he')
  · exact Prod.ext h1.symm h2.symm
  · exfalso
    -- `e'` is the reversal of `e`, which is impossible for east/north oriented steps
    have key : e.1 = (e.2.1 + 1, e.2.2) ∨ e.1 = (e.2.1, e.2.2 + 1) := by
      rcases he' with hh | hh
      · left
        have hthis : e.1 = (e'.1.1 + 1, e'.1.2) := by rw [← h2]; exact hh
        rw [h1] at hthis
        exact hthis
      · right
        have hthis : e.1 = (e'.1.1, e'.1.2 + 1) := by rw [← h2]; exact hh
        rw [h1] at hthis
        exact hthis
    have key2 : e.2 = (e.1.1 + 1, e.1.2) ∨ e.2 = (e.1.1, e.1.2 + 1) := he
    rcases key with hk | hk <;> rcases key2 with hk2 | hk2
    · have a1 : e.1.1 = e.2.1 + 1 := by simpa using congrArg Prod.fst hk
      have a2 : e.2.1 = e.1.1 + 1 := by simpa using congrArg Prod.fst hk2
      omega
    · have a1 : e.1.1 = e.2.1 + 1 := by simpa using congrArg Prod.fst hk
      have a2 : e.2.1 = e.1.1 := by simpa using congrArg Prod.fst hk2
      omega
    · have a1 : e.1.1 = e.2.1 := by simpa using congrArg Prod.fst hk
      have a2 : e.2.1 = e.1.1 + 1 := by simpa using congrArg Prod.fst hk2
      omega
    · have a1 : e.1.2 = e.2.2 + 1 := by simpa using congrArg Prod.snd hk
      have a2 : e.2.2 = e.1.2 + 1 := by simpa using congrArg Prod.snd hk2
      omega
  · exact absurd (h1.trans h2.symm) (isStep_ne he')

/-- Two distinct unit steps have segments meeting only in common endpoints. -/
theorem unitStep_seg_inter_subset {e e' : (ℤ × ℤ) × (ℤ × ℤ)} (he : IsUnitStep e)
    (he' : IsUnitStep e') (hne : e ≠ e') :
    stepSeg e ∩ stepSeg e' ⊆ ({lpt e.1, lpt e.2} : Set ℂ) ∩ {lpt e'.1, lpt e'.2} := by
  have hadj : IsUnitAdj e.1 e.2 := isUnitAdj_of_isUnitStep he
  have hadj' : IsUnitAdj e'.1 e'.2 := isUnitAdj_of_isUnitStep he'
  intro z hz
  obtain ⟨hz1, hz2⟩ := hz
  rw [stepSeg_eq_segment he] at hz1
  rw [stepSeg_eq_segment he'] at hz2
  have hz1' : z ∈ adjSeg e.1 e.2 := hz1
  have hz2' : z ∈ adjSeg e'.1 e'.2 := hz2
  by_cases hlat : ∃ r : ℤ × ℤ, z = lpt r
  · obtain ⟨r, rfl⟩ := hlat
    have k1 : r = e.1 ∨ r = e.2 := eq_lpt_of_mem_adjSeg hadj hz1' rfl
    have k2 : r = e'.1 ∨ r = e'.2 := eq_lpt_of_mem_adjSeg hadj' hz2' rfl
    refine ⟨?_, ?_⟩
    · simpa using k1
    · simpa using k2
  · push_neg at hlat
    have hseg : adjSeg e.1 e.2 = adjSeg e'.1 e'.2 :=
      adjSeg_eq_of_mem_of_not_lattice hadj hadj' hz1' hz2' hlat
    exfalso
    have hmem1 : e.1 ∈ ({e'.1, e'.2} : Finset (ℤ × ℤ)) := by
      have hz' : lpt e.1 ∈ adjSeg e'.1 e'.2 := by
        rw [← hseg]
        exact left_mem_segment ℝ _ _
      simpa using eq_lpt_of_mem_adjSeg hadj' hz' rfl
    have hmem2 : e.2 ∈ ({e'.1, e'.2} : Finset (ℤ × ℤ)) := by
      have hz' : lpt e.2 ∈ adjSeg e'.1 e'.2 := by
        rw [← hseg]
        exact right_mem_segment ℝ _ _
      simpa using eq_lpt_of_mem_adjSeg hadj' hz' rfl
    have hsub : ({e.1, e.2} : Finset (ℤ × ℤ)) ⊆ {e'.1, e'.2} := by
      intro x hx
      rcases Finset.mem_insert.mp hx with hx | hx
      · rw [hx]; exact hmem1
      · rw [Finset.mem_singleton.mp hx]; exact hmem2
    have hcard : ({e'.1, e'.2} : Finset (ℤ × ℤ)).card ≤ ({e.1, e.2} : Finset (ℤ × ℤ)).card := by
      rw [Finset.card_pair (isStep_ne he'), Finset.card_pair (isStep_ne he)]
    have heq : ({e.1, e.2} : Finset (ℤ × ℤ)) = {e'.1, e'.2} :=
      Finset.eq_of_subset_of_card_le hsub hcard
    exact hne (eq_of_unitStep_same_ends he he' heq)

end

end Work.HornSC.CellBoundaryJordan.BO

import Mathlib
import Submission.Work.OROneRel.Basic

namespace Work.OROneRel

universe u

/-- The set of generators occurring in a relator is finite: it is the image under `Prod.fst` of the
(finite) set of letters of the reduced word `FreeGroup.toWord r`. -/
theorem finite_relatorLetters {α : Type u} (r : FreeGroup α) :
    (Work.OROneRel.relatorLetters r).Finite := by
  classical
  refine Set.Finite.subset
    ((Finset.finite_toSet (FreeGroup.toWord r).toFinset).image Prod.fst) ?_
  intro a ha
  simp only [relatorLetters, Set.mem_ofPred_eq] at ha
  obtain ⟨b, hb⟩ := ha
  exact ⟨(a, b), by simpa using (List.mem_toFinset.mpr hb), rfl⟩

end Work.OROneRel

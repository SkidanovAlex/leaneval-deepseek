import Mathlib
import Submission.Work.ORReductions.Basic

namespace Work.ORReductions.FreeGroupGens

/-- The generators occurring in a free-group word form a finite set: they are all first
coordinates of the (finite) list of letters of `x.toWord`. -/
theorem freeGens_finite {α : Type*} (x : FreeGroup α) : (FreeGroup.gens x).Finite := by
  classical
  refine (Finset.finite_toSet (x.toWord.toFinset.image Prod.fst)).subset ?_
  intro a ha
  simp only [FreeGroup.gens, Set.mem_ofPred_eq] at ha
  rcases ha with h | h
  · have hm : (a, true) ∈ x.toWord := List.singleton_sublist.mp h
    exact Finset.mem_image.mpr ⟨(a, true), by simpa using hm, rfl⟩
  · have hm : (a, false) ∈ x.toWord := List.singleton_sublist.mp h
    exact Finset.mem_image.mpr ⟨(a, false), by simpa using hm, rfl⟩

end Work.ORReductions.FreeGroupGens

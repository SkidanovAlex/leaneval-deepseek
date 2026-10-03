import Mathlib
import Submission.Work.ORReductions.Basic

namespace Work.ORReductions.FreeGroupGens

/-- In the inverse (reversed, letter-flipped) word, the *single-letter* sublist condition
is the condition for the flipped letter in the original word. -/
lemma singleton_sublist_invRev {α : Type*} (a : α) (b : Bool) (w : List (α × Bool)) :
    List.Sublist [(a, b)] (FreeGroup.invRev w) ↔ List.Sublist [(a, Bool.not b)] w := by
  simp only [FreeGroup.invRev, List.singleton_sublist, List.mem_reverse, List.mem_map]
  constructor
  · rintro ⟨p, hp, hpe⟩
    have h1 : p.1 = a := (Prod.ext_iff.mp hpe).1
    have h2 : Bool.not p.2 = b := (Prod.ext_iff.mp hpe).2
    have h3 : p.2 = Bool.not b := by rw [← h2, Bool.not_not]
    have hp' : p = (a, Bool.not b) := Prod.ext h1 h3
    rw [hp'] at hp
    exact hp
  · intro h
    exact ⟨(a, Bool.not b), h, by simp [Bool.not_not]⟩

theorem freeGens_inv {α : Type*} (x : FreeGroup α) : FreeGroup.gens x⁻¹ = FreeGroup.gens x := by
  classical
  ext a
  simp only [FreeGroup.gens, Set.mem_ofPred_eq]
  rw [FreeGroup.toWord_inv]
  constructor
  · rintro (h | h)
    · exact Or.inr ((singleton_sublist_invRev a true x.toWord).mp h)
    · exact Or.inl ((singleton_sublist_invRev a false x.toWord).mp h)
  · rintro (h | h)
    · exact Or.inr ((singleton_sublist_invRev a false x.toWord).mpr h)
    · exact Or.inl ((singleton_sublist_invRev a true x.toWord).mpr h)

end Work.ORReductions.FreeGroupGens

import Mathlib
import Submission.Work.ORHughesFree.StarRegular

namespace Work.ORHughesFree.StarRegular

theorem starSubringClosure_mono {U : Type*} [Ring U] [StarRing U] {s t : Set U} (h : s ⊆ t) :
    (starSubringClosure s : Set U) ⊆ (starSubringClosure t : Set U) := by
  apply Subring.closure_mono
  intro x hx
  rcases hx with hx | ⟨y, hy, rfl⟩
  · exact Or.inl (h hx)
  · exact Or.inr ⟨y, h hy, rfl⟩

end Work.ORHughesFree.StarRegular

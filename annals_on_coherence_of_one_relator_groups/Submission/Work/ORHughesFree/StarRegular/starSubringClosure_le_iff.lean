import Mathlib
import Submission.Work.ORHughesFree.StarRegular

namespace Work.ORHughesFree.StarRegular

theorem starSubringClosure_le_iff {U : Type*} [Ring U] [StarRing U] {s : Set U}
    {T : StarSubring U} :
    (starSubringClosure s : Set U) ⊆ (T : Set U) ↔ s ⊆ (T : Set U) := by
  constructor
  · intro h
    exact (Work.ORHughesFree.subset_starSubringClosure s).trans h
  · exact fun h => Work.ORHughesFree.starSubringClosure_le h

end Work.ORHughesFree.StarRegular

import Mathlib
import Submission.Work.ORHughesFree.StarRegular

namespace Work.StarRegular

theorem map_starSubringClosure_subset {U : Type*} [Ring U] [StarRing U]
    (f : U →+* U) (hf : ∀ a : U, f (star a) = star (f a)) {g : Set U}
    (hg : ∀ x ∈ g, f x ∈ (Work.ORHughesFree.starSubringClosure g : Set U)) :
    ∀ x ∈ (Work.ORHughesFree.starSubringClosure g : Set U),
      f x ∈ (Work.ORHughesFree.starSubringClosure g : Set U) := by
  intro x hx
  let S : Subring U :=
    { carrier := {y : U | f y ∈ (Work.ORHughesFree.starSubringClosure g : Set U)}
      zero_mem' := by
        show f 0 ∈ (Work.ORHughesFree.starSubringClosure g : Set U)
        rw [map_zero]
        exact Subring.zero_mem _
      one_mem' := by
        show f 1 ∈ (Work.ORHughesFree.starSubringClosure g : Set U)
        rw [map_one]
        exact Subring.one_mem _
      add_mem' := by
        intro a b ha hb
        show f (a + b) ∈ (Work.ORHughesFree.starSubringClosure g : Set U)
        rw [map_add]
        exact Subring.add_mem _ ha hb
      neg_mem' := by
        intro a ha
        show f (-a) ∈ (Work.ORHughesFree.starSubringClosure g : Set U)
        rw [map_neg]
        exact Subring.neg_mem _ ha
      mul_mem' := by
        intro a b ha hb
        show f (a * b) ∈ (Work.ORHughesFree.starSubringClosure g : Set U)
        rw [map_mul]
        exact Subring.mul_mem _ ha hb }
  have hsub : ((g ∪ star '' g : Set U)) ⊆ (S : Set U) := by
    rintro y (hy | ⟨z, hz, rfl⟩)
    · exact hg y hy
    · show f (star z) ∈ (Work.ORHughesFree.starSubringClosure g : Set U)
      rw [hf z]
      exact (Work.ORHughesFree.starSubringClosure g).star_mem' (hg z hz)
  exact Subring.closure_le.mpr hsub hx

end Work.StarRegular

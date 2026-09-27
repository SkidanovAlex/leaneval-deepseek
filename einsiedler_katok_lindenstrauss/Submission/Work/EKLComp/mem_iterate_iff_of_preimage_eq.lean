import Mathlib

namespace Work.EKLComp

theorem mem_iterate_iff_of_preimage_eq {X : Type*} (T : X → X) (U : Set X)
    (hinv : T ⁻¹' U = U) (k : ℕ) (x : X) : T^[k] x ∈ U ↔ x ∈ U := by
  have h : ∀ y, T y ∈ U ↔ y ∈ U := fun y => Set.ext_iff.mp hinv y
  induction k with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (h _).trans ih

end Work.EKLComp

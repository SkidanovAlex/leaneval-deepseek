import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Commons.Data.Finset

lemma sum_over_image_fibers {α β : Type*} [DecidableEq β] (L : Finset α) (f : α → β)
    (g : β → ℕ) : (∑ i ∈ L, g (f i)) =
      (∑ o ∈ L.image f, g o * (L.filter (fun i => f i = o)).card) := by
  classical
  calc
    (∑ i ∈ L, g (f i)) = ∑ o ∈ L.image f, ∑ i ∈ L with f i = o, g o := by
      symm
      exact Finset.sum_fiberwise_of_maps_to' (s := L) (t := L.image f) (g := f) (f := g)
        (by intro i hi; exact Finset.mem_image_of_mem f hi)
    _ = ∑ o ∈ L.image f, g o * (L.filter (fun i => f i = o)).card := by
      apply Finset.sum_congr rfl
      intro o ho
      rw [Finset.sum_const_nat (s := L.filter (fun i => f i = o)) (f := fun _ : α => g o) (m := g o)
        (by intro i hi; rfl)]
      rw [Nat.mul_comm]

end Commons.Data.Finset
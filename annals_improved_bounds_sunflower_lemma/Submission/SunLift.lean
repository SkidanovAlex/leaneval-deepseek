import Mathlib
import Submission.SunBasic
import Submission.SunExtras

/-!
# Forward lifting of sunflowers (adding a set disjoint from all members)
-/
open Finset

namespace Submission.Sun

variable {α : Type*} [DecidableEq α]

/-- union distributes over intersection (in a distributive lattice). -/
private lemma inter_distrib_union_left (T A B : Finset α) :
    (T ∪ A) ∩ (T ∪ B) = T ∪ (A ∩ B) := by
  ext x
  simp only [mem_inter, mem_union]
  tauto

/-- If `S` is an `r`-sunflower and `T` is disjoint from every member, then
`T ∪ A` over `A ∈ S` is an `r`-sunflower (size is preserved by disjointness). -/
lemma IsSunflower_lift_disj {S : Finset (Finset α)} {r : ℕ} (T : Finset α)
    (hT : ∀ A ∈ S, Disjoint A T) (hS : IsSunflower S r) :
    IsSunflower (S.image (fun A : Finset α => T ∪ A)) r := by
  constructor
  · rw [image_union_inj T hT, hS.1]
  · intro A' hA' B' hB' hAB'
    rcases Finset.mem_image.mp hA' with ⟨A, hAS, rfl⟩
    rcases Finset.mem_image.mp hB' with ⟨B, hBS, rfl⟩
    have hAneB : A ≠ B := by
      intro hAB
      apply hAB'
      simp [hAB]
    have hSnon : S.Nonempty := ⟨A, hAS⟩
    have hinter : interAll (S.image (fun C : Finset α => T ∪ C)) = T ∪ interAll S :=
      interAll_union_image T S hSnon
    calc
      (T ∪ A) ∩ (T ∪ B) = T ∪ (A ∩ B) := inter_distrib_union_left T A B
      _ = T ∪ interAll S := by rw [hS.2 A hAS B hBS hAneB]
      _ = interAll (S.image (fun C : Finset α => T ∪ C)) := hinter.symm

/-- union with T distributes over the common intersection. -/
lemma interAll_lift {S : Finset (Finset α)} (T : Finset α) (hS : S.Nonempty) :
    interAll (S.image (fun A : Finset α => T ∪ A)) = T ∪ interAll S := by
  exact interAll_union_image T S hS

end Submission.Sun

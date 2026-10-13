import Mathlib
import Submission.Work.WilE5.Basic

namespace Work.WilE5.Cells

/-- General combinatorial form of `flatMapProps`: `g` is any "carrier" of a list element to a
set, and the three assertions (`Pairwise` disjointness of the flattened list, the union
identity, and the length bound) are proved for arbitrary types.  Only the disjointness part
uses `l.Nodup` (to know that distinct positions of `l` carry distinct keys, so that `hcross`
applies). -/
theorem flatMapPropsGeneral {α β γ : Type*} (l : List α) (f : α → List β) (g : β → Set γ)
    (hl : l.Nodup)
    (hpair : ∀ a ∈ l, (f a).Pairwise (fun S T => Disjoint (g S) (g T)))
    (hcross : ∀ a ∈ l, ∀ b ∈ l, a ≠ b → ∀ S ∈ f a, ∀ T ∈ f b, Disjoint (g S) (g T)) :
    (l.flatMap f).Pairwise (fun S T => Disjoint (g S) (g T)) ∧
    (⋃ S ∈ l.flatMap f, g S) = (⋃ a ∈ l, ⋃ S ∈ f a, g S) ∧
    (∀ B : ℕ, (∀ a ∈ l, (f a).length ≤ B) → (l.flatMap f).length ≤ l.length * B) := by
  refine ⟨?_, ?_, ?_⟩
  · -- Pairwise disjointness: within blocks from `hpair`, across distinct blocks from `hcross`.
    rw [List.pairwise_flatMap]
    refine ⟨hpair, ?_⟩
    refine List.Pairwise.imp_of_mem ?_ (List.nodup_iff_pairwise_ne.mp hl)
    intro a b ha hb hne
    exact hcross a ha b hb hne
  · -- The union of the flattened list is the iterated union over the blocks.
    ext x
    simp only [Set.mem_iUnion, List.mem_flatMap]
    tauto
  · -- Length bound.
    intro B hB
    rw [List.length_flatMap]
    calc (l.map (fun a => (f a).length)).sum
        ≤ (l.map (fun _ => B)).sum := List.sum_le_sum (fun a ha => hB a ha)
      _ = l.length * B := by simp

theorem flatMapProps {α : Type*} {p q : ℕ} (l : List α) (f : α → List (WilkiesDesign.E.Stratum p q))
    (hl : l.Nodup)
    (hpair : ∀ a ∈ l, (f a).Pairwise (fun S T => Disjoint S.X.set T.X.set))
    (hcross : ∀ a ∈ l, ∀ b ∈ l, a ≠ b → ∀ S ∈ f a, ∀ T ∈ f b, Disjoint S.X.set T.X.set) :
    (l.flatMap f).Pairwise (fun S T => Disjoint S.X.set T.X.set) ∧
    (⋃ S ∈ l.flatMap f, S.X.set) = (⋃ a ∈ l, ⋃ S ∈ f a, S.X.set) ∧
    (∀ B : ℕ, (∀ a ∈ l, (f a).length ≤ B) → (l.flatMap f).length ≤ l.length * B) :=
  flatMapPropsGeneral l f (fun S => S.X.set) hl hpair hcross

end Work.WilE5.Cells

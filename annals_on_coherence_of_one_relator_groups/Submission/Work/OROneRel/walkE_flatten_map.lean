import Mathlib
import Submission.Work.OROneRel.winBasisDefs
import Submission.Work.OROneRel.decor_pow_flatMap
import Submission.Work.OROneRel.coedgeBase

namespace Work.OROneRel

/-- **The decoration of a concatenation of vanishing-weight blocks.**  If every block `f p` of a
list `l` has vanishing total weight `lsig c (f p) = 0`, then the decoration of the concatenation of
the blocks is the concatenation of the decorations of the blocks (each block starting afresh at
level `0`).  This is the `decor`-analogue of `decor_flatten_replicate`, with an arbitrary list of
blocks in place of a constant repetition. -/
theorem decor_flatten_map_eq {α β : Type*} (c : α → ℤ) (f : β → List (α × Bool)) :
    ∀ (l : List β), (∀ p ∈ l, lsig c (f p) = 0) →
      decor c 0 ((l.map f).flatten) =
        (l.map (fun p => decor c 0 (f p))).flatten
  | [], _ => rfl
  | p :: l, h => by
      have hp : lsig c (f p) = 0 := h p (List.mem_cons_self ..)
      have hl : ∀ q ∈ l, lsig c (f q) = 0 := fun q hq => h q (List.mem_cons_of_mem _ hq)
      simp only [List.map_cons, List.flatten_cons]
      rw [decor_append, hp, add_zero, decor_flatten_map_eq c f l hl]

theorem walkE_flatten_map {α : Type*} {β : Type*} (c : α → ℤ) (lo hi : ℤ) (l : List (β × Bool))
    (f : β × Bool → List (α × Bool))
    (hwalk : ∀ p ∈ l, ∀ q ∈ decor c 0 (f p), coverEdge q ∈ winE c lo hi)
    (hlsig : ∀ p ∈ l, lsig c (f p) = 0) :
    ∀ q ∈ decor c 0 ((l.map f).flatten), coverEdge q ∈ winE c lo hi := by
  intro q hq
  rw [decor_flatten_map_eq c f l hlsig] at hq
  obtain ⟨M, hM, hqM⟩ := List.mem_flatten.mp hq
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hM
  exact hwalk p hp q hqM

end Work.OROneRel

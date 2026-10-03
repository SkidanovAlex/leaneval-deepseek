/-
# The maximum and the minimum of a path

`pathMax ω p` (resp. `pathMin ω p`) is the maximum (resp. minimum) of the codes of the arrows of
`p`, as an element of `WithBot α` (resp. `WithTop α`).

This file records the elementary facts about these maxima and minima that the small-model
construction needs: the maximum of a nonempty list of codes is one of them (so it is a code of one
of the arrows of the path), and it dominates every element of the list.
-/
import Mathlib
import Submission.Work.ORLocInd.Howie.Relator

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.Case1

open Quiver

namespace MaxMem

variable {α : Type*} [LinearOrder α]

theorem le_foldr_max {l : List (WithBot α)} {x : WithBot α} (hx : x ∈ l) :
    x ≤ l.foldr max ⊥ := by
  induction l with
  | nil => simp at hx
  | cons y t ih =>
      show x ≤ max y (t.foldr max ⊥)
      rcases List.mem_cons.mp hx with rfl | hx
      · exact le_max_left _ _
      · exact le_trans (ih hx) (le_max_right _ _)

theorem foldr_max_mem : ∀ {l : List (WithBot α)}, l ≠ [] → l.foldr max ⊥ ∈ l := by
  intro l
  induction l with
  | nil => intro h; exact absurd rfl h
  | cons y t ih =>
      intro _
      show max y (t.foldr max ⊥) ∈ y :: t
      rcases eq_or_ne t [] with rfl | ht
      · show max y ⊥ ∈ [y]
        rw [le_antisymm (max_le le_rfl (bot_le : (⊥ : WithBot α) ≤ y)) (le_max_left _ _)]
        exact List.mem_cons.mpr (Or.inl rfl)
      · rcases max_choice y (t.foldr max ⊥) with h | h
        · rw [h]; exact List.mem_cons.mpr (Or.inl rfl)
        · rw [h]; exact List.mem_cons.mpr (Or.inr (ih ht))

theorem foldr_min_le {l : List (WithTop α)} {x : WithTop α} (hx : x ∈ l) :
    l.foldr min ⊤ ≤ x := by
  induction l with
  | nil => simp at hx
  | cons y t ih =>
      show min y (t.foldr min ⊤) ≤ x
      rcases List.mem_cons.mp hx with rfl | hx
      · exact min_le_left _ _
      · exact le_trans (min_le_right _ _) (ih hx)

theorem foldr_min_mem : ∀ {l : List (WithTop α)}, l ≠ [] → l.foldr min ⊤ ∈ l := by
  intro l
  induction l with
  | nil => intro h; exact absurd rfl h
  | cons y t ih =>
      intro _
      show min y (t.foldr min ⊤) ∈ y :: t
      rcases eq_or_ne t [] with rfl | ht
      · show min y ⊤ ∈ [y]
        rw [← le_antisymm (le_min le_rfl (le_top : y ≤ (⊤ : WithTop α))) (min_le_left _ _)]
        exact List.mem_cons.mpr (Or.inl rfl)
      · rcases min_choice y (t.foldr min ⊤) with h | h
        · rw [h]; exact List.mem_cons.mpr (Or.inl rfl)
        · rw [h]; exact List.mem_cons.mpr (Or.inr (ih ht))

end MaxMem

section Paths

variable {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V] {α : Type u} [LinearOrder α]

/-- The maximum of a path is the code of one of its arrows. -/
theorem exists_pathMax_eq (ω : Quiver.Total V → α) {a b : V} {p : Quiver.Path a b}
    (hp : p.arrowList ≠ []) : ∃ g ∈ p.arrowList, Work.ORLocInd.Howie.pathMax ω p = (ω g : WithBot α) := by
  have hne : p.arrowList.map (fun e => (ω e : WithBot α)) ≠ [] := by simpa using hp
  have hmem := MaxMem.foldr_max_mem (l := p.arrowList.map (fun e => (ω e : WithBot α))) hne
  obtain ⟨g, hg, hgeq⟩ := List.mem_map.mp hmem
  exact ⟨g, hg, hgeq.symm⟩

/-- The minimum of a path is the code of one of its arrows. -/
theorem exists_pathMin_eq (ω : Quiver.Total V → α) {a b : V} {p : Quiver.Path a b}
    (hp : p.arrowList ≠ []) : ∃ g ∈ p.arrowList, Work.ORLocInd.Howie.pathMin ω p = (ω g : WithTop α) := by
  have hne : p.arrowList.map (fun e => (ω e : WithTop α)) ≠ [] := by simpa using hp
  have hmem := MaxMem.foldr_min_mem (l := p.arrowList.map (fun e => (ω e : WithTop α))) hne
  obtain ⟨g, hg, hgeq⟩ := List.mem_map.mp hmem
  exact ⟨g, hg, hgeq.symm⟩

end Paths

end Work.Case1

import Mathlib
import Submission.Work.OROneRel.Basic

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- Membership in `FreeGroup.invRev L` is membership of the flipped letter in `L`. -/
lemma mem_invRev {L : List (α × Bool)} {p : α × Bool} :
    p ∈ FreeGroup.invRev L ↔ (p.1, !p.2) ∈ L := by
  simp only [FreeGroup.invRev, List.mem_reverse, List.mem_map]
  constructor
  · rintro ⟨q, hq, hqe⟩
    have : (p.1, !p.2) = q := by rw [← hqe]; simp
    rw [this]; exact hq
  · intro h
    exact ⟨(p.1, !p.2), h, by simp⟩

/-- The set of elements of `FreeGroup α` all of whose letters lie in `T` is a subgroup. -/
def lettersSubgroup (T : Set α) : Subgroup (FreeGroup α) where
  carrier := {x | relatorLetters x ⊆ T}
  mul_mem' := by
    classical
    intro x y hx hy a ha
    simp only [relatorLetters] at ha
    obtain ⟨b, hb⟩ := ha
    rw [FreeGroup.toWord_mul] at hb
    rcases List.mem_append.mp (List.Sublist.mem hb (FreeGroup.Red.sublist FreeGroup.reduce.red)) with h | h
    · exact hx ⟨b, h⟩
    · exact hy ⟨b, h⟩
  one_mem' := by
    classical
    intro a ha
    simp only [relatorLetters] at ha
    obtain ⟨b, hb⟩ := ha
    rw [FreeGroup.toWord_one] at hb
    simp at hb
  inv_mem' := by
    classical
    intro x hx a ha
    simp only [relatorLetters] at ha
    obtain ⟨b, hb⟩ := ha
    rw [FreeGroup.toWord_inv] at hb
    exact hx ⟨!b, mem_invRev.mp hb⟩

lemma of_mem_lettersSubgroup {T : Set α} {a : α} (ha : a ∈ T) :
    FreeGroup.of a ∈ lettersSubgroup T := by
  classical
  intro a' ha'
  simp only [relatorLetters] at ha'
  obtain ⟨b, hb⟩ := ha'
  rw [FreeGroup.toWord_of] at hb
  simp only [List.mem_singleton, Prod.mk.injEq] at hb
  rw [hb.1]
  exact ha

lemma closure_le_lettersSubgroup (T : Set α) :
    Subgroup.closure (FreeGroup.of '' T) ≤ lettersSubgroup T :=
  (Subgroup.closure_le (lettersSubgroup T)).mpr fun x hx => by
    obtain ⟨a, ha, rfl⟩ := hx
    exact of_mem_lettersSubgroup ha

lemma mk_mem_closure {T : Set α} {L : List (α × Bool)}
    (h : ∀ a b, (a, b) ∈ L → a ∈ T) :
    FreeGroup.mk L ∈ Subgroup.closure (FreeGroup.of '' T) := by
  have key : FreeGroup.mk L =
      List.prod (L.map fun p => cond p.2 (FreeGroup.of p.1) (FreeGroup.of p.1)⁻¹) := by
    have := FreeGroup.lift_mk (f := (FreeGroup.of : α → FreeGroup α)) (L := L)
    rw [FreeGroup.lift_of_eq_id] at this
    simpa using this
  rw [key]
  apply list_prod_mem
  intro y hy
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hy
  obtain ⟨a, b⟩ := p
  have hmem : FreeGroup.of a ∈ Subgroup.closure (FreeGroup.of '' T) :=
    Subgroup.subset_closure ⟨a, h a b hp, rfl⟩
  cases b
  · simpa using Subgroup.inv_mem _ hmem
  · simpa using hmem

lemma lettersSubgroup_le_closure (T : Set α) :
    lettersSubgroup T ≤ Subgroup.closure (FreeGroup.of '' T) := by
  classical
  intro x hx
  have h : ∀ a b, (a, b) ∈ x.toWord → a ∈ T := fun a b hab => hx ⟨b, hab⟩
  have := mk_mem_closure (T := T) h
  rwa [FreeGroup.mk_toWord] at this

theorem letters_closure_iff {α : Type u} (r : FreeGroup α) (T : Set α) :
    r ∈ Subgroup.closure (FreeGroup.of '' T) ↔ Work.OROneRel.SupportedOn r T := by
  constructor
  · intro hr
    exact closure_le_lettersSubgroup T hr
  · intro hr
    exact lettersSubgroup_le_closure T hr

end Work.OROneRel

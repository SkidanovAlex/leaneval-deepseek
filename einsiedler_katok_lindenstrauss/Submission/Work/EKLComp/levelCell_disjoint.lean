import Mathlib
import Submission.Work.EKLComp.FinPartLevel

namespace Work.EKLComp

open Set

/-- Membership in a staircase cell: a point lies in `levelCell e U C m` exactly when it lies in
`U (e.symm m)` and in every `C (e.symm j)` for `j < m`. -/
lemma mem_levelCell_iff {X ι : Type*} [Fintype ι] (e : ι ≃ Fin (Fintype.card ι))
    (U C : ι → Set X) (m : Fin (Fintype.card ι)) (x : X) :
    x ∈ levelCell e U C m ↔
      x ∈ U (e.symm m) ∧ ∀ j : Fin (Fintype.card ι), j < m → x ∈ C (e.symm j) := by
  simp only [levelCell, Set.mem_inter_iff, Set.mem_iInter]
  constructor
  · rintro ⟨hU, h⟩; exact ⟨hU, fun j hj => h ⟨j, hj⟩⟩
  · rintro ⟨hU, h⟩; exact ⟨hU, fun j => h j.1 j.2⟩

/-- Membership in the residual core: `levelCore C = ⋂ i, C i`. -/
lemma mem_levelCore_iff {X ι : Type*} (C : ι → Set X) (x : X) :
    x ∈ levelCore C ↔ ∀ i, x ∈ C i :=
  Set.mem_iInter

theorem levelCell_disjoint {X ι : Type*} [Fintype ι] (e : ι ≃ Fin (Fintype.card ι))
    (U C : ι → Set X) (hUC : ∀ i, C i = (U i)ᶜ) :
    (∀ m m' : Fin (Fintype.card ι), m ≠ m' →
        Disjoint (Work.EKLComp.levelCell e U C m) (Work.EKLComp.levelCell e U C m')) ∧
    (∀ m : Fin (Fintype.card ι),
        Disjoint (Work.EKLComp.levelCell e U C m) (Work.EKLComp.levelCore C)) := by
  constructor
  · -- Two distinct cells: the larger one records the smaller cell's `U` inside its `C` part.
    intro m m' hne
    rw [Set.disjoint_left]
    intro x hx hx'
    rw [mem_levelCell_iff] at hx hx'
    rcases lt_or_gt_of_ne hne with h | h
    · have hc : x ∈ C (e.symm m) := hx'.2 m h
      rw [hUC] at hc
      exact hc hx.1
    · have hc : x ∈ C (e.symm m') := hx.2 m' h
      rw [hUC] at hc
      exact hc hx'.1
  · -- A cell lies in `U (e.symm m)`, the core lies in its complement `C (e.symm m)`.
    intro m
    rw [Set.disjoint_left]
    intro x hx hxc
    rw [mem_levelCell_iff] at hx
    rw [mem_levelCore_iff] at hxc
    have hc : x ∈ C (e.symm m) := hxc (e.symm m)
    rw [hUC] at hc
    exact hc hx.1

end Work.EKLComp

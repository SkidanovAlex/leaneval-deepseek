import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# The union of a family of sets indexed by the members of a finite set

`Work.SphHomology.finsetUnion t C` is the union `⋃ i : {i // i ∈ t}, C i.1`.  Keeping it as a single
definition (rather than writing the `Set.iUnion` out) keeps the set-terms that occur in Mayer–Vietoris
arguments syntactically small, which matters when they are compared up to definitional equality.
-/

open Set

namespace Work.SphHomology

/-- The union of a family of sets indexed by the members of a `Finset`. -/
def finsetUnion {ι : Type*} {X : Type*} (t : Finset ι) (C : ι → Set X) : Set X :=
  ⋃ j : {j // j ∈ t}, C j.1

theorem mem_finsetUnion {ι : Type*} {X : Type*} {t : Finset ι} {C : ι → Set X} {x : X} :
    x ∈ finsetUnion t C ↔ ∃ i ∈ t, x ∈ C i := by
  simp only [finsetUnion, Set.mem_iUnion, Subtype.exists, exists_prop]

theorem finsetUnion_empty {ι : Type*} {X : Type*} (C : ι → Set X) :
    finsetUnion (∅ : Finset ι) C = (∅ : Set X) := by
  refine Set.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
  obtain ⟨i, hi, -⟩ := mem_finsetUnion.mp hx
  exact Finset.notMem_empty i hi

theorem finsetUnion_cons {ι : Type*} {X : Type*} {a : ι} {t : Finset ι} (h : a ∉ t)
    (C : ι → Set X) : finsetUnion (Finset.cons a t h) C = C a ∪ finsetUnion t C := by
  ext x
  rw [mem_finsetUnion, Set.mem_union, mem_finsetUnion]
  constructor
  · rintro ⟨i, hi, hx⟩
    rcases Finset.mem_cons.mp hi with rfl | hi'
    · exact Or.inl hx
    · exact Or.inr ⟨i, hi', hx⟩
  · rintro (hx | ⟨i, hi, hx⟩)
    · exact ⟨a, Finset.mem_cons_self a t, hx⟩
    · exact ⟨i, Finset.mem_cons_of_mem hi, hx⟩

theorem finsetUnion_inter {ι : Type*} {X : Type*} (t : Finset ι) (C : ι → Set X) (D : Set X) :
    finsetUnion t C ∩ D = finsetUnion t (fun i => C i ∩ D) := by
  ext x
  rw [Set.mem_inter_iff, mem_finsetUnion, mem_finsetUnion]
  constructor
  · rintro ⟨⟨i, hi, hx⟩, hd⟩
    exact ⟨i, hi, hx, hd⟩
  · rintro ⟨i, hi, hx, hd⟩
    exact ⟨⟨i, hi, hx⟩, hd⟩

theorem isClosed_finsetUnion {ι : Type*} {X : Type*} [TopologicalSpace X] {t : Finset ι}
    {C : ι → Set X} (h : ∀ i ∈ t, IsClosed (C i)) : IsClosed (finsetUnion t C) := by
  induction t using Finset.cons_induction with
  | empty =>
      rw [finsetUnion_empty]
      exact isClosed_empty
  | cons a t ha ih =>
      rw [finsetUnion_cons ha]
      exact (h a (Finset.mem_cons_self a t)).union
        (ih fun i hi => h i (Finset.mem_cons_of_mem hi))

theorem subset_finsetUnion {ι : Type*} {X : Type*} {t : Finset ι} {C : ι → Set X} {i : ι}
    (hi : i ∈ t) : C i ⊆ finsetUnion t C :=
  fun x hx => mem_finsetUnion.mpr ⟨i, hi, hx⟩

end Work.SphHomology

import Mathlib

set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

namespace Work.EQ

/-- A total linear order on a finite type, obtained by transporting the order on `Fin n` along an
enumeration of the type.  This is the canonical-order device used to pick representatives. -/
noncomputable def finLinearOrder (α : Type*) [Fintype α] : LinearOrder α :=
  LinearOrder.lift' (Fintype.equivFin α) (Fintype.equivFin α).injective

/-- `Finset.min'` depends on the given nonemptiness proof only through proof irrelevance. -/
lemma min'_congr {β : Type*} [LinearOrder β] {s t : Finset β} (h : s = t)
    (hs : s.Nonempty) (ht : t.Nonempty) : s.min' hs = t.min' ht := by
  subst h
  exact congrArg (Finset.min' s) (Subsingleton.elim hs ht)

/-- **Deduplication of a finite set modulo an equivalence relation.**  If `Rel` is reflexive,
symmetric and transitive on `G`, there is a choice of representative `Rep` taking values in a
finset `Reps` of `G`, fixed on `Reps`, with `Rel i (Rep i)` for all `i ∈ G`, and with `Rep i = Rep j`
exactly when `Rel i j`. -/
theorem dedup_finset {α : Type*} [Fintype α] [DecidableEq α] (G : Finset α) (Rel : α → α → Prop)
    [DecidableRel Rel]
    (hrefl : ∀ i ∈ G, Rel i i)
    (hsymm : ∀ i ∈ G, ∀ j ∈ G, Rel i j → Rel j i)
    (htrans : ∀ i ∈ G, ∀ j ∈ G, ∀ k ∈ G, Rel i j → Rel j k → Rel i k) :
    ∃ Rep : α → α, ∃ Reps : Finset α,
      (∀ i ∈ G, Rep i ∈ Reps) ∧ (∀ i ∈ Reps, i ∈ G) ∧ (∀ i ∈ Reps, Rep i = i) ∧
      (∀ i ∈ G, Rel i (Rep i)) ∧
      (∀ i ∈ G, ∀ j ∈ G, Rep i = Rep j → Rel i j) ∧
      (∀ i ∈ G, ∀ j ∈ G, Rel i j → Rep i = Rep j) := by
  classical
  -- Fix a linear order on `α` and let `R i` be the class of `i` inside `G`.
  letI : LinearOrder α := finLinearOrder α
  let cls : α → Finset α := fun i => G.filter (fun j => Rel i j)
  have mem_cls : ∀ i, i ∈ G → (cls i).Nonempty :=
    fun i hi => ⟨i, Finset.mem_filter.mpr ⟨hi, hrefl i hi⟩⟩
  -- `Rep i` is the least element of the class of `i` (and `i` itself outside `G`).
  let Rep : α → α := fun i => if h : i ∈ G then (cls i).min' (mem_cls i h) else i
  have hRep : ∀ i (hi : i ∈ G), Rep i = (cls i).min' (mem_cls i hi) := by
    intro i hi
    dsimp only [Rep]
    rw [dite_eq_left hi]
  -- `Rep i` is in the class of `i`.
  have hA : ∀ i (hi : i ∈ G), Rep i ∈ G ∧ Rel i (Rep i) := by
    intro i hi
    have hmem : (cls i).min' (mem_cls i hi) ∈ cls i := Finset.min'_mem _ _
    obtain ⟨hG, hR⟩ := Finset.mem_filter.mp hmem
    rw [hRep i hi]
    exact ⟨hG, hR⟩
  -- Related elements of `G` have the same class.
  have hcls_eq : ∀ i (hi : i ∈ G) (j) (hj : j ∈ G), Rel i j → cls i = cls j := by
    intro i hi j hj hij
    ext k
    simp only [cls, Finset.mem_filter]
    constructor
    · rintro ⟨hk, hik⟩
      exact ⟨hk, htrans j hj i hi k hk (hsymm i hi j hj hij) hik⟩
    · rintro ⟨hk, hjk⟩
      exact ⟨hk, htrans i hi j hj k hk hij hjk⟩
  -- `Rep` is constant on classes.
  have hB : ∀ i (hi : i ∈ G) (j) (hj : j ∈ G), Rel i j → Rep i = Rep j := by
    intro i hi j hj hij
    rw [hRep i hi, hRep j hj]
    exact min'_congr (hcls_eq i hi j hj hij) _ _
  -- `Rep` is idempotent on `G`.
  have hC : ∀ i (hi : i ∈ G), Rep (Rep i) = Rep i := by
    intro i hi
    have hAi := hA i hi
    exact (hB i hi (Rep i) hAi.1 hAi.2).symm
  refine ⟨Rep, G.image Rep, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
  · intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    exact (hA j hj).1
  · intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    exact hC j hj
  · intro i hi
    exact (hA i hi).2
  · intro i hi j hj heq
    have hAi := hA i hi
    have hAj := hA j hj
    have hjr : Rel j (Rep i) := heq.symm ▸ hAj.2
    exact htrans i hi (Rep i) hAi.1 j hj hAi.2 (hsymm j hj (Rep i) hAi.1 hjr)
  · intro i hi j hj hij
    exact hB i hi j hj hij

end Work.EQ

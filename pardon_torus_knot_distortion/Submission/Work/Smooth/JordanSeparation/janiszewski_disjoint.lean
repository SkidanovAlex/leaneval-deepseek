import Mathlib
import Submission.Work.Smooth.JordanSeparation.componentIn_inter_componentIn

/-!
# Janiszewski's theorem for two disjoint compact plane sets

`Work.Smooth.JordanSeparation.janiszewski_disjoint`: if `A`, `B ⊆ ℂ` are compact and **disjoint**,
and `p, q ∉ A ∪ B` lie in the same connected component both of `Aᶜ` and of `Bᶜ`, then they lie in
the same connected component of `(A ∪ B)ᶜ`.

This is the plane case of the classical **Phragmén–Brouwer (Alexander) lemma**, in the form proved
in `Submission/Work/Smooth/JordanSeparation/componentIn_inter_componentIn.lean`
(`componentIn_inter_componentIn`): for disjoint compact `A`, `B` and `x ∉ A ∪ B` the intersection
`connectedComponentIn Aᶜ x ∩ connectedComponentIn Bᶜ x` is preconnected (indeed it *is* the
component of `x` in `(A ∪ B)ᶜ`).  Since that intersection is contained in `(A ∪ B)ᶜ`, it follows
that `p` and `q` lie in the same component of `(A ∪ B)ᶜ`.
-/

open Set

namespace Work.Smooth.JordanSeparation

noncomputable section

/-- **Janiszewski's theorem for two disjoint compact plane sets.** -/
theorem janiszewski_disjoint {A B : Set ℂ} (hA : IsCompact A) (hB : IsCompact B)
    (hAB : Disjoint A B) {p q : ℂ} (hp : p ∉ A ∪ B) (hq : q ∉ A ∪ B)
    (hA' : q ∈ connectedComponentIn Aᶜ p) (hB' : q ∈ connectedComponentIn Bᶜ p) :
    q ∈ connectedComponentIn (A ∪ B)ᶜ p := by
  have hpA : p ∈ Aᶜ := fun h => hp (Or.inl h)
  have hpB : p ∈ Bᶜ := fun h => hp (Or.inr h)
  have hpre : IsPreconnected (connectedComponentIn Aᶜ p ∩ connectedComponentIn Bᶜ p) :=
    componentIn_inter_componentIn hA hB hAB hpA hpB
  have hpq : q ∈ connectedComponentIn Aᶜ p ∩ connectedComponentIn Bᶜ p := ⟨hA', hB'⟩
  have hsub : connectedComponentIn Aᶜ p ∩ connectedComponentIn Bᶜ p ⊆ (A ∪ B)ᶜ := by
    rintro z ⟨hz1, hz2⟩
    rw [Set.mem_compl_iff]
    rintro (h | h)
    · exact (connectedComponentIn_subset Aᶜ p hz1) h
    · exact (connectedComponentIn_subset Bᶜ p hz2) h
  exact hpre.subset_connectedComponentIn (x := p)
    ⟨mem_connectedComponentIn hpA, mem_connectedComponentIn hpB⟩ hsub hpq

end

end Work.Smooth.JordanSeparation

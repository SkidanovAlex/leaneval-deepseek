import Mathlib
import Submission.Work.Engulf.Defs
import Submission.Work.Engulf.Basic
import Submission.Work.Engulf.Auxi.face_subset_of_subset_union
import Submission.Work.Engulf.E4alt.Api

namespace Work.Engulf.E4S

/-- **`face_subset_of_subset_iUnion`**: the two-set version `face_subset_of_subset_union`, for an
arbitrary finite family of subcomplexes.  If the simplex of a face `s` of the finite complex `Γ`
is covered by `⋃ i ∈ u, A i` with every `A i` a subcomplex of `Γ`, then `PL.simp s` lies in one
single `A i`.  Proof by induction on the finite set `u`: split off one index `a`, apply the
two-set lemma to `A a` and `⋃ i ∈ u', A i` (a subcomplex by `isSubSp_biUnion`), and recurse. -/
theorem face_subset_of_subset_iUnion {N : ℕ} {Γ : PL.Cx N} (hfin : Γ.faces.Finite)
    {ι : Type*} (u : Finset ι) (A : ι → Set (PL.E N))
    (hA : ∀ i ∈ u, Work.Engulf.IsSubSp Γ (A i))
    {s : Finset (PL.E N)} (hs : s ∈ Γ.faces) (h : PL.simp s ⊆ ⋃ i ∈ u, A i) :
    ∃ i ∈ u, PL.simp s ⊆ A i := by
  classical
  revert hA h
  induction u using Finset.induction_on with
  | empty =>
      intro hA h
      obtain ⟨v, hv⟩ := Γ.nonempty_of_mem_faces hs
      exact absurd (h (Work.Engulf.subset_simp hv)) (by simp)
  | insert a u' ha ih =>
      intro hA h
      have hAa : Work.Engulf.IsSubSp Γ (A a) := hA a (Finset.mem_insert_self a u')
      have hA' : ∀ i ∈ u', Work.Engulf.IsSubSp Γ (A i) :=
        fun i hi => hA i (Finset.mem_insert_of_mem hi)
      have hU : Work.Engulf.IsSubSp Γ (⋃ i ∈ u', A i) :=
        Work.Engulf.Alt.isSubSp_biUnion u' A hA'
      have hsplit : PL.simp s ⊆ A a ∪ ⋃ i ∈ u', A i := by
        intro x hx
        have hx' : x ∈ ⋃ i ∈ insert a u', A i := h hx
        obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx'
        rw [Finset.mem_insert] at hi
        rcases hi with rfl | hiu
        · exact Set.mem_union_left _ hxi
        · exact Set.mem_union_right _ (Set.mem_iUnion₂.mpr ⟨i, hiu, hxi⟩)
      rcases Work.Engulf.Aux.face_subset_of_subset_union hfin hAa hU hs hsplit with h1 | h1
      · exact ⟨a, Finset.mem_insert_self a u', h1⟩
      · obtain ⟨i, hi, hsub⟩ := ih hA' h1
        exact ⟨i, Finset.mem_insert_of_mem hi, hsub⟩

end Work.Engulf.E4S

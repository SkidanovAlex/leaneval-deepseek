import Mathlib
import Submission.Work.PL.Subdiv.SdBasic

/-!
# A union of faces of `K` is a union of faces of the `r`-fold subdivision

If `T` is a finite set of faces of `K`, then the union of their simplices is a union of
faces of `sdIter r K hK`.  The helper lemma `sdIter_biUnion_simp` records this, and
`union_of_faces_sdIter` derives the version where the set is presented only by the pointwise
condition `hS'` (every point of `S` lies in a face of `K` whose simplex is contained in `S`).
-/

namespace Work.PL.Subdiv.Util

open Set

theorem sdIter_biUnion_simp {N : ℕ} (r : ℕ) (K : PL.Cx N) (hK : K.faces.Finite)
    (T : Finset (Finset (PL.E N))) (hT : ∀ s ∈ T, s ∈ K.faces) :
    ∃ T' : Finset (Finset (PL.E N)),
      (∀ t ∈ T', t ∈ (Work.PL.Subdiv.sdIter r K hK).faces) ∧
      ⋃ s ∈ T, PL.simp s = ⋃ t ∈ T', PL.simp t := by
  induction r with
  | zero => exact ⟨T, by simpa using hT, rfl⟩
  | succ n ih =>
      obtain ⟨T₁, hT₁, hunion₁⟩ := ih
      obtain ⟨T₂, hT₂, hunion₂⟩ :=
        Work.PL.Subdiv.biUnion_simp_sd (K := Work.PL.Subdiv.sdIter n K hK)
          (Work.PL.Subdiv.sdIter_faces_finite n K hK) T₁ hT₁
      exact ⟨T₂, by rw [Work.PL.Subdiv.sdIter_succ]; exact hT₂, by rw [hunion₁, hunion₂]⟩

theorem union_of_faces_sdIter {N : ℕ} {K : PL.Cx N} {S : Set (PL.E N)}
    (hS : S ⊆ K.space) (hS' : ∀ x ∈ S, ∃ s ∈ K.faces, x ∈ PL.simp s ∧ PL.simp s ⊆ S)
    (r : ℕ) (hK : K.faces.Finite) :
    ∃ T' : Finset (Finset (PL.E N)), (∀ t ∈ T', t ∈ (Work.PL.Subdiv.sdIter r K hK).faces) ∧
      S = ⋃ t ∈ T', PL.simp t := by
  classical
  set T : Finset (Finset (PL.E N)) := hK.toFinset.filter (fun s => PL.simp s ⊆ S) with hT
  have hTfac : ∀ s ∈ T, s ∈ K.faces ∧ PL.simp s ⊆ S := fun s hs => by
    obtain ⟨hsmem, hsS⟩ := Finset.mem_filter.mp hs
    exact ⟨(Set.Finite.mem_toFinset hK).mp hsmem, hsS⟩
  have hTmem : ∀ s ∈ T, s ∈ K.faces := fun s hs => (hTfac s hs).1
  have hUnionS : ⋃ s ∈ T, PL.simp s = S := by
    refine le_antisymm ?_ ?_
    · intro x hx
      obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.mp hx
      exact (hTfac s hs).2 hxs
    · intro x hxS
      obtain ⟨s, hs, hxs, hsS⟩ := hS' x hxS
      exact mem_iUnion₂.mpr
        ⟨s, Finset.mem_filter.mpr ⟨(Set.Finite.mem_toFinset hK).mpr hs, hsS⟩, hxs⟩
  obtain ⟨T', hT'faces, hT'union⟩ := sdIter_biUnion_simp r K hK T hTmem
  exact ⟨T', hT'faces, by rw [← hUnionS, hT'union]⟩

end Work.PL.Subdiv.Util

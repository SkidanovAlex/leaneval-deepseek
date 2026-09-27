import Mathlib
import Submission.Work.Engulf.Basic
import Submission.Work.Engulf.Auxi.simplex_cover

namespace Work.Engulf.Aux

/-- **`face_subset_of_subset_union`** (Hx1e of `Submission/Work/NOTES_LEAD_poincare_E1fix.md` §1): a face of a finite complex whose simplex lies in the union of two subcomplex sets lies in one of them.  Proof: every `x ∈ PL.simp s` lies in some face `t ⊆ A` or `t ⊆ B`; `PL.simp s ∩ PL.simp t = PL.simp (s ∩ t)` (`PL.simp_inter`), so `PL.simp s` is covered by finitely many `PL.simp (s ∩ t)` with `s ∩ t ⊆ s`, and `Work.Engulf.Aux.simplex_cover` gives `s = s ∩ t`, i.e. `s ⊆ t`. -/
theorem face_subset_of_subset_union {N : ℕ} {Γ : PL.Cx N} (hfin : Γ.faces.Finite)
    {A B : Set (PL.E N)} (hA : Work.Engulf.IsSubSp Γ A) (hB : Work.Engulf.IsSubSp Γ B)
    {s : Finset (PL.E N)} (hs : s ∈ Γ.faces) (h : PL.simp s ⊆ A ∪ B) :
    PL.simp s ⊆ A ∨ PL.simp s ⊆ B := by
  classical
  -- Decompose the two subcomplexes as unions of closed faces.
  obtain ⟨TA, hTA, hAeq⟩ := (Work.Engulf.isSubSp_iff Γ A).1 hA
  obtain ⟨TB, hTB, hBeq⟩ := (Work.Engulf.isSubSp_iff Γ B).1 hB
  -- The faces occurring in either decomposition, as a finset (finiteness of `Γ.faces`).
  have hTfin : (TA ∪ TB).Finite := hfin.subset (Set.union_subset hTA hTB)
  set T : Finset (Finset (PL.E N)) := hTfin.toFinset with hTdef
  have hTmem : ∀ t, t ∈ T ↔ t ∈ TA ∪ TB := by
    intro t; rw [hTdef]; exact Set.Finite.mem_toFinset hTfin
  have hTface : ∀ t ∈ T, t ∈ Γ.faces := by
    intro t ht
    rcases (hTmem t).1 ht with h1 | h1
    · exact hTA h1
    · exact hTB h1
  -- `PL.simp s` is covered by the simplices of the faces in `T`.
  have hcov : PL.simp s ⊆ ⋃ t ∈ T, PL.simp t := by
    intro x hx
    have hxAB : x ∈ A ∪ B := h hx
    rw [hAeq, hBeq] at hxAB
    rw [Set.mem_iUnion₂]
    rcases hxAB with hxA | hxB
    · obtain ⟨t, htTA, hxt⟩ := Set.mem_iUnion₂.1 hxA
      exact ⟨t, (hTmem t).2 (Or.inl htTA), hxt⟩
    · obtain ⟨t, htTB, hxt⟩ := Set.mem_iUnion₂.1 hxB
      exact ⟨t, (hTmem t).2 (Or.inr htTB), hxt⟩
  -- Replace each covering face `t` by its subface `s ∩ t ⊆ s`.
  set T' : Finset (Finset (PL.E N)) := T.image (fun t => s ∩ t) with hT'def
  have hsub' : ∀ u ∈ T', u ⊆ s := by
    intro u hu
    rw [hT'def, Finset.mem_image] at hu
    obtain ⟨t, _, rfl⟩ := hu
    exact Finset.inter_subset_left
  have hcov' : PL.simp s ⊆ ⋃ u ∈ T', PL.simp u := by
    intro x hx
    obtain ⟨t, htT, hxt⟩ := Set.mem_iUnion₂.1 (hcov hx)
    have htface : t ∈ Γ.faces := hTface t htT
    have hxt' : x ∈ PL.simp (s ∩ t) := by
      rw [← Work.Engulf.simp_inter hs htface]; exact ⟨hx, hxt⟩
    rw [Set.mem_iUnion₂]
    refine ⟨s ∩ t, ?_, hxt'⟩
    rw [hT'def, Finset.mem_image]
    exact ⟨t, htT, rfl⟩
  -- `simplex_cover`: one of the subfaces actually equals `s`.
  have hne : s.Nonempty := Γ.nonempty_of_mem_faces hs
  have hind : AffineIndependent ℝ (fun v : ↥s => (v : PL.E N)) := Γ.indep hs
  have hmem : s ∈ T' := Work.Engulf.Aux.simplex_cover s T' hne hind hsub' hcov'
  rw [hT'def, Finset.mem_image] at hmem
  obtain ⟨t, htT, hst⟩ := hmem
  -- Then `s ⊆ t` and `simp t` lies in `A` or in `B`.
  have hst' : s ⊆ t := Finset.inter_eq_left.1 hst
  have hsub_simp : PL.simp s ⊆ PL.simp t := Work.Engulf.simp_mono hst'
  rcases (hTmem t).1 htT with htTA | htTB
  · left
    rw [hAeq]
    exact hsub_simp.trans (Set.subset_biUnion_of_mem (u := fun i => PL.simp i) htTA)
  · right
    rw [hBeq]
    exact hsub_simp.trans (Set.subset_biUnion_of_mem (u := fun i => PL.simp i) htTB)

end Work.Engulf.Aux

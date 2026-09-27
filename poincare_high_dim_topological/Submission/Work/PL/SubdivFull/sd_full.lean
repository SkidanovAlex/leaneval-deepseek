import Mathlib
import Submission.Work.PL.SubdivFull.Defs
import Submission.Work.PL.SubdivFull.subset_of_bary_mem_simp

/-!
# Fullness of a union of closed faces after one barycentric subdivision

`sd_full` is the one-step form of the "A2 fullness" lemma of
`Submission/Work/NOTES_LEAD_poincare_E4fix.md` §5: if `L` is a union of closed faces of `K`
(`hLs` and `hL`), then in the barycentric subdivision `sd K` the vertices of any face which lie in
`L` span a simplex contained in `L`.

The proof is the one-step argument of the note:

* a face of `sd K` is the set of barycenters of a chain `C₀` of faces of `K`
  (`Work.PL.Subdiv.mem_sd_faces_iff`), and a subset `t` of it is the set of barycenters of the
  subchain `C` of `C₀` consisting of those `ρ` with `bary ρ ∈ t`;
* for `ρ ∈ C`, `bary ρ ∈ t ⊆ L`, so `hL` gives a face `u ∈ K.faces` with `bary ρ ∈ simp u ⊆ L`;
  since `bary ρ` lies in the relative interior of `simp ρ` and the faces of `K` glue nicely,
  `ρ ⊆ u` (`subset_of_bary_mem_simp`), whence `simp ρ ⊆ simp u ⊆ L`;
* applying this to the top `ρ* := chainTop C` of the (nonempty) chain and using `ρ ⊆ ρ*` for all
  `ρ ∈ C`, every barycenter of the chain lies in the convex set `simp ρ* ⊆ L`, so the convex hull
  of the vertices of `t` — that is, `simp t` — is contained in `L`.
-/

namespace Work.PL.SubdivFull

open Set Metric

theorem sd_full {N : ℕ} {K : PL.Cx N} {L : Set (PL.E N)} (hLs : L ⊆ K.space)
    (hL : ∀ x ∈ L, ∃ s ∈ K.faces, x ∈ PL.simp s ∧ PL.simp s ⊆ L)
    {s : Finset (PL.E N)} (hs : s ∈ (Work.PL.Subdiv.sd K).faces) {t : Finset (PL.E N)}
    (hts : t ⊆ s) (ht : t.Nonempty) (htL : (↑t : Set (PL.E N)) ⊆ L) : PL.simp t ⊆ L := by
  classical
  have _ := hLs
  -- a face of `sd K` is the set of barycenters of a chain of faces of `K`
  obtain ⟨-, C₀, hC₀, hs_eq⟩ := Work.PL.Subdiv.mem_sd_faces_iff.mp hs
  -- the subchain of `C₀` whose barycenters are exactly the vertices of `t`
  set C : Finset (Finset (PL.E N)) := C₀.filter (fun ρ => Work.PL.Subdiv.bary ρ ∈ t)
  have hCsub : C ⊆ C₀ := Finset.filter_subset _ _
  have hCch : Work.PL.Subdiv.IsChain K C := hC₀.mono hCsub
  have hbary_mem_t : ∀ ρ ∈ C, Work.PL.Subdiv.bary ρ ∈ t :=
    fun ρ hρ => (Finset.mem_filter.mp hρ).2
  have himg : C.image Work.PL.Subdiv.bary = t := by
    refine Finset.Subset.antisymm (fun v hv => ?_) (fun v hv => ?_)
    · obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hv
      exact hbary_mem_t ρ hρ
    · have hv' : v ∈ C₀.image Work.PL.Subdiv.bary := by
        rw [← hs_eq]
        exact hts hv
      obtain ⟨ρ, hρ, hρv⟩ := Finset.mem_image.mp hv'
      exact Finset.mem_image.mpr ⟨ρ, Finset.mem_filter.mpr ⟨hρ, hρv ▸ hv⟩, hρv⟩
  have hCne : C.Nonempty := by
    obtain ⟨v, hv⟩ := ht
    have hv' : v ∈ C₀.image Work.PL.Subdiv.bary := by
      rw [← hs_eq]
      exact hts hv
    obtain ⟨ρ, hρ, hρv⟩ := Finset.mem_image.mp hv'
    exact ⟨ρ, Finset.mem_filter.mpr ⟨hρ, hρv ▸ hv⟩⟩
  -- the top of the chain, which is an element of the chain
  have htop_mem : Work.PL.Subdiv.chainTop C ∈ C :=
    Work.PL.Subdiv.chainTop_mem_chain hCch.2 hCne
  -- `hL` keeps `L` convex along the chain: the top face of the chain has its simplex inside `L`
  have htopL : PL.simp (Work.PL.Subdiv.chainTop C) ⊆ L := by
    have hb : Work.PL.Subdiv.bary (Work.PL.Subdiv.chainTop C) ∈ L :=
      htL (Finset.mem_coe.mpr (hbary_mem_t _ htop_mem))
    obtain ⟨u, hu, hbu, huL⟩ := hL _ hb
    have hsub : Work.PL.Subdiv.chainTop C ⊆ u :=
      subset_of_bary_mem_simp (hCch.1 _ htop_mem) hu hbu
    exact (convexHull_mono (Finset.coe_subset.mpr hsub)).trans huL
  -- every barycenter of the chain lies in the convex set `simp (chainTop C)`
  have hfin : convexHull ℝ (↑(C.image Work.PL.Subdiv.bary) : Set (PL.E N)) ⊆
      convexHull ℝ (↑(Work.PL.Subdiv.chainTop C) : Set (PL.E N)) :=
    convexHull_min (fun v hv => by
      obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hv)
      exact convexHull_mono (Finset.coe_subset.mpr (Work.PL.Subdiv.le_chainTop hρ))
        (Work.PL.Subdiv.bary_mem_simp (K.nonempty_of_mem_faces (hCch.1 ρ hρ))))
      (convex_convexHull ℝ (↑(Work.PL.Subdiv.chainTop C) : Set (PL.E N)))
  rw [← himg]
  exact hfin.trans htopL

end Work.PL.SubdivFull

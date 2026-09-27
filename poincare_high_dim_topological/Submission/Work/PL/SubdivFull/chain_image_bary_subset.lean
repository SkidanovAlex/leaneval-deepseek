import Mathlib
import Submission.Work.PL.Subdiv
import Submission.Work.PL.SubdivFull.subset_of_bary_mem_simp

/-!
# The closed simplex on the barycenters of a chain lies in a face union

Let `C` be a nonempty chain of faces of a simplicial complex `K` and let `L ⊆ E N` be such that
for every `ρ ∈ C` there is a face `u ∈ K.faces` with `simp u ⊆ L` and `bary ρ ∈ simp u`.  Then the
closed simplex spanned by the barycenters of the members of `C` is contained in `L`.

The point is that a chain has a **top** `T = chainTop C` (its largest member, see
`Work.PL.Subdiv.chainTop_mem_chain`), and it suffices to look at the face `u` attached to `T`:
`bary T ∈ simp u` together with `T, u ∈ K.faces` gives `T ⊆ u`
(`Work.PL.SubdivFull.subset_of_bary_mem_simp`), and every `ρ ∈ C` satisfies `ρ ⊆ T`.  Hence all the
barycenters `bary ρ` lie in the convex set `simp u`, and so does the convex hull they span.

This is the `SubdivFull`-area step feeding fullness of face unions: the barycenters of a chain of
faces of `K` which meet `L` span a simplex contained in `L`.
-/

namespace Work.PL.SubdivFull

open Set Metric
open scoped BigOperators

theorem chain_image_bary_subset {N : ℕ} {K : PL.Cx N} {L : Set (PL.E N)}
    {C : Finset (Finset (PL.E N))} (hC : Work.PL.Subdiv.IsChain K C) (hne : C.Nonempty)
    (h : ∀ ρ ∈ C, ∃ u ∈ K.faces, PL.simp u ⊆ L ∧ Work.PL.Subdiv.bary ρ ∈ PL.simp u) :
    PL.simp (C.image Work.PL.Subdiv.bary) ⊆ L := by
  classical
  -- the top of the chain is a member of the chain, hence a face of `K`
  have hT : Work.PL.Subdiv.chainTop C ∈ C := Work.PL.Subdiv.chainTop_mem_chain hC.2 hne
  have hTf : Work.PL.Subdiv.chainTop C ∈ K.faces := hC.1 _ hT
  -- the face of `K` attached to the top of the chain
  obtain ⟨u, hu, huL, hbu⟩ := h _ hT
  -- `bary T ∈ simp u` forces `T ⊆ u`, since both are faces of `K`
  have hTu : Work.PL.Subdiv.chainTop C ⊆ u := subset_of_bary_mem_simp hTf hu hbu
  -- all barycenters lie in the convex set `simp u`
  have himg : (↑(C.image Work.PL.Subdiv.bary) : Set (PL.E N)) ⊆ PL.simp u := by
    intro x hx
    obtain ⟨ρ, hρ, hρx⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
    rw [← hρx]
    have hρne : ρ.Nonempty := K.nonempty_of_mem_faces (hC.1 ρ hρ)
    have hsub : ρ ⊆ u := (Work.PL.Subdiv.le_chainTop hρ).trans hTu
    exact convexHull_mono (Finset.coe_subset.mpr hsub) (Work.PL.Subdiv.bary_mem_simp hρne)
  -- so the convex hull they span lies in `simp u ⊆ L`
  exact (convexHull_min himg (convex_convexHull ℝ (u : Set (PL.E N)))).trans huL

end Work.PL.SubdivFull

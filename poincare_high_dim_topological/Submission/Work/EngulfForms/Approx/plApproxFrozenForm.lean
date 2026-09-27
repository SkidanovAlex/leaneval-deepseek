import Mathlib
import Submission.Work.EngulfForms.Prelude
import Submission.Work.PL.Approx.Frozen.pl_approx_frozen_faces
import Submission.Work.PL.Approx.Finite.exists_delta_of_continuousOn
import Submission.Work.PL.Approx.Finite.dist_lt_of_mesh
import Submission.Work.Engulf.Auxi.Carrier

/-!
# A5, coarse-frozen form: `Work.Engulf.PlApproxFrozenForm`

`Work.Engulf.PlApproxFrozenForm S n` is the form of the frozen PL approximation consumed by the
engulfing argument (blueprint §2 G5, frozen variant): given a finite complex `K`, a set `L` which
is a *union of coarse faces* of `K` (`IsSubSp K L`), a map `f` continuous on `K.space` which is
already affine on every coarse face contained in `L` whose `f`-image meets `closedCube β`, and
`0 < α < β < 1`, `ε > 0`, there are a level `r` and a map `g`, continuous on `K.space`,
`ε`-close to `f`, equal to `f` off the cube of radius `β` and **on all of `L`**, such that `g` is
affine on every face of the `r`-fold subdivision `S.sdIter r K hK` whose `g`-image meets
`closedCube α`.

The proof is the direct transcription of A5

* `Work.PL.Approx.Frozen.pl_approx_frozen_faces` — the cutoff/interpolation construction, stated
  for a subdivision `K'` of `K` with a finite family of frozen faces;
* `Work.Engulf.exists_coarse_face_of_simp_subset` (carrier lemma) — a face of the subdivision
  whose simplex lies in `L` lies in a single coarse face contained in `L`, which transfers the
  affinity hypothesis on coarse faces to the fine faces;
* `Work.Engulf.SubdivTools.fine` plus uniform continuity of `f` on the compact `K.space`
  (`Work.PL.Approx.Finite.exists_delta_of_continuousOn`) — to choose `r` so that `f` oscillates by
  less than `min ε ((β - α) / 24)` on every fine face;
* `Work.Engulf.SubdivTools.spaces` — a union of coarse faces is a union of fine faces, so the fine
  faces lying in `L` cover `L`, and freezing on them freezes `g = f` on all of `L`.

The last point is a lemma of independent interest, stated first
(`Work.EngulfForms.Approx.exists_fine_face_of_mem`).
-/

open Set Metric PL
open Work.Engulf

namespace Work.EngulfForms.Approx

/-- **A union of coarse faces is a union of fine faces.**  If `L` is a union of faces of `K` and
`x ∈ L`, then `x` lies in a face of the `r`-fold subdivision `S.sdIter r K hK` whose simplex is
contained in `L`.  It follows that the fine faces lying in `L` cover `L`. -/
theorem exists_fine_face_of_mem {N : ℕ} (S : SubdivTools N) {K : Cx N} {hK : K.faces.Finite}
    {L : Set (E N)} (hLK : IsSubSp K L) (r : ℕ) {x : E N} (hx : x ∈ L) :
    ∃ t ∈ (S.sdIter r K hK).faces, x ∈ simp t ∧ simp t ⊆ L := by
  obtain ⟨s, hs, hxs, hsL⟩ := hLK.2 x hx
  -- `simp s` is itself a union of coarse faces (namely, of the single face `s`)
  have hsp : IsSubSp K (simp s) :=
    ⟨fun y hy => K.convexHull_subset_space hs hy,
      fun y hy => ⟨s, hs, hy, subset_rfl⟩⟩
  -- ... hence a union of fine faces
  obtain ⟨t, ht, hxt, hts⟩ := (S.subsp r K hK (simp s) hsp).2 x hxs
  exact ⟨t, ht, hxt, hts.trans hsL⟩

theorem plApproxFrozenForm {N n : ℕ} (S : Work.Engulf.SubdivTools N) : Work.Engulf.PlApproxFrozenForm S n := by
  classical
  intro K hK L hLK f hf α β hα hαβ hβ1 hlin ε hε
  -- the accuracy demanded of the oscillation of `f` on the fine faces
  have hβmα : 0 < β - α := by linarith
  have hρpos : 0 < min ε ((β - α) / 24) := lt_min hε (by linarith)
  -- `f` is uniformly continuous on the compact `K.space`
  obtain ⟨δ, hδpos, hδ⟩ :=
    Work.PL.Approx.Finite.exists_delta_of_continuousOn K hK f hf hρpos
  -- the level of subdivision at which the mesh is below `δ`
  obtain ⟨r, hr⟩ := S.fine K hK δ hδpos
  have hmesh : MeshLT (S.sdIter r K hK) δ := hr r le_rfl
  have hfin : (S.sdIter r K hK).faces.Finite := S.fin r K hK
  have hsub : Subdivides (S.sdIter r K hK) K := S.subdiv r K hK
  have hspaces : (S.sdIter r K hK).space = K.space := hsub.1
  -- oscillation of `f` on the fine faces
  have hosc : ∀ s ∈ (S.sdIter r K hK).faces, ∀ x ∈ simp s, ∀ y ∈ simp s,
      dist (f x) (f y) < min ε ((β - α) / 24) := by
    intro s hs x hx y hy
    exact hδ x (by rw [← hspaces]; exact (S.sdIter r K hK).convexHull_subset_space hs hx)
      y (by rw [← hspaces]; exact (S.sdIter r K hK).convexHull_subset_space hs hy)
      (Work.PL.Approx.Finite.dist_lt_of_mesh (S.sdIter r K hK) hmesh hs hx hy)
  -- the frozen family: the fine faces lying in `L`
  obtain ⟨g, hgcont, hgdist, hgout, hgfrz, hglin⟩ :=
    Work.PL.Approx.Frozen.pl_approx_frozen_faces K (S.sdIter r K hK) hfin f hf hsub
      α β hα hαβ hβ1 ε hε (hfin.toFinset.filter fun s => simp s ⊆ L)
      (fun t ht => hfin.mem_toFinset.1 (Finset.mem_filter.1 ht).1)
      (fun t ht hz => by
        have ht' : t ∈ (S.sdIter r K hK).faces := hfin.mem_toFinset.1 (Finset.mem_filter.1 ht).1
        have htL : simp t ⊆ L := (Finset.mem_filter.1 ht).2
        obtain ⟨z, hzt, hzfz⟩ := hz
        -- the carrier of `t` is a coarse face contained in `L`
        obtain ⟨τ, hτK, hτL, hτt⟩ := Work.Engulf.exists_coarse_face_of_simp_subset S hLK ht' htL
        obtain ⟨A, hA⟩ := hlin τ hτK hτL ⟨z, hτt hzt, hzfz⟩
        exact ⟨A, fun y hy => hA (hτt hy)⟩)
      hosc
  refine ⟨r, g, hgcont, hgdist, ?_, hgout, ?_⟩
  · -- `g = f` on `L`
    intro x hx
    obtain ⟨t, ht, hxt, htL⟩ := exists_fine_face_of_mem S hLK r hx
    exact hgfrz t (Finset.mem_filter.2 ⟨hfin.mem_toFinset.2 ht, htL⟩) x hxt
  · -- affinity on the fine faces meeting `closedCube α`
    intro s hs hx
    obtain ⟨A, hA⟩ := hglin s hs hx
    exact ⟨A, fun y hy => hA y hy⟩

end Work.EngulfForms.Approx

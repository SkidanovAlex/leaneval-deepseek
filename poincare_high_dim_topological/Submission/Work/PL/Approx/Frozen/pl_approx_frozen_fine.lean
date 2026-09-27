import Mathlib
import Submission.Work.PL.Approx.Defs
import Submission.Work.PL.Approx.SdSubdiv
import Submission.Work.PL.Approx.Frozen.pl_approx_frozen_faces
import Submission.Work.PL.Subdiv.SdBasic

/-!
# Frozen PL approximation, frozen on a subcomplex `L ≤ K` of the *coarse* complex

`Work.PL.Approx.Frozen.pl_approx_frozen_fine` is the form of the frozen PL approximation used by
the engulfing argument: the map `f` is to be approximated by `g`, which

* is continuous on `K.space`,
* is `ε`-close to `f`,
* agrees with `f` outside the cube of radius `β`,
* agrees with `f` on the whole of `L.space`, where `L ≤ K` is a subcomplex,
* is affine on every face of the `r`-fold barycentric subdivision of `K` whose `g`-image meets
  the cube of radius `α`.

The main point is the bookkeeping: the faces of the `r`-fold barycentric subdivision `sdIter r K`
which lie over the subcomplex `L` cover `L.space` and each of them is contained in a simplex of
`L` (`exists_frozen_faces_of_sd`, from `sdIter_isSub_of_isSub` and `sdIter_subdivides`).  Feeding
this finite family `T` to `pl_approx_frozen_faces` (which freezes a finite list of faces of the
*subdivision*) proves the claim.
-/

namespace Work.PL.Approx.Frozen

open Set Metric

/-- **Subcomplexes survive iterated barycentric subdivision.** -/
theorem sdIter_isSub_of_isSub {N : ℕ} {V W : PL.Cx N} (h : PL.IsSub V W) (r : ℕ)
    (hV : V.faces.Finite) (hW : W.faces.Finite) :
    PL.IsSub (Work.PL.Subdiv.sdIter r V hV) (Work.PL.Subdiv.sdIter r W hW) := by
  induction r with
  | zero => exact h
  | succ n ih =>
    show PL.IsSub (Work.PL.Subdiv.sd (Work.PL.Subdiv.sdIter n V hV))
      (Work.PL.Subdiv.sd (Work.PL.Subdiv.sdIter n W hW))
    exact Work.PL.Subdiv.sd_isSub ih

/-- **A subcomplex is a finite union of faces of the subdivision.**  For a subcomplex `L ≤ K` of a
finite complex, the faces of the `r`-fold barycentric subdivision of `L` are faces of the `r`-fold
barycentric subdivision of `K`, they cover `L.space` (subdivision does not change the space), and
each of them lies in a simplex of `L`. -/
lemma exists_frozen_faces_of_sd {N : ℕ} (K : PL.Cx N) (hK : K.faces.Finite) (L : PL.Cx N)
    (hLK : PL.IsSub L K) (hLfin : L.faces.Finite) (r : ℕ) :
    ∃ T : Finset (Finset (PL.E N)),
      (∀ t ∈ T, t ∈ ((sdSubdiv N).iter r K hK).faces) ∧
      (⋃ t ∈ T, PL.simp t = L.space) ∧
      (∀ t ∈ T, ∃ ρ ∈ L.faces, PL.simp t ⊆ PL.simp ρ) := by
  classical
  refine ⟨(Work.PL.Subdiv.sdIter_faces_finite r L hLfin).toFinset, ?_, ?_, ?_⟩
  · -- every face of `sdIter r L` is a face of `sdIter r K`
    intro t ht
    rw [Work.PL.Approx.Subdiv.iter_sdSubdiv]
    exact sdIter_isSub_of_isSub hLK r hLfin hK ((Set.Finite.mem_toFinset _).mp ht)
  · -- the faces of `sdIter r L` cover its space, which is `L.space`
    have hsub : (Work.PL.Subdiv.sdIter r L hLfin).space = L.space :=
      (Work.PL.Subdiv.sdIter_subdivides r L hLfin).1
    refine le_antisymm ?_ ?_
    · intro x hx
      obtain ⟨t, ht, hxt⟩ := Set.mem_iUnion₂.mp hx
      have htL : t ∈ (Work.PL.Subdiv.sdIter r L hLfin).faces :=
        (Set.Finite.mem_toFinset _).mp ht
      rw [← hsub, Geometry.SimplicialComplex.space]
      exact Set.mem_iUnion₂.mpr ⟨t, htL, hxt⟩
    · intro x hx
      rw [← hsub, Geometry.SimplicialComplex.space] at hx
      obtain ⟨t, ht, hxt⟩ := Set.mem_iUnion₂.mp hx
      exact Set.mem_iUnion₂.mpr ⟨t, (Set.Finite.mem_toFinset _).mpr ht, hxt⟩
  · -- each face of `sdIter r L` lies in a simplex of `L`
    intro t ht
    exact (Work.PL.Subdiv.sdIter_subdivides r L hLfin).2 t
      ((Set.Finite.mem_toFinset _).mp ht)

lemma pl_approx_frozen_fine {N n : ℕ} (K : PL.Cx N) (hK : K.faces.Finite) (L : PL.Cx N)
    (hLK : PL.IsSub L K) (hLfin : L.faces.Finite) (r : ℕ) (f : PL.E N → PL.E n)
    (hf : ContinuousOn f K.space) (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (hβ1 : β < 1)
    (ε : ℝ) (hε : 0 < ε)
    (hlinL : ∀ ρ ∈ L.faces, (∃ z ∈ PL.simp ρ, f z ∈ PL.closedCube β) →
      ∃ A : PL.E N →ᵃ[ℝ] PL.E n, ∀ z ∈ PL.simp ρ, f z = A z)
    (hosc : ∀ s ∈ ((sdSubdiv N).iter r K hK).faces, ∀ x ∈ PL.simp s, ∀ y ∈ PL.simp s,
      dist (f x) (f y) < min ε ((β - α) / 24)) :
    ∃ g : PL.E N → PL.E n, ContinuousOn g K.space ∧ (∀ x ∈ K.space, dist (g x) (f x) < ε) ∧
      (∀ x ∈ K.space, f x ∉ PL.closedCube β → g x = f x) ∧ (∀ x ∈ L.space, g x = f x) ∧
      ∀ s ∈ ((sdSubdiv N).iter r K hK).faces, (∃ x ∈ PL.simp s, g x ∈ PL.closedCube α) →
        ∃ A : PL.E N →ᵃ[ℝ] PL.E n, ∀ y ∈ PL.simp s, g y = A y := by
  classical
  -- the faces of the fine complex lying over `L`
  obtain ⟨T, hTfaces, hTunion, hTsub⟩ := exists_frozen_faces_of_sd K hK L hLK hLfin r
  -- apply the finite-list frozen approximation with this family `T`
  obtain ⟨g, hgcont, hgdist, hgout, hgfro, hglin⟩ :=
    pl_approx_frozen_faces K ((sdSubdiv N).iter r K hK) ((sdSubdiv N).iter_fin r K hK) f hf
      ((sdSubdiv N).iter_subdivides r K hK) α β hα hαβ hβ1 ε hε T hTfaces
      (fun t htT hz => by
        obtain ⟨ρ, hρ, hρsub⟩ := hTsub t htT
        obtain ⟨z, hz, hfz⟩ := hz
        obtain ⟨A, hA⟩ := hlinL ρ hρ ⟨z, hρsub hz, hfz⟩
        exact ⟨A, fun z hz => hA z (hρsub hz)⟩)
      hosc
  refine ⟨g, hgcont, hgdist, hgout, ?_, hglin⟩
  -- `g` agrees with `f` on `L.space`, since the faces of `T` cover it
  intro x hxL
  rw [← hTunion] at hxL
  obtain ⟨t, htT, hxt⟩ := Set.mem_iUnion₂.mp hxL
  exact hgfro t htT x hxt

end Work.PL.Approx.Frozen

import Submission.Work.PL.Subdiv

/-!
# Fullness of a union of closed faces after at least one barycentric subdivision

This is the definition layer of area `Work.PL.SubdivFull` (the "A2 fullness" lemma of
`Submission/Work/NOTES_LEAD_poincare_E4fix.md` §5).  Vocabulary is `PL`
(`Submission.Work.PL.Defs`); the barycentric subdivision lives in the delivered area
`Submission.Work.PL.Subdiv` (`sd`, `sdIter`, `IsChain`, `chainTop`, `bary`).

* `IsFaceUnion K L` : `L` is a union of closed faces of `K` (the space of a "subcomplex" of `K`,
  presented as a set -- this is `Work.Engulf.IsSubSp` restated in `PL` vocabulary).
* `FullOn K' L` : `L` is *full* in the complex `K'`: the vertices of any nonempty face of `K'`
  which happen to lie in `L` span a simplex contained in `L`.

The main results of the area are
* `Work.PL.SubdivFull.fullOn_sd` / `sd_full` : `L` is full in `sd K` once `L` is a union of faces
  of `K`;
* `Work.PL.SubdivFull.fullOn_sdIter` / `sdIter_full` : the same for `sdIter r K` with `1 ≤ r`.

**It is false at `r = 0`**: taking `K` a triangle with vertices `a,b,c` and `L = [a,b] ∪ [b,c]`,
the face `s = {a,b,c}` of `sdIter 0 K = K` itself has all its vertices in `L`, but
`simp s ⊄ L`.
-/

open Set Metric
open scoped BigOperators
open PL

namespace Work.PL.SubdivFull

noncomputable section

variable {N : ℕ}

/-- `L` is a **union of closed faces** of `K`: `L ⊆ K.space` and every point of `L` lies in a
simplex of a face of `K` which is contained in `L`.  (Up to the definitional unfolding of
`Geometry.SimplicialComplex.space` this is `Work.Engulf.IsSubSp K L`.) -/
def IsFaceUnion (K : PL.Cx N) (L : Set (PL.E N)) : Prop :=
  L ⊆ K.space ∧ ∀ x ∈ L, ∃ s ∈ K.faces, x ∈ PL.simp s ∧ PL.simp s ⊆ L

/-- `L` is **full** in the complex `K'`: for every face `s` of `K'` and every nonempty set `t ⊆ s`
of vertices of `s` which all lie in `L`, the simplex spanned by `t` is contained in `L`.

This is the conclusion of the E4 repair's `full` field (`SdFullForm`), stated for an arbitrary
complex `K'` so that it can be applied to `K' = sdIter r K`. -/
def FullOn (K' : PL.Cx N) (L : Set (PL.E N)) : Prop :=
  ∀ s ∈ K'.faces, ∀ t ⊆ s, t.Nonempty → (↑t : Set (PL.E N)) ⊆ L → PL.simp t ⊆ L

/-- The vertices of a finite vertex set `s` which lie in `L` (the intersection of a face with the
frozen subcomplex, in the applications).  Defined with `Classical.decEq` so that the statements
below need no decidability hypothesis. -/
def vertsIn (s : Finset (PL.E N)) (L : Set (PL.E N)) : Finset (PL.E N) := by
  classical
  exact s.filter (fun v => v ∈ L)

theorem mem_vertsIn {s : Finset (PL.E N)} {L : Set (PL.E N)} {v : PL.E N} :
    v ∈ vertsIn s L ↔ v ∈ s ∧ v ∈ L := by
  classical
  simp [vertsIn]

theorem vertsIn_subset (s : Finset (PL.E N)) (L : Set (PL.E N)) : vertsIn s L ⊆ s :=
  fun _ hv => (mem_vertsIn.mp hv).1

theorem vertsIn_subset_L (s : Finset (PL.E N)) (L : Set (PL.E N)) :
    (↑(vertsIn s L) : Set (PL.E N)) ⊆ L :=
  fun _ hv => (mem_vertsIn.mp (Finset.mem_coe.mp hv)).2

theorem vertsIn_eq_self {s : Finset (PL.E N)} {L : Set (PL.E N)} (h : (↑s : Set (PL.E N)) ⊆ L) :
    vertsIn s L = s :=
  Finset.Subset.antisymm (vertsIn_subset s L)
    (fun v hv => mem_vertsIn.mpr ⟨hv, h hv⟩)

theorem vertsIn_mono {s s' : Finset (PL.E N)} {L : Set (PL.E N)} (h : s ⊆ s') :
    vertsIn s L ⊆ vertsIn s' L :=
  fun v hv => mem_vertsIn.mpr ⟨h (mem_vertsIn.mp hv).1, (mem_vertsIn.mp hv).2⟩

theorem vertsIn_simp {s : Finset (PL.E N)} {L : Set (PL.E N)} :
    PL.simp (vertsIn s L) ⊆ PL.simp s :=
  convexHull_mono (Finset.coe_subset.mpr (vertsIn_subset s L))

theorem IsFaceUnion.subset_space {K : PL.Cx N} {L : Set (PL.E N)} (h : IsFaceUnion K L) :
    L ⊆ K.space := h.1

theorem isFaceUnion_empty (K : PL.Cx N) : IsFaceUnion K (∅ : Set (PL.E N)) :=
  ⟨empty_subset _, by simp⟩

theorem isFaceUnion_space (K : PL.Cx N) : IsFaceUnion K K.space := by
  refine ⟨Subset.rfl, fun x hx => ?_⟩
  rw [Geometry.SimplicialComplex.mem_space_iff] at hx
  obtain ⟨s, hs, hxs⟩ := hx
  exact ⟨s, hs, hxs, Geometry.SimplicialComplex.convexHull_subset_space hs⟩

/-- A union of faces of `K`, presented by the index set of the faces. -/
theorem isFaceUnion_of_faces {K : PL.Cx N} {T : Set (Finset (PL.E N))} (hT : T ⊆ K.faces) :
    IsFaceUnion K (⋃ s ∈ T, PL.simp s) := by
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.mp hx
    exact Geometry.SimplicialComplex.convexHull_subset_space (hT hs) hxs
  · obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.mp hx
    exact ⟨s, hT hs, hxs, fun y hy => mem_iUnion₂.mpr ⟨s, hs, hy⟩⟩

/-- A union of faces of `K` given as a *finite* family. -/
theorem isFaceUnion_of_finset_faces {K : PL.Cx N} {T : Finset (Finset (PL.E N))}
    (hT : ∀ s ∈ T, s ∈ K.faces) : IsFaceUnion K (⋃ s ∈ T, PL.simp s) := by
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.mp hx
    exact Geometry.SimplicialComplex.convexHull_subset_space (hT s hs) hxs
  · obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.mp hx
    exact ⟨s, hT s hs, hxs, fun y hy => mem_iUnion₂.mpr ⟨s, hs, hy⟩⟩

/-- The index-set description of a union of closed faces: they are exactly the unions
`⋃ s ∈ T, simp s` over sets of faces. -/
theorem isFaceUnion_iff (K : PL.Cx N) (L : Set (PL.E N)) :
    IsFaceUnion K L ↔ ∃ T : Set (Finset (PL.E N)), T ⊆ K.faces ∧ L = ⋃ s ∈ T, PL.simp s := by
  constructor
  · intro h
    refine ⟨{s | s ∈ K.faces ∧ PL.simp s ⊆ L}, fun s hs => hs.1, Subset.antisymm ?_ ?_⟩
    · intro x hx
      obtain ⟨s, hs, hxs, hsub⟩ := h.2 x hx
      exact mem_iUnion₂.mpr ⟨s, ⟨hs, hsub⟩, hxs⟩
    · rintro x hx
      obtain ⟨s, ⟨hs, hsub⟩, hxs⟩ := mem_iUnion₂.mp hx
      exact hsub hxs
  · rintro ⟨T, hT, rfl⟩
    exact isFaceUnion_of_faces hT

theorem IsFaceUnion.union {K : PL.Cx N} {L L' : Set (PL.E N)} (h : IsFaceUnion K L)
    (h' : IsFaceUnion K L') : IsFaceUnion K (L ∪ L') := by
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · rcases hx with hx | hx
    exacts [h.1 hx, h'.1 hx]
  · rcases hx with hx | hx
    · obtain ⟨s, hs, hxs, hsub⟩ := h.2 x hx
      exact ⟨s, hs, hxs, fun y hy => Or.inl (hsub hy)⟩
    · obtain ⟨s, hs, hxs, hsub⟩ := h'.2 x hx
      exact ⟨s, hs, hxs, fun y hy => Or.inr (hsub hy)⟩

/-- `FullOn` applied to a face all of whose vertices lie in `L`. -/
theorem FullOn.simp_subset {K' : PL.Cx N} {L : Set (PL.E N)} (h : FullOn K' L)
    {s : Finset (PL.E N)} (hs : s ∈ K'.faces) (hsL : (↑s : Set (PL.E N)) ⊆ L) : PL.simp s ⊆ L :=
  h s hs s subset_rfl (K'.nonempty_of_mem_faces hs) hsL

end

end Work.PL.SubdivFull

import Mathlib
import Submission.Work.PL.Defs

namespace Work.PL.Subdiv.Embed

/-- The union of the face sets of two simplicial complexes in `ℝᴺ` whose underlying spaces are
disjoint is again a simplicial complex, and its underlying space is the union of the two spaces. -/
theorem exists_union_faces {N : ℕ} (K L : PL.Cx N) (h : Disjoint K.space L.space) :
    ∃ C : PL.Cx N,
      (∀ t, t ∈ C.faces ↔ t ∈ K.faces ∨ t ∈ L.faces) ∧
      C.space = K.space ∪ L.space := by
  refine ⟨{ faces := K.faces ∪ L.faces
            isRelLowerSet_faces := K.isRelLowerSet_faces.union L.isRelLowerSet_faces
            indep := ?_
            inter_subset_convexHull := ?_ }, ?_, ?_⟩
  · intro s hs
    rcases hs with hs | hs
    · exact K.indep hs
    · exact L.indep hs
  · -- The mixed case is impossible, since the two faces would then meet in both spaces.
    intro s t hs ht x hx
    rcases hs with hs | hs
    · rcases ht with ht | ht
      · exact K.inter_subset_convexHull hs ht hx
      · exact absurd (L.convexHull_subset_space ht hx.2)
          (Set.disjoint_left.1 h (K.convexHull_subset_space hs hx.1))
    · rcases ht with ht | ht
      · exact absurd (L.convexHull_subset_space hs hx.1)
          (Set.disjoint_left.1 h (K.convexHull_subset_space ht hx.2))
      · exact L.inter_subset_convexHull hs ht hx
  · intro t
    exact Iff.rfl
  · show (⋃ s ∈ (K.faces ∪ L.faces), convexHull ℝ (s : Set (PL.E N))) =
      (⋃ s ∈ K.faces, convexHull ℝ (s : Set (PL.E N))) ∪
        (⋃ s ∈ L.faces, convexHull ℝ (s : Set (PL.E N)))
    exact Set.biUnion_union K.faces L.faces _

end Work.PL.Subdiv.Embed

import Mathlib
import Submission.Work.PL.SubdivFull.Defs

open Set

namespace Work.PL.SubdivFull

/-- The closed simplex spanned by a face `Δ` of `K` is a union of closed faces of `K`: it is the
union of the single face `Δ` itself.  (This is the trivial "closed face" instance of
`IsFaceUnion`; the content of the `SubdivFull` area is that after a barycentric subdivision much
more general closed sets become face unions.) -/
theorem isFaceUnion_simp_of_mem_faces {N : ℕ} {K : PL.Cx N} {Δ : Finset (PL.E N)}
    (hΔ : Δ ∈ K.faces) : IsFaceUnion K (PL.simp Δ) :=
  ⟨Geometry.SimplicialComplex.convexHull_subset_space hΔ,
   fun _ hx => ⟨Δ, hΔ, hx, Subset.rfl⟩⟩

end Work.PL.SubdivFull

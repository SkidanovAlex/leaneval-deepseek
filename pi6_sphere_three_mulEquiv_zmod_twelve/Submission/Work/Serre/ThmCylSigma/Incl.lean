import Submission.Work.Serre.ThmCylSigma.Defs

/-!
# The inclusion of a piece maps a subspace into the subspace of the `σ`-type

`Work.Serre.Sigma.pieceIncl` is the inclusion of the `i`-th piece into the `σ`-type; it carries
`A i` into `sigmaSet A`.  (The proof of this definitional identification is isolated here so that
the files that use it can set the transparency options they need.)
-/

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial Topology

namespace Work.Serre.Sigma

variable {ι : Type} {Y : ι → Type} [∀ i, TopologicalSpace (Y i)]

/-- The inclusion of a piece carries the piece's subspace into the `σ`-type's subspace. -/
theorem pieceIncl_mem_sigmaSet (A : ∀ i, Set (Y i)) (i : ι) (x : Y i) (hx : x ∈ A i) :
    (pieceIncl (Y := Y) i) x ∈ sigmaSet A := hx

end Work.Serre.Sigma

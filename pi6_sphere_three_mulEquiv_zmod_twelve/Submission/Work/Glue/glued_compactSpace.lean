import Mathlib
import Submission.Work.Glue.Basic

/-!
# The glued space is compact

`Submission.Work.Glue.Basic` constructs, given two charted spaces/manifolds `X`, `Y` over a
common model `H` and gluing data `D : Data I n X Y`, the glued space `D.Glued` as a quotient of
the disjoint union `X ⊕ Y` by the relation identifying `x ∈ U` with `φ x ∈ V`.

If `X` and `Y` are compact then so is `D.Glued`: the disjoint union `X ⊕ Y` of two compact
spaces is compact, the quotient map `D.q` is continuous and surjective, and a continuous
surjective image of a compact space is compact.
-/

namespace Work.Glue

open scoped Manifold ContDiff Topology in
open Submission.Glue in
theorem glued_compactSpace
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I n X]
    {Y : Type*} [TopologicalSpace Y] [ChartedSpace H Y] [IsManifold I n Y]
    [CompactSpace X] [CompactSpace Y] (D : Data I n X Y) : CompactSpace D.Glued := by
  -- `D.Glued` is the image of the compact space `X ⊕ Y` under the continuous surjection `D.q`.
  exact @Function.Surjective.compactSpace (X ⊕ Y) D.Glued _ _ D.q D.continuous_q
    inferInstance (fun z => Quotient.inductionOn z (fun a => ⟨a, rfl⟩))

end Work.Glue

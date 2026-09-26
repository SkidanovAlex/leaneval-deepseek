import Mathlib
import Submission.Work.BoxShrink.Bubble.Plane.finite_preimage

namespace Work.BoxShrink.Bubble.Plane

open LeanEval.KnotTheory.PardonDistortion

/-- The preimage of a countable set under the parametrisation of a `ParamTorus`, restricted to a
compact set, is countable.

Indeed the parametrisation is injective modulo the lattice `(2πℤ)²`, so each fibre is discrete;
a compact set intersecting a discrete set is finite, and a countable union of finite sets is
countable. -/
theorem countable_preimage {P : Work.CoreTopology.ParamTorus}
    {Z : Set LeanEval.KnotTheory.PardonDistortion.R3} (hZ : Z.Countable) {K : Set (ℝ × ℝ)}
    (hK : IsCompact K) :
    (K ∩ {q : ℝ × ℝ | P.psi q.1 q.2 ∈ Z}).Countable := by
  have hcont : Continuous (fun q : ℝ × ℝ => P.psi q.1 q.2) := P.cont
  -- The preimage splits as the countable union, over `z ∈ Z`, of the fibre over `z`.
  have hsub : K ∩ {q : ℝ × ℝ | P.psi q.1 q.2 ∈ Z} ⊆
      ⋃ z ∈ Z, (K ∩ (fun q : ℝ × ℝ => P.psi q.1 q.2) ⁻¹' {z}) := by
    intro q hq
    obtain ⟨hqK, hqZ⟩ := hq
    exact Set.mem_biUnion hqZ ⟨hqK, rfl⟩
  refine (hZ.biUnion (fun z _ => ?_)).mono hsub
  -- Each fibre over a single point is closed and discrete, so its intersection with `K` is
  -- finite, hence countable.
  have hclosed : IsClosed ((fun q : ℝ × ℝ => P.psi q.1 q.2) ⁻¹' ({z} : Set R3)) :=
    isClosed_singleton.preimage hcont
  exact ((hK.inter_right hclosed).finite
    (isDiscrete_of_subset (fiber_isDiscrete P z) Set.inter_subset_right)).countable

end Work.BoxShrink.Bubble.Plane

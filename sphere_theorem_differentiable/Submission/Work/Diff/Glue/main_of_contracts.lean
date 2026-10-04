import Mathlib
import Submission.Diff.Interfaces

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

CONTEXT: this is one area of the Brendle–Schoen differentiable sphere theorem, driven by the lead. Read HANDOFF.md.
The contracts in Submission/Diff/Interfaces.lean and Submission/Diff/Alg.lean are frozen. Your statement's hypotheses are other
areas' contracts: USE them, do not re-prove them. Go wide: file all the independent sub-lemmas at once,
each with an exact statement, and write your assembly against their statements. If your statement looks
false or unprovable as stated, say so at once in `declare_false` with a precise reason. The lead will fix it.
Pure composition, a few lines. Take η and its property from hC. Apply hF to η to get g, cov, its smoothness,
torsion, compatibility, κ and the pinching. Then apply hC's ∀ with the same `letI` instance. Watch that the `letI` instances
unify, since both contracts use `⟨g.toRiemannianMetric⟩`.
-/

namespace Work.Diff.Glue

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

/-- **Glue**: the two frozen contracts compose.

`ClassicalEnd I M` provides a pinching threshold `η > 0` (and the diffeomorphism it produces for any
smooth metric whose Levi-Civita connection is `(κ, (1+η)κ]`-pinched).  `FlowContract I M` provides,
for that same `η`, a smooth metric `g` with a smooth, torsion-free, metric-compatible covariant
derivative `cov` that is `(κ, (1+η)κ]`-pinched, for some `κ > 0`.  Feeding the latter data into the
former yields a diffeomorphism onto the round sphere.

Both hypotheses instantiate the metric typeclass as `⟨g.toRiemannianMetric⟩` (see the `letI` in
`ClassicalEnd` and `FlowContract`), so the two `Pinched` statements are definitionally equal and the
composition is a direct application. -/
theorem main_of_contracts
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (hC : ClassicalEnd I M) (hF : FlowContract I M) :
    Nonempty (M ≃ₘ⟮I, 𝓡 (Module.finrank ℝ E)⟯ SphereD E) := by
  -- Extract the pinching threshold `η > 0` and the classical sphere theorem it feeds.
  obtain ⟨η, hη, hc⟩ := hC
  -- Run the flow contract at this `η`: it yields the metric, its connection, and the pinching.
  obtain ⟨g, cov, hs, ht, hm, κ, hκ, hp⟩ := hF η hη
  -- Apply the classical end to exactly this data.
  exact hc g cov hs ht hm κ hκ hp

end Work.Diff.Glue

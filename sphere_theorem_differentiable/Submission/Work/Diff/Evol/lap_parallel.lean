import Mathlib
import Submission.Diff.Evol
import Submission.Work.Diff.Evol.Vocab
import Submission.Work.Diff.Evol.LapKit
import Submission.Work.Diff.Evol.FrameMat

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

CONTEXT: this is one area of the Brendle–Schoen differentiable sphere theorem, driven by the lead. Read HANDOFF.md.
The contracts in Submission/Diff/Interfaces.lean and Submission/Diff/Alg.lean are frozen. Your statement's hypotheses are other
areas' contracts: USE them, do not re-prove them. Go wide: file all the independent sub-lemmas at once,
each with an exact statement, and write your assembly against their statements. If your statement looks
false or unprovable as stated, say so at once in `declare_false` with a precise reason. The lead will fix it.
ROUTE (LapRmFrameParallel). Extend e by PARALLEL TRANSPORT along radial geodesics from x inside a normal ball
(seeded library: ParallelField.lean, ParallelGlobal.lean, GExpSmooth.lean give smooth exp and parallel fields along curves).
Smoothness in y follows from smooth dependence of the parallel-transport ODE on the initial direction (the GExpSmooth pattern).
Orthonormality near x: parallel transport is an isometry (metric compatibility).
At x: ∇Ef(x) = 0 (every direction v is radial at x). And ∇²_{v,v}Ef(x) = 0 for every v, since Ef is parallel along the geodesic
through x in direction v and that geodesic has ∇_{γ'}γ' = 0. So ∑ₘ ∇²_{eₘ,eₘ}Ef(x) = 0 and the cross terms of the Laplacian vanish.
Then Δ(ℓ(Rm(Ef,…))) (x) = ℓ(∑ₘ ∇²_{eₘ,eₘ}Rm(e,…)) = ℓ(lapRmFrame g x e), by the product rule for ∇² of a contraction.
The cutoff: Ef must be a GLOBAL smooth field. Multiply by a bump equal to 1 near x (only the germ at x matters).

## Implementation

The proof is `Work.Diff.Evol.laplAt_ell_rmFrame_eq` (in `LapKit.lean`), which computes the Laplacian of
`ℓ ∘ rmFrame ∘ Ef` at `x` for any frame field `Ef` which is *parallel at `x` to first and second order*
(`∇_v Ef i = 0` and `∇_W ∇_W Ef i = 0` at `x`).  The existence of such a frame field `Ef`, smooth,
`g`-orthonormal near `x`, with `Ef i x = e i`, is `Work.Diff.Evol.frame_exists`.

(Note: the construction there uses parallel transport along the straight **chart lines** through `x`
rather than along geodesics; at `x` itself every direction is the initial velocity of exactly one such
line, and the covariant derivative of the transported field along the line vanishes identically, which
gives both `∇_v Ef i = 0` and `∇_v ∇_v Ef i = 0` at `x`.  No exponential map is needed, only the smooth
dependence of the parallel-transport ODE on the initial direction.)
-/

namespace Work.Diff.Evol

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

theorem lap_parallel
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : LCSmooth I M) :
    LapRmFrameParallel I M := by
  intro g x e he
  obtain ⟨Ef, hval, hsm, hON, hfirst, hsecond⟩ :=
    frame_exists_mat (I := I) (M := M) hLC g x e he
  exact ⟨Ef, hval, hsm, hON,
    fun ℓ => laplAt_ell_rmFrame_eq (I := I) (M := M) hLC g x e he Ef hval hsm hfirst hsecond ℓ⟩

end Work.Diff.Evol

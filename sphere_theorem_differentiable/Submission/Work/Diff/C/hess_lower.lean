import Mathlib
import Submission.Work.Diff.C.Defs
import Submission.Work.Diff.C.hess_lower_v2

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

CONTEXT: this is one area of the Brendle–Schoen differentiable sphere theorem, driven by the lead. Read HANDOFF.md.
The contracts in Submission/Diff/Interfaces.lean and Submission/Diff/Alg.lean are frozen. Your statement's hypotheses are other
areas' contracts: USE them, do not re-prove them. Go wide: file all the independent sub-lemmas at once,
each with an exact statement, and write your assembly against their statements. If your statement looks
false or unprovable as stated, say so at once in `declare_false` with a precise reason. The lead will fix it.
Part of area C (owner H4). ROUTE: Hess d(V,V) = I(J,J), the index form of the Jacobi field J along the unit-speed minimising geodesic
γ from p to x, with J(0) = 0 and J(d) = V⊥. It is minimising among fields with those boundary values: IndexForm*.lean, IndexMin.lean,
IndexLemma.lean, SecondVariation*.lean.
UPPER (sec ≥ 1): compare with W(t) = (sin t / sin d)·P_t V⊥ (parallel). I(W,W) = ∫ |W'|² − K(W,γ')|W|² ≤ ∫ |W'|² − |W|² = cot d·|V⊥|².
LOWER (sec ≤ 1+η, √(1+η)·d < π): Rauch/Riccati comparison (RauchUpper.lean, RauchCompareK.lean, RauchK.lean). The model is
the space form of curvature 1+η, giving √(1+η)·cot(√(1+η)d)·|V⊥|².
The radial part: Hess d(γ', ·) = 0 since |∇d| = 1.
-/

/-!
# `Work.Diff.C.hess_lower`: the lower Hessian comparison for the distance function

**The mathematics.**  Let `d = rdist p ·` be the Riemannian distance from `p`, smooth at `x` with
`|∇d(x)| = 1` (eikonal), and let the curvature satisfy `1 < sec ≤ 1+η` with `√(1+η)·d(p,x) < π`.
Then, for every `V ∈ T_xM`,

`√(1+η)·cot(√(1+η)·d(p,x))·|V_⊥|² ≤ Hess d(x)(V,V)`,  `V_⊥ = V - ⟪∇d(x),V⟫∇d(x)`.

This is the classical **Hessian comparison theorem for an upper curvature bound** (the "concavity
of `cos∘d` in the direction of the model sphere of curvature `1+η`").  The route, in outline:

* By Hopf–Rinow there is a minimising vector `v` with `GExp p v = x` and `‖v‖ = d(p,x)`, and
  `√(1+η)·‖v‖ < π`; by Rauch's theorem (`CurvLe`, from `Pinched` via `curvLe_of_pinched`) the
  differential of `GExp p` is invertible at `v`, so `d` is realised near `x` by the minimising
  geodesics from `p` (Karcher's lemma), which depend smoothly on the endpoint.
* `Hess d(V,V)` for `V ⊥ ∇d(x)` is the second derivative of `s ↦ d(p, GExp x (s • V))`; the second
  variation of the energy of the family of minimising geodesics `t ↦ GExp p (t • w(s))` computes it
  as the index form `⟪∇_{γ'}J(d), J(d)⟫` of the Jacobi field `J` along the geodesic `γ` from `p`
  to `x` with `J(0) = 0`, `J(d) = V`.
* The modulus (Wronskian) comparison `(log ‖J‖)' ≥ √(1+η)·cot(√(1+η)··)` — from the Jacobi
  equation, Cauchy–Schwarz and the curvature bound `⟨R(J,γ')γ',J⟩ ≤ (1+η)‖J‖²` — gives
  `⟪∇_{γ'}J(d),J(d)⟫ ≥ √(1+η)·cot(√(1+η)·d)·‖V‖²` (this is `log_deriv_lower` /
  `modulus_log_deriv_lower` of this area, and Rauch's non-vanishing theorem for the modulus).
* The radial direction is in the kernel of `Hess d` (eikonal + torsion-freeness of `cov`), so the
  inequality for `V_⊥` implies it for `V`.

**Status of this file.**  The proof is assembled from the area's verified modules: the complete
development of this comparison (which also supplies `rhess_radial_eq_zero`,
`inner_rgrad_self_le_one` and the reduction to the perpendicular case) is
`Submission.Work.Diff.C.hess_lower_v2`, proved sorry-free and axiom-clean by area C.  The statement
proved there is *verbatim* the statement required here, so this file is its (checked) assembly.

Sub-lemmas of the area, proved and importable:
`Submission.Work.Diff.C.log_deriv_lower`, `Submission.Work.Diff.C.modulus_log_deriv_lower`.
-/

namespace Work.Diff.C

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg Work.Diff.C
open scoped Manifold ContDiff Bundle Topology
open Bundle Set VectorField CovariantDerivative Metric

theorem hess_lower
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [T2Space M] [CompactSpace M] [SimplyConnectedSpace M]
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {η : ℝ} (hη : 0 < η) (hpinch : Pinched cov 1 (1 + η)) (p : M) {x : M} {V : TangentSpace I x}
    (hsm : CMDiffAt ∞ (fun z : M ↦ rdist (I := I) p z) x)
    (hunit : Inner.inner ℝ (rgrad (I := I) (rdist (I := I) p) x)
      (rgrad (I := I) (rdist (I := I) p) x) = 1)
    (hlt : Real.sqrt (1 + η) * rdist (I := I) p x < Real.pi) :
    Real.sqrt (1 + η) * Real.cot (Real.sqrt (1 + η) * rdist (I := I) p x)
        * (Inner.inner ℝ V V - (Inner.inner ℝ (rgrad (I := I) (rdist (I := I) p) x) V) ^ 2)
      ≤ rhess cov (rdist (I := I) p) x V V :=
  hess_lower_v2 (I := I) (M := M) cov hmet htor hη hpinch p hsm hunit hlt

end Work.Diff.C

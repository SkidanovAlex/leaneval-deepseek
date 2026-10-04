import Mathlib
import Submission.Work.Diff.C.Defs
import Submission.Work.Diff.C.Setup

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The cut-locus side conditions of the Rauch input of `SphereSizeProp`

`Work.Diff.C.GeoCrux.RauchSphereMapProp` (`geoCrux/RauchDefs.lean`) is proved from the modulus
comparison `Work.Diff.C.jld_modulus_le_sin` applied to the radial variation field
`Z t = curveVelocity (fun r => GExp q (t • (v + r • η))) 0` of the family of rays out of `q`.  Two of
the side conditions of that comparison are *not* calculus: they say that the radial family behaves
like rays in a ball of radius `ρ ≤ π - arccos (1-c)`.

This module isolates them, as a closed `Prop`:

* `hminW` — nearby radial rays are **minimising** up to the radial distance:
  `∀ᶠ s in 𝓝 0, rdist q (GExp q (ρ • (v + s • η))) = ‖ρ • (v + s • η)‖`.
  (This is the hypothesis `hminW` of `Work.Diff.C.dmRadialBridge`, **PROVED** without curvature
  hypotheses, and geometrically it is the statement that a small perturbation of the direction
  `v` does not yet reach the cut locus of `q`.)
* `hne` — the radial variation field **does not vanish** on `(0,ρ)`:
  `∀ t ∈ Ioo 0 ρ, curveVelocity (fun r => GExp q (t • (v + r • η))) 0 ≠ 0`;
  equivalently, `q` has no conjugate point along the ray in direction `v` before time `ρ`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle Set VectorField CovariantDerivative Metric

namespace Work.Diff.C.GeoCrux

/-- **The cut-locus side conditions of the Rauch input.**  For a base point `q`, a unit direction
`v` and an orthogonal direction `η`, and a radius `0 < ρ ≤ π - arccos (1-c)`: the radial family
`r ↦ GExp q (ρ • (v + r • η))` is minimising for `r` near `0`, and the radial variation field
`Z t = curveVelocity (fun r => GExp q (t • (v + r • η))) 0` does not vanish on `(0,ρ)`.

The hypotheses are those of the Rauch input (`hHess` etc. for every centre, `hdiam : diam ≤ π`,
`4 ε₁ π < c`); the conclusion is the pair of side conditions used by
`Work.Diff.C.dmRadialBridge` and `Work.Diff.C.jld_modulus_le_sin`. -/
abbrev RadialCutProp : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {c ε₁ : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 4) (hε₁ : 0 ≤ ε₁)
    (hnum2 : 4 * ε₁ * Real.pi < c)
    (hsmC : ∀ (q y : M), -1 + c ≤ fcos (I := I) (M := M) q y →
      CMDiffAt ∞ (fcos (I := I) (M := M) q) y)
    (hHess : ∀ q : M, HessBoundRegion (I := I) (M := M) cov c ε₁ (fcos (I := I) (M := M) q))
    (hcont : ∀ q : M, Continuous (fcos (I := I) (M := M) q))
    (hgrad : ∀ (q y : M), -1 + c < fcos (I := I) (M := M) q y →
      Inner.inner ℝ (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y)
        (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y)
        = 1 - (fcos (I := I) (M := M) q y) ^ 2)
    (hdiam : ∀ x y : M, rdist (I := I) (M := M) x y ≤ Real.pi),
    ∀ (q : M) (v η : TangentSpace I q), Inner.inner ℝ v v = 1 →
      Inner.inner ℝ v η = 0 → η ≠ 0 →
    ∀ ρ : ℝ, 0 < ρ → ρ ≤ Real.pi - Real.arccos (1 - c) →
      (∀ᶠ s in 𝓝 (0 : ℝ),
        rdist (I := I) (M := M) q
            (Submission.GlobalExp.GExp (cov := cov) hmet q (ρ • (v + s • η)))
          = ‖ρ • (v + s • η)‖)
      ∧ (∀ t ∈ Set.Ioo (0 : ℝ) ρ,
          Submission.Geodesic.curveVelocity (I := I) (M := M)
            (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (t • (v + r • η))) 0
            ≠ 0)

end Work.Diff.C.GeoCrux

import Mathlib
import Submission.Work.Diff.C.geoCrux.RauchInputDefs
import Submission.CutStep3
import Submission.SingularConj
import Submission.Work.Diff.C.no_conjTime_le_arccos
import Submission.Work.Diff.C.geoCrux.RadialKit
import Submission.Work.Diff.C.dmRadialBridge
import Submission.Work.Diff.C.ray_minimising_near_perturbation
import Submission.GExpLocalInj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The closed `Prop`s of the `CutInjectProp` argument

`Work.Diff.C.GeoCrux.CutInjectProp` (`geoCrux/RauchInputDefs.lean`) says that the exponential map at
every point `q` is injective on the ball of radius `ρ₀ = π - arccos (1-c)`.  Its proof (in
`geoCrux/cut_inject.lean`) runs the classical cut-point analysis with `m` the **maximal** injectivity
radius at `q`:

* the **two-minimising** alternative of Klingenberg's lemma
  (`Submission.CutStep3.exists_two_minimising_of_hloc_sphere`) is excluded by the chain rule at the
  common endpoint (`TwoMinKillProp`), and
* the **local-injectivity** input is the non-conjugacy statement `NoConjAtInjProp`, the classical
  Sturm comparison `Work.Diff.C.no_conjTime_le_arccos` applied to the radial variation field of the
  ray (`J m = 0` would be a conjugate time at `m ≤ ρ₀ < π`, which the two-sided shape-operator bound
  `Work.Diff.C.rhess_rdist_bound_of_hHess` forbids).

The two statements are packaged here as closed `Prop`-valued `abbrev`s, written with all the `open`s
of the area active — following `geoCrux/Defs.lean` — so that their proofs can be delegated to a file
that only imports this module (the delegation harness elaborates a submitted statement in a bare
context, without `open`s).

## The two statements

* `TwoMinKillProp` — two distinct minimising vectors of norm `m`, `m < ρ₀`, with the same image
  cannot exist.  Route: `Work.Diff.C.GeoCrux.false_of_two_minimising`, whose inputs are the
  smoothness of `rdist q` at the common endpoint (`Work.Diff.C.GeoCrux.rdist_smooth_eikonal`, since
  the endpoint is strictly inside the ball of radius `ρ₀`) and the unit-gradient identity
  `Work.Diff.C.rgrad_rdist_eikonal`.

* `NoConjAtInjProp` — for a unit `ξ` and `η ⊥ ξ`, `η ≠ 0`, and `m` below the injectivity radius and
  below `ρ₀`, the radial variation field `J s = ∂_r GExp q (s • (ξ + r • η))|_0` does **not** vanish
  at time `m`.  Route: `J 0 = 0`, `J ≢ 0` near `0`
  (`Submission.SingularConj.exists_pos_variation_ne_zero`), the Gauss pairing
  `⟪J s, γ'(s)⟫ = s ⟪η, ξ⟫` (`Work.Diff.C.ShapeAux.gauss_pairing_scalar`), the bridge
  `⟪∇_s J, J⟫ = Hess (rdist q) (J,J)` (`Work.Diff.C.dmRadialBridge`, which needs `J ≠ 0`, the
  minimisation of the perturbed rays coming from `InjAtLeast`) and the shape-operator bound
  `Work.Diff.C.rhess_rdist_bound_of_hHess`; then `Work.Diff.C.no_conjTime_le_arccos` applied on the
  interval `(0, t₀)` where `t₀` is the **first** zero of `J`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle Set VectorField CovariantDerivative Metric

namespace Work.Diff.C.geoCrux

/-- **No conjugate time of a radial variation family below `π - arccos (1-c)`.**

Let `m` be a radius at which the exponential map at `q` is injective (`0 < m < ρ₀`), let `ξ` be a
unit vector at `q` and `η ≠ 0` a vector orthogonal to `ξ`.  Then the radial variation field

`J s := ∂_r GExp q (s • (ξ + r • η)) |_{r=0}`

of the family of rays out of `q` **does not vanish at time `m`**.

This is the classical "no conjugate point below the conjugate radius" statement: the shape operator
of the geodesic spheres satisfies `|Hess (rdist q) - cot t · g| ≤ ε₁ / sin t` on the region
`{fcos q > -1 + c}` (`Work.Diff.C.rhess_rdist_bound_of_hHess`), and the Sturm comparison
`Work.Diff.C.no_conjTime_le_arccos` — applied to `⟪J, J⟫` on the interval between the first zero of
`J` (which is `> 0` by `Submission.SingularConj.exists_pos_variation_ne_zero`) and `m` — excludes a
vanishing of `J` at any time `≤ π - arccos (1-c)`. -/
abbrev NoConjAtInjProp : Prop :=
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
    (hdiam : ∀ x y : M, rdist (I := I) (M := M) x y ≤ Real.pi)
    {q : M} {m : ℝ} (hm0 : 0 < m) (hmρ : m < Real.pi - Real.arccos (1 - c))
    (hinj : Submission.InjRadius.InjAtLeast (I := I) hmet q m)
    {ξ η : TangentSpace I q} (hξ : ‖ξ‖ = 1) (hη : η ≠ 0)
    (horth : Inner.inner ℝ ξ η = 0)
    (hJm : Submission.Geodesic.curveVelocity (I := I) (M := M)
      (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (m • (ξ + r • η))) 0 = 0) ,
    False

/-- **Two distinct minimising rays of length `m < π - arccos (1-c)` cannot end at the same point.**

Both are minimising, so they both arrive with the gradient of `rdist q`, which is a unit vector and
`C^∞` at the common endpoint (the endpoint is strictly inside the ball of radius `ρ₀`); two
geodesics with the same position and velocity coincide. -/
abbrev TwoMinKillProp : Prop :=
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
    (hdiam : ∀ x y : M, rdist (I := I) (M := M) x y ≤ Real.pi)
    {q : M} {m : ℝ} (hm0 : 0 < m) (hmρ : m < Real.pi - Real.arccos (1 - c))
    {u v : TangentSpace I q} (huv : u ≠ v)
    (hG : Submission.GlobalExp.GExp (cov := cov) hmet q u
      = Submission.GlobalExp.GExp (cov := cov) hmet q v)
    (hun : ‖u‖ = m) (hvn : ‖v‖ = m)
    (hminu : Manifold.riemannianEDist I q (Submission.GlobalExp.GExp (cov := cov) hmet q u)
      = ENNReal.ofReal m) ,
    False


end Work.Diff.C.geoCrux

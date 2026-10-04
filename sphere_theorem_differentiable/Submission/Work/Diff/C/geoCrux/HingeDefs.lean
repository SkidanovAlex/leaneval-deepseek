import Mathlib
import Submission.Work.Diff.C.Defs
import Submission.Work.Diff.C.Setup
import Submission.Work.Diff.C.rgrad_fcos_eikonal
import Submission.Work.Diff.C.gp_ode_compare
import Submission.Work.Diff.C.geoCrux.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The hinge-cosine bound: the free half, and the hard half isolated

`Work.Diff.C.GeoCrux.HingeCosProp` (in `Submission/Work/Diff/C/geoCrux/FarDefs.lean`) states, for a
unit-speed ray `σ ↦ GExp x (σ • u)` and a centre `y`,

`cos (rdist y (γ s)) ≥ cos (rdist x y + s) - 40 (c + ε₁ π)`  (`0 ≤ s ≤ π`).

This module splits it into its two regimes and **proves the first one outright**:

* `hinge_cos_easy` — the regime `rdist x y + s ≤ π`: here the *triangle inequality* alone gives
  `rdist y (γ s) ≤ rdist x y + s` (with `rdist x (GExp x (s • u)) ≤ s`, the standard length bound
  `eik_rdist_GExp_smul_le`), and `Real.cos` is decreasing on `[0, π]`, so the conclusion holds with
  no correction at all.  No curvature input is used.

* `HingeCosHardProp` — the regime `π < rdist x y + s`, packaged as a closed `Prop` so that it can be
  delegated.  Here the triangle inequality is *anti*-monotone and the statement says the opposite
  bound: since `Real.cos` is increasing on `[π, 2π]` and `rdist y (γ s) ≤ rdist x y + s ≤ 2π`, the
  claim `cos (rdist y (γ s)) ≥ cos (rdist x y + s) - 40 (c + ε₁ π)` is equivalent (up to the slack)
  to `rdist y (γ s) ≤ 2π - rdist x y - s`, i.e. to the *perimeter* statement
  `rdist x y + rdist y (γ s) + rdist x (γ s) ≤ 2π + O(·)` for the triangle `(x, y, γ s)` — the
  classical "perimeter `≤ 2π`" half of the comparison theorem at `sec ≥ 1`.

Route for the hard half (as in `FarDefs.lean`): `h := cos ∘ rdist y ∘ γ` satisfies `h'' + h ≥ -ε₁`
on the region where `fcos y (γ σ) > -1 + c` (this is `hHess` pulled back to the ray, using
`Work.Diff.C.rhess_comp` for `Real.cos`), with `h(0) = cos (rdist x y)` and `|h'(0)| ≤ 1`; so `h` is
an approximate sinusoid of amplitude `≤ 1`, and the claim is that it is in phase with the model
`σ ↦ cos (rdist x y + σ)` up to `O(c + ε₁π)` at the time `s`.  The span of the ray inside the
antipodal cap `{rdist y · ≥ π - c}` is the only place where the ODE is unavailable; it is bounded by
`Work.Diff.C.GeoCrux.SphereSizeProp` (delegated, `FarDefs.lean`), and the phase bookkeeping across
it costs `O(c + ε₁π)`.
-/

set_option linter.unusedSectionVars false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle Set VectorField CovariantDerivative Metric

namespace Work.Diff.C.GeoCrux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M]
  {cov : CovariantDerivative I E (TangentSpace I (M := M))}
  [ContMDiffCovariantDerivative cov ∞]

/-- **The hinge-cosine bound in the regime `rdist x y + s ≤ π`** — the *free* half.

`rdist y (GExp x (s • u)) ≤ rdist x y + s` by the triangle inequality (the ray has length at most
`s`: `eik_rdist_GExp_smul_le`), both sides lie in `[0, π]`, and `Real.cos` is decreasing there, so

`cos (rdist y (γ s)) ≥ cos (rdist x y + s)`.

In particular `HingeCosProp` holds in this regime with error `0` (the stated slack `40 (c + ε₁ π)` is
not needed).  No smoothness, Hessian or eikonal hypothesis enters. -/
theorem hinge_cos_easy
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {c ε₁ : ℝ} (hc : 0 < c) (hε₁ : 0 ≤ ε₁)
    (x y : M) {u : TangentSpace I x} {s : ℝ}
    (hu : Inner.inner ℝ u u = 1) (hs0 : 0 ≤ s)
    (hle : rdist (I := I) (M := M) x y + s ≤ Real.pi)
    (hdiam : rdist (I := I) (M := M) y
        (Submission.GlobalExp.GExp (cov := cov) hmet x (s • u)) ≤ Real.pi) :
    Real.cos (rdist (I := I) (M := M) y
        (Submission.GlobalExp.GExp (cov := cov) hmet x (s • u)))
      ≥ Real.cos (rdist (I := I) (M := M) x y + s) - 40 * (c + ε₁ * Real.pi) := by
  have hu' : ‖u‖ = 1 := by
    have h : ‖u‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq u]; exact hu
    nlinarith [norm_nonneg u]
  -- the ray has length at most `s`
  have hray : rdist (I := I) (M := M) x
      (Submission.GlobalExp.GExp (cov := cov) hmet x (s • u)) ≤ s := by
    have h := eik_rdist_GExp_smul_le (I := I) (M := M) (cov := cov) hmet x u hs0
    rwa [hu', mul_one] at h
  have htri := eik_rdist_triangle_le (I := I) (M := M) (cov := cov) hmet htor y x
    (Submission.GlobalExp.GExp (cov := cov) hmet x (s • u))
  have hcomm : rdist (I := I) (M := M) y x = rdist (I := I) (M := M) x y := by
    rw [rdist, rdist, Manifold.riemannianEDist_comm]
  have hB : rdist (I := I) (M := M) y
      (Submission.GlobalExp.GExp (cov := cov) hmet x (s • u))
      ≤ rdist (I := I) (M := M) x y + s := by linarith
  have hcos : Real.cos (rdist (I := I) (M := M) x y + s)
      ≤ Real.cos (rdist (I := I) (M := M) y
          (Submission.GlobalExp.GExp (cov := cov) hmet x (s • u))) := by
    refine Real.cos_le_cos_of_nonneg_of_le_pi ?_ hle hB
    rw [rdist]; exact ENNReal.toReal_nonneg
  have hslack : 0 ≤ 40 * (c + ε₁ * Real.pi) := by
    have h1 : 0 ≤ c := le_of_lt hc
    have h2 : 0 ≤ ε₁ * Real.pi := mul_nonneg hε₁ (le_of_lt Real.pi_pos)
    nlinarith
  linarith

abbrev HingeCosHardProp : Prop :=
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
    ∀ (x y : M) (u : TangentSpace I x) (s : ℝ),
      Inner.inner ℝ u u = 1 → 0 ≤ s → s ≤ Real.pi →
      Real.pi < rdist (I := I) (M := M) x y + s →
      Real.cos (rdist (I := I) (M := M) y
          (Submission.GlobalExp.GExp (cov := cov) hmet x (s • u)))
        ≥ Real.cos (rdist (I := I) (M := M) x y + s)
          - 40 * (c + ε₁ * Real.pi)

end Work.Diff.C.GeoCrux

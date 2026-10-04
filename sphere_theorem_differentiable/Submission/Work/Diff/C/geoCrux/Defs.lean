import Mathlib
import Submission.Work.Diff.C.Defs
import Submission.Work.Diff.C.Setup
import Submission.Work.Diff.C.psi_estimates
import Submission.Work.Diff.C.init_data
import Submission.Work.Diff.C.gram_along
import Submission.Work.Diff.C.gram_along_pair
import Submission.Work.Diff.C.ray_model_stay
import Submission.Work.Diff.C.dip_model_through

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The geometric core of the classical endgame: statement wrappers

The delegated lemmas of the "bad branch" of `Work.Diff.C.gram_pointwise2` need to be *stated* against
the whole Riemannian-bundle vocabulary (`fcos`, `rdist`, `rgrad`, `HessBoundRegion`, `InitData`, …).
The delegation harness elaborates a submitted statement in a file that contains only the modules
listed in `depends_on` and **no `open` commands**; in that bare context the binders of the form
`[IsContMDiffRiemannianBundle … (fun x ↦ TangentSpace I x)]`, and even the instance
`Inner ℝ (TangentSpace I y)`, are not found — they live behind the `Bundle` scope (verified: the
same statement compiles as soon as `open Bundle` is present).

This module therefore packages the statements of the delegated lemmas as **closed `abbrev`s**
(`Prop`-valued), written here with all the `open`s active, so that a submitted statement
`theorem name : Work.Diff.C.GeoCrux.<Prop> := by sorry` elaborates in the bare context.  Because
they are `abbrev`s they unfold definitionally: `intro` (possibly repeated) turns the goal into the
familiar form with one hypothesis per binder.

## Piece 1: `PerimeterBoundProp`

The **perimeter bound** (classical for `sec ≥ 1`): if for *every* centre `q` the function
`fcos q = cos ∘ d(q,·)` is smooth and continuous on the region `{fcos q > -1 + c}`, satisfies there
`|Hess fcos q + (fcos q)·g| ≤ ε₁` (`HessBoundRegion`) and the eikonal identity
`|∇ fcos q|² = 1 - (fcos q)²` (`hgrad`), and if moreover `diam ≤ π` (`hdiam2`) and `4 ε₁ π < c`,
then every geodesic triangle has perimeter at most `2π + 20 (√c + ε₁ π)`.

Unwrapped, the statement is

```
theorem perimeter_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {α c ε₁ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1/4) (hc : 0 < c) (hc1 : c ≤ 1/4)
    (hε₁ : 0 ≤ ε₁) (hnum1 : 3*c ≤ 1 - Real.cos α) (hnum2 : 4*ε₁*Real.pi < c)
    (hdiam2 : ∀ x y, rdist x y ≤ Real.pi)
    (hsmC : ∀ q y, -1 + c ≤ fcos q y → CMDiffAt ∞ (fcos q) y)
    (hHess : ∀ q, HessBoundRegion cov c ε₁ (fcos q))
    (hcont : ∀ q, Continuous (fcos q))
    (hgrad : ∀ q y, -1 + c < fcos q y → ⟪∇(fcos q) y, ∇(fcos q) y⟫ = 1 - (fcos q y)^2) :
    ∀ x y z, rdist x y + rdist y z + rdist z x ≤ 2*π + 20*(√c + ε₁*π)
```

This is the single geometric input of the bad branch: applied to the triangle `(p, q_k, γ τ)` with
`rdist p q_k = π/2` it gives the *dip location* `τ ≤ π/2 + O(√c + ε₁π)` at every time `τ` where
`fcos q_k (γ τ) ≤ -1 + c`.

## Piece 2: `GramShiftedProp`

The **shifted Gram comparison**: along the unit-speed ray `γ σ = GExp p (σ • u)`, if two of the
functions `Fᵢ = ψ ∘ fFam hmet p e i` stay in the smooth region `f > -1 + 2c` on the sub-interval
`[a,s]`, then `gp Fᵢ Fⱼ = ⟪∇Fᵢ,∇Fⱼ⟫ + Fᵢ Fⱼ` changes by at most `2 ε₁ (s-a)` between `γ a` and
`γ s`.  This is `Work.Diff.C.gram_along_pair` with `[0,s]` replaced by `[a,s]`; route:
`Work.Diff.C.gram_deriv_along` (`Diff/C/gram_along.lean`, PROVED) gives the derivative
`d/dτ gp Fᵢ Fⱼ (γ τ) = gval cov Fᵢ Fⱼ γ τ` pointwise, `Work.Diff.C.gram_deriv_bound` (PROVED) bounds
it by `2ε₁`, and the mean value theorem on `[a,s]` finishes — with
`Work.Diff.C.psi_comp_eq_self'` (`Diff/C/gram_along_pair.lean`, PROVED) providing
`rgrad (ψ∘f) = rgrad f`, `rhess (ψ∘f) = rhess f` on the region `f ≥ -1+2c`
(`Work.Diff.C.psi_deriv_good` gives `deriv ψ = 1`, `iteratedDeriv 2 ψ = 0` there).
-/

namespace Work.Diff.C.GeoCrux

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle Set VectorField CovariantDerivative Metric

/-- **The perimeter bound** (the statement is described in the module docstring). -/
abbrev PerimeterBoundProp : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {α c ε₁ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hc : 0 < c) (hc1 : c ≤ 1 / 4)
    (hε₁ : 0 ≤ ε₁) (hnum1 : 3 * c ≤ 1 - Real.cos α) (hnum2 : 4 * ε₁ * Real.pi < c)
    (hdiam2 : ∀ x y : M, rdist (I := I) (M := M) x y ≤ Real.pi)
    (hsmC : ∀ (q y : M), -1 + c ≤ fcos (I := I) (M := M) q y →
      CMDiffAt ∞ (fcos (I := I) (M := M) q) y)
    (hHess : ∀ q : M, HessBoundRegion (I := I) (M := M) cov c ε₁ (fcos (I := I) (M := M) q))
    (hcont : ∀ q : M, Continuous (fcos (I := I) (M := M) q))
    (hgrad : ∀ (q y : M), -1 + c < fcos (I := I) (M := M) q y →
      Inner.inner ℝ (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y)
        (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y)
        = 1 - (fcos (I := I) (M := M) q y) ^ 2),
    ∀ x y z : M,
      rdist (I := I) (M := M) x y + rdist (I := I) (M := M) y z + rdist (I := I) (M := M) z x
        ≤ 2 * Real.pi + 20 * (Real.sqrt c + ε₁ * Real.pi)

/-- **The shifted Gram comparison** (the statement is described in the module docstring). -/
abbrev GramShiftedProp : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {c ε₁ : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 4) (hε₁ : 0 ≤ ε₁)
    {p : M} {e : Fin (Module.finrank ℝ E) → TangentSpace I p}
    (hON : ∀ i j, Inner.inner ℝ (e i) (e j) = if i = j then 1 else 0)
    (hsmC : ∀ (q y : M), -1 + c ≤ fcos (I := I) (M := M) q y →
      CMDiffAt ∞ (fcos (I := I) (M := M) q) y)
    (hHess : ∀ q : M, HessBoundRegion (I := I) (M := M) cov c ε₁ (fcos (I := I) (M := M) q))
    (hcont : ∀ q : M, Continuous (fcos (I := I) (M := M) q))
    (hgrad : ∀ (q y : M), -1 + c < fcos (I := I) (M := M) q y →
      Inner.inner ℝ (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y)
        (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y)
        = 1 - (fcos (I := I) (M := M) q y) ^ 2)
    (hinit : InitData (I := I) (M := M) (cov := cov) hmet p e)
    {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ ∧ Monotone ψ ∧
      (∀ t : ℝ, 0 ≤ deriv ψ t ∧ deriv ψ t ≤ 2) ∧
      (∀ t : ℝ, -1 + 2 * c ≤ t → ψ t = t) ∧ (∀ t : ℝ, t ≤ -1 + c → ψ t = -1 + c))
    {u : TangentSpace I p} {s a : ℝ} (hu : Inner.inner ℝ u u = 1)
    (ha0 : 0 ≤ a) (has : a ≤ s)
    (i j : Fin (Module.finrank ℝ E + 1))
    (hstay : ∀ σ ∈ Set.Icc a s,
      -1 + 2 * c ≤ fFam (I := I) (M := M) (cov := cov) hmet p e i
          (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u)) ∧
      -1 + 2 * c ≤ fFam (I := I) (M := M) (cov := cov) hmet p e j
          (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u))),
    |gp (I := I) (M := M)
        (fun y : M => ψ (fFam (I := I) (M := M) (cov := cov) hmet p e i y))
        (fun y : M => ψ (fFam (I := I) (M := M) (cov := cov) hmet p e j y))
        (Submission.GlobalExp.GExp (cov := cov) hmet p (s • u))
      - gp (I := I) (M := M)
        (fun y : M => ψ (fFam (I := I) (M := M) (cov := cov) hmet p e i y))
        (fun y : M => ψ (fFam (I := I) (M := M) (cov := cov) hmet p e j y))
        (Submission.GlobalExp.GExp (cov := cov) hmet p (a • u))|
      ≤ 2 * ε₁ * (s - a)

end Work.Diff.C.GeoCrux

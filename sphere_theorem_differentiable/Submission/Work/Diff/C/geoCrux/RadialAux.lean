import Mathlib
import Submission.Work.Diff.C.geoCrux.RadialKit
import Submission.Work.Diff.C.geoCrux.cutTime_ge
import Submission.Work.Diff.C.dmRadialBridge
import Submission.Work.Diff.C.no_conjTime_le_arccos

/-!
# Auxiliary statements for `Work.Diff.C.GeoCrux.RadialCutProp`

This module collects, as closed `Prop`s, the three auxiliary statements out of which
`Work.Diff.C.geoCrux.radial_cut` (`RadialCutProp`) is assembled.  They are stated here (in the bare
namespace context of the delegation harness) so that they can be proved in parallel; all of them
import only this module.

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

* `RdistMinProp` — the distance function is `C^∞` **on the closed ball** of radius
  `ρ₀ = π - arccos (1-c)`, with unit gradient there.  (The strict form, for `rdist < ρ₀`, is
  `Work.Diff.C.GeoCrux.RdistSmoothProp`/`Work.Diff.C.rgrad_rdist_eikonal`.)
* `RadialVariationProp` — **(the second half of `RadialCutProp`)** the radial variation field of the
  family of rays out of `q` never vanishes before `ρ₀`: this is the classical "no conjugate point
  below `π - arccos (1-c)`" statement in the exact form in which `RadialCutProp` needs it.
* `RadialConjOfSingularProp` — a *sharpened* form of `Submission.ConjCut.SingularImpConjTime`: a
  singular differential of `GExp q` at `v ≠ 0` produces a **radial variation field** (not just an
  abstract Jacobi field) vanishing at time `‖v‖`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle Set VectorField CovariantDerivative Metric

namespace Work.Diff.C.GeoCrux

/-- **The distance function is smooth and eikonal on the closed ball of radius `π - arccos (1-c)`.**

If `u ≠ 0` has `‖u‖ ≤ ρ₀` and the ray of `u` is minimising
(`riemannianEDist q (GExp q u) = ofReal ‖u‖`), then `rdist q` is `C^∞` at `GExp q u` and its
gradient is a unit vector there.

Route.  Write `ξ := unitOf u` (`‖ξ‖ = 1`) and `t := ‖u‖`, so `u = t • ξ`.

* the ray is minimising at every earlier time: `Submission.CutTime.edist_GExp_smul_eq_of_le_of_eq`
  applied to the hypothesis `hmin` gives
  `riemannianEDist q (GExp q (s • ξ)) = ofReal s` for `0 ≤ s ≤ t`;
* hence `rdist q (GExp q u) = t` and `fcos q (GExp q u) = cos t ≥ -1 + c`
  (`Real.cos_le_cos_of_nonneg_of_le_pi`, `Real.cos (π - arccos (1-c)) = -1 + c`);
* **smoothness**: `rdist q = arccos ∘ fcos q` near `GExp q u` (both in `(0,π)` there), `fcos q` is
  `C^∞` at `GExp q u` by `hsmC`, so `CMDiffAt ∞ (rdist q)` follows with
  `Real.contDiffAt_arccos` (same proof as `Work.Diff.C.GeoCrux.rdist_smooth_eikonal`, but with the
  weaker hypothesis `-1+c ≤ fcos` and `rdist < π` supplied from `t ≤ ρ₀ < π`);
* **eikonal at the endpoint**: for `s < t` we have `0 < rdist q (GExp q (s • ξ)) = s < ρ₀`, so
  `hgrad` gives `⟪∇(fcos q), ∇(fcos q)⟫ = 1 - cos²`, hence (via `Work.Diff.C.rgrad_fcos`)
  `⟪∇(rdist q), ∇(rdist q)⟫ = 1` at `GExp q (s • ξ)`; passing to the limit `s → t⁻` using the
  continuity of `rgrad (rdist q)` at `GExp q u` (from the smoothness just proved, via
  `Work.Diff.C.grad_smoothAt`) and `GExp q (s • ξ) → GExp q (t • ξ)` gives the eikonal at
  `GExp q u`.  (The pointwise statement "on the region `{0 < rdist q · < ρ₀}` the eikonal holds" is
  the proof of `Work.Diff.C.GeoCrux.eventually_eikonal_rdist`, in `cutTime_ge.lean`.) -/
abbrev RdistMinProp : Prop :=
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
    {q : M} {u : TangentSpace I q} (hu : u ≠ 0)
    (hρ : ‖u‖ ≤ Real.pi - Real.arccos (1 - c))
    (hmin : Manifold.riemannianEDist I q
      (Submission.GlobalExp.GExp (cov := cov) hmet q u) = ENNReal.ofReal ‖u‖),
    CMDiffAt ∞ (fun z : M ↦ rdist (I := I) (M := M) q z)
        (Submission.GlobalExp.GExp (cov := cov) hmet q u) ∧
      Inner.inner ℝ
        (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z)
          (Submission.GlobalExp.GExp (cov := cov) hmet q u))
        (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z)
          (Submission.GlobalExp.GExp (cov := cov) hmet q u)) = 1

/-- **The radial variation field does not vanish before `ρ₀`.**

Assume that every ray out of `q` is minimising up to `ρ₀ = π - arccos (1-c)`
(`hcut : ∀ ξ, ‖ξ‖ = 1 → ρ₀ ≤ cutTime hmet q ξ`).  Then for a unit `v`, a vector `η ⊥ v` with
`η ≠ 0` and every `0 < d ≤ ρ₀`, the radial variation field

`J d = curveVelocity (fun r ↦ GExp q (d • (v + r • η))) 0`

does not vanish.  Equivalently: `q` has no conjugate point along the ray of `v` before `ρ₀`.

Route (all inputs proved).  Prove `J d ≠ 0` by contradiction, using the classical Sturm comparison
`Work.Diff.C.no_conjTime_le_arccos` (in `Submission/Work/Diff/C/no_conjTime_le_arccos.lean`) with
`L := ρ₀` (`ρ₀ < π`), `u := v`, `d := d` and `J` the variation field.  Its hypotheses:

* `hJ : ∀ t, IsJacobiAt cov γ J t` — `Submission.RayJacobi.isJacobiAt_GExp_variation`
  (needs `‖v‖ = 1`, `v ≠ 0`);
* `hJ0 : J 0 = 0` — `Work.OddBound.longHomotopy.variation_zero_at_zero`;
* `hJd : J d = 0` — the contradiction hypothesis;
* `hne : ∃ s ∈ Ioo 0 d, J s ≠ 0` — `Submission.SingularConj.exists_pos_variation_ne_zero`
  (needs `η ≠ 0`) gives one on `(0, δ)`; take `min δ d / 2`;
* `hperp : ∀ t ∈ Ioo 0 d, ⟪J t, ∇(rdist q)(γ t)⟫ = 0` — `Work.Diff.C.ShapeAux.gauss_pairing_scalar`
  gives `⟪J t, γ'(t)⟫ = t * ⟪η, v⟫ = 0` (curvature-free!), and `∇(rdist q)(γ t) = γ'(t)` because the
  ray is minimising at `t ≤ d ≤ ρ₀`: `Submission.CutTime.mem_minimisingSet_iff` with `hcut` (note
  `⟪v,v⟫ = 1` gives `‖v‖ = 1`) plus `Work.Diff.C.curveVelocity_GExp_eq_smul_rgrad` (which needs the
  eikonal `Work.Diff.C.rgrad_rdist_eikonal` at `γ t` and the smoothness
  `Work.Diff.C.GeoCrux.rdist_smooth_eikonal`);
* `hbridge : ∀ t ∈ Ioo 0 d, ⟪covAlong J t, J t⟫ = rhess (rdist q)(γ t)(J t)(J t)` — case split on
  `J t = 0`: then both sides vanish; otherwise `Work.Diff.C.dmRadialBridge` (with `p := q`,
  `d := t`, `u := v`, `η := η`, its `hne` being the case hypothesis).  `dmRadialBridge`'s remaining
  hypotheses: `⟪u,u⟫ = 1`, `⟪u,η⟫ = 0`, `hsm` = smoothness of `rdist q` at `GExp q (t • v)` (from
  `Work.Diff.C.GeoCrux.rdist_smooth_eikonal`, since `0 < rdist q (GExp q (t • v)) = t < ρ₀`),
  `hrgrad = γ'(t)` (`Work.Diff.C.curveVelocity_GExp_eq_smul_rgrad`), `hcsm` = `ContMDiff` of
  `s ↦ GExp q (t • (v + s • η))` (`Submission.GExpSmooth.exists_contMDiffAt_GExp` gives
  `ContMDiffAt` at every point of the line, hence `ContMDiff`),
  and `hminW : ∀ᶠ s, rdist q (GExp q (t • (v + s • η))) = ‖t • (v + s • η)‖` (for `s` near `0`,
  `t * ‖v + s • η‖ < ρ₀`, and `t • (v + s • η) = T • w` with `w` unit, `T = t*‖v+s•η‖ ≤ ρ₀`, so
  `Submission.CutTime.mem_minimisingSet_iff` + `hcut` give the minimising property, converted to
  `rdist` with `ENNReal.toReal_ofReal`);
* `hshape : ∀ t ∈ Ioo 0 d, (cot t - ε₁/sin t) * ⟪J t, J t⟫ ≤ rhess (rdist q)(γ t)(J t)(J t)` — from
  `Work.Diff.C.rhess_rdist_bound_of_hHess` with `V := J t`: it needs `-1 + c < fcos q (γ t)`
  (⟺ `rdist q (γ t) = t < ρ₀`), the smoothness and `0 < rdist < π` just discussed, and the
  orthogonality `⟪∇(fcos q)(γ t), J t⟫ = 0`, which follows from `Work.Diff.C.rgrad_fcos` and
  `hperp`.  (Also `Real.cot`/`Real.sin` of `rdist q (γ t) = t`.) -/
abbrev RadialVariationProp : Prop :=
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
    {q : M}
    (hcut : ∀ ξ : TangentSpace I q, ‖ξ‖ = 1 →
      Real.pi - Real.arccos (1 - c) ≤ Submission.CutTime.cutTime (I := I) hmet q ξ)
    (v η : TangentSpace I q) (hv : Inner.inner ℝ v v = 1)
    (horth : Inner.inner ℝ v η = 0) (hη : η ≠ 0)
    (d : ℝ) (hd0 : 0 < d) (hdρ : d ≤ Real.pi - Real.arccos (1 - c)),
    Submission.Geodesic.curveVelocity (I := I) (M := M)
      (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (d • (v + r • η))) 0 ≠ 0

/-- **A singular differential of `GExp q` produces a vanishing *radial variation* field.**

This is the sharpening of `Submission.SingularConj.singular_imp_conjTime` needed by the
cut-locus argument of `radial_cut`: from `¬ (d GExp q)_v` invertible (`v ≠ 0`) it produces
`η ≠ 0` such that the **radial variation field** out of `q` in the direction `unitOf v` with
parameter `η` vanishes at time `‖v‖`:

`curveVelocity (fun r ↦ GExp q (‖v‖ • (unitOf v + r • η))) 0 = 0`.

Route.  `Submission.RayConj.exists_ne_zero_apply_eq_zero` gives `ξ ≠ 0` with
`(d GExp q)_v (ξ) = 0`.  Put `η := ‖v‖⁻¹ • ξ` (so `‖v‖ • η = ξ`, `η ≠ 0`).  The field
`J s = curveVelocity (fun r ↦ GExp q (s • (unitOf v + r • η))) 0` is a Jacobi field
(`Submission.RayJacobi.isJacobiAt_GExp_variation`), satisfies `J 0 = 0`
(`Work.OddBound.longHomotopy.variation_zero_at_zero` or `curveVelocity_congr` with the constant
curve) and `J ‖v‖ = 0` by the chain rule
(`Submission.ChartGeoAt.curveVelocity_eq_mfderiv_comp`, `Submission.GExpLocalInj.contMDiffAt_GExp_one`,
and `‖v‖ • η = ξ` with `(d GExp q)_v(ξ) = 0`); `‖v‖ • (unitOf v) = v` by
`Submission.GlobalExp.unitOf`.  This is *verbatim* the proof of
`Submission.SingularConj.singular_imp_conjTime` (`Submission/SingularConj.lean`, section 6), which
constructs exactly this field and then only records the `IsConjugateTime`; the only change needed
is to return the field's vanishing at `‖v‖` instead of packing it into `IsConjugateTime`.  Copy
that proof (it needs `Submission.RayConj.exists_ne_zero_apply_eq_zero`,
`Submission.RayJacobi.isJacobiAt_GExp_variation`, `Submission.RayJacobi.curveVelocity_congr`,
`Submission.GeodesicExtend.curveVelocity_const`,
`Submission.ChartGeoAt.curveVelocity_eq_mfderiv_comp`,
`Submission.GExpLocalInj.contMDiffAt_GExp_one`) and state the conclusion as above. -/
abbrev RadialConjOfSingularProp : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {q : M} {v : TangentSpace I q} (hv : v ≠ 0)
    (hsing : ¬ (mfderiv 𝓘(ℝ, E) I
      (fun u : E => Submission.GlobalExp.GExp (cov := cov) hmet q (show TangentSpace I q from u))
      (show E from v)).IsInvertible),
    ∃ η : TangentSpace I q, η ≠ 0 ∧
      Submission.Geodesic.curveVelocity (I := I) (M := M)
        (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q
          (‖v‖ • (Submission.GlobalExp.unitOf v hv + r • η))) 0 = 0

end Work.Diff.C.GeoCrux

/-
# `RiemLib/API.lean` — the interface of the vendored Riemannian-geometry library

Area `Submission/Work/RiemLib/` (area RL) hosts the *vendored* Riemannian-geometry library: the
import closure of the modules used by the sphere-theorem development.  This file is the **re-export
list for the Cartan–Hadamard area (CH)**: it imports the modules CH uses, records the exact
signature of every declaration CH may need in the `#check` block below (the build verifies that all
of them exist with those names), and supplies the small amount of glue the CH interface needs
(`namespace Work.RiemLib`).

## How CH should use this area

    import Submission.Work.RiemLib.All       -- or, to get only the interface: RiemLib/API.lean
    open scoped Manifold ContDiff Bundle Topology ENNReal
    open Bundle CovariantDerivative

`Submission.Work.RiemLib.API` imports every module listed below, so a caller of CH never has to
reach past this file.  Nothing here is specialized to the sphere theorem's pinching hypothesis:
the comparison theorems are parametric in an *upper* bound `sec ≤ K`, which is exactly what a
non-positively-curved `M̂` provides (take `K` arbitrarily large; see `Work.RiemLib.CurvLe_of_nonpos`
and `Work.RiemLib.exists_lt_pi_div_sqrt` at the end of this file).

## The framework (the variable block every theorem below assumes)

```
{E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
{H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
{M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
[RiemannianBundle (fun x : M ↦ TangentSpace I x)]
[IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
[I.Boundaryless] [Nontrivial E] [CompactSpace M]
{cov : CovariantDerivative I E (TangentSpace I (M := M))}
[ContMDiffCovariantDerivative cov ∞]
```

`cov` is the Levi-Civita connection, *hypothesized*: a smooth torsion-free metric-compatible
covariant derivative.  The two hypotheses that carry the geometry are

* `hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov`  (`RiemLib/SphereDeps.lean`), and
* `htor : cov.torsion = 0`.

## `sec ≤ K` for non-positive curvature: `CurvLe`

```
def Submission.RauchK.CurvLe (cov) (K : ℝ) : Prop :=
  ∀ (x : M) (u v : TangentSpace I x), ‖u‖ = 1 → ‖v‖ = 1 → inner ℝ u v = 0 →
    inner ℝ (Submission.CurvatureVec.curvVec cov x u v v) u ≤ K
```

`CurvLe cov K` is the *upper* half of `QuarterPinched`, isolated so that Rauch's theorem is
parametric in the bound.  **For `sec ≤ 0` it holds for every `K > 0`**; the glue lemma

```
Work.RiemLib.CurvLe_of_nonpos   -- sec ≤ 0  ⟹  CurvLe cov K   (0 < K)
Work.RiemLib.CurvLe_mono        -- CurvLe cov K ⟹ CurvLe cov K'  (K ≤ K')
Work.RiemLib.exists_lt_pi_div_sqrt -- ∀ L, ∃ K > 0, L < π/√K
```

at the end of this file turn "every upper bound `K`" into "the bound `π/√K` exceeds any prescribed
length", which is all the `_of_short` lifting machinery below needs.

## WARNING: the fibre norm versus the model norm

`TangentSpace I x` is definitionally `E`, but the two carry **different norms**: the Riemannian
fibre norm (from `[RiemannianBundle …]`) on `TangentSpace I x`, and the model norm of `E` on `E`.
They are *not* equal, and `‖v‖` with `v : E` is the MODEL norm.  Every curvature statement of this
library is therefore phrased in the fibre norm: the hypotheses read `‖v‖ < π/√K` for
`{v : TangentSpace I p}`, or `{(show E from v)}` when a map on the model space is at stake.  The
conversions are `Submission.Geodesic.exists_model_norm_le_fibre_div` (model ≤ fibre/√λ) and the
`(show TangentSpace I p from u)` / `(show E from v)` coercions used throughout the library.

## Contents

* §1 the exponential map and `π/√K`: `XuLift`, `RayConj`, `ConjCut`, `GExpLocalInj`, `SingularConj`
* §2 Rauch / conjugate radius: `RauchK`, `RauchGlobal`, `ChartCurv`, `ConjRadius`
* §3 Hopf–Rinow and the injectivity radius: `HopfRinow2` (`Submission.HopfRinow.*`), `InjRadius`
* §4 the Klingenberg long-homotopy lifting kit: `Work.OddBound.longHomotopy.*`
* §5 glue lemmas and the two norm-corrected exponential-map corollaries (this file)

### §1 exponential map

```
Submission.GlobalExp.GExp : (hmet : IsMetricCompatible cov) (x : M) (v : TangentSpace I x) → M
Submission.XuLift.gexpMap : (hmet) (p : M) (u : E) → M          -- GExp p with the model source
Submission.XuLift.gexpMap_apply : gexpMap hmet p u = GExp hmet p (show TangentSpace I p from u)
Submission.XuLift.contMDiffOn_GExp_model : ContMDiffOn 𝓘(ℝ, E) I ∞ (gexpMap hmet p) univ
Submission.XuLift.isLocalDiffeomorphAt_GExp :
  (mfderiv 𝓘(ℝ, E) I (gexpMap hmet p) v).IsInvertible →
    IsLocalDiffeomorphAt 𝓘(ℝ, E) I ∞ (gexpMap hmet p) v
Submission.XuLift.exists_pos_ball_lift_GExp :  -- the "sheet" statement
  (mfderiv 𝓘(ℝ, E) I (gexpMap hmet p) v).IsInvertible →
  ∃ r > 0, InjOn (gexpMap hmet p) (ball v (2*r)) ∧
    ∃ δ > 0, ∀ y, riemannianEDist I (gexpMap hmet p v) y < ofReal δ →
      ∃! w, w ∈ ball v r ∧ gexpMap hmet p w = y
Submission.ConjCut.isInvertible_mfderiv_GExp_of_norm_lt_pi_div_sqrt :
  (v : TangentSpace I p) → v ≠ 0 → ‖v‖ < π/√K → (mfderiv ... at (show E from v)).IsInvertible
Submission.RayConj.pi_div_sqrt_le_of_singular_mfderiv :
  singular mfderiv at w ≠ 0  ⟹  π/√K ≤ ‖w‖
Submission.RayConj.locallyInjectiveAtGExp_of_norm_lt_pi_div_sqrt :
  ‖v‖ < π/√K → v ≠ 0 → LocallyInjectiveAtGExp hmet p v
Submission.GExpLocalInj.locallyInjectiveAtGExp_of_lt_pi_div_sqrt :
  the same, but with the conjugate-radius input as an explicit hypothesis
Submission.SingularConj.singular_imp_conjTime : a singular d GExp gives a conjugate time
Work.RiemLib.isInvertible_mfderiv_gexpMap_of_norm_lt_pi_div_sqrt   -- this file, v = 0 included
Work.RiemLib.exists_pos_ball_lift_gexpMap_of_norm_lt_pi_div_sqrt  -- this file, hypotheses discharged
```

### §2 Rauch

```
Submission.RauchK.eqOn_zero_of_jacobi_of_curvLe : no conjugate point before π/√K
Submission.RauchK.pi_div_sqrt_le_of_isConjugateTime : isConjugateTime cov γ t → π/√K ≤ t
Submission.ChartCurv.curvVec_eq_chart : the curvature tensor in a chart
```

### §3 Hopf–Rinow, injectivity radius

```
Submission.HopfRinow.GExp_eq_geodCurve : GExp x (t • u) = geodCurve hmet T hT x u hu t
Submission.HopfRinow.riemannianEDist_GExp_ray_le : the radial distance bound along a ray
Submission.HopfRinow.exists_geodesic_riemannianEDist_eq :  -- Hopf-Rinow
  ∀ p q, ∃ v, GExp hmet p v = q ∧ riemannianEDist I p q = ofReal ‖v‖
Submission.InjRadius.InjAtLeast, InjAllAtLeast : the injectivity radius as a predicate
Submission.InjRadius.edist_GExp_eq_norm_of_injAtLeast : below inj. radius rays are minimising
Submission.InjRadius.exists_unique_GExp_of_injAtLeast : every point at distance < r has a unique
  exponential preimage of norm exactly that distance (the "normal ball")
Submission.InjRadius.two_mul_le_of_injAllAtLeast_of_geodCurve_loop : a geodesic loop bounds inj. r
```

### §4 the long-homotopy kit (`Work.OddBound.longHomotopy`)

```
exists_lift_of_short : a C¹ curve h on [0,S] with h 0 = p and length < π/√K lifts to a continuous
  W : ℝ → T_pM with W 0 = 0, GExp p (W s) = h s and ‖W s‖ ≤ curveLength h 0 s
continuousOn_lift_family_of_short : joint continuity of a family of such lifts (given the slices)
lift_family_of_short : the same, hypotheses on the family and existence in one statement
exists_tendsto_of_lift : a lift that stays in a closed ball of radius ρ < π/√K has a limit at T
lift_family_continuity_core : the abstract metric core of the parametric lifting argument
gauss_pairing_fibre : the Gauss lemma along every exponential ray
curveLength_toolkit, continuousOn_curveLength_family : length monotonicity / continuity in t
```

Any C¹ curve (and any smooth 2-parameter family of curves) of length `< π/√K` from `p` therefore
lifts through `GExp p`; since `K > 0` is arbitrary, this is the "all curves lift" half of
Cartan–Hadamard for a complete `M` with `sec ≤ 0`.  What is *not* in this library is the
evenly-covered-neighbourhood argument; that is area CH's own work.

## What is proved here (`namespace Work.RiemLib`)

* `CurvLe_mono`, `CurvLe_of_nonpos` — monotonicity of the upper bound, and `sec ≤ 0 ⟹ CurvLe cov K`;
* `pi_div_sqrt_pos`, `pi_div_sqrt_anti`, `exists_lt_pi_div_sqrt` — the arithmetic of the conjugate
  radius `π/√K`;
* `isInvertible_mfderiv_gexpMap_of_norm_lt_pi_div_sqrt` — the differential of `gexpMap` is
  invertible at every vector of fibre norm `< π/√K`, the zero vector included;
* `exists_pos_ball_lift_gexpMap_of_norm_lt_pi_div_sqrt` — the sheet statement of
  `XuLift.exists_pos_ball_lift_GExp` with the invertibility hypothesis discharged;
* `exists_gexpMap_eq` — Hopf–Rinow surjectivity of `gexpMap` in its model-space form.

and, in `RiemLib/SecNonpos/` (import `Submission.Work.RiemLib.SecNonpos.All`), the `sec ≤ 0` lifting
theorems that CH consumes directly (each with
`CurvLe cov K` derived from `sec ≤ 0` and `K` chosen from `exists_lt_pi_div_sqrt`, so that no
length hypothesis is needed):

```
Work.RiemLib.SecNonpos.exists_lift_of_short_of_nonpos
  -- a C¹ curve from p on [0,S] lifts, with ‖W s‖ ≤ curveLength h 0 s, for ANY length
Work.RiemLib.SecNonpos.lift_family_of_short_of_nonpos
  -- the same for a jointly smooth family with slices of length ≤ L, with joint continuity
```
-/

import Submission.Work.RiemLib.SphereDeps
import Submission.Work.RiemLib.CurvatureVec
import Submission.Work.RiemLib.GlobalExp
import Submission.Work.RiemLib.Length
import Submission.Work.RiemLib.ChartCurv
import Submission.Work.RiemLib.SingularConj
import Submission.Work.RiemLib.GExpLocalInj
import Submission.Work.RiemLib.XuLift
import Submission.Work.RiemLib.RayConj
import Submission.Work.RiemLib.ConjCut
import Submission.Work.RiemLib.RauchK
import Submission.Work.RiemLib.HopfRinow2
import Submission.Work.RiemLib.InjRadius
import Submission.Work.RiemLib.Work.OddBound.longHomotopy.exists_lift_of_short
import Submission.Work.RiemLib.Geodesic
import Submission.Work.RiemLib.GeodesicSpeed
import Submission.Work.RiemLib.Distance
import Submission.Work.RiemLib.InjBall
import Submission.Work.RiemLib.SegmentDomain
import Submission.Work.RiemLib.XuMain
import Submission.Work.RiemLib.EDist
import Submission.Work.RiemLib.GExpRay2
import Submission.Work.RiemLib.GExpJoint
import Submission.Work.RiemLib.GExpFlow
import Submission.Work.RiemLib.Commons.Geometry.Manifold.exists_finite_cover_isCompact_subset_chartAt
import Submission.Work.RiemLib.GeodesicGlobal
import Submission.Work.RiemLib.CutStep2
import Submission.Work.RiemLib.ChartPieces
import Submission.Work.RiemLib.ChartIndep
import Submission.Work.RiemLib.CoeffSmooth2
import Submission.Work.RiemLib.JacobiGlobal
import Submission.Work.RiemLib.Commons.Analysis.ODE.exists_linearODE_solution_Icc
import Submission.Work.RiemLib.IndexCorner2
import Submission.Work.RiemLib.InjHalf
import Submission.Work.RiemLib.LensLoop
import Submission.Work.RiemLib.UniformInj
import Submission.Work.RiemLib.ConjRadius
import Submission.Work.RiemLib.Gauss
import Submission.Work.RiemLib.ExpBound2
import Submission.Work.RiemLib.JacobiGauss
import Submission.Work.RiemLib.Minimal
import Submission.Work.RiemLib.Work.OddBound.longHomotopy.exists_tendsto_of_lift
import Submission.Work.RiemLib.Work.OddBound.longHomotopy.gauss_pairing_fibre

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle CovariantDerivative

/-! ## The machine-checked re-export list -/

#check @Submission.GlobalExp.GExp
#check @Submission.GlobalExp.GExp_zero
#check @Submission.XuLift.gexpMap
#check @Submission.XuLift.gexpMap_apply
#check @Submission.XuLift.contMDiffOn_GExp_model
#check @Submission.XuLift.isLocalDiffeomorphAt_GExp
#check @Submission.XuLift.exists_pos_ball_lift_GExp
#check @Submission.GExpSmooth.exists_contMDiffAt_GExp
#check @Submission.GExpLocalInj.locallyInjectiveAtGExp_of_lt_pi_div_sqrt
#check @Submission.GExpLocalInj.mfderiv_GExp_zero
#check @Submission.RayConj.locallyInjectiveAtGExp_of_norm_lt_pi_div_sqrt
#check @Submission.RayConj.pi_div_sqrt_le_of_singular_mfderiv
#check @Submission.ConjCut.isInvertible_mfderiv_GExp_of_norm_lt_pi_div_sqrt
#check @Submission.SingularConj.singular_imp_conjTime
#check @Submission.CutStep2.LocallyInjectiveAtGExp
#check @Submission.RauchK.CurvLe
#check @Submission.RauchK.eqOn_zero_of_jacobi_of_curvLe
#check @Submission.RauchK.pi_div_sqrt_le_of_isConjugateTime
#check @Submission.ChartCurv.curvVec_eq_chart
#check @Submission.ConjRadius.IsConjugateTime
#check @Submission.HopfRinow.GExp_eq_geodCurve
#check @Submission.HopfRinow.riemannianEDist_GExp_ray_le
#check @Submission.HopfRinow.exists_geodesic_riemannianEDist_eq
#check @Submission.InjRadius.InjAtLeast
#check @Submission.InjRadius.InjAllAtLeast
#check @Submission.InjRadius.injAtLeast_mono
#check @Submission.InjRadius.edist_GExp_eq_norm_of_injAtLeast
#check @Submission.InjRadius.exists_unique_GExp_of_injAtLeast
#check @Submission.InjRadius.two_mul_le_of_injAllAtLeast_of_geodCurve_loop
#check @Submission.Length.curveLength
#check @Submission.Length.curveSpeed
#check @Work.OddBound.longHomotopy.exists_lift_of_short
#check @Work.OddBound.longHomotopy.exists_tendsto_of_lift
#check @Work.OddBound.longHomotopy.gauss_pairing_fibre

/-! ## Glue: `namespace Work.RiemLib` -/

namespace Work.RiemLib

open LeanEval.Geometry.SphereTheorem

/-- **Monotonicity of the upper curvature bound**: `sec ≤ K` and `K ≤ K'` give `sec ≤ K'`. -/
theorem CurvLe_mono
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    {K K' : ℝ} (h : Submission.RauchK.CurvLe cov K) (hle : K ≤ K') :
    Submission.RauchK.CurvLe cov K' :=
  fun x u v hu hv huv => le_trans (h x u v hu hv huv) hle

/-- **`sec ≤ 0` gives every upper bound**: if every sectional curvature (written as
`inner ℝ (curvVec cov x u v v) u` on an orthonormal pair) is `≤ 0`, then `CurvLe cov K` holds for
every `K > 0`.  This is the form in which a non-positively-curved manifold enters the parametric
comparison theorems of this library. -/
theorem CurvLe_of_nonpos
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    (h : ∀ (x : M) (u v : TangentSpace I x), ‖u‖ = 1 → ‖v‖ = 1 → inner ℝ u v = 0 →
      inner ℝ (Submission.CurvatureVec.curvVec cov x u v v) u ≤ 0)
    {K : ℝ} (hK : 0 < K) : Submission.RauchK.CurvLe cov K :=
  fun x u v hu hv huv => le_trans (h x u v hu hv huv) hK.le

/-- **`CurvLe cov 0` is the pointwise `sec ≤ 0` hypothesis.**  This is an `iff` only because of the
definition of `CurvLe`; it lets a caller holding `CurvLe cov 0` (the form in which the library's
comparison theorems state a curvature bound) feed the `hsec` hypothesis of the `sec ≤ 0` lifting
theorems of `RiemLib/SecNonpos/`. -/
theorem CurvLe_zero_iff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    (cov : CovariantDerivative I E (TangentSpace I (M := M))) :
    Submission.RauchK.CurvLe cov 0 ↔
      (∀ (x : M) (u v : TangentSpace I x), ‖u‖ = 1 → ‖v‖ = 1 → inner ℝ u v = 0 →
        inner ℝ (Submission.CurvatureVec.curvVec cov x u v v) u ≤ 0) :=
  Iff.rfl

/-- The conjugate radius `π/√K` is positive for `K > 0`. -/
theorem pi_div_sqrt_pos {K : ℝ} (hK : 0 < K) : 0 < Real.pi / Real.sqrt K :=
  div_pos Real.pi_pos (Real.sqrt_pos.mpr hK)

/-- **`π/√K` is antitone in `K`**: a smaller upper curvature bound gives a larger conjugate radius. -/
theorem pi_div_sqrt_anti {K K' : ℝ} (hK : 0 < K) (hle : K ≤ K') :
    Real.pi / Real.sqrt K' ≤ Real.pi / Real.sqrt K :=
  div_le_div_of_nonneg_left Real.pi_pos.le (Real.sqrt_pos.mpr hK) (Real.sqrt_le_sqrt hle)

/-- **`π/√K` is unbounded**: for every real `L` there is `K > 0` with `L < π/√K`.

This is what lets the `_of_short` lifting theorems of §4 be applied to a curve of *any* length once
`CurvLe cov K` is known for every `K > 0` (the case `sec ≤ 0`). -/
theorem exists_lt_pi_div_sqrt (L : ℝ) :
    ∃ K : ℝ, 0 < K ∧ L < Real.pi / Real.sqrt K := by
  set c : ℝ := L + |L| + 2 with hc
  have hcpos : 0 < c := by
    rw [hc]
    have h1 : -L ≤ |L| := neg_le_abs L
    linarith
  refine ⟨(Real.pi / c) ^ 2, pow_pos (div_pos Real.pi_pos hcpos) 2, ?_⟩
  have hs : Real.sqrt ((Real.pi / c) ^ 2) = Real.pi / c :=
    Real.sqrt_sq (le_of_lt (div_pos Real.pi_pos hcpos))
  rw [hs]
  have h1 : Real.pi / (Real.pi / c) = c := by
    field_simp
    try ring
  rw [h1]
  have h2 : L < c := by
    rw [hc]
    have := le_abs_self L
    linarith
  exact h2

/-- **The differential of `gexpMap` is invertible below the conjugate radius** (in the fibre norm,
with the case `v = 0` included).  `hv : ‖v‖ < π/√K` is a hypothesis on the **Riemannian fibre
norm** of the tangent vector `v : TangentSpace I p`, not on the model norm of `E`.

For `v ≠ 0` this is `Submission.ConjCut.isInvertible_mfderiv_GExp_of_norm_lt_pi_div_sqrt` (the
contrapositive of `RayConj.pi_div_sqrt_le_of_singular_mfderiv`, i.e. Rauch's conjugate-radius
bound); at `v = 0` it is `Submission.GExpLocalInj.mfderiv_GExp_zero`.  It is the hypothesis that
discharges `Submission.XuLift.isLocalDiffeomorphAt_GExp` and
`Submission.XuLift.exists_pos_ball_lift_GExp` unconditionally (see the next lemma). -/
theorem isInvertible_mfderiv_gexpMap_of_norm_lt_pi_div_sqrt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {K : ℝ} (hKpos : 0 < K) (hK : Submission.RauchK.CurvLe cov K)
    {p : M} {v : TangentSpace I p} (hv : ‖v‖ < Real.pi / Real.sqrt K) :
    (mfderiv 𝓘(ℝ, E) I (Submission.XuLift.gexpMap (cov := cov) hmet p)
      (show E from v)).IsInvertible := by
  rcases eq_or_ne v 0 with hv0 | hv0
  · subst hv0
    change (mfderiv 𝓘(ℝ, E) I
      (fun u : E => Submission.GlobalExp.GExp (cov := cov) hmet p (show TangentSpace I p from u))
      (0 : E)).IsInvertible
    rw [Submission.GExpLocalInj.mfderiv_GExp_zero (cov := cov) hmet p]
    exact ⟨ContinuousLinearEquiv.refl ℝ E, rfl⟩
  · exact Submission.ConjCut.isInvertible_mfderiv_GExp_of_norm_lt_pi_div_sqrt
      (cov := cov) hmet htor hK hKpos hv0 hv

/-- **The "sheet" statement of the exponential map, hypotheses discharged.**

For a vector `v` of **fibre** norm `< π/√K` there are `r > 0` and `δ > 0` such that `gexpMap` is
injective on the ball of radius `2r` around `(show E from v)` and every point of `M` at Riemannian
distance `< δ` from `gexpMap hmet p (show E from v)` has a *unique* preimage in the ball of radius
`r`.  This is `Submission.XuLift.exists_pos_ball_lift_GExp` with its invertibility hypothesis
supplied by `isInvertible_mfderiv_gexpMap_of_norm_lt_pi_div_sqrt`; it is the local input of the
evenly-covered-neighbourhood argument of Cartan–Hadamard (area CH).

The balls in the conclusion are balls in the model space `E`, with the **model** norm. -/
theorem exists_pos_ball_lift_gexpMap_of_norm_lt_pi_div_sqrt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {K : ℝ} (hKpos : 0 < K) (hK : Submission.RauchK.CurvLe cov K)
    {p : M} {v : TangentSpace I p} (hv : ‖v‖ < Real.pi / Real.sqrt K) :
    ∃ r : ℝ, 0 < r ∧
      Set.InjOn (Submission.XuLift.gexpMap (cov := cov) hmet p)
        (Metric.ball (show E from v) (2 * r)) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ y : M,
        Manifold.riemannianEDist I
            (Submission.XuLift.gexpMap (cov := cov) hmet p (show E from v)) y <
          ENNReal.ofReal δ →
        ∃! w : E, w ∈ Metric.ball (show E from v) r ∧
          Submission.XuLift.gexpMap (cov := cov) hmet p w = y := by
  have hinv := isInvertible_mfderiv_gexpMap_of_norm_lt_pi_div_sqrt
    (cov := cov) hmet htor hKpos hK hv
  exact Submission.XuLift.exists_pos_ball_lift_GExp (cov := cov) hmet p
    (v := (show E from v)) hinv

/-- **Surjectivity of `gexpMap` onto a path-connected `M`** (Hopf–Rinow, in the model-space
domain `E` of `gexpMap`): every point of `M` is `gexpMap hmet p u` for some `u : E`.

This is the first conjunct of `Submission.HopfRinow.exists_geodesic_riemannianEDist_eq` restated in
the domain of `gexpMap`.  It is what makes the fibres of the exponential map non-empty on a
connected base, which the evenly-covered-neighbourhood argument of Cartan–Hadamard (area CH) needs
to identify the sheets of the covering. -/
theorem exists_gexpMap_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (p q : M) :
    ∃ u : E, Submission.XuLift.gexpMap (cov := cov) hmet p u = q := by
  obtain ⟨v, hv, -⟩ :=
    Submission.HopfRinow.exists_geodesic_riemannianEDist_eq (cov := cov) hmet htor p q
  exact ⟨(show E from v), hv⟩

end Work.RiemLib

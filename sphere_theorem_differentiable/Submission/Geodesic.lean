import ChallengeDeps
import Submission.Curvature
import Submission.Commons.Geometry.Manifold.Tangent.mfderiv_extChartAt_comp
import Submission.Commons.Geometry.Manifold.Tangent.hasMFDerivAt_extChartAt_symm_comp
import Submission.Commons.Geometry.Manifold.Tangent.mvfderiv_comp_curve
import Submission.Commons.Geometry.Manifold.Tangent.eqOn_sum_frameSection_of_basis
import Submission.Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.cov_eq_sum_of_eventuallyEq_pointwise
import Submission.Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contDiffOn_chartSpray
import Submission.Commons.Geometry.Manifold.VectorField.mlieBracket_trivializationAt_symmL_smooth
import Submission.Commons.Geometry.Manifold.LocalDiffeomorph.isLocalDiffeomorphAt_of_contMDiffOn_of_mfderiv_isInvertible
import Submission.Commons.Analysis.ODE.exists_secondOrderODE_local_solution
import Submission.Commons.Analysis.ODE.secondOrderODE_solution_unique
import Submission.Commons.Analysis.ODE.secondOrderODE_solution_unique_of_contDiffAt
import Submission.Commons.Analysis.ODE.exists_uniform_secondOrderODE_solution_in_open
import Submission.Commons.Analysis.ODE.contDiffAt_solutionMap_of_eventually

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Geodesics for a covariant derivative: definitions and the chart setup

The topological sphere theorem of Berger–Klingenberg–Rauch rests on the geodesic
exponential map of the Levi-Civita connection, the comparison theory for Jacobi
fields and Klingenberg's injectivity-radius estimate.  None of this exists in
Mathlib at the pinned revision.  This module starts the chapter.

## The geodesic equation

A curve `γ : ℝ → M` is a geodesic for `cov` if the covariant derivative of its
velocity field along `γ` vanishes.  Since a covariant derivative acts on global
sections, we formulate this as: *every* smooth global section `Z` agreeing with
the velocity field `t ↦ γ'(t)` near `t` satisfies `∇_{γ'(t)} Z = 0` (by locality
of covariant derivatives this is independent of the choice of `Z`).

## Status and roadmap

Proved here (all `sorry`-free):

* `curveVelocity` and its basic laws; the pointwise geodesic equation `IsGeodesicAt` and the
  global `IsGeodesic`.
* the coordinate frame `frameSection` / `frameVector` (smooth on the chart) and the Christoffel
  symbol `christoffelEval`, together with its `ℝ`-bilinearity in both slots;
  `cov_frameSection_eq` (`∇_w σ_v = σ_{Γ(v,w)}`).
* `continuousLinearMapAt_curveVelocity` (the coordinates of `γ'` are the derivative of the
  coordinate curve, from the commons lemma `mfderiv_extChartAt_comp`) and
  `curveVelocity_extChartAt_symm` (the converse, from `hasMFDerivAt_extChartAt_symm_comp`).
* the chart vector field `chartGeodesicVectorField` (with the *second* Christoffel slot the
  tangent vector `frameVector x₀ p v`, i.e. `u'' = -Γ(u)(u')(γ')` in coordinates) and the chart
  equation `IsGeodesicInChart`, with local existence and uniqueness reduced to the commons ODE
  lemmas.
* `cov_eq_zero_of_chartGeodesic` and `isGeodesic_of_isGeodesicInChart`: a solution of the chart
  equation is a geodesic (the proof decomposes a smooth section along the curve in the chart
  frame, uses the commons lemma `cov_eq_sum_of_eventuallyEq_pointwise` and
  `mvfderiv_comp_curve`, and uses continuity to evaluate the section at the base point).
* homogeneity: `chartGeodesicVectorField_smul` (degree two in the velocity) and
  `isGeodesicInChart_comp_mul` (scaling of the chart equation in time).
* `HasChartGeodesic`, the exponential map `expMap cov x v` (time-`1` value of a chart geodesic),
  and `isGeodesicAt_chartSolution`.
* `exists_contMDiff_spray_extension`: a globally `C^∞` field `G` agreeing with the chart geodesic
  spray on an open neighbourhood `U` of `((extChartAt I x₀) x₀, 0)` contained in the chart target
  (built by multiplying the spray, which is smooth only on the chart, by a smooth bump function
  supported in the chart; from the commons lemma `contDiffOn_chartSpray`).  This is the tool that
  makes the geodesic spray a *globally* defined smooth field on the model space, so that the
  standard ODE machinery (uniqueness, smooth dependence) applies without junk-value obstructions.
* `hasChartGeodesic_const_smul`: the chart geodesic equation is invariant under time scaling.
* **Uniqueness of chart geodesics** (all with `[I.Boundaryless]`, since the chart target must be
  open): `contDiffAt_spray_of_hasChartGeodesic` (`ContDiffAt ℝ 1` of the spray along a chart
  geodesic, from `contDiffOn_chartSpray`), the local agreement lemma `hasChartGeodesic_local_eq`
  (from the commons `secondOrderODE_solution_unique_of_contDiffAt`), and the interval version
  `hasChartGeodesic_eqOn` (open-and-closed argument on `Ioo (-2) 2` with the agreement set of the
  *full state* `(u, w)`, closed under the local lemma and closed by continuity).
* the exponential-map API: `expMap_eq_of_hasChartGeodesic` (well-definedness),
  `expMap_zero`, and the geodesic-flow identity `expMap_smul`
  (`expMap cov x (c • v) = (extChartAt I x).symm (u c)` for `|c| ≤ 1` and any chart geodesic `u`).

* the exponential-map API: `expMap_eq_of_hasChartGeodesic` (well-definedness),
  `expMap_zero`, and the geodesic-flow identity `expMap_smul`
  (`expMap cov x (c • v) = (extChartAt I x).symm (u c)` for `|c| ≤ 1` and any chart geodesic `u`).
* `prod_local_unique` / `prod_eqOn`: uniqueness on an interval for the first-order system
  `y' = (y.2, G y)` with `G` smooth (needed to apply the smooth-dependence results to the
  globally-defined spray extension; also useful in their own right).
* `continuousLinearMapAt_trivializationAt_self`: the tangent-bundle trivialisation at its own base
  point is the identity, `T.cLMAt ℝ x x = 1` (from `TangentBundle.continuousLinearMapAt_trivializationAt`
  and `mfderiv_extChartAt_self`).
* **`contMDiffAt_expMap_zero`**: the exponential map `v ↦ expMap cov x₀ v` is `C^∞` at `0`.
  Proof: take the globally smooth extension `G` of the spray (`exists_contMDiff_spray_extension`),
  get uniform existence with confinement to the region where `G` is the spray
  (`exists_uniform_secondOrderODE_solution_in_open`), package the solutions into a family
  `sol : E → ℝ → E × E` by `Classical.choose`, apply the smooth-dependence theorem
  `contDiffAt_solutionMap_of_eventually` (`huniq` via `prod_eqOn`, which is why `G` must be
  globally smooth), identify `expMap cov x₀ w = (extChartAt I x₀).symm ((sol w 1).1)` through
  `expMap_eq_of_hasChartGeodesic`, and compose with the smooth chart inverse.

* **The differential of `expMap` at the origin** (all `sorry`-free):
  - `exists_pos_hasChartGeodesic`: chart geodesics exist for all velocities in a ball around `0`
    (uniform local existence for the spray, applied to the globally smooth extension);
  - `mfderiv_expMap_zero_of_hasChartGeodesic` (the case of a single velocity admitting a chart
    geodesic) and `mfderiv_expMap_zero`: `mfderiv 𝓘(ℝ, E) I (fun v : E => expMap cov x₀ v) 0`
    `= ContinuousLinearMap.id ℝ E`.
  The proof uses the ray identity `expMap_smul`, the chain rule
  `mfderiv_comp_apply_of_eq` for `s ↦ s • v`, and `curveVelocity_extChartAt_symm`
  (with `Trivialization.symmL_continuousLinearMapAt` and
  `continuousLinearMapAt_trivializationAt_self`) to compute the velocity of the geodesic ray;
  the general velocity is reduced to the ball by linearity of `mfderiv`.

* **Smoothness of `expMap` on a ball of velocities** (`exists_radius_contMDiffAt_expMap`): the
  proof of `contMDiffAt_expMap_zero` is carried out at an arbitrary interior point `v₀` of the ball
  where uniform existence holds, and `contMDiffAt_expMap_zero` is the special case `v₀ = 0`.
* **The exponential map is a local diffeomorphism at the origin**
  (`isLocalDiffeomorphAt_expMap_zero`, via `Commons.Geometry.Manifold.LocalDiffeomorph.
  isLocalDiffeomorphAt_of_contMDiffOn_of_mfderiv_isInvertible`).  The auxiliary statements are
  `exists_open_contMDiffOn_expMap` (`ContMDiffOn ∞` on an open ball, the *local* form of
  smoothness: pointwise `ContMDiffAt ∞` does **not** suffice, see the gotchas below) and
  `isInvertible_mfderiv_expMap_zero` (from `mfderiv_expMap_zero`).  Consequences available from
  Mathlib's `IsLocalDiffeomorphAt` API: `localInverse`, `localInverse_left_inv`,
  `localInverse_right_inv`, `contmdiffOn_localInverse`, `localInverse_eventuallyEq_left/right`,
  `localInverse_isLocalDiffeomorphAt`.  Two immediate consequences are recorded:
  `exists_injOn_expMap_nhds` (`expMap` is injective on an open neighbourhood of `0`) and
  `exists_open_subset_range_expMap` (its image contains an open neighbourhood of `x₀`).
* **Torsion-freeness makes the Christoffel symbol symmetric**: `cov_frameSection_frameVector_comm`
  and `christoffelEval_comm` (`Γ(v)(w) = Γ(w)(v)` for tangent vectors with coordinates `v`, `w`),
  from `cov.torsion_eq_zero_iff` and
  `Commons.Geometry.Manifold.VectorField.mlieBracket_trivializationAt_symmL_smooth` (the coordinate
  vector fields of a chart commute).  This is the first use of the hypothesis `cov.torsion = 0`.
* **The chain rule along a curve in the tangent space** (`mfderiv_expMap_comp`): for a curve
  `γ : ℝ → E` with `HasDerivAt γ c' t` on which `expMap` is differentiable at `γ t`, one has
  `mfderiv (expMap) (γ t) c' = curveVelocity (fun s => expMap (γ s)) t`.  The **radial
  derivative** `mfderiv_expMap_ray` is the case `γ c = c • v`, using `expMap_smul` to replace the
  curve by the chart geodesic.

Next steps (in order):

1. **Gauss lemma.**  For `v, w ∈ T_{x₀}M` with a chart geodesic for `v`: the two-parameter family
   `f(s,t) = expMap x₀ (s • (v + t • w))` has `∂_s f(s,0) =` velocity of the geodesic `γ_v` and
   `∂_t f(s,0)` the variation field; the identity
   `⟪∂_s f, ∂_t f⟫(s,0) = s ⟪v, w⟫` follows from `∇_{∂_s}∂_s f = 0` (the `s`-lines are geodesics)
   and the symmetry `∇_{∂_s}∂_t f = ∇_{∂_t}∂_s f` (torsion-freeness), together with metric
   compatibility applied to `t ↦ ⟪∂_s f, ∂_s f⟫ = ‖v + t w‖²`.  This is the first genuine use of
   the hypotheses `cov.torsion = 0` and `IsMetricCompatible cov`, and it needs the covariant
   derivative of a *family* of vector fields along a map (two-parameter variations) — the next
   chapter of the library.
2. Then: normal coordinates, geodesic completeness / Hopf–Rinow for the compact case, Jacobi
   fields and the comparison theorems (Rauch, Toponogov), Klingenberg's injectivity radius bound,
   Berger's lemma, and finally the topological assembly `M ≃ₜ S^n`.

## Gotchas for the next session (hard-won)

* **`∞` versus `ω` in `ℕ∞ω`.**  `ℕ∞ω = WithTop ℕ∞`, and Mathlib's scoped notation has
  `∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)` ("smooth") while `ω = (⊤ : WithTop ℕ∞)` ("analytic").  These are
  *different* elements: `IsManifold I ∞ M` does **not** imply `IsManifold I ω M`.  Everywhere in
  this file the smoothness level is the scoped notation `∞`, which is what all our instances
  provide.  When *requesting* commons lemmas (whose file may not `open scoped ContDiff`) write
  `((⊤ : ENat) : WithTop ENat)` explicitly -- a bare `⊤` there means `ω` (analytic) and the
  resulting lemma will be unusable here.  (Two such lemmas had to be re-requested:
  `...mlieBracket_trivializationAt_symmL_smooth` and
  `...isLocalDiffeomorphAt_infty_of_mfderiv_isInvertible`.)
* **Instance paths on the tangent bundle.**  `TangentSpace I x` is a type synonym for `E`, so the
  fiber carries two (propositionally equal, but not notionally identical) instances.  This makes
  Mathlib's `ContMDiffAt.inner_bundle` / `MDifferentiableAt.inner_bundle` *fail to elaborate* in
  our context with "synthesized type class instance is not definitionally equal to expression
  inferred by typing rules" (the synthesized one is the `RiemannianBundle`-provided
  `NormedAddCommGroup`, the inferred one is that of `E`).  Consequence: *differentiability of the
  function `y ↦ ⟪Y y, Z y⟫` is currently not available*, which is exactly what the product rule
  for the metric along a curve needs (see below).  Workarounds to try: prove the instance equality,
  or reproduce the proof of `inner_bundle` inline with the instances fixed by the goal.
* `curveVelocity` needs its model `I` passed explicitly (`curveVelocity (I := I) γ t`) when `γ` is
  written as an anonymous lambda, otherwise `ChartedSpace ?M M` synthesis gets stuck.
* Statements mentioning `mfderiv` at a point that is only *propositionally* equal to the expected
  one (`f 0` versus `x₀`) must use `mfderiv_congr_point` (which is stated with an explicit CLM
  type `E →L E'`, sidestepping the transparency issues) and `mfderiv_congr` for definitionally
  equal functions.  `rw` on `mfderiv`-applications often fails with "not type-correct under the
  implicit transparency level"; the robust pattern is to produce a helper `key : ((L : ℝ →L[ℝ] E))
  (1 : ℝ) = v` at the *plain* type and finish with `exact key`.

## Detailed plan for the Gauss lemma (starts the next session)

Notation: `x₀ : M`, `v w : E`, `u` a chart geodesic for `v`, `e = extChartAt I x₀`.
For `t` small, let `F(s,t) = expMap cov x₀ (s • (v + t • w))` (defined for `s ∈ [0,1]` and small
`t` by `exists_radius_contMDiffAt_expMap` + `expMap_smul`), and put

* `S(s,t) = ∂_s F`  (the velocity of the `s`-line, a geodesic),  `T(s,t) = ∂_t F`.

Everything is computed through curves and global sections, so the following auxiliary notions
have to be built first (they are the next chapter of the library):

1. **Covariant derivative of a section along a curve.**  For a curve `γ` and a global smooth
   section `Z`, `∇_{γ'}Z` at `t` is `cov Z (γ t) (γ'(t))`; the pointwise version
   (`∀ᶠ s in 𝓝 t, Z (γ s) = V (γ s)` for a prescribed field `V` along `γ`) is well defined by
   locality of `cov` (`Commons...cov_eq_sum_of_eventuallyEq_pointwise` already available).
2. **Product rule** (this is where `IsMetricCompatible` first enters):
   `deriv (fun s => ⟪Y (γ s), Z (γ s)⟫) t = ⟪cov Y (γ t) γ'(t), Z (γ t)⟫ + ⟪Y (γ t), cov Z (γ t) γ'(t)⟫`.
   Immediate from `IsMetricCompatible cov` + the commons chain rule `mvfderiv_comp_curve`
   (`mvfderiv I (fun y => ⟪Y y, Z y⟫) (γ t) (mfderiv γ t 1) = deriv (fun s => ⟪Y (γ s), Z (γ s)⟫) t`).
3. **Torsion-freeness in the two-parameter family** (this is where `cov.torsion = 0` first enters):
   `∇_S T = ∇_T S` at `(s,0)`.  Two equivalent routes:
   * coordinate route: the Christoffel symbol is symmetric,
     `christoffelEval_comm`/`cov_frameSection_frameVector_comm` (already proved here!);
   * intrinsic route: extend `S` and `T` to global smooth sections `Y`, `Z` on a neighbourhood of
     `F(s,0)` (Whitney-type extension of a section along a `2`-dimensional family), note that
     `mpullback F Y = ∂_s`, `mpullback F Z = ∂_t` so that `mpullback_mlieBracket` gives
     `[Y,Z] = 0` at the point, and apply `cov.torsion_eq_zero_iff`.
4. **The computation.**  With `S` geodesic along `s` and constant speed `‖S(s,t)‖ = ‖v + t • w‖`:
   ```
   d/ds ⟪S, T⟫ = ⟪∇_S S, T⟫ + ⟪S, ∇_S T⟫ = 0 + ⟪S, ∇_T S⟫
                = (1/2) d/dt ⟪S, S⟫        (at t = 0)
                = ⟪v, w⟫,
   ```
   using 2. twice and 3.  Since `⟪S,T⟫(0,0) = 0` (as `F(0,t) = x₀`), this gives
   `⟪S, T⟫(s,0) = s ⟪v, w⟫`, i.e. **Gauss's lemma**
   `⟪ (mfderiv expMap (s • v)) v, (mfderiv expMap (s • v)) (s • w) ⟫ = s ⟪v, w⟫`
   (`mfderiv_expMap_ray` computes the first factor, `mfderiv_expMap_comp` the second).

A remaining gap in the chart picture is the converse direction
`IsGeodesic cov γ → IsGeodesicInChart cov x₀ (extChartAt I x₀ ∘ γ)`: it needs a smooth global
section agreeing with the velocity of `γ` along an *interval*, which in turn needs an extension
of a section along a curve (flow-box/Whitney extension), not available in Mathlib.  It is *not*
needed for the development as long as `expMap` is built from chart solutions (as above): those are
known to be geodesics by `isGeodesicAt_chartSolution`.

## Christoffel symbols

In a chart `e = extChartAt I x₀` with tangent-bundle trivialisation `T`, put
`σ_v (q) = T.symmL ℝ q v` (the section with constant coordinates `v`, junk value
`0` outside the chart) and

  `christoffelEval cov x₀ p v w = T.linearMapAt ℝ p (∇_w σ_v)`.

Then `christoffelEval` is `ℝ`-bilinear in `(v, w)`, and the chart form of the
geodesic equation is `u'' + christoffelEval cov x₀ (γ t) (u' t) (u' t) = 0` for
`u = e ∘ γ`.
-/

set_option linter.unusedSectionVars false

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.Geodesic

noncomputable section

/-! ## The velocity of a curve -/

/-- The velocity vector `γ'(t) ∈ T_{γ t} M` of a curve in `M`. -/
def curveVelocity (γ : ℝ → M) (t : ℝ) : TangentSpace I (γ t) :=
  mfderiv 𝓘(ℝ) I γ t (1 : ℝ)

@[simp]
lemma curveVelocity_apply (γ : ℝ → M) (t : ℝ) :
    curveVelocity (I := I) γ t = mfderiv 𝓘(ℝ) I γ t (1 : ℝ) := rfl

lemma curveVelocity_const (p : M) (t : ℝ) :
    curveVelocity (I := I) (fun _ : ℝ => p) t = 0 := by
  rw [curveVelocity_apply, mfderiv_const]
  show (0 : ℝ →L[ℝ] TangentSpace I p) 1 = 0
  exact zero_apply 1

/-! ## The geodesic equation -/

/-- `γ` satisfies the **geodesic equation at the time `t`**: for every smooth global section `Z`
agreeing with the velocity field of `γ` near `t`, the covariant derivative of `Z` at `γ t` in the
direction `γ'(t)` vanishes. -/
def IsGeodesicAt (cov : CovariantDerivative I E (TangentSpace I (M := M))) (γ : ℝ → M)
    (t : ℝ) : Prop :=
  ∀ Z : Π x : M, TangentSpace I x, CMDiff ∞ (T% Z) →
    (∀ᶠ s in 𝓝 t, Z (γ s) = curveVelocity (I := I) γ s) →
    cov Z (γ t) (curveVelocity (I := I) γ t) = 0

/-- `γ` is a **geodesic** for the covariant derivative `cov` if it satisfies the geodesic equation
at every time. -/
def IsGeodesic (cov : CovariantDerivative I E (TangentSpace I (M := M))) (γ : ℝ → M) : Prop :=
  ∀ t : ℝ, IsGeodesicAt cov γ t

@[simp] lemma isGeodesic_iff (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (γ : ℝ → M) : IsGeodesic cov γ ↔ ∀ t : ℝ, IsGeodesicAt cov γ t := Iff.rfl

/-- Constant curves are geodesics. -/
lemma isGeodesic_const (cov : CovariantDerivative I E (TangentSpace I (M := M))) (p : M) :
    IsGeodesic cov (fun _ : ℝ => p) := by
  intro t Z _ _
  rw [curveVelocity_const]
  exact map_zero _

/-! ## Christoffel symbols -/

/-- The section of the tangent bundle with **constant coordinates** `v` in the
chart at `x₀`: at `q` it is the vector whose coordinates in the chart are `v`.
Outside the chart the trivialisation returns the junk value `0`. -/
def frameSection (x₀ : M) (v : E) : Π x : M, TangentSpace I x :=
  fun q => (trivializationAt E (TangentSpace I) x₀).symmL ℝ q v

lemma frameSection_apply (x₀ : M) (v : E) (q : M) :
    frameSection (I := I) x₀ v q =
      (trivializationAt E (TangentSpace I) x₀).symmL ℝ q v := rfl

lemma frameSection_add (x₀ : M) (v w : E) :
    frameSection (I := I) x₀ (v + w)
      = frameSection (I := I) x₀ v + frameSection (I := I) x₀ w := by
  funext q
  exact map_add ((trivializationAt E (TangentSpace I) x₀).symmL ℝ q) v w

lemma frameSection_smul (x₀ : M) (c : ℝ) (v : E) :
    frameSection (I := I) x₀ (c • v) = c • frameSection (I := I) x₀ v := by
  funext q
  exact map_smul ((trivializationAt E (TangentSpace I) x₀).symmL ℝ q) c v

@[simp]
lemma frameSection_zero (x₀ : M) :
    frameSection (I := I) x₀ (0 : E) = 0 := by
  funext q
  exact map_zero ((trivializationAt E (TangentSpace I) x₀).symmL ℝ q)

/-- The section with constant coordinates `v` is smooth at every point of the
chart. -/
lemma contMDiffAt_frameSection (x₀ : M) (v : E) {x : M}
    (hx : x ∈ (chartAt H x₀).source) :
    CMDiffAt ∞ (T% (frameSection (I := I) x₀ v)) x := by
  rw [Trivialization.contMDiffAt_section_iff
    (trivializationAt E (TangentSpace I) x₀) (by simpa using hx)]
  refine (contMDiffAt_const (c := v)).congr_of_eventuallyEq ?_
  filter_upwards [(trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds
    (by simpa using hx)] with y hy
  rw [show frameSection (I := I) x₀ v y
      = (trivializationAt E (TangentSpace I) x₀).symmL ℝ y v from rfl]
  rw [Trivialization.symmL_apply (e := trivializationAt E (TangentSpace I) x₀) (R := ℝ) hy v]
  exact congrArg Prod.snd ((trivializationAt E (TangentSpace I) x₀).apply_mk_symm hy v)

lemma mdiffAt_frameSection (x₀ : M) (v : E) {x : M}
    (hx : x ∈ (chartAt H x₀).source) :
    MDiffAt (T% (frameSection (I := I) x₀ v)) x :=
  (contMDiffAt_frameSection x₀ v hx).mdifferentiableAt (by simp)

/-- **Christoffel symbol** of `cov` at `p`, in the chart at `x₀`: the coordinates
of `∇_w σ_v`, where `σ_v` is the section with constant coordinates `v`. -/
def christoffelEval (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (x₀ : M) (p : M) (v : E) (w : TangentSpace I p) : E :=
  (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ p
    (cov (frameSection (I := I) x₀ v) p w)

lemma christoffelEval_def
    (cov : CovariantDerivative I E (TangentSpace I (M := M))) (x₀ p : M) (v : E)
    (w : TangentSpace I p) :
    christoffelEval cov x₀ p v w =
      (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ p
        (cov (frameSection (I := I) x₀ v) p w) := rfl

/-- The coordinates of the vector `frameSection x₀ v q` are `v`. -/
lemma continuousLinearMapAt_frameSection (x₀ : M) (v : E) {q : M}
    (hq : q ∈ (chartAt H x₀).source) :
    (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ q
      (frameSection (I := I) x₀ v q) = v := by
  rw [show frameSection (I := I) x₀ v q
      = (trivializationAt E (TangentSpace I) x₀).symmL ℝ q v from rfl]
  exact Trivialization.continuousLinearMapAt_symmL (trivializationAt E (TangentSpace I) x₀)
    (R := ℝ) (by simpa using hq) v

/-- `christoffelEval` is additive in its first vector argument. -/
lemma christoffelEval_add_left
    (cov : CovariantDerivative I E (TangentSpace I (M := M))) (x₀ p : M) (v₁ v₂ : E)
    (w : TangentSpace I p) (hp : p ∈ (chartAt H x₀).source) :
    christoffelEval cov x₀ p (v₁ + v₂) w
      = christoffelEval cov x₀ p v₁ w + christoffelEval cov x₀ p v₂ w := by
  have h₁ := mdiffAt_frameSection (I := I) x₀ v₁ hp
  have h₂ := mdiffAt_frameSection (I := I) x₀ v₂ hp
  rw [christoffelEval_def, frameSection_add, christoffelEval_def, christoffelEval_def]
  rw [cov.isCovariantDerivativeOn.add h₁ h₂]
  rw [ContinuousLinearMap.add_apply]
  exact map_add _ _ _

/-- `christoffelEval` is homogeneous in its first vector argument. -/
lemma christoffelEval_smul_left
    (cov : CovariantDerivative I E (TangentSpace I (M := M))) (x₀ p : M) (c : ℝ) (v : E)
    (w : TangentSpace I p) (hp : p ∈ (chartAt H x₀).source) :
    christoffelEval cov x₀ p (c • v) w = c • christoffelEval cov x₀ p v w := by
  have h₁ := mdiffAt_frameSection (I := I) x₀ v hp
  rw [christoffelEval_def, frameSection_smul, christoffelEval_def]
  rw [cov.isCovariantDerivativeOn.smul_const c h₁]
  rw [ContinuousLinearMap.smul_apply]
  exact map_smul _ _ _

/-- `christoffelEval` is additive in its second (direction) argument. -/
lemma christoffelEval_add_right
    (cov : CovariantDerivative I E (TangentSpace I (M := M))) (x₀ p : M) (v : E)
    (w₁ w₂ : TangentSpace I p) :
    christoffelEval cov x₀ p v (w₁ + w₂)
      = christoffelEval cov x₀ p v w₁ + christoffelEval cov x₀ p v w₂ := by
  rw [christoffelEval_def, christoffelEval_def, christoffelEval_def]
  rw [map_add, map_add]

/-- `christoffelEval` is homogeneous in its second (direction) argument. -/
lemma christoffelEval_smul_right
    (cov : CovariantDerivative I E (TangentSpace I (M := M))) (x₀ p : M) (c : ℝ) (v : E)
    (w : TangentSpace I p) :
    christoffelEval cov x₀ p v (c • w) = c • christoffelEval cov x₀ p v w := by
  rw [christoffelEval_def, christoffelEval_def]
  rw [map_smul, map_smul]

@[simp]
lemma christoffelEval_zero_left
    (cov : CovariantDerivative I E (TangentSpace I (M := M))) (x₀ p : M)
    (w : TangentSpace I p) :
    christoffelEval cov x₀ p 0 w = 0 := by
  rw [christoffelEval_def, frameSection_zero, CovariantDerivative.zero]
  simp only [Pi.zero_apply, zero_apply, map_zero]

@[simp]
lemma christoffelEval_zero_right
    (cov : CovariantDerivative I E (TangentSpace I (M := M))) (x₀ p : M) (v : E) :
    christoffelEval cov x₀ p v 0 = 0 := by
  rw [christoffelEval_def]
  rw [map_zero, map_zero]

/-! ## The geodesic equation in a chart

For a chart `e = extChartAt I x₀` and a curve `u : ℝ → E` in coordinates, the geodesic equation
`∇_{γ'} γ' = 0` for `γ = e.symm ∘ u` becomes the second-order ODE

  `u'' + christoffelEval cov x₀ (e.symm u) (u') (u') = 0`.

We package the right-hand side as `chartGeodesicVectorField`, and the equation as the first-order
system `IsGeodesicInChart`.  Picard–Lindelöf (`Commons.Analysis.ODE.exists_secondOrderODE_local_solution`)
then gives local solutions as soon as the chart vector field is `C¹`. -/

/-- The tangent vector at `p` with **coordinates** `v` in the chart at `x₀`: the image of `v`
under the inverse of the tangent-bundle trivialisation at `x₀` (junk value `0` outside the chart).
Note this is *not* the element `v` of `E` viewed as a tangent vector via the defeq
`TangentSpace I p = E`; the two differ by the coordinate change of the trivialisation. -/
noncomputable def frameVector (x₀ p : M) (v : E) : TangentSpace I p :=
  (trivializationAt E (TangentSpace I) x₀).symmL ℝ p v

lemma frameSection_eq_frameVector (x₀ : M) (v : E) :
    frameSection (I := I) x₀ v = fun q => frameVector (I := I) x₀ q v := rfl

/-- The right-hand side of the geodesic equation in the chart at `x₀`:
for `z = (y, v)` (a chart point and a chart velocity) it is `-Γ(y)(v, v)`, where the *second*
Christoffel slot is the tangent vector `frameVector x₀ y v` whose coordinates are `v`. -/
noncomputable def chartGeodesicVectorField
    (cov : CovariantDerivative I E (TangentSpace I (M := M))) (x₀ : M) (z : E × E) : E :=
  - christoffelEval cov x₀ ((extChartAt I x₀).symm z.1) z.2
      (frameVector (I := I) x₀ ((extChartAt I x₀).symm z.1) z.2)

/-- `u : ℝ → E` satisfies the **geodesic equation in the chart at `x₀`** if there is a velocity
field `v` with `u' = v` and `v' = -Γ(u)(v,v)`. -/
def IsGeodesicInChart (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (x₀ : M) (u : ℝ → E) : Prop :=
  ∃ v : ℝ → E, (∀ t : ℝ, HasDerivAt u (v t) t) ∧
    ∀ t : ℝ, HasDerivAt v (chartGeodesicVectorField cov x₀ (u t, v t)) t

/-- **Local existence for the geodesic equation in a chart** (Picard–Lindelöf): if the chart
vector field is `C¹` near `(p₀, v₀)`, there is a geodesic in the chart with `u 0 = p₀`,
`u' 0 = v₀`, defined on a neighbourhood of `0`. -/
theorem exists_isGeodesicInChart (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (x₀ : M) {p₀ v₀ : E}
    (hG : ContDiffAt ℝ 1 (chartGeodesicVectorField cov x₀) (p₀, v₀)) :
    ∃ ε > (0 : ℝ), ∃ u v : ℝ → E,
      u 0 = p₀ ∧ v 0 = v₀ ∧
      (∀ t ∈ Ioo (-ε) ε, HasDerivAt u (v t) t) ∧
      (∀ t ∈ Ioo (-ε) ε,
        HasDerivAt v (chartGeodesicVectorField cov x₀ (u t, v t)) t) :=
  Commons.Analysis.ODE.exists_secondOrderODE_local_solution hG

/-- **Local uniqueness for the geodesic equation in a chart**: two solutions with the same value
and velocity at `0` agree near `0`. -/
theorem isGeodesicInChart_unique (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (x₀ : M) (hG : ContDiff ℝ 1 (chartGeodesicVectorField cov x₀))
    {u₁ v₁ u₂ v₂ : ℝ → E} {ε₁ ε₂ : ℝ} (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂)
    (h₁ : ∀ t ∈ Ioo (-ε₁) ε₁, HasDerivAt u₁ (v₁ t) t ∧
      HasDerivAt v₁ (chartGeodesicVectorField cov x₀ (u₁ t, v₁ t)) t)
    (h₂ : ∀ t ∈ Ioo (-ε₂) ε₂, HasDerivAt u₂ (v₂ t) t ∧
      HasDerivAt v₂ (chartGeodesicVectorField cov x₀ (u₂ t, v₂ t)) t)
    (h0 : u₁ 0 = u₂ 0 ∧ v₁ 0 = v₂ 0) :
    ∃ δ > (0 : ℝ), δ ≤ ε₁ ∧ δ ≤ ε₂ ∧ ∀ t ∈ Ioo (-δ) δ, u₁ t = u₂ t :=
  Commons.Analysis.ODE.secondOrderODE_solution_unique hG hε₁ hε₂ h₁ h₂ h0

/-- **The coordinate velocity of a curve.**  If `γ` is differentiable at `t` and `γ t` is in the
chart at `x₀`, then the coordinates of the velocity `γ'(t)` are the derivative of the coordinate
curve `extChartAt I x₀ ∘ γ`. -/
lemma continuousLinearMapAt_curveVelocity (x₀ : M) {γ : ℝ → M} {t : ℝ}
    (hγ : MDifferentiableAt 𝓘(ℝ) I γ t) (hx : γ t ∈ (chartAt H x₀).source) :
    (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ (γ t)
        (curveVelocity (I := I) γ t)
      = mfderiv 𝓘(ℝ) 𝓘(ℝ, E) ((extChartAt I x₀) ∘ γ) t (1 : ℝ) := by
  rw [curveVelocity_apply,
    Commons.Geometry.Manifold.Tangent.mfderiv_extChartAt_comp (I := I) hγ hx]
  rfl

/-- **The Christoffel symbol computes `∇` of the coordinate frame.**  If `p` is in the chart at
`x₀`, the covariant derivative at `p` in direction `w` of the frame section with constant
coordinates `v` is the frame vector with coordinates `christoffelEval cov x₀ p v w`. -/
lemma cov_frameSection_eq (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (x₀ p : M) (v : E) (w : TangentSpace I p) (hp : p ∈ (chartAt H x₀).source) :
    cov (frameSection (I := I) x₀ v) p w =
      (trivializationAt E (TangentSpace I) x₀).symmL ℝ p (christoffelEval cov x₀ p v w) := by
  rw [christoffelEval_def]
  exact ((trivializationAt E (TangentSpace I) x₀).symmL_continuousLinearMapAt (R := ℝ)
    (by simpa using hp) (cov (frameSection (I := I) x₀ v) p w)).symm

/-- The `symm` form of `cov_frameSection_eq`. -/
lemma cov_frameSection_eq_symm (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (x₀ p : M) (v : E) (w : TangentSpace I p) (hp : p ∈ (chartAt H x₀).source) :
    cov (frameSection (I := I) x₀ v) p w =
      (trivializationAt E (TangentSpace I) x₀).symm p (christoffelEval cov x₀ p v w) := by
  rw [← Trivialization.symmL_apply (e := trivializationAt E (TangentSpace I) x₀) (R := ℝ)
    (by simpa using hp)]
  exact cov_frameSection_eq cov x₀ p v w hp

/-- **Torsion-freeness makes the Christoffel symbol symmetric.**  The sections `frameSection x₀ v`
are the coordinate vector fields of the chart at `x₀`; their Lie bracket vanishes
(`Commons.Geometry.Manifold.VectorField.mlieBracket_trivializationAt_symmL_smooth`), so
`cov.torsion = 0` gives `∇_{σ_v} σ_w = ∇_{σ_w} σ_v`. -/
theorem cov_frameSection_frameVector_comm
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    (htor : cov.torsion = 0) (x₀ p : M) (hp : p ∈ (chartAt H x₀).source) (v w : E) :
    cov (frameSection (I := I) x₀ v) p (frameVector (I := I) x₀ p w)
      = cov (frameSection (I := I) x₀ w) p (frameVector (I := I) x₀ p v) := by
  have hX : MDiffAt (T% (frameSection (I := I) x₀ v)) p := mdiffAt_frameSection x₀ v hp
  have hY : MDiffAt (T% (frameSection (I := I) x₀ w)) p := mdiffAt_frameSection x₀ w hp
  have h := (CovariantDerivative.torsion_eq_zero_iff (cov := cov)).mp htor hX hY
  have hbr : mlieBracket I (frameSection (I := I) x₀ v) (frameSection (I := I) x₀ w) p = 0 :=
    Commons.Geometry.Manifold.VectorField.mlieBracket_trivializationAt_symmL_smooth
      (I := I) x₀ v w hp
  rw [hbr] at h
  rw [show frameSection (I := I) x₀ v p = frameVector (I := I) x₀ p v from rfl,
    show frameSection (I := I) x₀ w p = frameVector (I := I) x₀ p w from rfl] at h
  exact (sub_eq_zero.mp h).symm

/-- **Symmetry of the Christoffel symbol** (the coordinate form of torsion-freeness):
`Γ(v)(w) = Γ(w)(v)` for tangent vectors with coordinates `v`, `w`. -/
theorem christoffelEval_comm
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    (htor : cov.torsion = 0) (x₀ p : M) (hp : p ∈ (chartAt H x₀).source) (v w : E) :
    christoffelEval cov x₀ p v (frameVector (I := I) x₀ p w)
      = christoffelEval cov x₀ p w (frameVector (I := I) x₀ p v) := by
  simp only [christoffelEval_def]
  rw [cov_frameSection_frameVector_comm htor x₀ p hp v w]

/-- **The velocity of a curve given in a chart.**  If `u` has derivative `v` at `t` and stays in
the target of the chart at `x₀` near `t`, then the velocity of `s ↦ (extChartAt I x₀).symm (u s)`
at `t` is the frame vector with coordinates `v`. -/
lemma curveVelocity_extChartAt_symm {x₀ : M} {u : ℝ → E} {t : ℝ} {v : E}
    (hu : HasDerivAt u v t) (ht : u t ∈ (extChartAt I x₀).target)
    (hstay : ∀ᶠ s in 𝓝 t, u s ∈ (extChartAt I x₀).target) :
    curveVelocity (I := I) (fun s => (extChartAt I x₀).symm (u s)) t
      = (trivializationAt E (TangentSpace I) x₀).symmL ℝ ((extChartAt I x₀).symm (u t)) v := by
  have h := (Commons.Geometry.Manifold.Tangent.hasMFDerivAt_extChartAt_symm_comp
    (I := I) hu ht hstay).mfderiv
  rw [curveVelocity_apply, h]
  change (trivializationAt E (TangentSpace I) x₀).symmL ℝ ((extChartAt I x₀).symm (u t))
      ((ContinuousLinearMap.toSpanSingleton ℝ v) 1)
    = (trivializationAt E (TangentSpace I) x₀).symmL ℝ ((extChartAt I x₀).symm (u t)) v
  rw [ContinuousLinearMap.toSpanSingleton_apply, one_smul]

/-- The coordinates of a smooth section in the chart at `x₀` are smooth at every point of the
chart. -/
lemma contMDiffAt_continuousLinearMapAt_apply (x₀ : M) {Z : Π x : M, TangentSpace I x} {x : M}
    (hZ : CMDiffAt ∞ (T% Z) x) (hx : x ∈ (chartAt H x₀).source) :
    CMDiffAt ∞ (fun y => (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ y
      (Z y)) x := by
  have hsec := (Trivialization.contMDiffAt_section_iff
    (trivializationAt E (TangentSpace I) x₀) (by simpa using hx)).mp hZ
  refine hsec.congr_of_eventuallyEq ?_
  filter_upwards [(trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds
    (by simpa using hx)] with y hy
  rw [Trivialization.continuousLinearMapAt_apply_of_mem
    (e := trivializationAt E (TangentSpace I) x₀) (R := ℝ) hy]

lemma frameVector_sum {ι : Type*} (s : Finset ι) (x₀ p : M) (c : ι → ℝ) (w : ι → E) :
    frameVector (I := I) x₀ p (∑ i ∈ s, c i • w i)
      = ∑ i ∈ s, c i • frameVector (I := I) x₀ p (w i) := by
  show (trivializationAt E (TangentSpace I) x₀).symmL ℝ p (∑ i ∈ s, c i • w i)
      = ∑ i ∈ s, c i • (trivializationAt E (TangentSpace I) x₀).symmL ℝ p (w i)
  rw [map_sum]
  simp_rw [map_smul]

lemma frameVector_neg (x₀ p : M) (v : E) :
    frameVector (I := I) x₀ p (-v) = -frameVector (I := I) x₀ p v := map_neg _ v

lemma christoffelEval_sum_left {ι : Type*} (s : Finset ι)
    (cov : CovariantDerivative I E (TangentSpace I (M := M))) (x₀ p : M) (c : ι → ℝ) (w : ι → E)
    (u : TangentSpace I p) (hp : p ∈ (chartAt H x₀).source) :
    christoffelEval cov x₀ p (∑ i ∈ s, c i • w i) u
      = ∑ i ∈ s, c i • christoffelEval cov x₀ p (w i) u := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      rw [christoffelEval_add_left cov x₀ p (c a • w a) (∑ i ∈ s, c i • w i) u hp,
        christoffelEval_smul_left cov x₀ p (c a) (w a) u hp, ih]

theorem cov_eq_zero_of_chartGeodesic
    (cov : CovariantDerivative I E (TangentSpace I (M := M))) (x₀ : M)
    {u v : ℝ → E} {a b t : ℝ} (ht : t ∈ Ioo a b)
    (hu : ∀ s ∈ Ioo a b, HasDerivAt u (v s) s)
    (hv : ∀ s ∈ Ioo a b, HasDerivAt v (chartGeodesicVectorField cov x₀ (u s, v s)) s)
    (hstay : ∀ s ∈ Ioo a b, u s ∈ (extChartAt I x₀).target)
    (Z : Π x : M, TangentSpace I x)
    (hZ : CMDiffAt ∞ (T% Z) ((extChartAt I x₀).symm (u t)))
    (hZeq : ∀ s ∈ Ioo a b, Z ((extChartAt I x₀).symm (u s)) =
      curveVelocity (I := I) (fun s => (extChartAt I x₀).symm (u s)) s) :
    cov Z ((extChartAt I x₀).symm (u t))
      (curveVelocity (I := I) (fun s => (extChartAt I x₀).symm (u s)) t) = 0 := by
  classical
  let γ : ℝ → M := fun s => (extChartAt I x₀).symm (u s)
  change cov Z (γ t) (curveVelocity (I := I) γ t) = 0
  have hZeq' : ∀ s ∈ Ioo a b, Z (γ s) = curveVelocity (I := I) γ s := fun s hs => hZeq s hs
  have hZ' : CMDiffAt ∞ (T% Z) (γ t) := hZ
  have htgt : u t ∈ (extChartAt I x₀).target := hstay t ht
  have hmem : ∀ s ∈ Ioo a b, γ s ∈ (chartAt H x₀).source := by
    intro s hs
    have h1 := PartialEquiv.target_subset_preimage_source (extChartAt I x₀) (hstay s hs)
    rwa [extChartAt_source] at h1
  have hsrc : γ t ∈ (chartAt H x₀).source := hmem t ht
  have hOoo : Ioo a b ∈ 𝓝 t := IsOpen.mem_nhds isOpen_Ioo ht
  have hvelAt : ∀ s ∈ Ioo a b, curveVelocity (I := I) γ s = frameVector (I := I) x₀ (γ s) (v s) := by
    intro s hs
    have h := curveVelocity_extChartAt_symm (I := I) (x₀ := x₀) (u := u) (t := s) (v := v s)
      (hu s hs) (hstay s hs)
      (Filter.mem_of_superset (IsOpen.mem_nhds isOpen_Ioo hs) (fun r hr => hstay r hr))
    simpa [frameVector, γ] using h
  have hnear : ∀ᶠ s in 𝓝 t, u s ∈ (extChartAt I x₀).target :=
    Filter.mem_of_superset hOoo (fun s hs => hstay s hs)
  have hvel : curveVelocity (I := I) γ t = frameVector (I := I) x₀ (γ t) (v t) := hvelAt t ht
  have hmdγ : MDifferentiableAt 𝓘(ℝ) I γ t :=
    (Commons.Geometry.Manifold.Tangent.hasMFDerivAt_extChartAt_symm_comp (I := I) (x₀ := x₀)
      (u := u) (t := t) (v := v t) (hu t ht) htgt hnear).mdifferentiableAt
  -- the value of `Z` at `γ t`
  have hZval :
      (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ (γ t) (Z (γ t)) = v t := by
    have hcont : ContinuousAt (fun y : M =>
        (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ y (Z y)) (γ t) :=
      (contMDiffAt_continuousLinearMapAt_apply (I := I) x₀ hZ' hsrc).continuousAt
    have hT1 : Filter.Tendsto (fun s => (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ
        (γ s) (Z (γ s))) (𝓝 t)
        (𝓝 ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ (γ t) (Z (γ t)))) :=
      (hcont.comp hmdγ.continuousAt).tendsto
    have hev : (fun s => (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ
        (γ s) (Z (γ s))) =ᶠ[𝓝 t] v := by
      filter_upwards [hOoo] with s hs
      rw [hZeq' s hs, hvelAt s hs]
      exact continuousLinearMapAt_frameSection (I := I) x₀ (v s) (hmem s hs)
    have hT2 : Filter.Tendsto (fun s => (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ
        (γ s) (Z (γ s))) (𝓝 t) (𝓝 (v t)) :=
      ((hv t ht).continuousAt.tendsto).congr' hev.symm
    exact tendsto_nhds_unique hT1 hT2
  -- the basis and the frame
  let b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := Module.finBasis ℝ E
  let σ : Fin (Module.finrank ℝ E) → Π x : M, TangentSpace I x :=
    fun i => frameSection (I := I) x₀ (b i)
  let f : Fin (Module.finrank ℝ E) → M → ℝ := fun i y =>
    b.coord i ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ y (Z y))
  have hσsm : ∀ i, CMDiffAt ∞ (T% (σ i)) (γ t) := fun i => by
    simpa [σ] using contMDiffAt_frameSection (I := I) x₀ (b i) hsrc
  have hfsm : ∀ i, CMDiffAt ∞ (f i) (γ t) := fun i => by
    have hg := contMDiffAt_continuousLinearMapAt_apply (I := I) x₀ hZ' hsrc
    have hcomp : CMDiffAt ∞ (fun y : M =>
        ((b.coord i : E →ₗ[ℝ] ℝ).toContinuousLinearMap)
          ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ y (Z y))) (γ t) :=
      ContMDiffAt.comp (γ t)
        (ContinuousLinearMap.contMDiffAt ((b.coord i : E →ₗ[ℝ] ℝ).toContinuousLinearMap)) hg
    simpa [f, Function.comp, LinearMap.coe_toContinuousLinearMap'] using hcomp
  have hdec : Z =ᶠ[𝓝 (γ t)] fun y => ∑ i, f i y • σ i y := by
    filter_upwards [(chartAt H x₀).open_source.mem_nhds hsrc] with y hy
    have h := Commons.Geometry.Manifold.Tangent.eqOn_sum_frameSection_of_basis (I := I) b x₀ Z hy
    simpa [f, σ, frameSection] using h
  have hmain :=
    Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.cov_eq_sum_of_eventuallyEq_pointwise
      (cov := cov) (s := Finset.univ) (f := f) (σ := σ) (Z := Z) (x := γ t)
      (v := curveVelocity (I := I) γ t) hZ' hσsm hfsm hdec
  have hfx : ∀ i, f i (γ t) = b.coord i (v t) := by
    intro i
    simp only [f, hZval]
  have hcov : ∀ i, cov (σ i) (γ t) (curveVelocity (I := I) γ t)
      = frameVector (I := I) x₀ (γ t)
          (christoffelEval cov x₀ (γ t) (b i) (curveVelocity (I := I) γ t)) := by
    intro i
    have h := cov_frameSection_eq cov x₀ (γ t) (b i) (curveVelocity (I := I) γ t) hsrc
    simpa only [σ, frameVector] using h
  have hder : ∀ i, mvfderiv I (f i) (γ t) (curveVelocity (I := I) γ t)
      = b.coord i (chartGeodesicVectorField cov x₀ (u t, v t)) := by
    intro i
    have hmdf : MDifferentiableAt I 𝓘(ℝ, ℝ) (f i) (γ t) := (hfsm i).mdifferentiableAt (by simp)
    have hcomp := Commons.Geometry.Manifold.Tangent.mvfderiv_comp_curve (I := I) hmdf hmdγ
    have hcongr : deriv (f i ∘ γ) t = deriv (fun s => b.coord i (v s)) t := by
      apply Filter.EventuallyEq.deriv_eq
      filter_upwards [hOoo] with s hs
      show f i (γ s) = b.coord i (v s)
      simp only [f]
      rw [hZeq' s hs, hvelAt s hs]
      exact congrArg (b.coord i) (continuousLinearMapAt_frameSection (I := I) x₀ (v s) (hmem s hs))
    have hlinear : deriv (fun s => b.coord i (v s)) t
        = b.coord i (chartGeodesicVectorField cov x₀ (u t, v t)) := by
      have hd : HasDerivAt (fun s => b.coord i (v s))
          (b.coord i (chartGeodesicVectorField cov x₀ (u t, v t))) t :=
        (((b.coord i : E →ₗ[ℝ] ℝ).toContinuousLinearMap).hasFDerivAt.comp_hasDerivAt
          t (hv t ht))
      exact hd.deriv
    change mvfderiv I (f i) (γ t) (mfderiv 𝓘(ℝ) I γ t (1 : ℝ))
      = b.coord i (chartGeodesicVectorField cov x₀ (u t, v t))
    rw [hcomp, hcongr, hlinear]
  rw [hmain]
  have hS1 : (∑ i : Fin (Module.finrank ℝ E),
        f i (γ t) • cov (σ i) (γ t) (curveVelocity (I := I) γ t))
      = frameVector (I := I) x₀ (γ t)
          (christoffelEval cov x₀ (γ t) (v t) (curveVelocity (I := I) γ t)) := by
    have h1 : (∑ i : Fin (Module.finrank ℝ E),
          f i (γ t) • cov (σ i) (γ t) (curveVelocity (I := I) γ t))
        = ∑ i, b.coord i (v t) • frameVector (I := I) x₀ (γ t)
            (christoffelEval cov x₀ (γ t) (b i) (curveVelocity (I := I) γ t)) :=
      Finset.sum_congr rfl (fun i _ => by rw [hfx i, hcov i])
    have h2 : (∑ i, b.coord i (v t) • frameVector (I := I) x₀ (γ t)
            (christoffelEval cov x₀ (γ t) (b i) (curveVelocity (I := I) γ t)))
        = frameVector (I := I) x₀ (γ t)
            (christoffelEval cov x₀ (γ t) (v t) (curveVelocity (I := I) γ t)) := by
      rw [← frameVector_sum, ← christoffelEval_sum_left Finset.univ cov x₀ (γ t)
        (fun i => b.coord i (v t)) (fun i => b i) (curveVelocity (I := I) γ t) hsrc]
      have hbv : (∑ i, b.coord i (v t) • b i) = v t := by
        simpa only [Module.Basis.coord_apply] using b.sum_repr (v t)
      rw [hbv]
    rw [h1, h2]
  have hS2 : (∑ i : Fin (Module.finrank ℝ E),
        mvfderiv I (f i) (γ t) (curveVelocity (I := I) γ t) • σ i (γ t))
      = frameVector (I := I) x₀ (γ t) (chartGeodesicVectorField cov x₀ (u t, v t)) := by
    have h1 : (∑ i : Fin (Module.finrank ℝ E),
          mvfderiv I (f i) (γ t) (curveVelocity (I := I) γ t) • σ i (γ t))
        = ∑ i, b.coord i (chartGeodesicVectorField cov x₀ (u t, v t)) •
            frameVector (I := I) x₀ (γ t) (b i) :=
      Finset.sum_congr rfl (fun i _ => by rw [hder i]; simp only [σ, frameSection, frameVector])
    have h2 : (∑ i, b.coord i (chartGeodesicVectorField cov x₀ (u t, v t)) •
            frameVector (I := I) x₀ (γ t) (b i))
        = frameVector (I := I) x₀ (γ t) (chartGeodesicVectorField cov x₀ (u t, v t)) := by
      rw [← frameVector_sum]
      have hbv : (∑ i, b.coord i (chartGeodesicVectorField cov x₀ (u t, v t)) • b i)
          = chartGeodesicVectorField cov x₀ (u t, v t) := by
        simpa only [Module.Basis.coord_apply] using
          b.sum_repr (chartGeodesicVectorField cov x₀ (u t, v t))
      rw [hbv]
    rw [h1, h2]
  rw [hS1, hS2]
  have hG : chartGeodesicVectorField cov x₀ (u t, v t)
      = -christoffelEval cov x₀ (γ t) (v t) (curveVelocity (I := I) γ t) := by
    change -christoffelEval cov x₀ (γ t) (v t) (frameVector (I := I) x₀ (γ t) (v t)) = _
    rw [hvel]
  rw [hG, frameVector_neg]
  exact add_neg_cancel _

/-- **A chart solution of the geodesic equation is a geodesic.**  If `u : ℝ → E` solves the
geodesic equation `u'' = -Γ(u')(u')` in the chart at `x₀` and stays in the target of that chart,
then the curve `t ↦ (extChartAt I x₀).symm (u t)` is a geodesic for `cov`. -/
theorem isGeodesic_of_isGeodesicInChart
    (cov : CovariantDerivative I E (TangentSpace I (M := M))) (x₀ : M) {u : ℝ → E}
    (h : IsGeodesicInChart cov x₀ u) (hstay : ∀ t, u t ∈ (extChartAt I x₀).target) :
    IsGeodesic cov (fun s => (extChartAt I x₀).symm (u s)) := by
  intro t Z hZ hZeq
  obtain ⟨v, hu, hv⟩ := h
  obtain ⟨δ, hδ, hδsub⟩ := (nhds_basis_Ioo_pos t).mem_iff.mp hZeq
  exact cov_eq_zero_of_chartGeodesic cov x₀ (a := t - δ) (b := t + δ)
    ⟨sub_lt_self t hδ, lt_add_of_pos_right t hδ⟩
    (fun s _ => hu s) (fun s _ => hv s) (fun s _ => hstay s) Z hZ.contMDiffAt (fun s hs => hδsub hs)

/-- The frame vector is linear in the coordinate vector. -/
lemma frameVector_smul (x₀ p : M) (c : ℝ) (v : E) :
    frameVector (I := I) x₀ p (c • v) = c • frameVector (I := I) x₀ p v := map_smul _ c v

lemma frameVector_add (x₀ p : M) (v w : E) :
    frameVector (I := I) x₀ p (v + w)
      = frameVector (I := I) x₀ p v + frameVector (I := I) x₀ p w := map_add _ v w

/-! ## Homogeneity of the geodesic equation

The chart geodesic spray `-Γ(y)(v)(v)` is homogeneous of degree two in the velocity.  It follows
that if `u` solves the chart geodesic equation with velocity `v`, then `s ↦ u (c * s)` solves it
with velocity `s ↦ c • v (c * s)`; this is what makes the exponential map well defined on a
neighbourhood of the origin of `T_x M`. -/

/-- The geodesic spray of a chart is homogeneous of degree two in the velocity. -/
lemma chartGeodesicVectorField_smul
    (cov : CovariantDerivative I E (TangentSpace I (M := M))) (x₀ : M) (c : ℝ) (z : E × E)
    (hz : z.1 ∈ (extChartAt I x₀).target) :
    chartGeodesicVectorField cov x₀ (z.1, c • z.2)
      = c ^ 2 • chartGeodesicVectorField cov x₀ z := by
  have hsrc : (extChartAt I x₀).symm z.1 ∈ (chartAt H x₀).source := by
    have h := PartialEquiv.target_subset_preimage_source (extChartAt I x₀) hz
    rwa [extChartAt_source] at h
  rw [chartGeodesicVectorField, chartGeodesicVectorField, frameVector_smul]
  rw [christoffelEval_smul_right]
  rw [christoffelEval_smul_left cov x₀ ((extChartAt I x₀).symm z.1) c z.2
    (frameVector (I := I) x₀ ((extChartAt I x₀).symm z.1) z.2) hsrc]
  rw [pow_two, smul_neg, smul_smul]

/-- The chart geodesic equation is invariant under the scaling `t ↦ c * t`, `v ↦ c • v`. -/
lemma isGeodesicInChart_comp_mul
    (cov : CovariantDerivative I E (TangentSpace I (M := M))) (x₀ : M) (c : ℝ) {u v : ℝ → E}
    (hu : ∀ t, HasDerivAt u (v t) t)
    (hv : ∀ t, HasDerivAt v (chartGeodesicVectorField cov x₀ (u t, v t)) t)
    (htgt : ∀ t, u t ∈ (extChartAt I x₀).target) :
    (∀ t, HasDerivAt (fun s => u (c * s)) (c • v (c * t)) t) ∧
    (∀ t, HasDerivAt (fun s => c • v (c * s))
      (chartGeodesicVectorField cov x₀ (u (c * t), c • v (c * t))) t) := by
  constructor
  · intro t
    exact (hu (c * t)).scomp t (hasDerivAt_const_mul c)
  · intro t
    have h1 : HasDerivAt (fun s => v (c * s))
        (c • chartGeodesicVectorField cov x₀ (u (c * t), v (c * t))) t :=
      (hv (c * t)).scomp t (hasDerivAt_const_mul c)
    have h2 : HasDerivAt (fun s => c • v (c * s))
        (c • (c • chartGeodesicVectorField cov x₀ (u (c * t), v (c * t)))) t :=
      h1.const_smul c
    have h3 : c • (c • chartGeodesicVectorField cov x₀ (u (c * t), v (c * t)))
        = chartGeodesicVectorField cov x₀ (u (c * t), c • v (c * t)) := by
      rw [smul_smul, ← pow_two]
      rw [← chartGeodesicVectorField_smul cov x₀ c (u (c * t), v (c * t)) (htgt (c * t))]
    rwa [h3] at h2

/-! ## The exponential map

The exponential map at `x` is the time-`1` value of the geodesic starting at `x` with prescribed
velocity.  We build it from solutions of the chart geodesic equation in the chart at `x`; the
uniform local existence for the spray makes the set of admissible velocities a neighbourhood of
`0` in `T_x M`, and uniqueness makes the definition independent of the chosen solution. -/

/-- A solution of the chart geodesic equation in the chart at `x`, with initial position
`(extChartAt I x) x` and initial velocity the coordinates of the tangent vector `v`, defined on the
fixed interval `Ioo (-2) 2` (which contains `[0,1]`) and staying in the chart. -/
def HasChartGeodesic (cov : CovariantDerivative I E (TangentSpace I (M := M))) (x : M)
    (v : TangentSpace I x) (u w : ℝ → E) : Prop :=
  u 0 = (extChartAt I x) x ∧
    w 0 = (trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ x v ∧
    (∀ t ∈ Ioo (-2) 2, u t ∈ (extChartAt I x).target) ∧
    (∀ t ∈ Ioo (-2) 2, HasDerivAt u (w t) t) ∧
    (∀ t ∈ Ioo (-2) 2, HasDerivAt w (chartGeodesicVectorField cov x (u t, w t)) t)

/-- **The exponential map** at `x` for the covariant derivative `cov`: the time-`1` value of a
geodesic starting at `x` with velocity `v`.  It is defined on the set of `v` admitting such a
geodesic on `Ioo (-2) 2` inside the chart at `x`; outside that set it takes the junk value `x`. -/
noncomputable def expMap (cov : CovariantDerivative I E (TangentSpace I (M := M))) (x : M)
    (v : TangentSpace I x) : M := by
  classical
  exact if h : ∃ u w : ℝ → E, HasChartGeodesic cov x v u w then
    (extChartAt I x).symm ((Classical.choose h) 1)
  else x

/-- The constant curve is a chart geodesic through `(extChartAt I x) x` with zero velocity. -/
theorem hasChartGeodesic_zero (cov : CovariantDerivative I E (TangentSpace I (M := M))) (x : M) :
    HasChartGeodesic cov x (0 : TangentSpace I x)
      (fun _ : ℝ => (extChartAt I x) x) (fun _ : ℝ => (0 : E)) := by
  have htgt : (extChartAt I x) x ∈ (extChartAt I x).target :=
    PartialEquiv.map_source (extChartAt I x) (mem_extChartAt_source x)
  have hG0 : chartGeodesicVectorField cov x ((extChartAt I x) x, (0 : E)) = 0 := by
    rw [chartGeodesicVectorField]
    simp only [frameVector, map_zero, christoffelEval_zero_left, neg_zero]
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · simp
  · intro t ht; exact htgt
  · intro t ht; exact hasDerivAt_const t _
  · intro t ht; rw [hG0]; exact hasDerivAt_const t 0

/-- **A chart geodesic is a geodesic.**  On the interval `Ioo (-2) 2` on which the chart solution
is defined and stays in the chart, the curve `t ↦ (extChartAt I x).symm (u t)` satisfies the
geodesic equation. -/
theorem isGeodesicAt_chartSolution {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    {x : M} {v : TangentSpace I x} {u w : ℝ → E}
    (h : HasChartGeodesic cov x v u w) {t : ℝ} (ht : t ∈ Ioo (-2) 2) :
    IsGeodesicAt cov (fun s => (extChartAt I x).symm (u s)) t := by
  intro Z hZ hZeq
  obtain ⟨δ, hδ, hδsub⟩ := (nhds_basis_Ioo_pos t).mem_iff.mp hZeq
  have htI : t ∈ Ioo (max (-2) (t - δ)) (min 2 (t + δ)) :=
    ⟨max_lt (by linarith [ht.1]) (by linarith),
     lt_min (by linarith [ht.2]) (by linarith)⟩
  refine cov_eq_zero_of_chartGeodesic cov x htI
    (fun s hs => h.2.2.2.1 s ⟨lt_of_le_of_lt (le_max_left _ _) hs.1,
      lt_of_lt_of_le hs.2 (min_le_left _ _)⟩)
    (fun s hs => h.2.2.2.2 s ⟨lt_of_le_of_lt (le_max_left _ _) hs.1,
      lt_of_lt_of_le hs.2 (min_le_left _ _)⟩)
    (fun s hs => h.2.2.1 s ⟨lt_of_le_of_lt (le_max_left _ _) hs.1,
      lt_of_lt_of_le hs.2 (min_le_left _ _)⟩) Z hZ.contMDiffAt
    (fun s hs => hδsub ⟨lt_of_le_of_lt (le_max_right _ _) hs.1,
      lt_of_lt_of_le hs.2 (min_le_right _ _)⟩)

/-- **A globally smooth field agreeing with the chart geodesic spray near the origin of the
chart.**  The spray is only `C^∞` on the chart, so it is multiplied by a smooth bump function
supported in the chart; the result agrees with the spray on an open neighbourhood of `(e x₀, 0)`,
which is where the local theory of the geodesic equation is used. -/
theorem exists_contMDiff_spray_extension
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞] [I.Boundaryless] (x₀ : M) :
    ∃ (U : Set (E × E)) (G : E × E → E), IsOpen U ∧ ((extChartAt I x₀) x₀, (0 : E)) ∈ U ∧
      U ⊆ (extChartAt I x₀).target ×ˢ (univ : Set E) ∧
      (∀ z ∈ U, G z = chartGeodesicVectorField cov x₀ z) ∧
      ContMDiff 𝓘(ℝ, E × E) 𝓘(ℝ, E) ∞ G ∧ G ((extChartAt I x₀) x₀, 0) = 0 := by
  have hz₀ : ((extChartAt I x₀) x₀, (0 : E)) ∈ (extChartAt I x₀).target ×ˢ (univ : Set E) :=
    ⟨mem_extChartAt_target x₀, mem_univ _⟩
  have hnb : (extChartAt I x₀).target ×ˢ (univ : Set E) ∈ 𝓝 ((extChartAt I x₀) x₀, (0 : E)) :=
    ((isOpen_extChartAt_target x₀).prod isOpen_univ).mem_nhds hz₀
  obtain ⟨ψ, -, hψts⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓘(ℝ, E × E))
      ((extChartAt I x₀) x₀, (0 : E))).mem_iff.mp hnb
  obtain ⟨s, hs, hsub⟩ := Filter.eventually_iff_exists_mem.mp ψ.eventuallyEq_one
  obtain ⟨U, hUs, hUopen, hz0U⟩ := _root_.mem_nhds_iff.mp hs
  refine ⟨U, fun z => ψ z • chartGeodesicVectorField cov x₀ z, hUopen, hz0U, ?_, ?_, ?_, ?_⟩
  · intro z hz
    refine hψts (subset_closure ?_)
    have h1 : (ψ : E × E → ℝ) z = 1 := hsub z (hUs hz)
    exact fun hzero => one_ne_zero (h1 ▸ hzero)
  · intro z hz
    have h1 : ψ z = 1 := hsub z (hUs hz)
    simp only [h1, one_smul]
  · -- smoothness of the product
    have hspray_on : ContMDiffOn 𝓘(ℝ, E × E) 𝓘(ℝ, E) ∞ (chartGeodesicVectorField cov x₀)
        ((extChartAt I x₀).target ×ˢ (univ : Set E)) :=
      (Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contDiffOn_chartSpray (cov := cov) x₀).contMDiffOn
    have htarget : (extChartAt I x₀).target ×ˢ (univ : Set E) ∈ 𝓝
        ((extChartAt I x₀) x₀, (0 : E)) := hnb
    refine contMDiff_of_tsupport (f := fun z => ψ z • chartGeodesicVectorField cov x₀ z) ?_
    intro z hz
    have hzψ : z ∈ tsupport (ψ : E × E → ℝ) := tsupport_smul_subset_left _ _ hz
    have hztgt : z ∈ (extChartAt I x₀).target ×ˢ (univ : Set E) := hψts hzψ
    have hnbz : (extChartAt I x₀).target ×ˢ (univ : Set E) ∈ 𝓝 z :=
      ((isOpen_extChartAt_target x₀).prod isOpen_univ).mem_nhds hztgt
    exact (ψ.contMDiff.contMDiffAt).smul
      ((hspray_on z hztgt).contMDiffAt hnbz)
  · have hG0 : chartGeodesicVectorField cov x₀ ((extChartAt I x₀) x₀, (0 : E)) = 0 := by
      rw [chartGeodesicVectorField]
      simp only [frameVector, map_zero]
      exact neg_eq_zero.mpr (christoffelEval_zero_left cov x₀
        ((extChartAt I x₀).symm ((extChartAt I x₀) x₀))
        (0 : TangentSpace I ((extChartAt I x₀).symm ((extChartAt I x₀) x₀))))
    show ψ ((extChartAt I x₀) x₀, (0 : E)) •
      chartGeodesicVectorField cov x₀ ((extChartAt I x₀) x₀, (0 : E)) = 0
    rw [hG0, smul_zero]

/-- Scaling a chart geodesic in time by a factor `c` with `|c| ≤ 1` gives a chart geodesic with
velocity `c • v`. -/
theorem hasChartGeodesic_const_smul {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    {x : M} {v : TangentSpace I x} {u w : ℝ → E} {c : ℝ} (hc : |c| ≤ 1)
    (h : HasChartGeodesic cov x v u w) :
    HasChartGeodesic cov x (c • v) (fun τ => u (c * τ)) (fun τ => c • w (c * τ)) := by
  have hmem : ∀ {τ : ℝ}, τ ∈ Ioo (-2) 2 → c * τ ∈ Ioo (-2) 2 := by
    intro τ hτ
    have h1 : |c * τ| < 2 := by
      rw [abs_mul]
      have h2 : |τ| < 2 := abs_lt.mpr hτ
      nlinarith [abs_nonneg c, abs_nonneg τ, hc, h2]
    exact abs_lt.mp h1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show u (c * 0) = (extChartAt I x) x
    rw [mul_zero]; exact h.1
  · show c • w (c * 0) = _
    rw [mul_zero, h.2.1, map_smul]
  · intro τ hτ
    exact h.2.2.1 (c * τ) (hmem hτ)
  · intro τ hτ
    exact (h.2.2.2.1 (c * τ) (hmem hτ)).scomp τ (hasDerivAt_const_mul c)
  · intro τ hτ
    have hv : HasDerivAt w (chartGeodesicVectorField cov x (u (c * τ), w (c * τ))) (c * τ) :=
      h.2.2.2.2 (c * τ) (hmem hτ)
    have h1 : HasDerivAt (fun τ => w (c * τ))
        (c • chartGeodesicVectorField cov x (u (c * τ), w (c * τ))) τ :=
      hv.scomp τ (hasDerivAt_const_mul c)
    have h2 : HasDerivAt (fun τ => c • w (c * τ))
        (c • (c • chartGeodesicVectorField cov x (u (c * τ), w (c * τ)))) τ :=
      h1.const_smul c
    have h3 : c • (c • chartGeodesicVectorField cov x (u (c * τ), w (c * τ)))
        = chartGeodesicVectorField cov x (u (c * τ), c • w (c * τ)) := by
      rw [smul_smul, ← pow_two]
      rw [← chartGeodesicVectorField_smul cov x c (u (c * τ), w (c * τ))
        (h.2.2.1 (c * τ) (hmem hτ))]
    rwa [h3] at h2


/-! ## Uniqueness of chart geodesics, and the exponential map

All statements in this section assume `[I.Boundaryless]`, which is what makes the chart target
`(extChartAt I x).target` open; the geodesic spray is only `C^∞` *on* the chart. -/

section Boundaryless

variable [I.Boundaryless]

/-- The chart-geodesic spray is `C¹` at the points of a chart geodesic. -/
lemma contDiffAt_spray_of_hasChartGeodesic
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    {x : M} {v : TangentSpace I x} {u w : ℝ → E}
    (h : HasChartGeodesic cov x v u w) {t : ℝ} (ht : t ∈ Ioo (-2) 2) :
    ContDiffAt ℝ 1 (chartGeodesicVectorField cov x) (u t, w t) := by
  have hz : (u t, w t) ∈ (extChartAt I x).target ×ˢ (univ : Set E) :=
    ⟨h.2.2.1 t ht, mem_univ _⟩
  have hnb : (extChartAt I x).target ×ˢ (univ : Set E) ∈ 𝓝 (u t, w t) :=
    ((isOpen_extChartAt_target x).prod isOpen_univ).mem_nhds hz
  exact (((Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contDiffOn_chartSpray
      (cov := cov) x) (u t, w t) hz).contDiffAt hnb).of_le (by norm_num)

/-- Local agreement of two chart geodesics with the same state at a time `t`. -/
lemma hasChartGeodesic_local_eq {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    {x : M} {v : TangentSpace I x} {u w u' w' : ℝ → E}
    (h : HasChartGeodesic cov x v u w) (h' : HasChartGeodesic cov x v u' w')
    {t : ℝ} (ht : t ∈ Ioo (-2) 2) (heq : u t = u' t) (heqw : w t = w' t) :
    ∃ δ > 0, ∀ σ ∈ Ioo (t - δ) (t + δ), u σ = u' σ ∧ w σ = w' σ := by
  have hmin : 0 < min (2 - t) (t + 2) := lt_min (by linarith [ht.2]) (by linarith [ht.1])
  set ε : ℝ := min (2 - t) (t + 2) / 2 with hεdef
  have hε : 0 < ε := by positivity
  have hεle : ε ≤ min (2 - t) (t + 2) := by rw [hεdef]; linarith [hmin]
  set sh : ℝ → ℝ := fun y => t + y with hsh
  have hsub : ∀ τ ∈ Ioo (-ε) ε, t + τ ∈ Ioo (-2 : ℝ) 2 := by
    intro τ hτ
    have h4 := abs_lt.mp (abs_lt.mpr hτ : |τ| < ε)
    have h5 := min_le_left (2 - t) (t + 2)
    have h6 := min_le_right (2 - t) (t + 2)
    constructor <;> linarith
  have hsh_deriv : ∀ τ : ℝ, HasDerivAt sh 1 τ := fun τ => by
    have := (hasDerivAt_id τ).const_add t
    simpa [hsh] using this
  have h₁ : ∀ τ ∈ Ioo (-ε) ε, HasDerivAt (u ∘ sh) (w (t + τ)) τ ∧
      HasDerivAt (w ∘ sh) (chartGeodesicVectorField cov x (u (t + τ), w (t + τ))) τ := by
    intro τ hτ
    have hts := hsub τ hτ
    refine ⟨?_, ?_⟩
    · have hd := (h.2.2.2.1 (t + τ) hts).scomp τ (hsh_deriv τ)
      rw [one_smul] at hd
      exact hd
    · have hd := (h.2.2.2.2 (t + τ) hts).scomp τ (hsh_deriv τ)
      rw [one_smul] at hd
      exact hd
  have h₂ : ∀ τ ∈ Ioo (-ε) ε, HasDerivAt (u' ∘ sh) (w' (t + τ)) τ ∧
      HasDerivAt (w' ∘ sh) (chartGeodesicVectorField cov x (u' (t + τ), w' (t + τ))) τ := by
    intro τ hτ
    have hts := hsub τ hτ
    refine ⟨?_, ?_⟩
    · have hd := (h'.2.2.2.1 (t + τ) hts).scomp τ (hsh_deriv τ)
      rw [one_smul] at hd
      exact hd
    · have hd := (h'.2.2.2.2 (t + τ) hts).scomp τ (hsh_deriv τ)
      rw [one_smul] at hd
      exact hd
  have hF : ContDiffAt ℝ 1 (chartGeodesicVectorField cov x) ((u ∘ sh) 0, (w ∘ sh) 0) := by
    have := contDiffAt_spray_of_hasChartGeodesic h ht
    simpa [hsh] using this
  have h0 : (u ∘ sh) 0 = (u' ∘ sh) 0 ∧ (w ∘ sh) 0 = (w' ∘ sh) 0 := by
    simpa [hsh] using And.intro heq heqw
  obtain ⟨δ, hδ, hδε, -, hδeq⟩ :=
    Commons.Analysis.ODE.secondOrderODE_solution_unique_of_contDiffAt
      (F := chartGeodesicVectorField cov x) (u₁ := u ∘ sh) (v₁ := w ∘ sh)
      (u₂ := u' ∘ sh) (v₂ := w' ∘ sh) hε hε hF h₁ h₂ h0
  refine ⟨δ, hδ, fun σ hσ => ?_⟩
  have hσδ : σ - t ∈ Ioo (-δ) δ := ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
  have hσ2 : σ ∈ Ioo (-2 : ℝ) 2 := by
    have h1 : |σ - t| < ε := lt_of_lt_of_le (abs_lt.mpr hσδ) hδε
    have h4 := abs_lt.mp h1
    have h5 := min_le_left (2 - t) (t + 2)
    have h6 := min_le_right (2 - t) (t + 2)
    constructor <;> linarith
  have hpos : u σ = u' σ := by
    have h := hδeq (σ - t) hσδ
    simpa [hsh] using h
  refine ⟨hpos, ?_⟩
  have hnear : (u ∘ sh) =ᶠ[𝓝 (σ - t)] (u' ∘ sh) := by
    filter_upwards [IsOpen.mem_nhds isOpen_Ioo hσδ] with τ hτ
    exact hδeq τ hτ
  have hσt : t + (σ - t) = σ := by ring
  have hd1 : HasDerivAt (u' ∘ sh) (w σ) (σ - t) := by
    have hd := (h.2.2.2.1 (t + (σ - t)) (by simpa using hσ2)).scomp (σ - t) (hsh_deriv (σ - t))
    rw [one_smul, hσt] at hd
    exact hd.congr_of_eventuallyEq hnear.symm
  have hd2 : HasDerivAt (u' ∘ sh) (w' σ) (σ - t) := by
    have hd := (h'.2.2.2.1 (t + (σ - t)) (by simpa using hσ2)).scomp (σ - t) (hsh_deriv (σ - t))
    rw [one_smul, hσt] at hd
    exact hd
  have := HasDerivAt.unique hd1 hd2
  simpa using this

/-- **Uniqueness of chart geodesics.**  Two solutions of the chart geodesic equation with the
same initial position and velocity agree on the whole interval `Ioo (-2) 2`. -/
theorem hasChartGeodesic_eqOn {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    {x : M} {v : TangentSpace I x} {u w u' w' : ℝ → E}
    (h : HasChartGeodesic cov x v u w) (h' : HasChartGeodesic cov x v u' w') :
    EqOn u u' (Ioo (-2) 2) := by
  intro σ hσ
  set s : Set ℝ := Ioo (-2) 2 with hs
  set B : Set ℝ := {t | u t = u' t ∧ w t = w' t} with hB
  have hloc : ∀ t ∈ s, t ∈ B → ∃ δ > 0, Ioo (t - δ) (t + δ) ⊆ B :=
    fun t ht htB => hasChartGeodesic_local_eq h h' ht htB.1 htB.2
  -- the closed-in-`s` part
  have hzero : ∀ (f g : ℝ → E) (u₀ : ℝ), ContinuousAt f u₀ → ContinuousAt g u₀ →
      (∃ᶠ y in 𝓝 u₀, f y = g y) → f u₀ = g u₀ := by
    intro f g u₀ hf hg hfr
    by_contra hne
    have hsub : ContinuousAt (fun y => f y - g y) u₀ := hf.sub hg
    have hmem : (fun y => f y - g y) u₀ ∈ ({0}ᶜ : Set E) := by
      simp only [mem_compl_iff, mem_singleton_iff]
      exact sub_ne_zero.mpr hne
    have hnb : (fun y => f y - g y) ⁻¹' ({0}ᶜ : Set E) ∈ 𝓝 u₀ :=
      hsub.preimage_mem_nhds (isClosed_singleton.isOpen_compl.mem_nhds hmem)
    have hev : ∀ᶠ y in 𝓝 u₀, ¬ (f y = g y) := by
      filter_upwards [hnb] with y hy h
      exact hy (by simp [h])
    exact (Filter.not_frequently.mpr hev) hfr
  have hclosed : ∀ t ∈ s, t ∈ closure (B ∩ s) → t ∈ B := by
    intro t ht hmem
    have hfreq : ∃ᶠ y in 𝓝 t, y ∈ B ∩ s := mem_closure_iff_frequently.mp hmem
    have hfr : ∃ᶠ y in 𝓝 t, u y = u' y ∧ w y = w' y :=
      hfreq.mono (fun y hy => by
        have h1 : y ∈ B := hy.1
        rw [hB] at h1
        exact h1)
    have hcu : ContinuousAt u t := (h.2.2.2.1 t ht).continuousAt
    have hcw : ContinuousAt w t := (h.2.2.2.2 t ht).continuousAt
    have hcu' : ContinuousAt u' t := (h'.2.2.2.1 t ht).continuousAt
    have hcw' : ContinuousAt w' t := (h'.2.2.2.2 t ht).continuousAt
    refine ⟨hzero u u' t hcu hcu' ?_, hzero w w' t hcw hcw' ?_⟩
    · exact hfr.mono (fun y hy => hy.1)
    · exact hfr.mono (fun y hy => hy.2)
  -- the open set where the state agrees
  set U : Set ℝ := s ∩ interior B with hU
  have hUopen : IsOpen U := IsOpen.inter isOpen_Ioo isOpen_interior
  have hUsub : U ⊆ B := fun t ht => interior_subset ht.2
  have hsU : s ∩ B ⊆ U := by
    intro t ht
    obtain ⟨hts, htB⟩ := ht
    obtain ⟨δ, hδ, hδB⟩ := hloc t hts htB
    refine ⟨hts, mem_interior_iff_mem_nhds.mpr ?_⟩
    exact Filter.mem_of_superset (Ioo_mem_nhds (by linarith) (by linarith)) hδB
  set V : Set ℝ := (closure (B ∩ s))ᶜ with hV
  have hVopen : IsOpen V := isClosed_closure.isOpen_compl
  have hdisj : Disjoint U V := by
    rw [Set.disjoint_left]
    intro t htU htV
    rw [hV] at htV
    exact htV (subset_closure ⟨hUsub htU, htU.1⟩)
  have hcover : s ⊆ U ∪ V := by
    intro t ht
    by_cases htB : t ∈ B
    · exact Or.inl (hsU ⟨ht, htB⟩)
    · refine Or.inr ?_
      rw [hV]
      exact fun hmem => htB (hclosed t ht hmem)
  have hne : (s ∩ U).Nonempty := ⟨0, by
    refine ⟨⟨by norm_num, by norm_num⟩, hsU ?_⟩
    exact ⟨⟨by norm_num, by norm_num⟩, h.1.trans h'.1.symm, h.2.1.trans h'.2.1.symm⟩⟩
  rcases isPreconnected_Ioo.subset_or_subset hUopen hVopen hdisj hcover with hsub | hsub
  · exact (hUsub (hsub hσ)).1
  · obtain ⟨x, hxs, hxU⟩ := hne
    exact (Set.disjoint_left.mp hdisj hxU (hsub hxs)).elim

/-- **The value of `expMap` is the value at time `1` of any chart geodesic with the same initial
data.** -/
theorem expMap_eq_of_hasChartGeodesic {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞] {x : M} {v : TangentSpace I x} {u w : ℝ → E}
    (h : HasChartGeodesic cov x v u w) :
    expMap cov x v = (extChartAt I x).symm (u 1) := by
  have hex : ∃ u w : ℝ → E, HasChartGeodesic cov x v u w := ⟨u, w, h⟩
  have hc : HasChartGeodesic cov x v (Classical.choose hex)
      (Classical.choose (Classical.choose_spec hex)) :=
    Classical.choose_spec (Classical.choose_spec hex)
  rw [expMap, dif_pos hex]
  exact congrArg (fun z => (extChartAt I x).symm z)
    (hasChartGeodesic_eqOn hc h (by norm_num : (1 : ℝ) ∈ Ioo (-2) 2))

/-- **The exponential map sends the zero velocity to the base point.** -/
theorem expMap_zero (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    [ContMDiffCovariantDerivative cov ∞] (x : M) :
    expMap cov x (0 : TangentSpace I x) = x := by
  rw [expMap_eq_of_hasChartGeodesic (hasChartGeodesic_zero cov x)]
  exact (extChartAt I x).left_inv (mem_extChartAt_source x)

section Scaling

/-- **The exponential map is the geodesic flow**: `expMap x (c • v)` is the value at time `c` of
the geodesic with velocity `v`, as long as `|c| ≤ 1`. -/
theorem expMap_smul {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞] {x : M} {v : TangentSpace I x} {u w : ℝ → E} {c : ℝ}
    (hc : |c| ≤ 1) (h : HasChartGeodesic cov x v u w) :
    expMap cov x (c • v) = (extChartAt I x).symm (u c) := by
  rcases eq_or_ne c 0 with rfl | hc0
  · rw [zero_smul, expMap_zero, h.1]
    exact ((extChartAt I x).left_inv (mem_extChartAt_source x)).symm
  · rw [expMap_eq_of_hasChartGeodesic (hasChartGeodesic_const_smul hc h)]
    simp

end Scaling

end Boundaryless

/-- Local agreement of two solutions of `y' = (y.2, G y)` for a smooth field `G`. -/
lemma prod_local_unique {G : E × E → E} (hG : ContDiff ℝ ∞ G) {y₁ y₂ : ℝ → E × E}
    {a b t : ℝ} (ht : t ∈ Ioo a b)
    (h₁ : ∀ s ∈ Ioo a b, HasDerivAt y₁ ((y₁ s).2, G (y₁ s)) s)
    (h₂ : ∀ s ∈ Ioo a b, HasDerivAt y₂ ((y₂ s).2, G (y₂ s)) s)
    (h0 : y₁ t = y₂ t) :
    ∃ δ > 0, ∀ s ∈ Ioo (t - δ) (t + δ), y₁ s = y₂ s := by
  have hF : ContDiff ℝ 1 (fun z : E × E => (z.2, G z)) :=
    (contDiff_snd (𝕜 := ℝ) (E := E) (F := E)).prodMk (hG.of_le (by norm_num))
  obtain ⟨K, u, hu, hlip⟩ := (hF.contDiffAt (x := y₁ t)).exists_lipschitzOnWith
  have hu₂ : u ∈ 𝓝 (y₂ t) := h0 ▸ hu
  have hm₁ : ∀ᶠ s in 𝓝 t, y₁ s ∈ u := (h₁ t ht).continuousAt.eventually hu
  have hm₂ : ∀ᶠ s in 𝓝 t, y₂ s ∈ u := (h₂ t ht).continuousAt.eventually hu₂
  have hd₁ : ∀ᶠ s in 𝓝 t, HasDerivAt y₁ ((y₁ s).2, G (y₁ s)) s := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    exact h₁ s hs
  have hd₂ : ∀ᶠ s in 𝓝 t, HasDerivAt y₂ ((y₂ s).2, G (y₂ s)) s := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    exact h₂ s hs
  have key : y₁ =ᶠ[𝓝 t] y₂ :=
    ODE_solution_unique_of_eventually
      (v := fun (_ : ℝ) (z : E × E) => (z.2, G z)) (s := fun _ => u) (K := K)
      (f := y₁) (g := y₂) (t₀ := t)
      (Filter.Eventually.of_forall (fun _ => hlip)) (hd₁.and hm₁) (hd₂.and hm₂) h0
  obtain ⟨v, hv, hH⟩ := Filter.eventually_iff_exists_mem.mp key
  obtain ⟨δ, hδ, hδv⟩ := Metric.mem_nhds_iff.mp hv
  refine ⟨δ, hδ, fun s hs => ?_⟩
  have hs' : s ∈ ball t δ := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hs.1, hs.2]
  exact hH s (hδv hs')

/-- Uniqueness on an interval for `y' = (y.2, G y)` with `G` smooth. -/
lemma prod_eqOn {G : E × E → E} (hG : ContDiff ℝ ∞ G) {y₁ y₂ : ℝ → E × E}
    {a b : ℝ} (ha : a < 0) (hb : 0 < b)
    (h₁ : ∀ s ∈ Ioo a b, HasDerivAt y₁ ((y₁ s).2, G (y₁ s)) s)
    (h₂ : ∀ s ∈ Ioo a b, HasDerivAt y₂ ((y₂ s).2, G (y₂ s)) s)
    (h0 : y₁ 0 = y₂ 0) : ∀ s ∈ Ioo a b, y₁ s = y₂ s := by
  set s : Set ℝ := Ioo a b with hsdef
  set B : Set ℝ := {t | y₁ t = y₂ t} with hB
  have hloc : ∀ t ∈ s, t ∈ B → ∃ δ > 0, Ioo (t - δ) (t + δ) ⊆ B := by
    intro t ht htB
    have h := prod_local_unique hG (by rw [hsdef] at ht; exact ht) h₁ h₂ htB
    obtain ⟨δ, hδ, hδB⟩ := h
    exact ⟨δ, hδ, fun σ hσ => hδB σ hσ⟩
  have hcont : ∀ t ∈ s, ContinuousAt y₁ t ∧ ContinuousAt y₂ t := by
    intro t ht
    exact ⟨(h₁ t ht).continuousAt, (h₂ t ht).continuousAt⟩
  have hclosed : ∀ t ∈ s, t ∈ closure (B ∩ s) → t ∈ B := by
    intro t ht hmem
    have hfreq : ∃ᶠ y in 𝓝 t, y ∈ B ∩ s := mem_closure_iff_frequently.mp hmem
    have hfr : ∃ᶠ y in 𝓝 t, y₁ y = y₂ y := by
      refine hfreq.mono ?_
      intro y hy
      have h1 : y ∈ B := hy.1
      rw [hB] at h1
      exact h1
    have hc1 : ContinuousAt y₁ t := (hcont t ht).1
    have hc2 : ContinuousAt y₂ t := (hcont t ht).2
    by_contra hne
    have hpos : 0 < ‖y₁ t - y₂ t‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    have hsub : ContinuousAt (fun y => y₁ y - y₂ y) t := hc1.sub hc2
    have hmem0 : (fun y => y₁ y - y₂ y) t ∈ ({0}ᶜ : Set (E × E)) := by
      simp only [mem_compl_iff, mem_singleton_iff]
      exact sub_ne_zero.mpr hne
    have hnb : (fun y => y₁ y - y₂ y) ⁻¹' ({0}ᶜ : Set (E × E)) ∈ 𝓝 t :=
      hsub.preimage_mem_nhds (isClosed_singleton.isOpen_compl.mem_nhds hmem0)
    have hev : ∀ᶠ y in 𝓝 t, ¬ (y₁ y = y₂ y) := by
      filter_upwards [hnb] with y hy h
      exact hy (by simp [h])
    exact (Filter.not_frequently.mpr hev) hfr
  set U : Set ℝ := s ∩ interior B with hU
  have hUopen : IsOpen U := IsOpen.inter isOpen_Ioo isOpen_interior
  have hUsub : U ⊆ B := fun t ht => interior_subset ht.2
  have hsU : s ∩ B ⊆ U := by
    intro t ht
    obtain ⟨hts, htB⟩ := ht
    obtain ⟨δ, hδ, hδB⟩ := hloc t hts htB
    refine ⟨hts, mem_interior_iff_mem_nhds.mpr ?_⟩
    exact Filter.mem_of_superset (Ioo_mem_nhds (by linarith) (by linarith)) hδB
  set V : Set ℝ := (closure (B ∩ s))ᶜ with hV
  have hVopen : IsOpen V := isClosed_closure.isOpen_compl
  have hdisj : Disjoint U V := by
    rw [Set.disjoint_left]
    intro t htU htV
    rw [hV] at htV
    exact htV (subset_closure ⟨hUsub htU, htU.1⟩)
  have hcover : s ⊆ U ∪ V := by
    intro t ht
    by_cases htB : t ∈ B
    · exact Or.inl (hsU ⟨ht, htB⟩)
    · refine Or.inr ?_
      rw [hV]
      exact fun hmem => htB (hclosed t ht hmem)
  have hne : (s ∩ U).Nonempty := ⟨0, by
    refine ⟨⟨ha, hb⟩, hsU ?_⟩
    exact ⟨⟨ha, hb⟩, h0⟩⟩
  rcases isPreconnected_Ioo.subset_or_subset hUopen hVopen hdisj hcover with hsub | hsub
  · intro t ht
    exact (hUsub (hsub (by rw [hsdef]; exact ht)))
  · obtain ⟨x, hxs, hxU⟩ := hne
    exact (Set.disjoint_left.mp hdisj hxU (hsub hxs)).elim

section Bound

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
  [I.Boundaryless]

lemma continuousLinearMapAt_trivializationAt_self (x : M) :
    (trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ x
      = ContinuousLinearMap.id ℝ (TangentSpace I x) := by
  rw [TangentBundle.continuousLinearMapAt_trivializationAt (I := I) (x₀ := x) (x := x)
    (mem_chart_source H x), mfderiv_extChartAt_self]

/-- **The exponential map is smooth on a ball of velocities around the origin.**  The proof is the
same one as for the origin, but carried out at an arbitrary interior point `v₀` of the ball in
which uniform existence holds: the unique solution family `sol` of the spray equation is smooth in
its parameter by `Commons.Analysis.ODE.contDiffAt_solutionMap_of_eventually`, `expMap` is identified
with it through `expMap_eq_of_hasChartGeodesic`, and one composes with the smooth chart inverse. -/
theorem exists_radius_contMDiffAt_expMap
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞] (x₀ : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ v₀ : E, ‖v₀‖ < ρ →
      ContMDiffAt 𝓘(ℝ, E) I ∞ (fun v : E => expMap cov x₀ v) v₀ := by
  classical
  obtain ⟨U, G, hUopen, hz0U, hUsub, hGU, hGsm, hG0⟩ :=
    exists_contMDiff_spray_extension (cov := cov) x₀
  have hGdiff : ContDiff ℝ ∞ G := contMDiff_iff_contDiff.mp hGsm
  obtain ⟨ρ, hρ, hunif⟩ :=
    Commons.Analysis.ODE.exists_uniform_secondOrderODE_solution_in_open (G := G)
      (U := U) (p₀ := (extChartAt I x₀) x₀) hUopen hz0U
      (fun z hz => (hGsm.contMDiffAt.contDiffAt).of_le (by norm_num)) hG0
  refine ⟨ρ, hρ, fun v₀ hv₀ => ?_⟩
  let sol : E → ℝ → E × E := fun w =>
    if h : ∃ α : ℝ → E × E, α 0 = ((extChartAt I x₀) x₀, w) ∧
        (∀ t ∈ Ioo (-2) 2, α t ∈ U) ∧
        (∀ t ∈ Ioo (-2) 2, HasDerivAt α ((α t).2, G (α t)) t)
      then Classical.choose h else fun _ => ((extChartAt I x₀) x₀, w)
  have hex : ∀ w : E, ‖w‖ ≤ ρ → ∃ α : ℝ → E × E,
      α 0 = ((extChartAt I x₀) x₀, w) ∧ (∀ t ∈ Ioo (-2) 2, α t ∈ U) ∧
      (∀ t ∈ Ioo (-2) 2, HasDerivAt α ((α t).2, G (α t)) t) := by
    intro w hw
    obtain ⟨u, v, hu0, hv0, hmem, hdu, hdv⟩ := hunif w hw
    refine ⟨fun t => (u t, v t), ?_, ?_, ?_⟩
    · simp [hu0, hv0]
    · exact fun t ht => by simpa using hmem t ht
    · intro t ht
      exact HasDerivAt.prodMk (hdu t ht) (hdv t ht)
  have hρ' : ∀ᶠ w in 𝓝 v₀, ‖w‖ ≤ ρ := by
    filter_upwards [Metric.ball_mem_nhds v₀ (sub_pos.mpr hv₀)] with w hw
    rw [Metric.mem_ball, dist_eq_norm] at hw
    have h1 : ‖w‖ = ‖(w - v₀) + v₀‖ := by rw [sub_add_cancel]
    rw [h1]
    linarith [norm_add_le (w - v₀) v₀]
  have hsl : ∀ (w : E) (hw : ‖w‖ ≤ ρ), sol w = Classical.choose (hex w hw) := by
    intro w hw
    dsimp only [sol]
    rw [dif_pos (hex w hw)]
  have h0f : ∀ᶠ w in 𝓝 v₀, sol w 0 = ((extChartAt I x₀) x₀, w) := by
    filter_upwards [hρ'] with w hw
    rw [hsl w hw]
    exact (Classical.choose_spec (hex w hw)).1
  have hsolf : ∀ᶠ w in 𝓝 v₀, ∀ t ∈ Ioo (-1 : ℝ) 2,
      HasDerivAt (sol w) ((sol w t).2, G (sol w t)) t := by
    filter_upwards [hρ'] with w hw
    intro t ht
    rw [hsl w hw]
    exact (Classical.choose_spec (hex w hw)).2.2 t ⟨by linarith [ht.1], ht.2⟩
  have huniqf : ∀ᶠ w in 𝓝 v₀, ∀ y : ℝ → E × E,
      (∀ t ∈ Ioo (-1 : ℝ) 2, HasDerivAt y ((y t).2, G (y t)) t) →
      y 0 = ((extChartAt I x₀) x₀, w) → ∀ t ∈ Ioo (-1 : ℝ) 2, y t = sol w t := by
    filter_upwards [hρ'] with w hw
    have hspec := Classical.choose_spec (hex w hw)
    intro y hy hy0 t ht
    rw [hsl w hw]
    refine prod_eqOn (a := -1) (b := 2) hGdiff (by norm_num) (by norm_num) ?_ ?_ ?_ t ht
    · intro s hs
      exact hy s ⟨hs.1, hs.2⟩
    · intro s hs
      exact hspec.2.2 s ⟨by linarith [hs.1], by linarith [hs.2]⟩
    · rw [hy0, hspec.1]
  have hsm : ContDiffAt ℝ ∞ (fun p : E × ℝ => sol p.1 p.2) (v₀, 1) :=
    Commons.Analysis.ODE.contDiffAt_solutionMap_of_eventually
      (X := E) (E := E × E)
      (a := -1) (b := 2)
      (f := fun (_ : ℝ) (z : E × E) => (z.2, G z))
      (by have := hGdiff; fun_prop) (by norm_num) (by norm_num)
      (c := fun w : E => ((extChartAt I x₀) x₀, w))
      (by fun_prop) (x₀ := v₀) (u := sol) h0f hsolf huniqf (by norm_num)
  -- the identification of `expMap` with the flow
  have hident : ∀ᶠ w in 𝓝 v₀,
      expMap cov x₀ w = (extChartAt I x₀).symm ((sol w 1).1) := by
    filter_upwards [hρ'] with w hw
    have hspec := Classical.choose_spec (hex w hw)
    have hsolw : sol w = Classical.choose (hex w hw) := hsl w hw
    have hmem : ∀ t ∈ Ioo (-2 : ℝ) 2, sol w t ∈ U := by
      intro t ht
      rw [hsolw]
      exact hspec.2.1 t ht
    have hH : HasChartGeodesic cov x₀ w (fun t => (sol w t).1) (fun t => (sol w t).2) := by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · show (sol w 0).1 = (extChartAt I x₀) x₀
        rw [hsolw, hspec.1]
      · show (sol w 0).2
            = (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ x₀ w
        rw [hsolw, hspec.1, continuousLinearMapAt_trivializationAt_self]
        rfl
      · intro t ht
        exact (hUsub (hmem t ht)).1
      · intro t ht
        rw [hsolw]
        exact (hspec.2.2 t ht).fst
      · intro t ht
        have hd : HasDerivAt (fun s => (sol w s).2) (G (sol w t)) t := by
          rw [hsolw]
          exact (hspec.2.2 t ht).snd
        rw [hGU (sol w t) (hmem t ht)] at hd
        exact hd
    exact expMap_eq_of_hasChartGeodesic hH
  -- smoothness of the parametrised flow and of the chart inverse
  have hstep : ContDiffAt ℝ ∞ (fun w : E =>
      (fun p : E × ℝ => sol p.1 p.2) (w, 1)) v₀ :=
    hsm.comp v₀ (contDiffAt_id.prodMk contDiffAt_const)
  have hfst : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (fun w : E => (sol w 1).1) v₀ :=
    (contDiffAt_fst.comp v₀ hstep).contMDiffAt
  have hv0le : ‖v₀‖ ≤ ρ := le_of_lt hv₀
  have hmemU : sol v₀ 1 ∈ U := by
    rw [hsl v₀ hv0le]
    exact (Classical.choose_spec (hex v₀ hv0le)).2.1 1 (by norm_num)
  have htgt : (sol v₀ 1).1 ∈ (extChartAt I x₀).target := (hUsub hmemU).1
  have hsymm : ContMDiffAt 𝓘(ℝ, E) I ∞ (fun z : E => (extChartAt I x₀).symm z)
      ((sol v₀ 1).1) :=
    (contMDiffOn_extChartAt_symm (I := I) x₀).contMDiffAt
      ((isOpen_extChartAt_target x₀).mem_nhds htgt)
  refine (hsymm.comp v₀ hfst).congr_of_eventuallyEq hident

/-- **The exponential map is smooth at the origin.** -/
theorem contMDiffAt_expMap_zero
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞] (x₀ : M) :
    ContMDiffAt 𝓘(ℝ, E) I ∞ (fun v : E => expMap cov x₀ v) 0 := by
  obtain ⟨ρ, hρ, h⟩ := exists_radius_contMDiffAt_expMap (cov := cov) x₀
  exact h 0 (by simpa using hρ)

/-! ### The differential of the exponential map at the origin

`mfderiv_expMap_zero` is the last ingredient of the local theory: the derivative of `expMap` at
`0` is the identity, so that `expMap` is a local diffeomorphism at the origin by the inverse
function theorem (Mathlib's `HasMFDerivAt`/`contMDiffAt` local inverse theory).

The proof is the standard one and only uses the ray identity `expMap_smul`:

* for `v` admitting a chart geodesic `u`, the curve `s ↦ expMap x (s • v)` agrees near `0` with
  `s ↦ (extChartAt I x).symm (u s)`, whose velocity at `0` is `v` by
  `curveVelocity_extChartAt_symm` (`Trivialization.symmL_continuousLinearMapAt`);
* the chain rule `mfderiv_comp_apply_of_eq` applied to `s ↦ s • v` then gives
  `mfderiv (expMap) 0 v = v`;
* both sides being linear in `v`, the identity extends from a ball (where chart geodesics exist by
  `exists_pos_hasChartGeodesic`) to all of `E`. -/

/-- **Chart geodesics exist for all velocities in a ball around `0`.**  This is the (uniform)
local existence theorem for the geodesic spray, applied to the globally smooth extension of the
spray constructed in `exists_contMDiff_spray_extension`. -/
theorem exists_pos_hasChartGeodesic
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞] (x₀ : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ v : E, ‖v‖ ≤ ρ → ∃ u w : ℝ → E, HasChartGeodesic cov x₀ v u w := by
  classical
  obtain ⟨U, G, hUopen, hz0U, hUsub, hGU, hGsm, hG0⟩ :=
    exists_contMDiff_spray_extension (cov := cov) x₀
  obtain ⟨ρ, hρ, hunif⟩ :=
    Commons.Analysis.ODE.exists_uniform_secondOrderODE_solution_in_open (G := G)
      (U := U) (p₀ := (extChartAt I x₀) x₀) hUopen hz0U
      (fun z hz => (hGsm.contMDiffAt.contDiffAt).of_le (by norm_num)) hG0
  refine ⟨ρ, hρ, fun v hv => ?_⟩
  obtain ⟨u, w, hu0, hw0, hmem, hdu, hdw⟩ := hunif v hv
  refine ⟨u, w, ?_, ?_, ?_, ?_, ?_⟩
  · exact hu0
  · rw [hw0, continuousLinearMapAt_trivializationAt_self]
    rfl
  · intro t ht
    exact (hUsub (hmem t ht)).1
  · intro t ht
    exact hdu t ht
  · intro t ht
    have hd : HasDerivAt w (G (u t, w t)) t := hdw t ht
    rw [hGU (u t, w t) (hmem t ht)] at hd
    exact hd

/-- **The differential of `expMap` at the origin, on velocities admitting a chart geodesic**: it is
the identity. -/
theorem mfderiv_expMap_zero_of_hasChartGeodesic
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞] (x₀ : M) {v : E}
    (hex : ∃ u w : ℝ → E, HasChartGeodesic cov x₀ v u w) :
    mfderiv 𝓘(ℝ, E) I (fun w : E => expMap cov x₀ w) 0 v = v := by
  classical
  obtain ⟨u, w, huw⟩ := hex
  have hcd : ContMDiffAt 𝓘(ℝ, E) I ∞ (fun w : E => expMap cov x₀ w) 0 :=
    contMDiffAt_expMap_zero (cov := cov) x₀
  have hmd : MDifferentiableAt 𝓘(ℝ, E) I (fun w : E => expMap cov x₀ w) 0 :=
    hcd.mdifferentiableAt (by simp)
  have hray0 : (fun s : ℝ => s • v) 0 = (0 : E) := zero_smul ℝ v
  have hscl : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun s : ℝ => s • v) 0
      (ContinuousLinearMap.toSpanSingleton ℝ v) :=
    ((ContinuousLinearMap.toSpanSingleton ℝ v).hasFDerivAt).hasMFDerivAt
  have hrayderiv : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun s : ℝ => s • v) 0 (1 : ℝ) = v := by
    have hF : HasFDerivAt (fun s : ℝ => s • v) (ContinuousLinearMap.toSpanSingleton ℝ v) 0 :=
      hscl.hasFDerivAt
    have key : ((ContinuousLinearMap.toSpanSingleton ℝ v : ℝ →L[ℝ] E)) (1 : ℝ) = v := by
      rw [ContinuousLinearMap.toSpanSingleton_apply, one_smul]
    rw [mfderiv_eq_fderiv, hF.fderiv]
    exact key
  -- the velocity of the geodesic ray `s ↦ expMap x₀ (s • v)` at `0` is `v`
  have hcurvevel : curveVelocity (I := I) (fun s : ℝ => expMap cov x₀ (s • v)) 0 = v := by
    have heq : (fun s : ℝ => expMap cov x₀ (s • v)) =ᶠ[𝓝 (0 : ℝ)]
        (fun s : ℝ => (extChartAt I x₀).symm (u s)) := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with s hs
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hs
      exact expMap_smul (I := I) (x := x₀) (v := v) (u := u) (w := w) hs.le huw
    have h2 : curveVelocity (I := I) (fun s : ℝ => expMap cov x₀ (s • v)) 0
        = curveVelocity (I := I) (fun s : ℝ => (extChartAt I x₀).symm (u s)) 0 := by
      rw [curveVelocity_apply, curveVelocity_apply, heq.mfderiv_eq]
      rfl
    have h3 : curveVelocity (I := I) (fun s : ℝ => (extChartAt I x₀).symm (u s)) 0 = v := by
      have htgt : u 0 ∈ (extChartAt I x₀).target := huw.2.2.1 0 (by norm_num)
      have hstay : ∀ᶠ s in 𝓝 (0 : ℝ), u s ∈ (extChartAt I x₀).target := by
        filter_upwards [isOpen_Ioo.mem_nhds (by norm_num : (0 : ℝ) ∈ Ioo (-2) 2)] with s hs
        exact huw.2.2.1 s hs
      have h := curveVelocity_extChartAt_symm (I := I) (x₀ := x₀) (u := u) (t := 0) (v := w 0)
        (huw.2.2.2.1 0 (by norm_num)) htgt hstay
      rw [h, huw.1, huw.2.1, PartialEquiv.left_inv (extChartAt I x₀) (mem_extChartAt_source x₀)]
      exact Trivialization.symmL_continuousLinearMapAt (R := ℝ) (b := x₀)
        (e := trivializationAt E (TangentSpace I) x₀) (by simp) v
    rw [h2, h3]
  have hcurve : (mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ => expMap cov x₀ (s • v)) 0) (1 : ℝ) = v := by
    rw [← curveVelocity_apply (I := I) (γ := fun s : ℝ => expMap cov x₀ (s • v)) 0]
    exact hcurvevel
  -- the chain rule for the geodesic ray
  have hcomp := mfderiv_comp_apply_of_eq (x := (0 : ℝ)) (y := (0 : E))
    (f := fun s : ℝ => s • v) (g := fun w : E => expMap cov x₀ w)
    hmd hscl.mdifferentiableAt hray0 (1 : ℝ)
  have hcomp' : (mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ => expMap cov x₀ (s • v)) 0) (1 : ℝ)
      = (mfderiv 𝓘(ℝ, E) I (fun w : E => expMap cov x₀ w) 0)
          ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun s : ℝ => s • v) 0) (1 : ℝ)) := by
    rw [← mfderiv_congr (f := (fun w : E => expMap cov x₀ w) ∘ (fun s : ℝ => s • v))
      (f' := fun s : ℝ => expMap cov x₀ (s • v)) (x := (0 : ℝ)) rfl]
    exact hcomp
  have hmain : ((mfderiv 𝓘(ℝ, E) I (fun w : E => expMap cov x₀ w) 0 : E →L[ℝ] E)) v = v := by
    have h := hcomp'
    rw [hcurve, hrayderiv] at h
    exact h.symm
  change ((mfderiv 𝓘(ℝ, E) I (fun w : E => expMap cov x₀ w) 0 : E →L[ℝ] E)) v = v
  exact hmain

/-- **The exponential map is smooth at the origin, with differential the identity.** -/
theorem mfderiv_expMap_zero
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞] (x₀ : M) :
    mfderiv 𝓘(ℝ, E) I (fun v : E => expMap cov x₀ v) 0 = ContinuousLinearMap.id ℝ E := by
  obtain ⟨ρ, hρ, hex⟩ := exists_pos_hasChartGeodesic (cov := cov) x₀
  have hball : ∀ v : E, ‖v‖ ≤ ρ →
      ((mfderiv 𝓘(ℝ, E) I (fun w : E => expMap cov x₀ w) 0 : E →L[ℝ] E)) v = v :=
    fun v hv => mfderiv_expMap_zero_of_hasChartGeodesic (cov := cov) x₀ (hex v hv)
  have hgen : ∀ v : E,
      ((mfderiv 𝓘(ℝ, E) I (fun w : E => expMap cov x₀ w) 0 : E →L[ℝ] E)) v = v := by
    intro v
    by_cases hv : v = 0
    · subst hv
      exact map_zero _
    · have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
      set c : ℝ := ρ / (2 * ‖v‖) with hc
      have hcpos : 0 < c := by rw [hc]; positivity
      have hcle : ‖c • v‖ ≤ ρ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hcpos, hc]
        have : ρ / (2 * ‖v‖) * ‖v‖ = ρ / 2 := by field_simp
        rw [this]; linarith
      have h1 := hball (c • v) hcle
      have h2 : ((mfderiv 𝓘(ℝ, E) I (fun w : E => expMap cov x₀ w) 0 : E →L[ℝ] E)) (c • v)
          = c • ((mfderiv 𝓘(ℝ, E) I (fun w : E => expMap cov x₀ w) 0 : E →L[ℝ] E)) v :=
        map_smul _ c v
      rw [h2] at h1
      exact (smul_right_inj (ne_of_gt hcpos)).mp h1
  change ((mfderiv 𝓘(ℝ, E) I (fun w : E => expMap cov x₀ w) 0 : E →L[ℝ] E))
    = ContinuousLinearMap.id ℝ E
  ext v
  exact hgen v

/-- **The chain rule for `expMap` along a curve in the tangent space at `x₀`.**  If `γ` has
derivative `c'` at `t` and `expMap cov x₀` is differentiable at `γ t`, then the differential of
`expMap` there evaluated at `c'` is the velocity at `t` of the curve `s ↦ expMap cov x₀ (γ s)`.
This is the technical form of the chain rule that is used for the radial derivative of `expMap`
and for the derivative in the direction of a variation. -/
theorem mfderiv_expMap_comp
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞] (x₀ : M) {γ : ℝ → E} {t : ℝ} {c' : E}
    (hd : MDifferentiableAt 𝓘(ℝ, E) I (fun a : E => expMap cov x₀ a) (γ t))
    (hγ : HasDerivAt γ c' t) :
    mfderiv 𝓘(ℝ, E) I (fun a : E => expMap cov x₀ a) (γ t) c'
      = curveVelocity (I := I) (fun s : ℝ => expMap cov x₀ (γ s)) t := by
  have hmdγ : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t := hγ.differentiableAt.mdifferentiableAt
  have h1 : (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t) (1 : ℝ) = c' := by
    have hF : HasFDerivAt γ (ContinuousLinearMap.toSpanSingleton ℝ c') t := hγ.hasFDerivAt
    have key : ((ContinuousLinearMap.toSpanSingleton ℝ c' : ℝ →L[ℝ] E)) (1 : ℝ) = c' := by
      rw [ContinuousLinearMap.toSpanSingleton_apply, one_smul]
    rw [mfderiv_eq_fderiv, hF.fderiv]
    exact key
  have hcomp := mfderiv_comp_apply (x := t) hd hmdγ (1 : ℝ)
  have hgoal : curveVelocity (I := I) (fun s : ℝ => expMap cov x₀ (γ s)) t
      = (mfderiv 𝓘(ℝ, E) I (fun a : E => expMap cov x₀ a) (γ t)) c' := by
    rw [curveVelocity_apply]
    rw [show mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ => expMap cov x₀ (γ s)) t
        = mfderiv 𝓘(ℝ, ℝ) I ((fun a : E => expMap cov x₀ a) ∘ γ) t from
      mfderiv_congr rfl]
    erw [hcomp]
    exact congrArg (fun x => (mfderiv 𝓘(ℝ, E) I (fun a : E => expMap cov x₀ a) (γ t)) x) h1
  exact hgoal.symm

/-- **The derivative of `expMap` in the radial direction.**  For a velocity `v` admitting a chart
geodesic `u` and `|s| < 1`, the differential of `expMap` at `s • v` in the direction `v` is the
velocity at time `s` of the geodesic `c ↦ (extChartAt I x₀).symm (u c)`. -/
theorem mfderiv_expMap_ray
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞] (x₀ : M) {v : E}
    {u w : ℝ → E} (huw : HasChartGeodesic cov x₀ v u w) {s : ℝ} (hs : |s| < 1)
    (hd : MDifferentiableAt 𝓘(ℝ, E) I (fun a : E => expMap cov x₀ a) (s • v)) :
    mfderiv 𝓘(ℝ, E) I (fun a : E => expMap cov x₀ a) (s • v) v
      = curveVelocity (I := I) (fun c : ℝ => (extChartAt I x₀).symm (u c)) s := by
  have hγ : HasDerivAt (fun c : ℝ => c • v) v s := by
    simpa using (hasDerivAt_id s).smul_const v
  have hchain := mfderiv_expMap_comp (cov := cov) x₀ (γ := fun c : ℝ => c • v)
    (t := s) (c' := v) hd hγ
  have heq : (fun c : ℝ => expMap cov x₀ (c • v)) =ᶠ[𝓝 s]
      (fun c : ℝ => (extChartAt I x₀).symm (u c)) := by
    filter_upwards [Metric.ball_mem_nhds s (by linarith [abs_nonneg s] : (0:ℝ) < 1 - |s|)]
      with c hc
    rw [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs] at hc
    have h2 : |c| ≤ |c - s| + |s| := by
      have h3 : ‖(c - s) + s‖ ≤ ‖c - s‖ + ‖s‖ := norm_add_le _ _
      rw [sub_add_cancel] at h3
      simpa [Real.norm_eq_abs] using h3
    exact expMap_smul (I := I) (x := x₀) (v := v) (u := u) (w := w)
      (by linarith : |c| ≤ 1) huw
  have h2 : curveVelocity (I := I) (fun c : ℝ => expMap cov x₀ (c • v)) s
      = curveVelocity (I := I) (fun c : ℝ => (extChartAt I x₀).symm (u c)) s := by
    rw [curveVelocity_apply, curveVelocity_apply, heq.mfderiv_eq]
    rfl
  rw [hchain, h2]

/-- **`expMap` is smooth on an open neighbourhood of the origin** (in the strong local form
`ContMDiffOn`, as opposed to the pointwise `ContMDiffAt`). -/
theorem exists_open_contMDiffOn_expMap
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞] (x₀ : M) :
    ∃ U : Set E, IsOpen U ∧ (0 : E) ∈ U ∧
      ContMDiffOn 𝓘(ℝ, E) I ∞ (fun v : E => expMap cov x₀ v) U := by
  obtain ⟨ρ, hρ, h⟩ := exists_radius_contMDiffAt_expMap (cov := cov) x₀
  refine ⟨Metric.ball (0 : E) (ρ / 2), Metric.isOpen_ball, Metric.mem_ball_self (by linarith), ?_⟩
  intro v hv
  exact (h v (by rw [Metric.mem_ball, dist_zero_right] at hv; linarith)).contMDiffWithinAt

/-- The differential of `expMap` at the origin is invertible. -/
theorem isInvertible_mfderiv_expMap_zero
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞] (x₀ : M) :
    (mfderiv 𝓘(ℝ, E) I (fun v : E => expMap cov x₀ v) 0).IsInvertible := by
  rw [mfderiv_expMap_zero]
  exact ⟨ContinuousLinearEquiv.refl ℝ E, by ext; rfl⟩

/-- **The exponential map is a local diffeomorphism at the origin.**  This combines the local
smoothness (`exists_open_contMDiffOn_expMap`), the fact that `0` is an interior point of the model
space, and the invertibility of the differential (`isInvertible_mfderiv_expMap_zero`) through the
inverse function theorem for manifolds
(`Commons.Geometry.Manifold.LocalDiffeomorph.isLocalDiffeomorphAt_of_contMDiffOn_of_mfderiv_isInvertible`). -/
theorem isLocalDiffeomorphAt_expMap_zero
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞] (x₀ : M) :
    IsLocalDiffeomorphAt 𝓘(ℝ, E) I ∞ (fun v : E => expMap cov x₀ v) 0 := by
  obtain ⟨U, hUopen, h0U, hU⟩ := exists_open_contMDiffOn_expMap (cov := cov) x₀
  refine Commons.Geometry.Manifold.LocalDiffeomorph.isLocalDiffeomorphAt_of_contMDiffOn_of_mfderiv_isInvertible
    hUopen h0U hU ?_ (isInvertible_mfderiv_expMap_zero (cov := cov) x₀)
  rw [ModelWithCorners.IsInteriorPoint]
  simp [modelWithCornersSelf_coe]

/-- **`expMap` is injective near the origin.** -/
theorem exists_injOn_expMap_nhds
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞] (x₀ : M) :
    ∃ U : Set E, IsOpen U ∧ (0 : E) ∈ U ∧ Set.InjOn (fun v : E => expMap cov x₀ v) U := by
  have hf : IsLocalDiffeomorphAt 𝓘(ℝ, E) I ∞ (fun v : E => expMap cov x₀ v) 0 :=
    isLocalDiffeomorphAt_expMap_zero (cov := cov) x₀
  refine ⟨hf.localInverse.target, hf.localInverse.open_target, hf.localInverse_mem_target, ?_⟩
  intro a ha b hb hab
  calc a = hf.localInverse (expMap cov x₀ a) := (hf.localInverse_left_inv ha).symm
    _ = hf.localInverse (expMap cov x₀ b) := congrArg hf.localInverse hab
    _ = b := hf.localInverse_left_inv hb

/-- **The image of `expMap` contains a neighbourhood of `x₀`.** -/
theorem exists_open_subset_range_expMap
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞] (x₀ : M) :
    ∃ V : Set M, IsOpen V ∧ x₀ ∈ V ∧ V ⊆ Set.range (fun v : E => expMap cov x₀ v) := by
  have hf : IsLocalDiffeomorphAt 𝓘(ℝ, E) I ∞ (fun v : E => expMap cov x₀ v) 0 :=
    isLocalDiffeomorphAt_expMap_zero (cov := cov) x₀
  refine ⟨hf.localInverse.source, hf.localInverse.open_source, ?_, ?_⟩
  · have hz : expMap cov x₀ (0 : E) = x₀ := expMap_zero (cov := cov) x₀
    have h := hf.localInverse_mem_source
    rw [hz] at h
    exact h
  · intro y hy
    exact ⟨hf.localInverse y, hf.localInverse_right_inv hy⟩

end Bound

end

end Submission.Geodesic

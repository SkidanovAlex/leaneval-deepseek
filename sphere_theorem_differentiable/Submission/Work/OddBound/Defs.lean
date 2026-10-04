import Submission.EnergyGeoShorten
import Submission.KlingenbergEven
import Submission.KlingenbergTransfer
import Submission.InjSup
import Submission.LensLoop
import Submission.IndexIntrinsic

set_option backward.isDefEq.respectTransparency.types false

/-!
# The odd-dimensional Klingenberg length bound — definitions

`Submission.KlingenbergEven` reduces the even-dimensional case of Klingenberg's length bound to
Synge's lemma: at the closest cut point the two minimising geodesics glue to a **closed geodesic**
`Γ` of length `L = 2m`, and the *parallel transport of the normal bundle* around `Γ` is an element
of `SO(n-1)` with `n-1` **odd**, hence has a fixed vector — a parallel periodic unit normal field.
The second variation of `Γ` along that field is `-∫ sec < 0`, so nearby closed curves are shorter,
contradicting the "exactly two minimising geodesics" structure at the closest cut point.

In **odd** dimensions `n-1` is even and the holonomy need not have a fixed vector, so a *parallel*
field is unavailable.  What replaces it is the **rotating** test field: if the normal holonomy has a
rotation angle `ψ` on an invariant 2-plane, then for parallel orthonormal fields `X₁, X₂` spanning
that plane the field

  `V(s) = cos (ψ s / L) • X₁ s - sin (ψ s / L) • X₂ s`

is again a *periodic* unit normal field (this is where the twist relation of the holonomy on the
plane is used), and

  `∇_{γ'} V = -(ψ/L) • (sin (ψ s / L) • X₁ s + cos (ψ s / L) • X₂ s)`,
  `‖∇V‖  = |ψ| / L`  (constant),

so the index form is `I(V,V) = ψ²/L - ∫₀^L sec(V, γ') ≤ ψ²/L - δ L`, which is negative **iff**
`ψ < L √δ`.  This module records exactly these objects.

## What is in this file

* `IsUnitNormalField` — a field with `‖V t‖ = 1` and `V t ⊥ γ'(t)` for all `t`;
* `HasSmallCovDeriv` — the `L²` smallness `∫₀^L ‖∇V‖² < δ L` of the covariant derivative;
* `IsShorteningField`, `ExistsShorteningField` — the complete test-field package (a *structure*,
  so that its fields are accessible by projection);
* `HolonomyRotationData` and `HolonomyRotationData.rotatingField` — a genuine holonomy rotation pair
  `(X₁, X₂, ψ)` on a closed geodesic and the associated rotating field;
* `HasHolonomyAngleInput`, `HasRotatingFieldInput` — the two forms of the (open) input of the odd
  case, and `FlushNoShorteningInput`, the shared compactness input of the even and odd cases.

## Conventions

`γ : ℝ → M` is a closed unit-speed geodesic of length `L > 0` (`γ L = γ 0`), `δ = K/4` is the
*lower* curvature bound and `K` the upper one, so `sec ∈ [δ, K]`.  The parameter interval is
`[0, L]` everywhere; the fields are asked to be smooth on the slightly larger interval
`[-(1 : ℝ), L + 1]` so that `covAlong` (which is a *germ* statement) is available at the endpoints.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory Interval
open Submission.Geodesic
open Submission.JacobiGlobal
open Submission.GlobalExp
open Submission.Length
open Submission.InjRadius
open Submission.CurvatureVec

namespace Work.OddBound

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-! ## 1. The test fields along a closed geodesic -/

/-- A field `V` along a curve `γ` is a **unit normal field** when it has norm one and is orthogonal
to the velocity of `γ` at every time.  Together with periodicity `V L = V 0` this is a legitimate
variation field for *closed* curves: the variation `s ↦ GExp (γ s) (σ • V s)` is closed. -/
def IsUnitNormalField (γ : ℝ → M) (L : ℝ) (V : (t : ℝ) → TangentSpace I (γ t)) : Prop :=
  ∀ t ∈ Icc (0 : ℝ) L, ‖V t‖ = 1 ∧ inner ℝ (V t) (curveVelocity (I := I) γ t) = 0

/-- **Smallness of the covariant derivative**: `∫₀^L ‖∇_{γ'} V‖² < δ L`.  For the rotating field of
a holonomy rotation angle `ψ` this integral is `ψ²/L`, so the condition is exactly `ψ² < δ L²`;
for a *parallel* field (`∇V = 0`) it holds for every `δ > 0`. -/
def HasSmallCovDeriv (cov : CovariantDerivative I E (TangentSpace I (M := M))) (γ : ℝ → M)
    (L δ : ℝ) (V : (t : ℝ) → TangentSpace I (γ t)) : Prop :=
  (∫ t in (0 : ℝ)..L, ‖covAlong cov V t‖ ^ 2) < δ * L

/-- **A shortening field** along a closed geodesic `γ` of length `L`: a `C^∞` field `field` on
`[-(1 : ℝ), L + 1]`, periodic (`field L = field 0`), unit and normal, with small covariant
derivative.  The second variation of the length of `γ` along `field` is then strictly negative, and
the length is strictly decreased by the closed curves `s ↦ GExp (γ s) (σ • (d • field s))`. -/
structure IsShorteningField (cov : CovariantDerivative I E (TangentSpace I (M := M))) (γ : ℝ → M)
    (L δ : ℝ) where
  /-- The test field. -/
  field : (t : ℝ) → TangentSpace I (γ t)
  /-- Smoothness on the enlarged interval. -/
  smooth : ∀ s ∈ Icc (-1) (L + 1), SmoothAlongAt (I := I) γ field s
  /-- Periodicity: the variation of *closed* curves is closed. -/
  periodic : field L = field 0
  /-- Unit and normal to the velocity. -/
  unitNormal : IsUnitNormalField (I := I) γ L field
  /-- The smallness of `∇field` in `L²`. -/
  smallDeriv : HasSmallCovDeriv cov γ L δ field

/-- The existence form of a shortening field. -/
def ExistsShorteningField (cov : CovariantDerivative I E (TangentSpace I (M := M))) (γ : ℝ → M)
    (L δ : ℝ) : Prop :=
  Nonempty (IsShorteningField cov γ L δ)

/-! ## 2. The holonomy rotation pair -/

/-- **Rotation data for the normal holonomy of a closed curve.**  Two *parallel* orthonormal normal
fields `X₁, X₂` along `γ` spanning an invariant 2-plane of the normal holonomy, with the twist
relation of a rotation by the angle `ψ` around the loop, and the smallness `ψ² < δ L²`.

The eigenvalues `e^{±iψ}` of `P ∈ SO(n-1)` on an invariant plane give exactly such `X₁, X₂`; `ψ` may
always be normalised into `[0, π]`.  `ψ = 0` (Synge's case, a fixed vector of the holonomy) is
allowed and then gives the parallel field `X₁` back. -/
structure HolonomyRotationData (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (γ : ℝ → M) (L δ : ℝ) where
  /-- The first parallel normal field. -/
  X₁ : (t : ℝ) → TangentSpace I (γ t)
  /-- The second parallel normal field. -/
  X₂ : (t : ℝ) → TangentSpace I (γ t)
  /-- The rotation angle of the holonomy on the plane `span{X₁, X₂}`. -/
  ψ : ℝ
  smoothX₁ : ∀ s ∈ Icc (-1) (L + 1), SmoothAlongAt (I := I) γ X₁ s
  smoothX₂ : ∀ s ∈ Icc (-1) (L + 1), SmoothAlongAt (I := I) γ X₂ s
  parallelX₁ : ∀ s ∈ Icc (-1) (L + 1), covAlong cov X₁ s = 0
  parallelX₂ : ∀ s ∈ Icc (-1) (L + 1), covAlong cov X₂ s = 0
  normX₁ : ∀ t ∈ Icc (0 : ℝ) L, ‖X₁ t‖ = 1
  normX₂ : ∀ t ∈ Icc (0 : ℝ) L, ‖X₂ t‖ = 1
  orthX₁X₂ : ∀ t ∈ Icc (0 : ℝ) L, inner ℝ (X₁ t) (X₂ t) = 0
  normalX₁ : ∀ t ∈ Icc (0 : ℝ) L, inner ℝ (X₁ t) (curveVelocity (I := I) γ t) = 0
  normalX₂ : ∀ t ∈ Icc (0 : ℝ) L, inner ℝ (X₂ t) (curveVelocity (I := I) γ t) = 0
  twistX₁ : X₁ L = Real.cos ψ • X₁ 0 + Real.sin ψ • X₂ 0
  twistX₂ : X₂ L = -(Real.sin ψ) • X₁ 0 + Real.cos ψ • X₂ 0
  small : ψ ^ 2 < δ * L ^ 2

/-- **The rotating field of a holonomy rotation pair** (the candidate shortening field of the odd
case). -/
def HolonomyRotationData.rotatingField {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    {γ : ℝ → M} {L δ : ℝ} (h : HolonomyRotationData cov γ L δ) :
    (t : ℝ) → TangentSpace I (γ t) :=
  fun s => Real.cos (h.ψ * s / L) • h.X₁ s - Real.sin (h.ψ * s / L) • h.X₂ s

/-! ## 3. The open inputs of the odd case -/

/-- **The holonomy angle input (odd case, open).**  Every closed unit-speed geodesic `γ` of length
`L < 2π/√K` in a simply connected manifold with `sec ∈ [K/4, K]` carries a holonomy rotation pair
with `ψ² < (K/4) L²`.

*This is the Klingenberg 1961 content that is not available in the library*: it is a bound of the
rotation angle of the normal holonomy of a loop of length `L` by the area of a bounding disk and the
curvature bound (`ψ ≤ K·A`), combined with a bound on the area `A`.  See the module docstring of
`Submission/Work/OddBound/OddBound.lean` for the discussion, and for the obstruction. -/
def HasHolonomyAngleInput (K : ℝ) : Prop :=
  SimplyConnectedSpace M →
  (∀ (p : M) (u v : TangentSpace I p), ‖u‖ = 1 → ‖v‖ = 1 → inner ℝ u v = 0 →
      K / 4 ≤ inner ℝ (curvVec cov p u v v) u) →
  ∀ {γ : ℝ → M} {L : ℝ}, 0 < L → L < 2 * Real.pi / Real.sqrt K → γ L = γ 0 →
    (∀ t : ℝ, IsGeodesicAt (I := I) cov γ t) →
    (∀ t : ℝ, curveVelocity (I := I) γ t ≠ 0) →
    (∀ t ∈ Icc (0 : ℝ) L, curveSpeed (I := I) γ t = 1) →
    Nonempty (HolonomyRotationData cov γ L (K / 4))

/-- **The shortening input (odd case, open).**  The same content, stated directly as the existence
of a shortening field.  It is the exact hypothesis consumed by
`Work.OddBound.exists_shorter_closed_curve_of_shorteningField`, and it is *implied* by
`HasHolonomyAngleInput` through the rotating field
(`Work.OddBound.rotatingFieldInput_of_holonomyAngleInput`).

**This is the single remaining gap of the odd-dimensional Klingenberg estimate.**  Equivalently
(`Work.OddBound.HolonomyRotationData`, and the observation below), a prover must supply:

> for every closed unit-speed geodesic `γ` of length `L < 2π/√K` in a `K`-quarter-pinched simply
> connected manifold, the *normal holonomy* `P ∈ SO(n-1)` of `γ` has a periodic unit normal field
> with `∫₀^L ‖∇V‖² < (K/4) L`.

The minimum of `∫₀^L ‖∇V‖²` over periodic unit normal fields is `δ(P)²/L`, where
`δ(P) = min_j ψ_j` is the smallest rotation angle of `P` (the pairing of the eigenvalues `e^{±iψ_j}`);
so the content is exactly the **rotation-angle estimate `δ(P) < L√(K/4)`**.  Two classical routes:

* the holonomy/area route: `δ(P) ≤ K · A` for the area `A` of a disk bounded by `γ` (the curvature
  flux through the disk; on a partition into small squares each contributes `O(Λ·area)` and the
  bi-invariant distance on `SO(n-1)` is subadditive), together with a bound on `A`.  **Caution:** the
  naive companion bound `A ≤ L²/4π` is *false* in general (a great circle of length `2π` on the round
  `S²` bounds only disks of area `2π > π = L²/4π`); in that configuration the holonomy is trivial and
  the parallel field shortens anyway, so the conclusion survives, but the combination
  `(δ ≤ K·A) + (A ≤ L²/4π)` is *not* a valid proof as it stands and needs an argument exploiting the
  flush structure (where the two halves are the *only* minimising geodesics) or a sharper area bound;
* the free-loop-space minimax (Klingenberg 1961): not available in this library. -/
def HasRotatingFieldInput (K : ℝ) : Prop :=
  SimplyConnectedSpace M →
  (∀ (p : M) (u v : TangentSpace I p), ‖u‖ = 1 → ‖v‖ = 1 → inner ℝ u v = 0 →
      K / 4 ≤ inner ℝ (curvVec cov p u v v) u) →
  ∀ {γ : ℝ → M} {L : ℝ}, 0 < L → L < 2 * Real.pi / Real.sqrt K → γ L = γ 0 →
    (∀ t : ℝ, IsGeodesicAt (I := I) cov γ t) →
    (∀ t : ℝ, curveVelocity (I := I) γ t ≠ 0) →
    (∀ t ∈ Icc (0 : ℝ) L, curveSpeed (I := I) γ t = 1) →
    ExistsShorteningField cov γ L (K / 4)

/-- **The shared flush-configuration input (even *and* odd cases).**  If the global injectivity radius
`m := injSup hmet` of a compact manifold is below `π/√K`, then at an **attained** closest cut point
`p` — one with `InjAtLeast hmet p m` and *no* larger injectivity radius, so that Xu's Theorem B
applies there — there are two distinct minimising unit directions `ξ ≠ η` whose rays meet at time
`m`, and the `GExp`-ray of `ξ` admits **no** shortening field.

The ray of `ξ` is then a periodic unit-speed geodesic `Γ` of length `2m`
(`Submission.KlingenbergEven.ray_periodic_of_two_minimising` needs the *global* injectivity radius,
which is available at `m = injSup hmet` from `Submission.InjSup.injAllAtLeast_injSup`), and the last
conjunct says that `Γ` cannot be shortened.

This packages the **dimension-independent compactness work** of Klingenberg's estimate:

* the **attainment** of `injSup hmet` (a point whose injectivity radius is the global minimum) —
  `Work.EvenBound.Attain.injSup_attained_of_lt_pi_div_sqrt`;
* the **cut-point dichotomy** `Submission.CutStep3.exists_two_minimising_or_not_locallyInjective`,
  which below `π/√K` produces the two minimising directions (the other branch, failure of local
  injectivity, is excluded by Rauch / `Submission.RayConj`);
* the **third-minimal-geodesic argument** — `Work.EvenBound.ThirdGeodesic.no_shorter_closed_of_only_two_minimising`
  (with `Work.EvenBound.FarthestPoint.inner_eq_zero_of_isLocalMax_edist`): the farthest point of the
  shortened closed curves, together with the first variation formula, produces a *third* minimising
  geodesic from `p` to `q`, contradicting the "exactly two" structure of Xu's Theorem B
  (`Work.OddBound.eq_fst_or_snd_of_minimising`).

It involves no normal holonomy, so it is the *same* input in both parities; the parallel subproject
`Submission/Work/EvenBound` is building it and uses it for the even-dimensional case. -/
def SharedFlushInput (hmet : IsMetricCompatible cov) (K : ℝ) : Prop :=
  Submission.InjSup.injSup hmet < Real.pi / Real.sqrt K →
    ∃ (p : M) (ξ η : TangentSpace I p),
      InjAtLeast hmet p (Submission.InjSup.injSup hmet) ∧
      (∀ r : ℝ, Submission.InjSup.injSup hmet < r → ¬ InjAtLeast hmet p r) ∧
      ‖ξ‖ = 1 ∧ ‖η‖ = 1 ∧ ξ ≠ η ∧
      GExp (cov := cov) hmet p (Submission.InjSup.injSup hmet • ξ)
        = GExp (cov := cov) hmet p (Submission.InjSup.injSup hmet • η) ∧
      Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (Submission.InjSup.injSup hmet • ξ))
        = ENNReal.ofReal (Submission.InjSup.injSup hmet) ∧
      Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (Submission.InjSup.injSup hmet • η))
        = ENNReal.ofReal (Submission.InjSup.injSup hmet) ∧
      ¬ ExistsShorteningField cov (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ))
          (2 * Submission.InjSup.injSup hmet) (K / 4)

/-- **The *flush-restricted* form of the odd-case input** (the weakest form of the remaining gap).
The assembly `Work.OddBound.klingenberg_length_bound_odd_of_rotatingFieldInput` only ever applies
`HasRotatingFieldInput` to the **flush configuration**: the ray of `ξ` at a maximal injectivity radius
`m = injSup hmet < π/√K`, periodic of period `2m` (which is what the flush structure supplies, via
Xu's Theorem B at `p` and at `q`).  This `Prop` asks for the shortening field *only* there, so it is
strictly weaker than `HasRotatingFieldInput K`
(`Work.OddBound.hasRotatingFieldInput_imp_flushShorteningInput`), and it carries the flush data ---
`InjAllAtLeast hmet m`, `InjAtLeast hmet p m`, maximality at `p`, unit `ξ`, and the periodicity
`GExp p ((2m) • ξ) = p`, hence via `Submission.KlingenbergEven.ray_periodic_of_two_minimising` the
full "exactly two minimising halves" structure --- as *hypotheses*, which is exactly the extra
geometric input a repaired area bound for the normal holonomy needs (the bare round-`S²`
counterexample to `A ≤ L²/4π` is not flush: there are infinitely many minimising geodesics between
antipodal points). -/
def FlushShorteningInput (hmet : IsMetricCompatible cov) (K : ℝ) : Prop :=
  SimplyConnectedSpace M →
  (∀ (p : M) (u v : TangentSpace I p), ‖u‖ = 1 → ‖v‖ = 1 → inner ℝ u v = 0 →
      K / 4 ≤ inner ℝ (curvVec cov p u v v) u) →
  ∀ {p : M} {m : ℝ} {ξ : TangentSpace I p}, 0 < m → m < Real.pi / Real.sqrt K →
    InjAtLeast hmet p m → (∀ r : ℝ, m < r → ¬ InjAtLeast hmet p r) →
    InjAllAtLeast hmet m → ‖ξ‖ = 1 →
    GExp (cov := cov) hmet p ((2 * m) • ξ) = p →
    ExistsShorteningField cov (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) (2 * m) (K / 4)

/-- The general odd-case input implies its flush-restricted form. -/
theorem hasRotatingFieldInput_imp_flushShorteningInput (hmet : IsMetricCompatible cov)
    {K : ℝ} (h : HasRotatingFieldInput (I := I) (cov := cov) K) :
    FlushShorteningInput (I := I) (cov := cov) hmet K := by
  intro hsc hpinch p m ξ hm hmπ hinjp _ hinjall hξ hper
  have hξne : ξ ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hξ; norm_num at hξ
  have hclosed : GExp (cov := cov) hmet p ((2 * m) • ξ) = GExp (cov := cov) hmet p ((0 : ℝ) • ξ) := by
    rw [zero_smul, GExp_zero]; exact hper
  have hgeo : ∀ t : ℝ, IsGeodesicAt (I := I) cov
      (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) t := fun t =>
    Submission.GExpRayZero.isGeodesicAt_GExp_smul_all (cov := cov) hmet p hξne t
  have hne : ∀ t : ℝ, curveVelocity (I := I)
      (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) t ≠ 0 := fun t =>
    Submission.EnergyRayCover.curveVelocity_GExp_smul_ne_zero (cov := cov) hmet hξne t
  have hsp : ∀ t ∈ Icc (0 : ℝ) ((2 : ℝ) * m),
      curveSpeed (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) t = 1 := fun t _ =>
    Submission.BrokenLength.curveSpeed_GExp_ray (cov := cov) hmet p hξne t ▸ hξ ▸ rfl
  have hlt : (2 : ℝ) * m < 2 * Real.pi / Real.sqrt K := by
    rw [mul_div_assoc]; linarith
  exact h hsc hpinch (by positivity) hlt hclosed hgeo hne hsp

end

end Work.OddBound

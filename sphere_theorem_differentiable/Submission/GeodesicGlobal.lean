import Submission.GeodesicExtend
import Submission.GeodesicSpeed
import Submission.Distance
import Submission.Commons.Analysis.ODE.contDiffOn_infty_of_hasDerivAt
import Submission.Commons.Analysis.ODE.ODE_solution_unique_Icc_left_of_contDiffAt

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Gluing geodesics across charts, and restarting them

`Submission/GeodesicExtend.lean` proves that an intrinsic geodesic satisfies the chart geodesic
equation in *every* chart.  This file draws the geometric consequences, and implements the
restart/extension step that lets a geodesic be continued beyond the chart in which it was
constructed.

## Contents

* `isGeodesicAt_of_chartODE`: a solution of the chart geodesic equation (on an interval, staying in
  the chart) is an intrinsic geodesic at every interior time (generalises
  `Geodesic.isGeodesicAt_chartSolution`, which is stated for the fixed interval `Ioo (-2) 2`);
* `chartODE_of_isGeodesic`: conversely, an intrinsic geodesic whose velocity field extends to a
  smooth section satisfies the chart geodesic equation on a neighbourhood of a point (interval form
  of `GeodesicExtend.hasDerivAt_deriv_chartCurve_of_isGeodesicAt`);
* `hasDerivAt_deriv_of_contDiffOn`: bookkeeping for `C^∞` functions on open subsets of `ℝ`;
* `contDiffOn_pair_of_chartODE`, `contMDiffOn_chartCurve_of_chartODE`: a solution `(u,w)` of the
  chart geodesic equation (on an open interval, staying in the chart) is `C^∞`, as is the intrinsic
  curve `t ↦ (extChartAt I x₀).symm (u t)`;
* `glue`, `glue_of_le`, `glue_of_lt`: the concatenation of `γ` (on `(-∞,T]`) with `σ (· - T)`
  (on `[T,∞)`);
* **`exists_geodesic_ray`**: if chart geodesics exist at `x` for every velocity of norm `≤ ρ`, then
  for every nonzero `ξ ∈ T_x M` there is a geodesic on the time interval `(-2ρ/‖ξ‖, 2ρ/‖ξ‖)` with
  initial velocity `ξ`, **constant speed** `‖ξ‖` (hence arclength `2ρ`), which is `C^∞` there.  The
  construction solves the chart equation for the small velocity `ρ·ξ/‖ξ‖` and rescales time by
  `‖ξ‖/ρ` (the chart spray is homogeneous of degree two);
* **`glue_chart`** (the main theorem): if `γ` is a geodesic on `[0,T]` (`T > 0`), `C^∞` on an open
  set containing `[0,T]`, with nonzero velocity at `T`, and `(u,w)` solves the chart geodesic
  equation in the chart at `x' = γ T` on `(-ε, ε+1)` with initial data equal to the chart data of
  `(γ T, γ'(T))`, then the concatenation of `γ` with `s ↦ (extChartAt I x').symm (u s)` is a geodesic
  on `[0, T + ε/2]`, `C^∞` on an open neighbourhood of it.

## Proof of `glue_chart` (the key step of the whole development)

The chart coordinates of `γ` near `T` satisfy the *same* chart geodesic equation as `u` — this is
chart-independence of the geodesic equation — with the same initial data at `T`; the one-sided
uniqueness theorem for the ODE (`Commons.Analysis.ODE.ODE_solution_unique_Icc_left_of_contDiffAt`)
then shows that the two agree to the *left* of `T`. That agreement simultaneously gives
(a) `C^∞`-smoothness of the concatenation across the junction and (b) the geodesic equation at the
junction (via `isGeodesicAt_of_chartODE` applied to the shifted solution `(u (· - T), w (· - T))`).

## Next steps (see `Submission/Roadmap.lean` §3.0)

1. **Uniform restart radius.** `exists_geodesic_ray` needs chart geodesics at the current point for
   velocities of norm `≤ ρ`. On a compact manifold the radius can be taken *uniform* over `M`:
   for `y` near `x` use the chart at `x` (the local existence is uniform on an open set of initial
   points, `Commons.Analysis.ODE.exists_uniform_secondOrderODE_solution_in_open`) together with the
   comparison of `‖frameVector x y a‖` with `‖a‖` on a compact set (`ChartBounds.exists_chartGram_bounds`
   — this needs `[Nontrivial E]`); compactness of `M` then gives a finite subcover and a positive
   minimum of the radius.
2. **Iteration.** By induction on `N ∈ ℕ`, using `exists_geodesic_ray` at the endpoint and
   `glue_chart` to attach the next piece, produce for every `T ≥ 0` a geodesic on `[0,T]` with
   prescribed initial data `(x, ξ)` (`‖ξ‖ = 1`), `C^∞` on a neighbourhood of `[0,T]`, of constant
   speed `1`.  Maintain the invariant as: `∃ V` open with `Icc 0 T ⊆ V`, `ContMDiffOn ∞ γ V`,
   `IsGeodesicAt` on `Icc 0 T`, and `‖γ' t‖ = 1` on `Icc 0 T` (the last two clauses of
   `exists_geodesic_ray` provide the speed at the new endpoint).
3. Then Hopf–Rinow (the shooting argument) follows as in `Submission/Roadmap.lean` §3.0 step 6.
-/

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.ChartConnection
open Submission.CurveField
open Commons.Geometry.Manifold.Tangent

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.GeodesicGlobal

noncomputable section

variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}

/-! ## Chart solutions are geodesics -/

/-- **A solution of the chart geodesic equation is an intrinsic geodesic.**  If `(u,w)` solves the
chart geodesic equation on the interval `Ioo a b` and stays in the target of the chart at `x₀`,
then the curve `s ↦ (extChartAt I x₀).symm (u s)` is an intrinsic geodesic at every interior time.
This is `Geodesic.isGeodesicAt_chartSolution` for an arbitrary interval. -/
theorem isGeodesicAt_of_chartODE (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (x₀ : M) {u w : ℝ → E} {a b : ℝ} (hab : a < b) {t : ℝ} (ht : t ∈ Ioo a b)
    (hstay : ∀ s ∈ Ioo a b, u s ∈ (extChartAt I x₀).target)
    (hu : ∀ s ∈ Ioo a b, HasDerivAt u (w s) s)
    (hw : ∀ s ∈ Ioo a b, HasDerivAt w (chartGeodesicVectorField cov x₀ (u s, w s)) s) :
    IsGeodesicAt cov (fun s => (extChartAt I x₀).symm (u s)) t := by
  intro Z hZ hZeq
  obtain ⟨δ, hδ, hδsub⟩ := (nhds_basis_Ioo_pos t).mem_iff.mp hZeq
  have htI : t ∈ Ioo (max a (t - δ)) (min b (t + δ)) :=
    ⟨max_lt ht.1 (by linarith), lt_min ht.2 (by linarith)⟩
  have hsub : Ioo (max a (t - δ)) (min b (t + δ)) ⊆ Ioo a b := fun s hs =>
    ⟨lt_of_le_of_lt (le_max_left _ _) hs.1, lt_of_lt_of_le hs.2 (min_le_left _ _)⟩
  exact cov_eq_zero_of_chartGeodesic cov x₀ htI
    (fun s hs => hu s (hsub hs)) (fun s hs => hw s (hsub hs)) (fun s hs => hstay s (hsub hs))
    Z hZ.contMDiffAt (fun s hs => hδsub ⟨lt_of_le_of_lt (le_max_right _ _) hs.1,
      lt_of_lt_of_le hs.2 (min_le_right _ _)⟩)

/-! ## Smoothness bookkeeping for the coordinate curve -/

/-- A `C^∞` function on an open set of `ℝ` has a derivative which is again differentiable, and
`deriv (deriv f) = (deriv f)'`. -/
lemma hasDerivAt_deriv_of_contDiffOn {f : ℝ → E} {s : Set ℝ} (hs : IsOpen s) {t : ℝ}
    (ht : t ∈ s) (hf : ContDiffOn ℝ ∞ f s) :
    HasDerivAt f (deriv f t) t ∧ HasDerivAt (deriv f) (deriv (deriv f) t) t := by
  have h1 : HasDerivWithinAt f (derivWithin f s t) s t :=
    ((hf.differentiableOn (by simp : ((⊤ : ℕ∞) : ℕ∞ω) ≠ 0) t ht)).hasFDerivWithinAt
      |>.hasDerivWithinAt
  rw [derivWithin_of_isOpen hs ht] at h1
  have hf' : ContDiffOn ℝ ∞ (deriv f) s := hf.deriv_of_isOpen hs (le_of_eq (by simp))
  have h2 : HasDerivWithinAt (deriv f) (derivWithin (deriv f) s t) s t :=
    ((hf'.differentiableOn (by simp : ((⊤ : ℕ∞) : ℕ∞ω) ≠ 0) t ht)).hasFDerivWithinAt
      |>.hasDerivWithinAt
  rw [derivWithin_of_isOpen hs ht] at h2
  exact ⟨h1.hasDerivAt (hs.mem_nhds ht), h2.hasDerivAt (hs.mem_nhds ht)⟩

/-! ## The chart equation holds in a neighbourhood of every point -/

/-- **The chart geodesic equation for an intrinsic geodesic, on an interval.**  If `γ` is `C^∞`
on an open set `V ∋ t₀`, is a geodesic at every point of `V`, and `Z` is a globally smooth section
agreeing with the velocity of `γ` near `t₀`, then the coordinate curve `u = (extChartAt I x₀) ∘ γ`
satisfies the chart geodesic equation `u'' = -Γ(u')(γ')` in a neighbourhood of `t₀` (in the chart
at `x₀`, provided `γ t₀` lies in that chart).

This is the interval version of
`Submission.GeodesicExtend.hasDerivAt_deriv_chartCurve_of_isGeodesicAt`; it is the form needed when
two solutions of the equation have to be compared on an interval. -/
theorem chartODE_of_isGeodesic (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (x₀ : M) {γ : ℝ → M} {V : Set ℝ} (hV : IsOpen V) {t₀ : ℝ} (ht₀ : t₀ ∈ V)
    (hγ : ContMDiffOn 𝓘(ℝ) I ∞ γ V) (hsrc : γ t₀ ∈ (chartAt H x₀).source)
    (hgeo : ∀ t ∈ V, IsGeodesicAt cov γ t)
    (Z : Π x : M, TangentSpace I x) (hZ : CMDiff ∞ (T% Z))
    (hZeq : ∀ᶠ t in 𝓝 t₀, Z (γ t) = curveVelocity (I := I) γ t) :
    ∃ δ > 0,
      (∀ s ∈ Ioo (t₀ - δ) (t₀ + δ), γ s ∈ (chartAt H x₀).source) ∧
      (∀ s ∈ Ioo (t₀ - δ) (t₀ + δ), Z (γ s) = curveVelocity (I := I) γ s) ∧
      (∀ s ∈ Ioo (t₀ - δ) (t₀ + δ),
        HasDerivAt (fun t => (extChartAt I x₀) (γ t))
          (deriv (fun t => (extChartAt I x₀) (γ t)) s) s) ∧
      (∀ s ∈ Ioo (t₀ - δ) (t₀ + δ),
        HasDerivAt (deriv (fun t => (extChartAt I x₀) (γ t)))
          (chartGeodesicVectorField cov x₀ ((extChartAt I x₀) (γ s),
            deriv (fun t => (extChartAt I x₀) (γ t)) s)) s) := by
  -- the open set on which everything is smooth
  have hW : IsOpen (V ∩ γ ⁻¹' (chartAt H x₀).source) := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    exact Filter.inter_mem (hV.mem_nhds ht.1)
      ((hγ.continuousOn.continuousAt (hV.mem_nhds ht.1)).preimage_mem_nhds
        ((chartAt H x₀).open_source.mem_nhds ht.2))
  have ht₀W : t₀ ∈ V ∩ γ ⁻¹' (chartAt H x₀).source := ⟨ht₀, hsrc⟩
  obtain ⟨δ, hδ, hδsub⟩ := (nhds_basis_Ioo_pos t₀).mem_iff.mp
    (Filter.inter_mem (hW.mem_nhds ht₀W) hZeq)
  set J : Set ℝ := Ioo (t₀ - δ) (t₀ + δ) with hJ
  have hJo : IsOpen J := isOpen_Ioo
  have hJW : J ⊆ V ∩ γ ⁻¹' (chartAt H x₀).source := fun s hs => (hδsub hs).1
  -- the coordinate curve
  set u : ℝ → E := fun t => (extChartAt I x₀) (γ t) with hu
  have hu_cd : ContDiffOn ℝ ∞ u J := by
    have hcomp : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ, E) ∞ (fun t : ℝ => (extChartAt I x₀) (γ t)) J :=
      (contMDiffOn_extChartAt (I := I) (x := x₀)).comp
        (hγ.mono (fun s hs => (hJW hs).1)) (fun s hs => (hJW hs).2)
    exact hcomp.contDiffOn
  have hder : ∀ s ∈ J, HasDerivAt u (deriv u s) s ∧ HasDerivAt (deriv u) (deriv (deriv u) s) s :=
    fun s hs => hasDerivAt_deriv_of_contDiffOn hJo hs hu_cd
  have hstay : ∀ s ∈ J, u s ∈ (extChartAt I x₀).target := fun s hs =>
    PartialEquiv.map_source (extChartAt I x₀) (by rw [extChartAt_source]; exact (hJW hs).2)
  have hleft : ∀ r ∈ J, (extChartAt I x₀).symm (u r) = γ r := fun r hr =>
    PartialEquiv.left_inv (extChartAt I x₀) (by rw [extChartAt_source]; exact (hJW hr).2)
  have hZeq' : ∀ r ∈ J, Z ((extChartAt I x₀).symm (u r))
      = curveVelocity (I := I) (fun s => (extChartAt I x₀).symm (u s)) r := by
    intro r hr
    have hagl : (fun s => (extChartAt I x₀).symm (u s)) =ᶠ[𝓝 r] γ :=
      Filter.eventuallyEq_of_mem (hJo.mem_nhds hr) (fun s hs => hleft s hs)
    rw [hleft r hr, Submission.GeodesicExtend.curveVelocity_congr_of_eventuallyEq (I := I) hagl]
    exact (hδsub hr).2
  refine ⟨δ, hδ, fun s hs => (hJW hs).2, fun s hs => (hδsub hs).2, fun s hs => (hder s hs).1, ?_⟩
  intro s hs
  have hsV : s ∈ V := (hJW hs).1
  have hagl : (fun r => (extChartAt I x₀).symm (u r)) =ᶠ[𝓝 s] γ :=
    Filter.eventuallyEq_of_mem (hJo.mem_nhds hs) (fun r hr => hleft r hr)
  have hgeo' : IsGeodesicAt cov (fun r => (extChartAt I x₀).symm (u r)) s :=
    (Submission.GeodesicExtend.isGeodesicAt_congr_of_eventuallyEq (I := I) hagl).mpr (hgeo s hsV)
  have heq := Submission.Geodesic.chartGeodesicVectorField_eq_of_isGeodesicAt (cov := cov) x₀
    (a := t₀ - δ) (b := t₀ + δ) (u := u) (v := deriv u) (w := deriv (deriv u)) hs
    (fun r hr => (hder r hr).1) (fun r hr => (hder r hr).2) hstay Z hZ
    hZeq' hgeo'
  rw [← heq]
  exact (hder s hs).2

/-! ## Gluing two geodesics -/

/-- The concatenation of `γ` (on `(-∞, T]`) with the time-shift of `σ` (on `[T, ∞)`). -/
noncomputable def glue (γ σ : ℝ → M) (T : ℝ) : ℝ → M :=
  fun t => if t ≤ T then γ t else σ (t - T)

@[simp] lemma glue_of_le {γ σ : ℝ → M} {T t : ℝ} (h : t ≤ T) : glue γ σ T t = γ t := if_pos h

@[simp] lemma glue_of_lt {γ σ : ℝ → M} {T t : ℝ} (h : T < t) :
    glue γ σ T t = σ (t - T) := if_neg (not_le.mpr h)

/-! ## Smoothness of chart solutions -/

section Smooth

variable [ContMDiffCovariantDerivative cov ∞]

/-- The chart geodesic spray is `C^∞` on the chart. -/
lemma contDiffOn_chartSpray' (x₀ : M) :
    ContDiffOn ℝ ∞ (fun z : E × E => chartGeodesicVectorField cov x₀ z)
      ((extChartAt I x₀).target ×ˢ (univ : Set E)) :=
  Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contDiffOn_chartSpray (cov := cov) x₀

/-- **A solution of the chart geodesic equation is `C^∞`.**  If `(u,w)` solves the chart geodesic
equation on the open interval `Ioo A B` and stays in the chart, then the *state* `t ↦ (u t, w t)`
is `C^∞` there.  This is the bootstrap for the vector field `z ↦ (z.2, spray z)` whose field is
`C^∞` on the chart (`contDiffOn_chartSpray`). -/
theorem contDiffOn_pair_of_chartODE (x₀ : M) {u w : ℝ → E} {A B : ℝ}
    (hstay : ∀ t ∈ Ioo A B, u t ∈ (extChartAt I x₀).target)
    (hu : ∀ t ∈ Ioo A B, HasDerivAt u (w t) t)
    (hw : ∀ t ∈ Ioo A B, HasDerivAt w (chartGeodesicVectorField cov x₀ (u t, w t)) t) :
    ContDiffOn ℝ ∞ (fun t : ℝ => (u t, w t)) (Ioo A B) := by
  set V : Set (E × E) := {z | z.1 ∈ (extChartAt I x₀).target} with hV
  have hF : ContDiffOn ℝ ∞ (fun z : E × E => (z.2, chartGeodesicVectorField cov x₀ z)) V :=
    ContDiffOn.prodMk (contDiffOn_snd.mono (Set.subset_univ V))
      ((contDiffOn_chartSpray' (cov := cov) x₀).mono
        (fun z hz => ⟨hz, Set.mem_univ _⟩))
  have hcont : ContinuousOn (fun t : ℝ => (u t, w t)) (Ioo A B) := fun t ht =>
    ((hu t ht).continuousAt.prodMk (hw t ht).continuousAt).continuousWithinAt
  apply contDiffOn_of_locally_contDiffOn
  intro t ht
  obtain ⟨htA, htB⟩ := ht
  refine ⟨Ioo ((A + t) / 2) ((t + B) / 2), isOpen_Ioo,
    ⟨by linarith, by linarith⟩, ?_⟩
  have hcd : (A + t) / 2 < (t + B) / 2 := by linarith
  have hsub : Set.Icc ((A + t) / 2) ((t + B) / 2) ⊆ Ioo A B := by
    intro s hs
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have key := Commons.Analysis.ODE.contDiffOn_infty_of_hasDerivAt (F := fun z : E × E =>
      (z.2, chartGeodesicVectorField cov x₀ z)) (V := V) hcd hF
    (fun s hs => hstay s (hsub hs))
    (fun s hs => (hu s (hsub hs)).prodMk (hw s (hsub hs)))
    (hcont.mono hsub)
  refine key.mono ?_
  intro s hs
  exact Set.Ioo_subset_Icc_self hs.2

/-- **A solution of the chart geodesic equation is a smooth curve.**  Under the hypotheses of
`contDiffOn_pair_of_chartODE`, the intrinsic curve `t ↦ (extChartAt I x₀).symm (u t)` is `C^∞` on
`Ioo A B`. -/
theorem contMDiffOn_chartCurve_of_chartODE (x₀ : M) {u w : ℝ → E} {A B : ℝ}
    (hstay : ∀ t ∈ Ioo A B, u t ∈ (extChartAt I x₀).target)
    (hu : ∀ t ∈ Ioo A B, HasDerivAt u (w t) t)
    (hw : ∀ t ∈ Ioo A B, HasDerivAt w (chartGeodesicVectorField cov x₀ (u t, w t)) t) :
    ContMDiffOn 𝓘(ℝ) I ∞ (fun t : ℝ => (extChartAt I x₀).symm (u t)) (Ioo A B) := by
  have hpair := contDiffOn_pair_of_chartODE (cov := cov) x₀ hstay hu hw
  have hufst : ContDiffOn ℝ ∞ u (Ioo A B) := by
    have h := hpair.fst
    simpa only using h
  have hmain : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ u (Ioo A B) := hufst.contMDiffOn
  have hsymm := (contMDiffOn_extChartAt_symm (I := I) (x := x₀)).comp hmain hstay
  simpa only [Function.comp_def] using hsymm

end Smooth

/-! ## Restarting a geodesic in a new chart -/

section Ray

variable [I.Boundaryless] [ContMDiffCovariantDerivative cov ∞]

/-- **A geodesic ray with prescribed initial velocity, of arclength `ρ`.**  If chart geodesics exist
at `x` for every velocity of norm `≤ ρ`, then for every nonzero `ξ ∈ T_x M` there is a geodesic
defined on the time interval `(-2ρ/‖ξ‖, 2ρ/‖ξ‖)`, with initial velocity `ξ` and constant speed
`‖ξ‖`; in particular it has arclength `2ρ` on that interval.

The construction solves the chart geodesic equation for the small velocity `ρ · ξ/‖ξ‖` and rescales
time by `‖ξ‖/ρ`, using that the chart spray is homogeneous of degree two. -/
theorem exists_geodesic_ray (x : M) {ρ : ℝ} (hρ : 0 < ρ)
    (hex : ∀ v : TangentSpace I x, ‖v‖ ≤ ρ → ∃ u w : ℝ → E, HasChartGeodesic cov x v u w)
    (hmet : IsMetricCompatible cov)
    (ξ : TangentSpace I x) (hξ : ξ ≠ 0) :
    ∃ u w : ℝ → E,
      u 0 = (extChartAt I x) x ∧
      w 0 = (trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ x ξ ∧
      (∀ t ∈ Ioo (-(2 * ρ / ‖ξ‖)) (2 * ρ / ‖ξ‖), u t ∈ (extChartAt I x).target) ∧
      (∀ t ∈ Ioo (-(2 * ρ / ‖ξ‖)) (2 * ρ / ‖ξ‖), HasDerivAt u (w t) t) ∧
      (∀ t ∈ Ioo (-(2 * ρ / ‖ξ‖)) (2 * ρ / ‖ξ‖),
        HasDerivAt w (chartGeodesicVectorField cov x (u t, w t)) t) ∧
      (∀ t ∈ Ioo (-(2 * ρ / ‖ξ‖)) (2 * ρ / ‖ξ‖),
        ‖curveVelocity (I := I) (fun s => (extChartAt I x).symm (u s)) t‖ = ‖ξ‖) ∧
      (∀ t ∈ Icc (-(ρ / ‖ξ‖)) (ρ / ‖ξ‖),
        IsGeodesicAt cov (fun s => (extChartAt I x).symm (u s)) t) ∧
      ContMDiffOn 𝓘(ℝ) I ∞ (fun s => (extChartAt I x).symm (u s))
        (Ioo (-(2 * ρ / ‖ξ‖)) (2 * ρ / ‖ξ‖)) := by
  classical
  have hξpos : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
  have hwpos : 0 < ρ / ‖ξ‖ := div_pos hρ hξpos
  have h2wpos : 0 < 2 * ρ / ‖ξ‖ := div_pos (by linarith) hξpos
  set c : ℝ := ‖ξ‖ / ρ with hc
  have hcpos : 0 < c := div_pos hξpos hρ
  have hcne : c ≠ 0 := ne_of_gt hcpos
  -- the small chart velocity
  have hsmall : ‖(ρ • ((‖ξ‖)⁻¹ • ξ) : TangentSpace I x)‖ = ρ := by
    rw [norm_smul, norm_smul, norm_inv, Real.norm_of_nonneg (norm_nonneg ξ),
      Real.norm_of_nonneg hρ.le, inv_mul_cancel₀ (ne_of_gt hξpos), mul_one]
  obtain ⟨u, wg, huw⟩ := hex (ρ • ((‖ξ‖)⁻¹ • ξ)) hsmall.le
  set u' : ℝ → E := fun t => u (c * t) with hu'
  set w' : ℝ → E := fun t => c • wg (c * t) with hw'
  have hsub : Icc (-(ρ / ‖ξ‖)) (ρ / ‖ξ‖) ⊆ Ioo (-(2 * ρ / ‖ξ‖)) (2 * ρ / ‖ξ‖) := by
    intro t ht
    have h2 : 2 * ρ / ‖ξ‖ = 2 * (ρ / ‖ξ‖) := by ring
    rw [h2]
    exact ⟨by linarith [ht.1, hwpos], by linarith [ht.2, hwpos]⟩
  have hct : ∀ t : ℝ, t ∈ Ioo (-(2 * ρ / ‖ξ‖)) (2 * ρ / ‖ξ‖) → c * t ∈ Ioo (-2 : ℝ) 2 := by
    intro t ht
    have h2 : 2 * ρ / ‖ξ‖ = 2 / c := by rw [hc]; field_simp
    rw [h2] at ht
    have h1 : c * t < 2 := by
      have h := mul_lt_mul_of_pos_left ht.2 hcpos
      rwa [mul_div_cancel₀ (2 : ℝ) hcne] at h
    have h2' : -2 < c * t := by
      have h := mul_lt_mul_of_pos_left ht.1 hcpos
      rw [mul_neg, mul_div_cancel₀ (2 : ℝ) hcne] at h
      linarith
    exact ⟨h2', h1⟩
  have htarget : ∀ t ∈ Ioo (-(2 * ρ / ‖ξ‖)) (2 * ρ / ‖ξ‖),
      u' t ∈ (extChartAt I x).target := fun t ht => huw.2.2.1 (c * t) (hct t ht)
  have hdu : ∀ t ∈ Ioo (-(2 * ρ / ‖ξ‖)) (2 * ρ / ‖ξ‖), HasDerivAt u' (w' t) t := by
    intro t ht
    have h := (huw.2.2.2.1 (c * t) (hct t ht)).scomp t (hasDerivAt_const_mul c)
    simpa only [hu', hw', Function.comp_def] using h
  have hdw : ∀ t ∈ Ioo (-(2 * ρ / ‖ξ‖)) (2 * ρ / ‖ξ‖),
      HasDerivAt w' (chartGeodesicVectorField cov x (u' t, w' t)) t := by
    intro t ht
    have h1 : HasDerivAt (fun s => wg (c * s))
        (c • chartGeodesicVectorField cov x (u (c * t), wg (c * t))) t :=
      (huw.2.2.2.2 (c * t) (hct t ht)).scomp t (hasDerivAt_const_mul c)
    have h2 : HasDerivAt (fun s => c • wg (c * s))
        (c • (c • chartGeodesicVectorField cov x (u (c * t), wg (c * t)))) t :=
      h1.const_smul c
    have h3 : c • (c • chartGeodesicVectorField cov x (u (c * t), wg (c * t)))
        = chartGeodesicVectorField cov x (u (c * t), c • wg (c * t)) := by
      rw [smul_smul, ← pow_two]
      rw [← chartGeodesicVectorField_smul cov x c (u (c * t), wg (c * t))
        (huw.2.2.1 (c * t) (hct t ht))]
    rw [h3] at h2
    simpa only [hu', hw', Function.comp_def] using h2
  let σ : ℝ → M := fun t => (extChartAt I x).symm (u' t)
  have hσ0 : (extChartAt I x).symm (u' 0) = x := by
    have h1 : u' 0 = (extChartAt I x) x := by
      show u (c * 0) = _
      rw [mul_zero]
      exact huw.1
    rw [h1]
    exact (extChartAt I x).left_inv (mem_extChartAt_source x)
  have hlev : ∀ t ∈ Ioo (-(2 * ρ / ‖ξ‖)) (2 * ρ / ‖ξ‖),
      curveVelocity (I := I) σ t
        = (trivializationAt E (TangentSpace I) x).symmL ℝ ((extChartAt I x).symm (u' t)) (w' t) := by
    intro t ht
    have hev : ∀ᶠ s in 𝓝 t, u' s ∈ (extChartAt I x).target :=
      Filter.eventually_of_mem (isOpen_Ioo.mem_nhds ht) htarget
    exact curveVelocity_extChartAt_symm (I := I) (x₀ := x) (u := u') (t := t) (v := w' t)
      (hdu t ht) (htarget t ht) hev
  -- the map `symmL` at the base point is the identity
  have hsymm : (trivializationAt E (TangentSpace I) x).symmL ℝ x ξ = ξ := by
    have h0 := Trivialization.symmL_continuousLinearMapAt (R := ℝ)
      (e := trivializationAt E (TangentSpace I) x) (mem_chart_source H x) ξ
    rwa [GeodesicSpeed.continuousLinearMapAt_self_eq] at h0
  have hcη : c • (ρ • ((‖ξ‖)⁻¹ • ξ)) = ξ := by
    have h3 : (c * ρ) * ‖ξ‖⁻¹ = 1 := by rw [hc]; field_simp
    exact ((smul_smul c ρ ((‖ξ‖)⁻¹ • ξ)).trans
      (smul_smul (c * ρ) (‖ξ‖⁻¹) ξ)).trans (by rw [h3, one_smul])
  have hcoe : c • ((trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ x
        (ρ • ((‖ξ‖)⁻¹ • ξ))) = ξ := by
    have h1 : (trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ x
        (ρ • ((‖ξ‖)⁻¹ • ξ)) = ρ • ((‖ξ‖)⁻¹ • ξ) :=
      GeodesicSpeed.continuousLinearMapAt_self_eq x (ρ • ((‖ξ‖)⁻¹ • ξ))
    rw [h1]
    exact hcη
  -- the velocity at `0`
  have hvel0 : (curveVelocity (I := I) σ 0 : E) = (ξ : E) := by
    have hmem0 : (0 : ℝ) ∈ Ioo (-(2 * ρ / ‖ξ‖)) (2 * ρ / ‖ξ‖) :=
      ⟨by linarith, by linarith⟩
    have h := hlev 0 hmem0
    rw [h]
    show (trivializationAt E (TangentSpace I) x).symmL ℝ ((extChartAt I x).symm (u' 0))
      (w' 0) = (ξ : E)
    have hw0 : w' 0 = c • wg 0 := by simp only [hw', mul_zero]
    rw [hw0, huw.2.1]
    rw [show (extChartAt I x).symm (u' 0) = x from hσ0]
    rw [hcoe]
    exact hsymm
  -- the constant speed
  have hbv : ∀ a : E, chartGram (I := I) x x a a
      = ‖(show TangentSpace I x from a)‖ ^ 2 := by
    intro a
    rw [Submission.Distance.chartGram_self_apply, real_inner_self_eq_norm_sq]
  have hspeed : ∀ t ∈ Ioo (-(2 * ρ / ‖ξ‖)) (2 * ρ / ‖ξ‖), ‖curveVelocity (I := I) σ t‖ = ‖ξ‖ := by
    intro t ht
    rw [hlev t ht]
    have h2 : ‖(trivializationAt E (TangentSpace I) x).symmL ℝ ((extChartAt I x).symm (u' t))
        (w' t)‖ ^ 2 = ‖ξ‖ ^ 2 := by
      rw [show (trivializationAt E (TangentSpace I) x).symmL ℝ ((extChartAt I x).symm (u' t))
          (w' t) = frameVector (I := I) x ((extChartAt I x).symm (u (c * t))) (w' t) from rfl,
        show w' t = c • wg (c * t) from rfl]
      have hb : ‖frameVector (I := I) x ((extChartAt I x).symm (u (c * t))) (c • wg (c * t))‖ ^ 2
          = chartGram (I := I) x ((extChartAt I x).symm (u (c * t))) (c • wg (c * t))
              (c • wg (c * t)) := by
        show ‖frameVector (I := I) x ((extChartAt I x).symm (u (c * t))) (c • wg (c * t))‖ ^ 2
          = inner ℝ (frameVector (I := I) x ((extChartAt I x).symm (u (c * t))) (c • wg (c * t)))
              (frameVector (I := I) x ((extChartAt I x).symm (u (c * t))) (c • wg (c * t)))
        rw [real_inner_self_eq_norm_sq]
      rw [hb, Submission.ChartBounds.chartGram_smul_smul,
        GeodesicSpeed.hasChartGeodesic_chartGram_const (cov := cov) hmet x huw (c * t)
          (hct t ht)]
      have hstep : chartGram (I := I) x x (ρ • ((‖ξ‖)⁻¹ • ξ)) (ρ • ((‖ξ‖)⁻¹ • ξ)) = ρ ^ 2 :=
        (hbv (ρ • ((‖ξ‖)⁻¹ • ξ))).trans (by rw [hsmall])
      rw [hstep, hc]
      field_simp
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h2 with h | h
    · exact h
    · exfalso
      have hnn := norm_nonneg ((trivializationAt E (TangentSpace I) x).symmL ℝ
        ((extChartAt I x).symm (u' t)) (w' t))
      linarith
  refine ⟨u', w', ?_, ?_, htarget, hdu, hdw, hspeed, ?_, ?_⟩
  · show u (c * 0) = (extChartAt I x) x
    rw [mul_zero]
    exact huw.1
  · rw [show w' 0 = c • wg 0 from by simp only [hw', mul_zero], huw.2.1, ← map_smul, hcη]
  · intro t ht
    exact isGeodesicAt_of_chartODE cov x (a := -(2 * ρ / ‖ξ‖)) (b := 2 * ρ / ‖ξ‖)
      (by linarith [h2wpos]) (hsub ht) htarget hdu hdw
  · exact contMDiffOn_chartCurve_of_chartODE (cov := cov) x htarget hdu hdw

end Ray

/-! ## Gluing a chart solution onto a geodesic -/

section Glue

variable [I.Boundaryless] [ContMDiffCovariantDerivative cov ∞]

/-- **Gluing a chart solution onto a geodesic.**  Let `γ` be a geodesic on `[0,T]` (`T > 0`) which
is `C^∞` on an open set containing `[0,T]` and has nonzero velocity at `T`.  Let `(u,w)` be a
solution of the chart geodesic equation in the chart at `x' = γ T` on the interval `(-ε, ε+1)`,
whose initial data at `0` are the chart data of `(γ T, γ'(T))`:
`u 0 = (extChartAt I x') x'` and `w 0 = (chart velocity of γ'(T))`.  Then the concatenation of `γ`
with `s ↦ (extChartAt I x').symm (u s)` is a geodesic on `[0, T + ε/2]`, and it is `C^∞` on an open
neighbourhood of that interval.

The point is that the chart coordinates of `γ` near `T` satisfy the *same* (chart) geodesic equation
as `u` — this is the chart-independence of the geodesic equation
(`Submission.GeodesicExtend.hasDerivAt_deriv_chartCurve_of_isGeodesicAt`) — with the same initial data
at `T`; the one-sided uniqueness theorem for the ODE
(`Commons.Analysis.ODE.ODE_solution_unique_Icc_left_of_contDiffAt`) then shows that they agree to the
left of `T`, which gives both `C^∞`-smoothness across the junction and the geodesic equation there. -/
theorem glue_chart (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    [ContMDiffCovariantDerivative cov ∞]
    {γ : ℝ → M} {T ε : ℝ} (hε : 0 < ε) (hTpos : 0 < T)
    {V : Set ℝ} (hV : IsOpen V) (hsub : Icc 0 T ⊆ V)
    (hγsm : ContMDiffOn 𝓘(ℝ) I ∞ γ V) (hγgeo : ∀ t ∈ Icc 0 T, IsGeodesicAt cov γ t)
    (hne : curveVelocity (I := I) γ T ≠ 0)
    {u w : ℝ → E}
    (hu : ∀ s ∈ Ioo (-ε) (ε + 1), HasDerivAt u (w s) s)
    (hw : ∀ s ∈ Ioo (-ε) (ε + 1), HasDerivAt w (chartGeodesicVectorField cov (γ T) (u s, w s)) s)
    (hstay : ∀ s ∈ Ioo (-ε) (ε + 1), u s ∈ (extChartAt I (γ T)).target)
    (hu0 : u 0 = (extChartAt I (γ T)) (γ T))
    (hw0 : w 0 = (trivializationAt E (TangentSpace I) (γ T)).continuousLinearMapAt ℝ (γ T)
      (curveVelocity (I := I) γ T)) :
    ∃ V' : Set ℝ, IsOpen V' ∧ Icc 0 (T + ε / 2) ⊆ V' ∧
      ContMDiffOn 𝓘(ℝ) I ∞ (glue γ (fun s => (extChartAt I (γ T)).symm (u s)) T) V' ∧
      (∀ t ∈ Icc 0 (T + ε / 2), IsGeodesicAt cov
        (glue γ (fun s => (extChartAt I (γ T)).symm (u s)) T) t) := by
  classical
  have hTV : T ∈ V := hsub ⟨hTpos.le, le_rfl⟩
  obtain ⟨Z, hZ, hZev⟩ := CurveField.exists_contMDiff_section_eventuallyEq_curveVelocity
    (I := I) hV hTV hγsm hne
  have hW : IsOpen (V ∩ γ ⁻¹' (chartAt H (γ T)).source) := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    exact Filter.inter_mem (hV.mem_nhds ht.1)
      ((hγsm.continuousOn.continuousAt (hV.mem_nhds ht.1)).preimage_mem_nhds
        ((chartAt H (γ T)).open_source.mem_nhds ht.2))
  have hTW : T ∈ V ∩ γ ⁻¹' (chartAt H (γ T)).source := ⟨hTV, mem_chart_source H (γ T)⟩
  obtain ⟨δ₀, hδ₀, hδ₀sub⟩ := (nhds_basis_Ioo_pos T).mem_iff.mp
    (Filter.inter_mem (hW.mem_nhds hTW) hZev)
  have hUcd : ContDiffOn ℝ ∞ (fun t : ℝ => (extChartAt I (γ T)) (γ t))
      (V ∩ γ ⁻¹' (chartAt H (γ T)).source) := by
    have hcomp : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ, E) ∞ (fun t : ℝ => (extChartAt I (γ T)) (γ t))
        (V ∩ γ ⁻¹' (chartAt H (γ T)).source) :=
      (contMDiffOn_extChartAt (I := I) (x := γ T)).comp
        (hγsm.mono Set.inter_subset_left) (fun t ht => ht.2)
    exact hcomp.contDiffOn
  set δ : ℝ := min (min (δ₀ / 2) (T / 2)) (ε / 2) with hδdef
  have hδpos : 0 < δ := lt_min (lt_min (by linarith) (by linarith)) (by linarith)
  have hδle₀ : δ ≤ δ₀ / 2 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hδleT : δ ≤ T / 2 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hδleε : δ ≤ ε / 2 := min_le_right _ _
  have hIoo : ∀ t ∈ Ioo (T - δ) (T + δ), t ∈ V ∩ γ ⁻¹' (chartAt H (γ T)).source :=
    fun t ht => (hδ₀sub ⟨by linarith [ht.1, hδle₀], by linarith [ht.2, hδle₀, hδ₀]⟩).1
  have hZeqIoo : ∀ t ∈ Ioo (T - δ) (T + δ),
      Z (γ t) = curveVelocity (I := I) γ t :=
    fun t ht => (hδ₀sub ⟨by linarith [ht.1, hδle₀], by linarith [ht.2, hδle₀, hδ₀]⟩).2
  -- the chart coordinates of `γ` satisfy the chart geodesic equation near `T`
  have hleft : ∀ t ∈ Ioc (T - δ) T,
      HasDerivAt (fun s : ℝ => (extChartAt I (γ T)) (γ s))
          (deriv (fun s : ℝ => (extChartAt I (γ T)) (γ s)) t) t ∧
        HasDerivAt (deriv (fun s : ℝ => (extChartAt I (γ T)) (γ s)))
          (chartGeodesicVectorField cov (γ T) ((extChartAt I (γ T)) (γ t),
            deriv (fun s : ℝ => (extChartAt I (γ T)) (γ s)) t)) t := by
    intro t ht
    have htI : t ∈ Ioo (T - δ) (T + δ) := ⟨ht.1, by linarith [ht.2, hδpos]⟩
    have hder := hasDerivAt_deriv_of_contDiffOn hW (hIoo t htI) hUcd
    refine ⟨hder.1, ?_⟩
    have hleft' : ∀ s ∈ Ioo (T - δ) (T + δ),
        Z ((extChartAt I (γ T)).symm ((extChartAt I (γ T)) (γ s)))
          = curveVelocity (I := I) (fun s : ℝ => (extChartAt I (γ T)).symm
              ((extChartAt I (γ T)) (γ s))) s := by
      intro s hs
      have hleftinv : (extChartAt I (γ T)).symm ((extChartAt I (γ T)) (γ s)) = γ s :=
        PartialEquiv.left_inv (extChartAt I (γ T)) (by rw [extChartAt_source]; exact (hIoo s hs).2)
      rw [hleftinv]
      have hagl : (fun r : ℝ => (extChartAt I (γ T)).symm ((extChartAt I (γ T)) (γ r)))
          =ᶠ[𝓝 s] γ :=
        Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hs)
          (fun r hr => PartialEquiv.left_inv (extChartAt I (γ T))
            (by rw [extChartAt_source]; exact (hIoo r hr).2))
      rw [Submission.GeodesicExtend.curveVelocity_congr_of_eventuallyEq (I := I) hagl]
      exact hZeqIoo s hs
    have hgeo' : IsGeodesicAt cov
        (fun s : ℝ => (extChartAt I (γ T)).symm ((extChartAt I (γ T)) (γ s))) t := by
      have hagl : (fun r : ℝ => (extChartAt I (γ T)).symm ((extChartAt I (γ T)) (γ r)))
          =ᶠ[𝓝 t] γ :=
        Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds htI)
          (fun r hr => PartialEquiv.left_inv (extChartAt I (γ T))
            (by rw [extChartAt_source]; exact (hIoo r hr).2))
      refine (Submission.GeodesicExtend.isGeodesicAt_congr_of_eventuallyEq (I := I) hagl).mpr
        (hγgeo t ⟨?_, ht.2⟩)
      linarith [ht.1, hδleT, hδpos, hTpos]
    have heq := Submission.Geodesic.chartGeodesicVectorField_eq_of_isGeodesicAt (cov := cov) (γ T)
      (a := T - δ) (b := T + δ)
      (u := fun s : ℝ => (extChartAt I (γ T)) (γ s))
      (v := deriv fun s : ℝ => (extChartAt I (γ T)) (γ s))
      (w := deriv (deriv fun s : ℝ => (extChartAt I (γ T)) (γ s)))
      htI (fun s hs => (hasDerivAt_deriv_of_contDiffOn hW (hIoo s hs) hUcd).1)
      (fun s hs => (hasDerivAt_deriv_of_contDiffOn hW (hIoo s hs) hUcd).2)
      (fun s hs => PartialEquiv.map_source (extChartAt I (γ T))
        (by rw [extChartAt_source]; exact (hIoo s hs).2))
      Z hZ hleft' hgeo'
    rw [← heq]
    exact hder.2
  -- the chart solution and its shift to the variable `t`
  set σ : ℝ → M := fun s => (extChartAt I (γ T)).symm (u s) with hσ
  set u₂ : ℝ → E := fun t => u (t - T) with hu₂
  set w₂ : ℝ → E := fun t => w (t - T) with hw₂
  have hstay₂ : ∀ s ∈ Ioo (T - ε) (T + ε + 1),
      u₂ s ∈ (extChartAt I (γ T)).target := fun s hs =>
    hstay (s - T) ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hd₂ : ∀ s ∈ Ioo (T - ε) (T + ε + 1), HasDerivAt u₂ (w₂ s) s := by
    intro s hs
    have h := (hu (s - T) ⟨by linarith [hs.1], by linarith [hs.2]⟩).scomp s
      ((hasDerivAt_id s).sub_const T)
    simpa only [hu₂, hw₂, Function.comp_def, id_eq, one_smul] using h
  have hw₂' : ∀ s ∈ Ioo (T - ε) (T + ε + 1),
      HasDerivAt w₂ (chartGeodesicVectorField cov (γ T) (u₂ s, w₂ s)) s := by
    intro s hs
    have h := (hw (s - T) ⟨by linarith [hs.1], by linarith [hs.2]⟩).scomp s
      ((hasDerivAt_id s).sub_const T)
    simpa only [hu₂, hw₂, Function.comp_def, id_eq, one_smul] using h
  have hσgeo₂ : ∀ s ∈ Ioo (T - ε) (T + ε + 1),
      IsGeodesicAt cov (fun r : ℝ => (extChartAt I (γ T)).symm (u₂ r)) s :=
    fun s hs => isGeodesicAt_of_chartODE cov (γ T) (a := T - ε) (b := T + ε + 1)
      (by linarith) hs hstay₂ hd₂ hw₂'
  have hσsm₂ : ContMDiffOn 𝓘(ℝ) I ∞ (fun r : ℝ => (extChartAt I (γ T)).symm (u₂ r))
      (Ioo (T - ε) (T + ε + 1)) :=
    contMDiffOn_chartCurve_of_chartODE (cov := cov) (γ T) hstay₂ hd₂ hw₂'
  have h2d : ∀ t ∈ Ioo (T - δ) (T + δ),
      HasDerivAt (fun s : ℝ => (u₂ s, w₂ s))
        (w₂ t, chartGeodesicVectorField cov (γ T) (u₂ t, w₂ t)) t := fun t ht =>
    (hd₂ t ⟨by linarith [ht.1, hδleε], by linarith [ht.2, hδpos]⟩).prodMk
      (hw₂' t ⟨by linarith [ht.1, hδleε], by linarith [ht.2, hδpos]⟩)
  -- the field of the ODE is `C¹` at the junction
  have hFT : ContDiffAt ℝ 1 (chartGeodesicVectorField cov (γ T))
      (((extChartAt I (γ T)) (γ T), deriv (fun s : ℝ => (extChartAt I (γ T)) (γ s)) T)) := by
    have hopen : IsOpen ((extChartAt I (γ T)).target ×ˢ (univ : Set E)) :=
      (isOpen_extChartAt_target (γ T)).prod isOpen_univ
    have hz : ((extChartAt I (γ T)) (γ T), deriv (fun s : ℝ => (extChartAt I (γ T)) (γ s)) T)
        ∈ (extChartAt I (γ T)).target ×ˢ (univ : Set E) :=
      ⟨PartialEquiv.map_source (extChartAt I (γ T)) (mem_extChartAt_source (γ T)),
        Set.mem_univ _⟩
    exact ((Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contDiffOn_chartSpray
      (cov := cov) (γ T)).contDiffAt (hopen.mem_nhds hz)).of_le (by norm_num)
  -- the matching data at the junction
  have hderivT : deriv (fun s : ℝ => (extChartAt I (γ T)) (γ s)) T
      = (trivializationAt E (TangentSpace I) (γ T)).continuousLinearMapAt ℝ (γ T)
          (curveVelocity (I := I) γ T) := by
    have hmd : MDifferentiableAt 𝓘(ℝ) I γ T :=
      (hγsm.contMDiffAt (hV.mem_nhds hTV)).mdifferentiableAt (by simp)
    exact CurveField.deriv_extChartAt_comp_eq_continuousLinearMapAt_curveVelocity (I := I) hmd
      (mem_chart_source H (γ T))
  -- continuity of both sides on `[T - δ, T]`
  have hsubIcc : Icc (T - δ) T ⊆ V ∩ γ ⁻¹' (chartAt H (γ T)).source := fun t ht =>
    (hδ₀sub ⟨by linarith [ht.1, hδle₀, hδ₀], by linarith [ht.2, hδ₀]⟩).1
  have h1c : ContinuousOn
      (fun t : ℝ => ((extChartAt I (γ T)) (γ t), deriv (fun s : ℝ => (extChartAt I (γ T)) (γ s)) t))
      (Icc (T - δ) T) :=
    (hUcd.continuousOn.mono hsubIcc).prodMk
      ((hUcd.continuousOn_deriv_of_isOpen hW
        (WithTop.coe_le_coe.mpr le_top : ((1 : ℕ∞) : ℕ∞ω) ≤ ∞)).mono hsubIcc)
  have hmem₂ : ∀ t ∈ Icc (T - δ) T, t ∈ Ioo (T - ε) (T + ε + 1) := by
    intro t ht
    refine ⟨?_, ?_⟩
    · have h1 : T - ε < T - δ := by linarith
      linarith [ht.1]
    · linarith [ht.2, hε]
  have h2c : ContinuousOn (fun t : ℝ => (u₂ t, w₂ t)) (Icc (T - δ) T) := by
    have h1 : ContinuousOn u₂ (Icc (T - δ) T) := fun t ht =>
      ((hd₂ t (hmem₂ t ht)).continuousAt).continuousWithinAt
    have h2 : ContinuousOn w₂ (Icc (T - δ) T) := fun t ht =>
      ((hw₂' t (hmem₂ t ht)).continuousAt).continuousWithinAt
    exact h1.prodMk h2
  -- the one-sided uniqueness
  obtain ⟨a', ha'T, hEqU, hEqV⟩ :=
    Commons.Analysis.ODE.ODE_solution_unique_Icc_left_of_contDiffAt
      (F := chartGeodesicVectorField cov (γ T))
      (u₁ := fun t : ℝ => (extChartAt I (γ T)) (γ t))
      (v₁ := deriv fun t : ℝ => (extChartAt I (γ T)) (γ t))
      (u₂ := u₂) (v₂ := w₂) (a := T - δ) (b := T) (by linarith)
      hFT h1c h2c
      (fun t ht => ((hleft t ht).1.prodMk (hleft t ht).2).hasDerivWithinAt)
      (fun t ht => (h2d t ⟨ht.1, by linarith [ht.2, hδpos]⟩).hasDerivWithinAt)
      ⟨by simpa only [hu₂, sub_self] using hu0.symm,
        by simpa only [hw₂, sub_self] using hderivT.trans hw0.symm⟩
  -- the two curves agree on `[a'', T]`
  set a'' : ℝ := max a' (T - δ) with ha''
  have ha''T : a'' < T := max_lt ha'T (by linarith)
  have hsubIcc' : Icc a'' T ⊆ V ∩ γ ⁻¹' (chartAt H (γ T)).source := fun t ht =>
    (hδ₀sub ⟨by linarith [ht.1, le_max_right a' (T - δ), hδle₀, hδ₀],
      by linarith [ht.2, hδ₀]⟩).1
  have hagreeU : ∀ t ∈ Icc a'' T,
      (extChartAt I (γ T)) (γ t) = u (t - T) := fun t ht =>
    hEqU ⟨le_trans (le_max_left _ _) ht.1, ht.2⟩
  have hagree : ∀ t ∈ Icc a'' T, γ t = σ (t - T) := by
    intro t ht
    have hsrc1 : γ t ∈ (extChartAt I (γ T)).source := by
      rw [extChartAt_source]; exact (hsubIcc' ht).2
    have hst : t - T ∈ Ioo (-ε) (ε + 1) :=
      ⟨by linarith [ht.1, le_max_right a' (T - δ), hδleε, hδpos],
        by linarith [ht.2, hε]⟩
    have hsrc2 : σ (t - T) ∈ (extChartAt I (γ T)).source := by
      show (extChartAt I (γ T)).symm (u (t - T)) ∈ (extChartAt I (γ T)).source
      exact PartialEquiv.target_subset_preimage_source (extChartAt I (γ T)) (hstay (t - T) hst)
    have h2 : (extChartAt I (γ T)) (σ (t - T)) = u (t - T) := by
      show (extChartAt I (γ T)) ((extChartAt I (γ T)).symm (u (t - T))) = u (t - T)
      exact PartialEquiv.right_inv (extChartAt I (γ T)) (hstay (t - T) hst)
    exact PartialEquiv.injOn (extChartAt I (γ T)) hsrc1 hsrc2 ((hagreeU t ht).trans h2.symm)
  -- the glued curve equals the shifted chart solution near the junction
  have hglue_eq : ∀ t ∈ Ioo a'' (T + ε), glue γ σ T t = σ (t - T) := by
    intro t ht
    by_cases hle : t ≤ T
    · rw [glue_of_le hle]
      exact hagree t ⟨le_of_lt ht.1, hle⟩
    · rw [glue_of_lt (not_le.mp hle)]
  -- the smoothness set
  refine ⟨(V ∩ Iio T) ∪ Ioo a'' (T + ε), (hV.inter isOpen_Iio).union isOpen_Ioo, ?_, ?_, ?_⟩
  · intro t ht
    by_cases hlt : t < T
    · exact Or.inl ⟨hsub ⟨ht.1, hlt.le⟩, hlt⟩
    · have hTt : T ≤ t := not_lt.mp hlt
      exact Or.inr ⟨by linarith [hTt, ha''T], by linarith [ht.2, hε]⟩
  · -- smoothness
    apply contMDiffOn_of_locally_contMDiffOn
    intro t ht
    rcases ht with ht | ht
    · refine ⟨V ∩ Iio T, hV.inter isOpen_Iio, ht, ?_⟩
      have hsub : (V ∩ Iio T ∪ Ioo a'' (T + ε)) ∩ (V ∩ Iio T) ⊆ V := fun u hu => hu.2.1
      refine (hγsm.mono hsub).congr fun u hu => ?_
      exact glue_of_le hu.2.2.le
    · refine ⟨Ioo a'' (T + ε), isOpen_Ioo, ht, ?_⟩
      have hsub : (V ∩ Iio T ∪ Ioo a'' (T + ε)) ∩ Ioo a'' (T + ε) ⊆ Ioo a'' (T + ε) :=
        fun u hu => hu.2
      have h1 : ContMDiffOn 𝓘(ℝ) I ∞ (fun r : ℝ => (extChartAt I (γ T)).symm (u₂ r))
          (Ioo a'' (T + ε)) :=
        hσsm₂.mono fun u hu =>
          ⟨by linarith [hu.1, le_max_right a' (T - δ), hδleε, hε], by linarith [hu.2, hε]⟩
      refine (h1.mono hsub).congr fun u hu => ?_
      exact (hglue_eq u hu.2).trans (by simp only [hσ, hu₂])
  · -- the geodesic equation
    intro t ht
    rcases lt_or_ge t T with hlt | hge
    · have hev : glue γ σ T =ᶠ[𝓝 t] γ := by
        filter_upwards [isOpen_Iio.mem_nhds hlt] with r hr
        exact glue_of_le hr.le
      exact (Submission.GeodesicExtend.isGeodesicAt_congr_of_eventuallyEq (I := I) hev).mpr
        (hγgeo t ⟨ht.1, hlt.le⟩)
    · rcases eq_or_lt_of_le hge with hT | hT
      · -- at the junction
        subst hT
        have hev : glue γ σ T =ᶠ[𝓝 T] fun r => σ (r - T) :=
          Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds ⟨by linarith [ha''T], by linarith [hε]⟩)
            (fun r hr => hglue_eq r hr)
        exact (Submission.GeodesicExtend.isGeodesicAt_congr_of_eventuallyEq (I := I) hev).mpr
          (hσgeo₂ T ⟨by linarith [ha''T], by linarith [hε]⟩)
      · -- beyond the junction
        have hev : glue γ σ T =ᶠ[𝓝 t] fun r => σ (r - T) :=
          Filter.eventuallyEq_of_mem
            (isOpen_Ioo.mem_nhds ⟨by linarith [hT], by linarith [ht.2, hε]⟩)
            (fun r hr => hglue_eq r hr)
        exact (Submission.GeodesicExtend.isGeodesicAt_congr_of_eventuallyEq (I := I) hev).mpr
          (hσgeo₂ t ⟨by linarith [hT, hε], by linarith [ht.2, hε]⟩)

end Glue

end

end Submission.GeodesicGlobal

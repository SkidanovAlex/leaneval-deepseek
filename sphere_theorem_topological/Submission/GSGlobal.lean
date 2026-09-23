import Submission.GSField
import Submission.GSStep1
import Submission.Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contDiffOn_chartSpray

/-!
# Gluing ascent directions: the global gradient-like field of `d(p,·)`

This continues Grove–Shiohama's step 3 (notes Prop. 5.2.18).  `Submission/GSField.lean` proves the
*local* persistence of the ascent property: for `x ≠ p` and an ascent direction `vv` at `x`, the
chart-parallel section `y ↦ frameVector x y vv` is an ascent direction on a whole neighbourhood
of `x`.

Here we do the two gluing steps:

* `isAscentAt_finsum` — a finite convex combination `∑ᵢ φᵢ • Vᵢ` of ascent directions with
  `φᵢ ≥ 0` and `∑ᵢ φᵢ > 0` is again an ascent direction.  (The pointwise algebra, in the form
  needed for a partition of unity: only the `i` with `φᵢ ≠ 0` carry a hypothesis.)
* `exists_open_ascent_field` — the local persistence theorem re-packaged as the existence of an
  *open* neighbourhood on which a single chart-parallel section is an ascent direction.

The remaining bookkeeping (a partition of unity on `M \ {p,q}`, the flow of the resulting
normalised field, the level-set homeomorphism and the two-disk assembly) is described in
`Submission/Roadmap.lean` §48.3.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal InnerProductSpace
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.ChartConnection
open Submission.GlobalExp
open Submission.GSCritical
open Submission.GSField
open Submission.Distance
open Submission.Gauss

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.GSGlobal

noncomputable section

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- **Gluing ascent directions at a point.**  If `V i` is an ascent direction at `x` for every `i`
with `φ i ≠ 0`, `φ i ≥ 0` and `∑ i, φ i > 0`, then `∑ i, φ i • V i` is again an ascent direction.
This is the pointwise core of the partition-of-unity construction of the gradient-like field. -/
theorem isAscentAt_finsum {hmet : IsMetricCompatible cov} {p x : M} {ι : Type*} [Fintype ι]
    {V : ι → TangentSpace I x} {φ : ι → ℝ}
    (hV : ∀ i, φ i ≠ 0 → IsAscentAt hmet p x (V i))
    (hφ : ∀ i, 0 ≤ φ i) (hpos : 0 < ∑ i, φ i) :
    IsAscentAt hmet p x (∑ i, φ i • V i) := by
  classical
  have hsub : (∑ i ∈ Finset.univ.filter (fun i => φ i ≠ 0), φ i • V i) = ∑ i, φ i • V i :=
    Finset.sum_filter_of_ne (fun a _ ha => fun h0 => ha (by rw [h0, zero_smul]))
  have hpos' : 0 < ∑ i ∈ Finset.univ.filter (fun i => φ i ≠ 0), φ i := by
    rw [Finset.sum_filter_of_ne (f := fun i => φ i) (p := fun i => φ i ≠ 0) (fun a _ ha => ha)]
    exact hpos
  rw [← hsub]
  exact isAscentAt_sum _ (fun i hi => hV i (Finset.mem_filter.mp hi).2)
    (fun i _ => hφ i) hpos'

/-- **Local ascent fields on an open neighbourhood.**  The local persistence theorem
(`Submission.GSField.eventually_isAscentAt_frameVector`) upgraded to the existence of an *open*
neighbourhood on which the chart-parallel section is an ascent direction. -/
theorem exists_open_ascent_field (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M] {p x : M} (hx : x ≠ p) {vv : E}
    (hv : IsAscentAt (cov := cov) hmet p x (frameVector (I := I) x x vv)) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ U, IsAscentAt (cov := cov) hmet p y (frameVector (I := I) x y vv) := by
  have h := eventually_isAscentAt_frameVector (cov := cov) hmet htor hx hv
  obtain ⟨U, hUsub, hUopen, hxU⟩ := mem_nhds_iff.mp h
  exact ⟨U, hUopen, hxU, fun y hy => hUsub hy⟩

/-- **Every point of `M \ {p,q}` carries an open neighbourhood with an ascent field**, in the
restricted Grove–Shiohama range (`diam ≤ 2π/3`). -/
theorem exists_open_ascent_field_of_diam (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (hpinch : QuarterPinched cov) [PathConnectedSpace M] [RegularSpace M]
    {p q x : M} {D : ℝ}
    (hdiam : ∀ r s : M, Manifold.riemannianEDist I r s ≤ ENNReal.ofReal D)
    (hDgt : Real.pi / 2 < D) (hDlt : D < Real.pi)
    (hpq : Manifold.riemannianEDist I p q = ENNReal.ofReal D)
    (hxp : x ≠ p) (hxq : x ≠ q) :
    ∃ (U : Set M) (V : (y : M) → TangentSpace I y), IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ U, IsAscentAt (cov := cov) hmet p y (V y) := by
  obtain ⟨v, hv1, hv⟩ := exists_isAscentAt_off_pq (cov := cov) hmet htor hpinch hdiam hDgt hDlt
    hpq hxp hxq
  have hxsrc : x ∈ (extChartAt I x).source := by
    rw [extChartAt_source]; exact mem_chart_source H x
  let vv : E := (trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ x v
  have hfv : IsAscentAt (cov := cov) hmet p x (frameVector (I := I) x x vv) := by
    rw [Submission.GExpFlow.frameVector_clm (I := I) hxsrc v]
    exact hv
  obtain ⟨U, hUopen, hxU, hUascent⟩ :=
    exists_open_ascent_field (cov := cov) hmet htor hxp hfv
  exact ⟨U, fun y => frameVector (I := I) x y vv, hUopen, hxU, hUascent⟩

/-- **The pointwise gluing of local ascent fields.**  If every point of a set `s` has an open
neighbourhood carrying a field which is an ascent direction at every point of that neighbourhood,
then there is a single field on `s` which is an ascent direction everywhere on `s`.

This is the *pointwise* form of the partition-of-unity gluing of Grove–Shiohama's step 3 (notes
Prop. 5.2.18); the partition of unity is what additionally makes the resulting field *continuous*
(which is what the flow argument needs), while `isAscentAt_finsum` is what makes the convex
combination an ascent direction. -/
theorem exists_ascent_field_of_local (hmet : IsMetricCompatible cov) {p : M} {s : Set M}
    (hloc : ∀ x ∈ s, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      ∃ W : (y : M) → TangentSpace I y, ∀ y ∈ U, IsAscentAt (cov := cov) hmet p y (W y)) :
    ∃ V : (y : M) → TangentSpace I y, ∀ x ∈ s, IsAscentAt (cov := cov) hmet p x (V x) := by
  classical
  have h : ∀ x : M, ∃ W : (y : M) → TangentSpace I y,
      x ∈ s → IsAscentAt (cov := cov) hmet p x (W x) := by
    intro x
    by_cases hx : x ∈ s
    · obtain ⟨U, -, hxU, W, hW⟩ := hloc x hx
      exact ⟨W, fun _ => hW x hxU⟩
    · exact ⟨fun _ => 0, fun h => absurd h hx⟩
  let W : ∀ x : M, (y : M) → TangentSpace I y := fun x => (h x).choose
  have hW : ∀ x ∈ s, IsAscentAt (cov := cov) hmet p x (W x x) := fun x hx => (h x).choose_spec hx
  exact ⟨fun y => W y y, hW⟩

/-- **Gluing with a *finite* partition of unity.**  Given a finite family of local ascent fields
`V i : U i → TM` and a finite partition of unity `φ` subordinate to `U`, the convex combination
`∑ i, φ i y • V i y` is again an ascent direction at every point `y`.

This is the exact form of Grove–Shiohama's step 3 gluing that the flow argument consumes: a finite
partition of unity is produced by `Topology.exists_continuous_sum_one_of_isOpen_isCompact` (or by
`PartitionOfUnity.exists_isSubordinate`), and the remaining work is only the *continuity* of the
resulting section (which needs the continuity of `y ↦ frameVector z₀ y v` in the bundle
topology). -/
theorem isAscentAt_finsum_of_partition {hmet : IsMetricCompatible cov} {p y : M} {ι : Type*}
    [Fintype ι] {U : ι → Set M} {V : ι → (z : M) → TangentSpace I z} {φ : ι → M → ℝ}
    (hV : ∀ i z, z ∈ U i → IsAscentAt (cov := cov) hmet p z (V i z))
    (hφ : ∀ i z, 0 ≤ φ i z) (hsup : ∀ i, Function.support (φ i) ⊆ U i)
    (hsum : ∑ i, φ i y = 1) :
    IsAscentAt (cov := cov) hmet p y (∑ i, φ i y • V i y) := by
  refine isAscentAt_finsum (x := y) (V := fun i => V i y) (φ := fun i => φ i y) ?_ ?_ ?_
  · intro i hi
    exact hV i y (hsup i (Function.mem_support.mpr hi))
  · intro i; exact hφ i y
  · rw [hsum]; norm_num

/-- **The ascent condition without the parameter quantifier.**  For `x ≠ p` the ascent condition is
equivalent to: every *unit* shortest direction `u` from `x` to `p`, i.e. every unit `u` with
`p = GExp x (d(x,p) · u)`, makes an obtuse angle with `v`.

This removes the `∃ r` from the definition (`IsAscentAt`), which is what the flow argument and the
openness of the ascent condition need. -/
theorem isAscentAt_iff (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M] {p x : M} (hx : x ≠ p) {v : TangentSpace I x} :
    IsAscentAt (cov := cov) hmet p x v ↔
      ∀ u : TangentSpace I x, ‖u‖ = 1 →
        p = GExp (cov := cov) hmet x ((Manifold.riemannianEDist I x p).toReal • u) →
        inner ℝ v u < 0 := by
  haveI hcb : IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x) :=
    Submission.EDist.isContinuousRiemannianBundle_infty (I := I)
  have hfin : Manifold.riemannianEDist I x p ≠ ⊤ :=
    (Submission.HopfRinow.riemannianEDist_lt_top (cov := cov) hmet htor x p).ne
  have hne : Manifold.riemannianEDist I x p ≠ 0 := fun h =>
    hx ((Submission.EDist.riemannianEDist_eq_zero_iff (I := I)).mp h)
  have hpos : 0 < (Manifold.riemannianEDist I x p).toReal := ENNReal.toReal_pos hne hfin
  have hof : Manifold.riemannianEDist I x p
      = ENNReal.ofReal ((Manifold.riemannianEDist I x p).toReal) :=
    (ENNReal.ofReal_toReal hfin).symm
  constructor
  · intro hv u hu hGu
    exact hv _ u hpos.le hu hGu hof
  · intro hv r u hr hu hpG hd
    have hr0 : r = (Manifold.riemannianEDist I x p).toReal := by
      rw [← ENNReal.toReal_ofReal hr, ← hd, hof, ENNReal.toReal_ofReal hpos.le]
    subst hr0
    exact hv u hu hpG

/-- **The chart-parallel section of the tangent bundle is smooth.**  For a fixed chart coordinate
vector `v`, `y ↦ frameVector z₀ y v` is `C^∞` on the chart piece at `z₀` — this is
`Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiffOn_trivializationAt_symmL_section`, restated for the
project's `frameVector`. -/
theorem contMDiffOn_frameVector (z₀ : M) (v : E) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => (⟨y, frameVector (I := I) z₀ y v⟩ : TangentBundle I M))
      ((chartAt H z₀).source) :=
  Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiffOn_trivializationAt_symmL_section (I := I) z₀ v

/-- The chart-parallel section of the tangent bundle is continuous on the chart piece at `z₀`. -/
theorem continuousOn_frameVector (z₀ : M) (v : E) :
    ContinuousOn (fun y : M => (⟨y, frameVector (I := I) z₀ y v⟩ : TangentBundle I M))
      ((chartAt H z₀).source) :=
  (contMDiffOn_frameVector z₀ v).continuousOn

end

end Submission.GSGlobal

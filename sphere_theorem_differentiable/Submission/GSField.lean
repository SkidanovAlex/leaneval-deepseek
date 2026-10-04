import Submission.GSNoCrit
import Submission.GSStep1
import Submission.GExpFlow
import Submission.CornerCut
import Submission.HingeKey
import Submission.HopfRinow2
import Submission.GeodesicExtend
import Submission.GExpRay
import Submission.ExpBound2
import Submission.GSDisk

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The gradient-like field of `d(p,·)`: ascent directions

This file starts Grove–Shiohama's step 3 (the flow argument, notes Prop. 5.2.18).  For
`f = d(p,·)` a tangent vector `v` at `x` is an **ascent direction** if every shortest direction
from `x` to `p` makes an obtuse angle with `v`; by the first variation formula this means that `f`
increases at the positive rate `-min_u ⟪v,u⟫` in the direction `v` (Theorem: the right derivative
of `t ↦ d(p, GExp x (t v))` at `0` is `max_u (-⟪v,u⟫) = -min_u ⟪v,u⟫`).

Contents:

* `IsAscentAt` — the predicate, with its algebra: it is invariant under positive scaling and
  stable under convex combinations with positive total weight.  The latter is exactly what makes
  the *partition-of-unity gluing* of local gradient-like fields work: if `V_i` is ascent on `U_i`
  and `Σ φ_i = 1` with `φ_i ≥ 0`, then `Σ φ_i V_i` is ascent wherever it is defined.
* `exists_isAscentAt_of_not_isCrit` / `exists_isAscentAt_off_pq` — the bridge from the critical
  point theory (`GSNoCrit.exists_unit_away_of_ne`).
* `chartFlowExp_continuousAt_joint` — joint continuity of the chart-flow exponential map
  `(q, u) ↦ chartFlowExp D q u` (the chart-independent `GExp` written in a fixed chart), which is
  the analytic engine of the local persistence argument.
* `frameVector_section_continuousAt` — continuity of the chart-parallel section
  `y ↦ frameVector x₀ y vv`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 2000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal InnerProductSpace
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.ChartConnection
open Submission.GlobalExp
open Submission.GExpFlow
open Submission.HopfRinow
open Submission.HingeKey
open Submission.GSCritical
open Submission.CornerCut
open Submission.GeodesicExtend
open Submission.GExpRay
open Submission.ExpBound2
open Submission.ChartBounds
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

namespace Submission.GSField

noncomputable section

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-! ## The ascent predicate -/

/-- **`v` is an ascent direction for `d(p,·)` at `x`.**  Every shortest direction from `x` to `p`
makes an obtuse angle with `v`.  By the first variation formula this says that the right derivative
of `t ↦ d(p, GExp x (t v))` at `0` is `-min_{u} ⟪v,u⟫ > 0` (the minimum over the shortest
directions `u`). -/
def IsAscentAt (hmet : IsMetricCompatible cov) (p x : M) (v : TangentSpace I x) : Prop :=
  ∀ (r : ℝ) (u : TangentSpace I x), 0 ≤ r → ‖u‖ = 1 →
    p = GExp (cov := cov) hmet x (r • u) →
    Manifold.riemannianEDist I x p = ENNReal.ofReal r → inner ℝ v u < 0

/-- The ascent condition is invariant under positive scaling of the direction. -/
theorem isAscentAt_smul {hmet : IsMetricCompatible cov} {p x : M} {v : TangentSpace I x}
    (hv : IsAscentAt hmet p x v) {c : ℝ} (hc : 0 < c) :
    IsAscentAt hmet p x (c • v) := by
  intro r u hr hu hp hd
  have h := hv r u hr hu hp hd
  rw [real_inner_smul_left]
  exact mul_neg_of_pos_of_neg hc h

/-- The ascent directions at a point form a cone: a convex combination with positive total weight
of two ascent directions is an ascent direction.  (This is what makes the partition-of-unity
gluing of local gradient-like fields work.) -/
theorem isAscentAt_add {hmet : IsMetricCompatible cov} {p x : M}
    {v w : TangentSpace I x} (hv : IsAscentAt hmet p x v) (hw : IsAscentAt hmet p x w)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a + b) :
    IsAscentAt hmet p x (a • v + b • w) := by
  intro r u hr hu hp hd
  have h1 := hv r u hr hu hp hd
  have h2 := hw r u hr hu hp hd
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
  rcases eq_or_lt_of_le ha with h | h
  · rw [← h]
    simpa using mul_neg_of_pos_of_neg (by linarith : (0:ℝ) < b) h2
  · exact add_neg_of_neg_of_nonpos (mul_neg_of_pos_of_neg h h1) (mul_nonpos_of_nonneg_of_nonpos hb h2.le)

/-- A finite convex combination (with positive total weight) of ascent directions is an ascent
direction. -/
theorem isAscentAt_sum {hmet : IsMetricCompatible cov} {p x : M} {ι : Type*} (s : Finset ι)
    {V : ι → TangentSpace I x} {φ : ι → ℝ} (hV : ∀ i ∈ s, IsAscentAt hmet p x (V i))
    (hφ : ∀ i ∈ s, 0 ≤ φ i) (hpos : 0 < ∑ i ∈ s, φ i) :
    IsAscentAt hmet p x (∑ i ∈ s, φ i • V i) := by
  intro r u hr hu hp hd
  have hterm : ∀ i ∈ s, φ i * inner ℝ (V i) u ≤ 0 := fun i hi =>
    mul_nonpos_of_nonneg_of_nonpos (hφ i hi) (hV i hi r u hr hu hp hd).le
  have hwit : ∃ i ∈ s, 0 < φ i := by
    have h0 : (∑ _i ∈ s, (0:ℝ)) < ∑ i ∈ s, φ i := by simpa using hpos
    exact Finset.exists_lt_of_sum_lt h0
  have hex : ∃ i ∈ s, φ i * inner ℝ (V i) u < 0 := by
    obtain ⟨i, hi, hi'⟩ := hwit
    exact ⟨i, hi, mul_neg_of_pos_of_neg hi' (hV i hi r u hr hu hp hd)⟩
  have hsum : ∑ i ∈ s, φ i * inner ℝ (V i) u < 0 := by
    have h := Finset.sum_lt_sum hterm (by simpa using hex)
    simpa using h
  rw [sum_inner]
  simpa only [real_inner_smul_left] using hsum

/-- `¬ IsCrit` is exactly the existence of a unit ascent direction. -/
theorem exists_isAscentAt_of_not_isCrit {hmet : IsMetricCompatible cov} {p x : M}
    (h : ¬ Submission.GSCritical.IsCrit hmet p x) :
    ∃ v : TangentSpace I x, ‖v‖ = 1 ∧ IsAscentAt hmet p x v :=
  Submission.GSNoCrit.exists_unit_away (cov := cov) hmet h

/-- **Every point of `M \ {p,q}` admits an ascent direction** in the restricted Grove–Shiohama
range (`diam ≤ 2π/3`). -/
theorem exists_isAscentAt_off_pq (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (hpinch : QuarterPinched cov) [PathConnectedSpace M] [RegularSpace M]
    {p q x : M} {D : ℝ}
    (hdiam : ∀ r s : M, Manifold.riemannianEDist I r s ≤ ENNReal.ofReal D)
    (hDgt : Real.pi / 2 < D) (hDlt : D < Real.pi)
    (hpq : Manifold.riemannianEDist I p q = ENNReal.ofReal D)
    (hxp : x ≠ p) (hxq : x ≠ q) :
    ∃ v : TangentSpace I x, ‖v‖ = 1 ∧ IsAscentAt hmet p x v :=
  exists_isAscentAt_of_not_isCrit (cov := cov)
    (Submission.GSNoCrit.not_isCrit_of_ne (cov := cov) hmet htor hpinch hdiam hDgt hDlt hpq hxp hxq)

/-! ## Joint continuity of the chart-flow exponential map -/

/-- The phase map `p ↦ ((chart p.1, flowScale D • p.2), (flowScale D)⁻¹)` is continuous. -/
lemma chartFlowExp_phase_continuousAt {z₀ : M} {Z : Set M}
    (D : ChartFlowData (cov := cov) (I := I) z₀ Z) {q : M}
    (hqsrc : q ∈ (extChartAt I z₀).source) (u : E) :
    ContinuousAt (fun p : M × E =>
      (((extChartAt I z₀) p.1, flowScale D • p.2), (flowScale D)⁻¹)) (q, u) := by
  have hfst : ContinuousAt (fun p : M × E => (extChartAt I z₀) p.1) (q, u) :=
    (continuousAt_extChartAt' (I := I) (x := z₀) hqsrc).comp continuousAt_fst
  refine ContinuousAt.prodMk ?_ continuousAt_const
  exact ContinuousAt.prodMk hfst (continuousAt_const.smul continuousAt_snd :
    ContinuousAt (fun p : M × E => flowScale D • p.2) (q, u))

/-- **Joint continuity of the chart-flow exponential map** `(q, u) ↦ chartFlowExp D q u` at a
point whose phase `((extChartAt I z₀) q, flowScale D • u)` lies in `chartData z₀ Z` (where the
uniform flow has joint smooth dependence on the initial data and the time). -/
lemma chartFlowExp_continuousAt_joint {z₀ : M} {Z : Set M}
    (D : ChartFlowData (cov := cov) (I := I) z₀ Z) {q : M}
    (hqsrc : q ∈ (extChartAt I z₀).source) {u : E}
    (hK : ((extChartAt I z₀) q, flowScale D • u) ∈ chartData (I := I) z₀ Z) :
    ContinuousAt (fun p : M × E => chartFlowExp (cov := cov) D p.1 p.2) (q, u) := by
  have ht : |(flowScale D)⁻¹| < D.ρ := by
    rw [inv_flowScale D, abs_of_pos (div_pos D.hρ two_pos)]
    linarith [D.hρ]
  have hO : ((extChartAt I z₀) q, flowScale D • u) ∈ D.O := D.hKO hK
  have hphase := chartFlowExp_phase_continuousAt (cov := cov) D hqsrc u
  have hα : ContinuousAt (fun z : (E × E) × ℝ => D.α z.1 z.2)
      (((extChartAt I z₀) q, flowScale D • u), (flowScale D)⁻¹) :=
    (D.hjoint ((extChartAt I z₀) q, flowScale D • u) hK (flowScale D)⁻¹ ht).continuousAt
  have hα0 : ContinuousAt (fun p : M × E =>
      D.α ((extChartAt I z₀) p.1, flowScale D • p.2) (flowScale D)⁻¹) (q, u) :=
    ContinuousAt.comp (x := (q, u))
      (f := fun p : M × E => (((extChartAt I z₀) p.1, flowScale D • p.2), (flowScale D)⁻¹))
      hα hphase
  have hα1 : ContinuousAt (fun p : M × E =>
      (D.α ((extChartAt I z₀) p.1, flowScale D • p.2) (flowScale D)⁻¹).1) (q, u) := hα0.fst
  have hmem : (D.α ((extChartAt I z₀) q, flowScale D • u) (flowScale D)⁻¹).1
      ∈ (extChartAt I z₀).target :=
    D.htgt _ hO (flowScale D)⁻¹ (le_of_lt ht)
  have hsymm : ContinuousAt (extChartAt I z₀).symm
      ((D.α ((extChartAt I z₀) q, flowScale D • u) (flowScale D)⁻¹).1) :=
    ((contMDiffOn_extChartAt_symm (I := I) (n := ∞) z₀).continuousOn).continuousAt
      ((isOpen_extChartAt_target z₀).mem_nhds hmem)
  have hres : ContinuousAt ((extChartAt I z₀).symm ∘ (fun p : M × E =>
      (D.α ((extChartAt I z₀) p.1, flowScale D • p.2) (flowScale D)⁻¹).1)) (q, u) :=
    ContinuousAt.comp (x := (q, u))
      (f := fun p : M × E => (D.α ((extChartAt I z₀) p.1, flowScale D • p.2) (flowScale D)⁻¹).1)
      hsymm hα1
  have hfun : (fun p : M × E => chartFlowExp (cov := cov) D p.1 p.2)
      = (extChartAt I z₀).symm ∘ (fun p : M × E =>
          (D.α ((extChartAt I z₀) p.1, flowScale D • p.2) (flowScale D)⁻¹).1) := by
    funext p
    rw [chartFlowExp_apply]
    rfl
  rw [hfun]
  exact hres

/-- **`GExp` in the chart form is continuous in the base point.**  This is `GExp_eq_chartFlow`
combined with the joint continuity of the chart flow: for `q` (a point whose phase lies in the flow
domain) and small non-zero coordinates `u`, the map `(y, w) ↦ GExp y (frameVector z₀ y w)` is
continuous at `(q, u)`. -/
lemma GExp_frameVector_continuousAt {z₀ : M} {Z : Set M}
    (D : ChartFlowData (cov := cov) (I := I) z₀ Z) (hmet : IsMetricCompatible cov) {q : M}
    (hqsrc : q ∈ (extChartAt I z₀).source) {u : E} (hu : u ≠ 0)
    (hK : ((extChartAt I z₀) q, flowScale D • u) ∈ chartData (I := I) z₀ Z) :
    ContinuousAt (fun p : M × E => GExp (cov := cov) hmet p.1 (frameVector (I := I) z₀ p.1 p.2))
      (q, u) := by
  have hO : ((extChartAt I z₀) q, flowScale D • u) ∈ D.O := D.hKO hK
  have h1 : ContinuousAt (fun p : M × E => chartFlowExp (cov := cov) D p.1 p.2) (q, u) :=
    chartFlowExp_continuousAt_joint (cov := cov) D hqsrc hK
  have hphase := chartFlowExp_phase_continuousAt (cov := cov) D hqsrc u
  have hev : (fun p : M × E => GExp (cov := cov) hmet p.1 (frameVector (I := I) z₀ p.1 p.2))
      =ᶠ[𝓝 (q, u)] fun p : M × E => chartFlowExp (cov := cov) D p.1 p.2 := by
    have hAo : {z : (E × E) × ℝ | z.1 ∈ D.O}
        ∈ 𝓝 (((extChartAt I z₀) q, flowScale D • u), (flowScale D)⁻¹) :=
      (D.hO.preimage continuous_fst).mem_nhds hO
    have hA : {p : M × E | ((extChartAt I z₀) p.1, flowScale D • p.2) ∈ D.O} ∈ 𝓝 (q, u) :=
      hphase.preimage_mem_nhds hAo
    have hB : {p : M × E | p.2 ≠ 0} ∈ 𝓝 (q, u) :=
      (isOpen_ne.preimage continuous_snd).mem_nhds hu
    have hC : {p : M × E | p.1 ∈ (extChartAt I z₀).source} ∈ 𝓝 (q, u) :=
      ((isOpen_extChartAt_source (I := I) z₀).preimage continuous_fst).mem_nhds hqsrc
    filter_upwards [hA, hB, hC] with p hp1 hp2 hp3
    exact GExp_eq_chartFlow (cov := cov) hmet D hp3 p.2 hp1 hp2
  exact h1.congr_of_eventuallyEq hev

/-! ## The "no-corner" step: limits of shortest directions are shortest directions -/

/-- **No corner at the junction.**  Suppose the broken path `x₀ → z → p` with
`z = GExp x₀ (t • w)` is minimising, i.e. `d(x₀,z) = t`, `d(z,p) = r - t` and `d(x₀,p) = r` with
`0 < t < r` and `‖w‖ = 1`.  Then the geodesic ray from `x₀` in the direction `w` already reaches
`p` at time `r`: `p = GExp x₀ (r • w)`.

This is `CornerCut.corner_cut` applied at the junction `z`: if the incoming direction (of the ray
from `x₀`) and the outgoing direction (of a minimising geodesic from `z` to `p`) were different,
cutting the corner would produce a path from `x₀` to `p` of length `< r`. -/
theorem eq_GExp_of_minimising_broken
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M]
    {x₀ p : M} {r t : ℝ} {w : TangentSpace I x₀}
    (hw : ‖w‖ = 1) (h0r : 0 ≤ r) (ht0 : 0 < t) (htr : t < r)
    (hz : Manifold.riemannianEDist I x₀ (GExp (cov := cov) hmet x₀ (t • w)) = ENNReal.ofReal t)
    (hzp : Manifold.riemannianEDist I (GExp (cov := cov) hmet x₀ (t • w)) p
      = ENNReal.ofReal (r - t))
    (hr : Manifold.riemannianEDist I x₀ p = ENNReal.ofReal r) :
    p = GExp (cov := cov) hmet x₀ (r • w) := by
  classical
  haveI hcb : IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x) :=
    Submission.EDist.isContinuousRiemannianBundle_infty (I := I)
  have hδ := geodDelta_pos (cov := cov) hmet
  have hrtt : 0 ≤ r - t := by linarith
  -- the minimising arc `[0,t]` of the ray from `x₀` in the direction `w`
  set G₀ : ℝ → M := geodCurve (cov := cov) hmet t ht0.le x₀ w hw with hG₀def
  have hG₀t : G₀ t = GExp (cov := cov) hmet x₀ (t • w) := by
    rw [hG₀def]
    exact (GExp_eq_geodCurve (cov := cov) hmet hw ht0.le (r := t) ht0.le le_rfl).symm
  have hG₀0 : G₀ 0 = x₀ := (geodCurve_spec (cov := cov) hmet t ht0.le x₀ w hw).1
  have hG₀min : Manifold.riemannianEDist I x₀ (G₀ t) = ENNReal.ofReal t := by
    rw [hG₀t]; exact hz
  have hsub₀ := geodCurve_sub_arc_minimising' (cov := cov) hmet ht0.le hw (s := t) ht0.le
    le_rfl hG₀min
  have hG₀dist : Manifold.riemannianEDist I (G₀ t) p = ENNReal.ofReal (r - t) := by
    rw [hG₀t]; exact hzp
  have hξ1 : ‖curveVelocity (I := I) G₀ t‖ = 1 :=
    norm_curveVelocity_geodCurve (cov := cov) hmet ht0.le x₀ w hw ht0.le le_rfl
  -- the outgoing unit direction at `z = G₀ t`
  obtain ⟨η, hη1, hpη⟩ := Submission.GSCritical.exists_unit_of_dist (cov := cov) hmet htor
    (x := G₀ t) (p := p) (t := r - t) hG₀dist (by linarith)
  set G₂ : ℝ → M := geodCurve (cov := cov) hmet (r - t) hrtt (G₀ t) η hη1 with hG₂def
  have hG₂r : G₂ (r - t) = p := by
    rw [hG₂def]
    rw [← GExp_eq_geodCurve (cov := cov) hmet hη1 hrtt (r := r - t) hrtt le_rfl]
    exact hpη.symm
  have hG₂min : Manifold.riemannianEDist I (G₀ t) (G₂ (r - t)) = ENNReal.ofReal (r - t) := by
    rw [hG₂r]; exact hG₀dist
  have hsub₂ := geodCurve_sub_arc_minimising' (cov := cov) hmet hrtt hη1 (s := r - t) hrtt
    le_rfl hG₂min
  have hG₂g : ∀ s ∈ Set.Icc (0:ℝ) (r - t), G₂ s = GExp (cov := cov) hmet (G₀ t) (s • η) := by
    intro s hs
    rw [hG₂def]
    exact (GExp_eq_geodCurve (cov := cov) hmet hη1 hrtt hs.1 hs.2).symm
  -- the two directions at `z` agree
  have hξη : curveVelocity (I := I) G₀ t = η := by
    by_contra hne
    obtain ⟨δ, hδpos, hδcut⟩ := corner_cut (cov := cov) hmet (G₀ t) hξ1 hη1 hne
    obtain ⟨τ, hτ0, hτδ, hτt, hτrt⟩ : ∃ τ : ℝ, 0 < τ ∧ τ < δ ∧ τ ≤ t ∧ τ ≤ r - t :=
      ⟨min (min δ (min t (r - t))) 1 / 2, by positivity,
        by linarith [min_le_left (min δ (min t (r - t))) 1, min_le_left δ (min t (r - t))],
        by linarith [min_le_left (min δ (min t (r - t))) 1, min_le_right δ (min t (r - t)),
          min_le_left t (r - t)],
        by linarith [min_le_left (min δ (min t (r - t))) 1, min_le_right δ (min t (r - t)),
          min_le_right t (r - t)]⟩
    have hback : GExp (cov := cov) hmet (G₀ t)
        ((-τ) • curveVelocity (I := I) G₀ t) = G₀ (t - τ) := by
      have h := GExp_neg_curveVelocity_geodCurve (cov := cov) hmet hw ht0.le ht0.le le_rfl
        hτ0.le hτt
      simpa only [smul_neg, neg_smul] using h
    have hfwd : GExp (cov := cov) hmet (G₀ t) (τ • η) = G₂ τ :=
      (hG₂g τ ⟨hτ0.le, hτrt⟩).symm
    have hcut := hδcut τ hτ0 hτδ
    rw [hback, hfwd] at hcut
    have ha : Manifold.riemannianEDist I x₀ (G₀ (t - τ))
        = ENNReal.ofReal (t - τ) := by
      have h := hsub₀ 0 ⟨le_refl 0, ht0.le⟩ (t - τ) ⟨by linarith, by linarith⟩ (by linarith)
      have h0 : (geodCurve (cov := cov) hmet t ht0.le x₀ w hw) 0 = x₀ :=
        (geodCurve_spec (cov := cov) hmet t ht0.le x₀ w hw).1
      rw [h0] at h
      simpa using h
    have hb : Manifold.riemannianEDist I (G₂ τ) p = ENNReal.ofReal ((r - t) - τ) := by
      have h := hsub₂ τ ⟨hτ0.le, hτrt⟩ (r - t) ⟨hrtt, le_refl _⟩ (by linarith)
      have hr2 : (geodCurve (cov := cov) hmet (r - t) hrtt (G₀ t) η hη1) (r - t) = p := hG₂r
      rw [hr2] at h
      simpa using h
    have hltR : (Manifold.riemannianEDist I x₀ p).toReal < r := by
      have hfin : ∀ (a b : M), Manifold.riemannianEDist I a b ≠ ⊤ := fun a b =>
        (Submission.HopfRinow.riemannianEDist_lt_top (cov := cov) hmet htor a b).ne
      have hcutR : (Manifold.riemannianEDist I (G₀ (t - τ)) (G₂ τ)).toReal < 2 * τ := by
        have h := (ENNReal.toReal_lt_toReal (hfin _ _) ENNReal.ofReal_ne_top).mpr hcut
        rwa [ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ 2 * τ)] at h
      have hA : (Manifold.riemannianEDist I x₀ (G₀ (t - τ))).toReal = t - τ := by
        rw [ha, ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ t - τ)]
      have hB : (Manifold.riemannianEDist I (G₂ τ) p).toReal = (r - t) - τ := by
        rw [hb, ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ (r - t) - τ)]
      have h1 := Manifold.riemannianEDist_triangle (I := I) (x := x₀) (y := G₀ (t - τ))
        (z := G₂ τ)
      have h2 := Manifold.riemannianEDist_triangle (I := I) (x := G₀ (t - τ)) (y := G₂ τ)
        (z := p)
      have h3 := Manifold.riemannianEDist_triangle (I := I) (x := x₀) (y := G₂ τ) (z := p)
      have hne : Manifold.riemannianEDist I x₀ (G₀ (t - τ))
          + (Manifold.riemannianEDist I (G₀ (t - τ)) (G₂ τ)
            + Manifold.riemannianEDist I (G₂ τ) p) ≠ ⊤ :=
        ENNReal.add_ne_top.mpr ⟨hfin _ _, ENNReal.add_ne_top.mpr ⟨hfin _ _, hfin _ _⟩⟩
      have htot : Manifold.riemannianEDist I x₀ p
          ≤ Manifold.riemannianEDist I x₀ (G₀ (t - τ))
            + (Manifold.riemannianEDist I (G₀ (t - τ)) (G₂ τ)
              + Manifold.riemannianEDist I (G₂ τ) p) := by
        calc Manifold.riemannianEDist I x₀ p
            ≤ Manifold.riemannianEDist I x₀ (G₂ τ) + Manifold.riemannianEDist I (G₂ τ) p := h3
          _ ≤ (Manifold.riemannianEDist I x₀ (G₀ (t - τ))
                + Manifold.riemannianEDist I (G₀ (t - τ)) (G₂ τ))
                + Manifold.riemannianEDist I (G₂ τ) p := add_le_add h1 le_rfl
          _ = Manifold.riemannianEDist I x₀ (G₀ (t - τ))
                + (Manifold.riemannianEDist I (G₀ (t - τ)) (G₂ τ)
                  + Manifold.riemannianEDist I (G₂ τ) p) := by rw [add_assoc]
      have hmono := ENNReal.toReal_mono hne htot
      rw [ENNReal.toReal_add (hfin _ _) (ENNReal.add_ne_top.mpr ⟨hfin _ _, hfin _ _⟩),
        ENNReal.toReal_add (hfin _ _) (hfin _ _), hA, hB] at hmono
      linarith
    rw [hr, ENNReal.toReal_ofReal (le_of_lt (by linarith : (0:ℝ) < r))] at hltR
    exact absurd hltR (lt_irrefl _)
  -- extend the ray beyond `t`
  set G : ℝ → M := geodCurve (cov := cov) hmet r h0r x₀ w hw with hGdef
  have hagree : G₀ t = G t := by
    have h := geodCurve_agree (cov := cov) hmet ht0.le h0r (le_of_lt htr) x₀ w hw
    exact h (Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩)
  have hvel : curveVelocity (I := I) G₀ t = curveVelocity (I := I) G t := by
    refine Submission.GeodesicExtend.curveVelocity_congr_of_eventuallyEq (I := I) ?_
    have h := geodCurve_agree (cov := cov) hmet ht0.le h0r (le_of_lt htr) x₀ w hw
    filter_upwards [Ioo_mem_nhds (by linarith : -(geodDelta (cov := cov) hmet) < t)
      (by linarith [hδ] : t < t + geodDelta (cov := cov) hmet)] with s hs
    exact h hs
  have hGr : G r = GExp (cov := cov) hmet x₀ (r • w) := by
    rw [hGdef]
    exact (GExp_eq_geodCurve (cov := cov) hmet hw h0r (r := r) h0r le_rfl).symm
  have h1 : GExp (cov := cov) hmet (G t)
      ((r - t) • curveVelocity (I := I) G t) = G r := by
    have h := GExp_geodCurve_add (cov := cov) hmet x₀ hw h0r ht0.le (le_of_lt htr) hrtt
      (by linarith : t + (r - t) ≤ r)
    rwa [show t + (r - t) = r from by ring] at h
  calc p = GExp (cov := cov) hmet (G₀ t) ((r - t) • η) := hpη
    _ = GExp (cov := cov) hmet (G t) ((r - t) • curveVelocity (I := I) G t) := by
          rw [hagree, ← hξη, hvel]
    _ = G r := h1
    _ = GExp (cov := cov) hmet x₀ (r • w) := hGr


/-! ## Local persistence of the ascent property -/

/-- The polarisation of the chart metric. -/
lemma chartGram_polar (x₀ q : M) (a b : E) :
    chartGram (I := I) x₀ q a b
      = (chartGram (I := I) x₀ q (a + b) (a + b) - chartGram (I := I) x₀ q a a
          - chartGram (I := I) x₀ q b b) / 2 := by
  rw [chartGram_add_fst, chartGram_add_snd, chartGram_add_snd, chartGram_comm x₀ q b a]
  ring


/-- **A compact piece of a chart around a point**, produced by a purely topological (regularity)
argument: `M` has no `PseudoMetricSpace` instance, so this cannot use a metric ball directly. -/
theorem exists_isCompact_subset_chart_source [RegularSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)] (x₀ : M) :
    ∃ Z : Set M, IsCompact Z ∧ x₀ ∈ Z ∧ Z ⊆ (chartAt H x₀).source ∧
      ∃ e : ℝ≥0∞, 0 < e ∧ e < ⊤ ∧ Z = {y : M | Manifold.riemannianEDist I x₀ y ≤ e} := by
  classical
  obtain ⟨c, hcpos, hcsub⟩ := Submission.EDist.setOf_riemannianEDist_lt_subset_nhds (I := I)
    (chart_source_mem_nhds H x₀)
  set e : ℝ≥0∞ := min c 1 / 2 with hedef
  have hm0 : min c 1 ≠ 0 := ne_of_gt (lt_min hcpos zero_lt_one)
  have hmt : min c 1 ≠ ⊤ := ne_of_lt (lt_of_le_of_lt (min_le_right _ _) ENNReal.one_lt_top)
  have hepos : 0 < e := by
    rw [hedef]
    exact ENNReal.div_pos hm0 (by norm_num)
  have hlt : e < min c 1 := by
    rw [hedef]
    exact ENNReal.half_lt_self hm0 hmt
  have helt : e < ⊤ :=
    lt_of_lt_of_le hlt (le_trans (min_le_right _ _) (le_of_lt ENNReal.one_lt_top))
  refine ⟨{y : M | Manifold.riemannianEDist I x₀ y ≤ e}, ?_, ?_, ?_, e, hepos, helt, rfl⟩
  · letI : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
    have hset : {y : M | Manifold.riemannianEDist I x₀ y ≤ e} = Metric.closedEBall x₀ e := by
      ext y
      rw [Set.mem_setOf_eq, Metric.mem_closedEBall, Submission.EDist.edist_eq_riemannianEDist,
        Manifold.riemannianEDist_comm]
    rw [hset]
    exact (Metric.isClosed_closedEBall (a := x₀) (r := e)).isCompact
  · show Manifold.riemannianEDist I x₀ x₀ ≤ e
    rw [Manifold.riemannianEDist_self]
    exact zero_le
  · intro y hy
    refine hcsub ?_
    have hy' : Manifold.riemannianEDist I x₀ y ≤ e := hy
    exact lt_of_lt_of_le (lt_of_le_of_lt hy' hlt) (min_le_left _ _)

/-- **Local persistence of the ascent property (notes Prop. 5.2.18, local step).**  If `vv` is an
ascent direction at `x₀ ≠ p`, then the chart-parallel section `y ↦ frameVector x₀ y vv` is an
ascent direction on a whole neighbourhood of `x₀`. -/
theorem eventually_isAscentAt_frameVector
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M] [CompactSpace M]
    {p x₀ : M} (hx₀ : x₀ ≠ p) {vv : E}
    (hv : IsAscentAt (cov := cov) hmet p x₀ (frameVector (I := I) x₀ x₀ vv)) :
    ∀ᶠ y in 𝓝 x₀, IsAscentAt (cov := cov) hmet p y (frameVector (I := I) x₀ y vv) := by
  classical
  haveI hcb : IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x) :=
    Submission.EDist.isContinuousRiemannianBundle_infty (I := I)
  letI : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  have hx₀src : x₀ ∈ (extChartAt I x₀).source := by
    rw [extChartAt_source]; exact mem_chart_source H x₀
  -- the compact chart piece
  obtain ⟨Z, hZc, hx₀Z, hZsrc, e, hepos, helt, hZeq⟩ :=
    exists_isCompact_subset_chart_source (I := I) x₀
  obtain ⟨D, -⟩ := exists_chartFlowData (cov := cov) (z₀ := x₀) hZc hZsrc
  obtain ⟨lam, hlam, Lam, hLam, hbnd⟩ := Submission.ChartBounds.exists_chartGram_bounds (I := I)
    x₀ hZc ⟨x₀, hx₀Z⟩ hZsrc
  have hsl : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have hpfin : Manifold.riemannianEDist I x₀ p ≠ ⊤ :=
    (Submission.HopfRinow.riemannianEDist_lt_top (cov := cov) hmet htor x₀ p).ne
  set r : ℝ := (Manifold.riemannianEDist I x₀ p).toReal with hrdef
  have hr_eq : Manifold.riemannianEDist I x₀ p = ENNReal.ofReal r :=
    (ENNReal.ofReal_toReal hpfin).symm
  have hrpos : 0 < r := by
    rw [hrdef]
    exact ENNReal.toReal_pos (fun h => hx₀ ((Submission.EDist.riemannianEDist_eq_zero_iff
      (I := I)).mp h)) hpfin
  have hene : e ≠ ⊤ := helt.ne
  have hepos' : 0 < e.toReal := ENNReal.toReal_pos hepos.ne' hene
  set t : ℝ := min (min 1 (Real.sqrt lam * (flowScale D)⁻¹)) (min r (e.toReal)) / 2 with htdef
  have htpos : 0 < t := by
    rw [htdef]
    exact div_pos (lt_min (lt_min one_pos (mul_pos hsl (inv_pos.mpr (flowScale_pos D))))
      (lt_min hrpos hepos')) (by norm_num)
  have hXnn : 0 ≤ min (min 1 (Real.sqrt lam * (flowScale D)⁻¹)) (min r e.toReal) :=
    (lt_min (lt_min one_pos (mul_pos hsl (inv_pos.mpr (flowScale_pos D))))
      (lt_min hrpos hepos')).le
  have ht_le_c : t ≤ Real.sqrt lam * (flowScale D)⁻¹ := by
    rw [htdef]
    have hX : min (min 1 (Real.sqrt lam * (flowScale D)⁻¹)) (min r e.toReal)
        ≤ Real.sqrt lam * (flowScale D)⁻¹ :=
      le_trans (min_le_left _ _) (min_le_right _ _)
    linarith
  have ht_le_half_r : t ≤ r / 2 := by
    rw [htdef]
    have hX : min (min 1 (Real.sqrt lam * (flowScale D)⁻¹)) (min r e.toReal) ≤ r :=
      le_trans (min_le_right _ _) (min_le_left _ _)
    linarith
  have ht_le_r : t ≤ r := le_trans ht_le_half_r (by linarith [hrpos])
  have ht_lt_r : t < r := lt_of_le_of_lt ht_le_half_r (by linarith [hrpos])
  have ht_le_e : t ≤ e.toReal := by
    rw [htdef]
    have hX : min (min 1 (Real.sqrt lam * (flowScale D)⁻¹)) (min r e.toReal) ≤ e.toReal :=
      le_trans (min_le_right _ _) (min_le_right _ _)
    linarith
  -- the sequence of counterexamples
  have hRpos : ∀ n : ℕ, 0 < min (t / 2) (((n : ℕ) : ℝ) + 1)⁻¹ := fun n =>
    lt_min (by linarith) (by positivity)
  have hball_eq : ∀ ε : ℝ≥0∞,
      Metric.eball x₀ ε = {y : M | Manifold.riemannianEDist I x₀ y < ε} := by
    intro ε
    ext y
    rw [Set.mem_setOf_eq, Metric.mem_eball, Submission.EDist.edist_eq_riemannianEDist,
      Manifold.riemannianEDist_comm]
  have hball_viol : ∀ ε : ℝ≥0∞, 0 < ε → ∃ y : M,
      Manifold.riemannianEDist I x₀ y < ε ∧
        ¬ IsAscentAt (cov := cov) hmet p y (frameVector (I := I) x₀ y vv) := by
    intro ε hε
    by_contra h
    push_neg at h
    have hmem : Metric.eball x₀ ε ∈ 𝓝 x₀ := Metric.eball_mem_nhds x₀ hε
    rw [hball_eq ε] at hmem
    refine hcon (Filter.Eventually.mono hmem ?_)
    intro y hy
    exact not_not.mpr (h y hy)
  have hseq : ∀ n : ℕ, ∃ y : M, Manifold.riemannianEDist I x₀ y
        < ENNReal.ofReal (min (t / 2) (((n : ℕ) : ℝ) + 1)⁻¹) ∧
      ¬ IsAscentAt (cov := cov) hmet p y (frameVector (I := I) x₀ y vv) :=
    fun n => hball_viol _ (ENNReal.ofReal_pos.mpr (hRpos n))
  choose y hy using hseq
  have hyball : ∀ n, Manifold.riemannianEDist I x₀ (y n)
      < ENNReal.ofReal (min (t / 2) (((n : ℕ) : ℝ) + 1)⁻¹) := fun n => (hy n).1
  have hybad : ∀ n, ¬ IsAscentAt (cov := cov) hmet p (y n) (frameVector (I := I) x₀ (y n) vv) :=
    fun n => (hy n).2
  have hyx : ∀ n, (Manifold.riemannianEDist I x₀ (y n)).toReal < t / 2 := by
    intro n
    have h2 : Manifold.riemannianEDist I x₀ (y n)
        < ENNReal.ofReal (t / 2) :=
      lt_of_lt_of_le (hyball n) (ENNReal.ofReal_le_ofReal (min_le_left _ _))
    have hfin : Manifold.riemannianEDist I x₀ (y n) ≠ ⊤ :=
      (Submission.HopfRinow.riemannianEDist_lt_top (cov := cov) hmet htor x₀ (y n)).ne
    have h3 := (ENNReal.toReal_lt_toReal hfin ENNReal.ofReal_ne_top).mpr h2
    rwa [ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ t / 2)] at h3
  have hyZ : ∀ n, y n ∈ Z := by
    intro n
    rw [hZeq]
    have hfin : Manifold.riemannianEDist I x₀ (y n) ≠ ⊤ :=
      (Submission.HopfRinow.riemannianEDist_lt_top (cov := cov) hmet htor x₀ (y n)).ne
    have h2 : (Manifold.riemannianEDist I x₀ (y n)).toReal ≤ e.toReal := by
      have h := hyx n
      linarith [ht_le_e]
    calc Manifold.riemannianEDist I x₀ (y n)
        = ENNReal.ofReal (Manifold.riemannianEDist I x₀ (y n)).toReal :=
          (ENNReal.ofReal_toReal hfin).symm
      _ ≤ ENNReal.ofReal e.toReal := ENNReal.ofReal_le_ofReal h2
      _ = e := ENNReal.ofReal_toReal hene
  have hysrc : ∀ n, y n ∈ (extChartAt I x₀).source := fun n => by
    rw [extChartAt_source]; exact hZsrc (hyZ n)
  -- unpack the negation of the ascent property
  have hun : ∀ n, ∃ (r' : ℝ) (u : TangentSpace I (y n)),
      0 ≤ r' ∧ ‖u‖ = 1 ∧ p = GExp (cov := cov) hmet (y n) (r' • u) ∧
      Manifold.riemannianEDist I (y n) p = ENNReal.ofReal r' ∧
      0 ≤ inner ℝ (frameVector (I := I) x₀ (y n) vv) u := by
    intro n
    have h := hybad n
    simp only [IsAscentAt] at h
    push Not at h
    exact h
  choose r' u hr'nn hu1 hpG hdist hinner using hun
  -- coordinates in the chart at `x₀`
  have hw : ∀ n, ∃ w : E, frameVector (I := I) x₀ (y n) w = u n := fun n =>
    ⟨(trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ (y n) (u n),
      frameVector_clm (I := I) (hysrc n) (u n)⟩
  choose ws hws using hw
  have hgram1 : ∀ n, chartGram (I := I) x₀ (y n) (ws n) (ws n) = 1 := by
    intro n
    rw [chartGram_apply, hws n, real_inner_self_eq_norm_sq, hu1 n, one_pow]
  have hwle : ∀ n, ws n ∈ Metric.closedBall (0 : E) (1 / Real.sqrt lam) := by
    intro n
    rw [Metric.mem_closedBall, dist_zero_right]
    have h1 : lam * ‖ws n‖ ^ 2 ≤ chartGram (I := I) x₀ (y n) (ws n) (ws n) :=
      (hbnd (y n) (hyZ n) (ws n)).1
    rw [hgram1 n] at h1
    have h2 : (Real.sqrt lam * ‖ws n‖) ^ 2 ≤ 1 := by
      rw [mul_pow, Real.sq_sqrt hlam.le]; linarith
    have h3 : Real.sqrt lam * ‖ws n‖ ≤ 1 := by
      nlinarith [h2, mul_nonneg hsl.le (norm_nonneg (ws n))]
    rw [div_eq_inv_mul, inv_mul_eq_div, le_div_iff₀ hsl]
    linarith
  obtain ⟨w, hwmem, φ, hφmono, hφtend⟩ := IsCompact.tendsto_subseq
    (isCompact_closedBall (0 : E) (1 / Real.sqrt lam)) hwle
  have hwtend : Tendsto (fun n => ws (φ n)) atTop (𝓝 w) := hφtend
  -- `y n → x₀`
  have hy_tend : Tendsto y atTop (𝓝 x₀) := by
    refine EMetric.tendsto_nhds.mpr ?_
    intro ε hε
    have hR : Tendsto (fun n : ℕ => ENNReal.ofReal (((n : ℕ) : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => (((n : ℕ) : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
        (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop).inv_tendsto_atTop
      have h2 := (ENNReal.continuous_ofReal.tendsto 0).comp h1
      rwa [ENNReal.ofReal_zero] at h2
    filter_upwards [hR.eventually (isOpen_Iio.mem_nhds (show (0 : ℝ≥0∞) < ε from hε))]
      with n hn
    have h1 := hyball n
    have hconv : edist (y n) x₀ = Manifold.riemannianEDist I x₀ (y n) := by
      rw [Submission.EDist.edist_eq_riemannianEDist, Manifold.riemannianEDist_comm]
    rw [hconv]
    exact lt_of_lt_of_le (lt_of_lt_of_le h1 (ENNReal.ofReal_le_ofReal (min_le_right _ _))) hn.le
  have hytend : Tendsto (fun n => y (φ n)) atTop (𝓝 x₀) := hy_tend.comp hφmono.tendsto_atTop
  -- `t ≤ r' n`
  have ht_r' : ∀ n, t ≤ r' n := by
    intro n
    have hfin1 : Manifold.riemannianEDist I x₀ (y n) ≠ ⊤ :=
      (Submission.HopfRinow.riemannianEDist_lt_top (cov := cov) hmet htor x₀ (y n)).ne
    have hfin2 : Manifold.riemannianEDist I (y n) p ≠ ⊤ :=
      (Submission.HopfRinow.riemannianEDist_lt_top (cov := cov) hmet htor (y n) p).ne
    have htri := Manifold.riemannianEDist_triangle (I := I) (x := x₀) (y := y n) (z := p)
    have hmono := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfin1, hfin2⟩) htri
    rw [ENNReal.toReal_add hfin1 hfin2, ← hrdef] at hmono
    have hr' : r' n = (Manifold.riemannianEDist I (y n) p).toReal := by
      rw [hdist n, ENNReal.toReal_ofReal (hr'nn n)]
    rw [hr']
    linarith [hmono, hyx n, ht_le_r]
  -- the two distance identities along the sequence
  have hz_eq : ∀ n, Manifold.riemannianEDist I (y n)
      (GExp (cov := cov) hmet (y n) (t • u n)) = ENNReal.ofReal t := by
    intro n
    have hGr : (geodCurve (cov := cov) hmet (r' n) (hr'nn n) (y n) (u n) (hu1 n)) (r' n) = p := by
      rw [← GExp_eq_geodCurve (cov := cov) hmet (hu1 n) (hr'nn n) (r := r' n) (hr'nn n) le_rfl]
      exact (hpG n).symm
    have hmin : Manifold.riemannianEDist I (y n)
        ((geodCurve (cov := cov) hmet (r' n) (hr'nn n) (y n) (u n) (hu1 n)) (r' n))
        = ENNReal.ofReal (r' n) := by rw [hGr]; exact hdist n
    have hsub := geodCurve_sub_arc_minimising' (cov := cov) hmet (hr'nn n) (hu1 n) (s := r' n)
      (hr'nn n) le_rfl hmin
    have h0 : (geodCurve (cov := cov) hmet (r' n) (hr'nn n) (y n) (u n) (hu1 n)) 0 = y n :=
      (geodCurve_spec (cov := cov) hmet (r' n) (hr'nn n) (y n) (u n) (hu1 n)).1
    have h := hsub 0 ⟨le_refl 0, hr'nn n⟩ t ⟨htpos.le, ht_r' n⟩ htpos.le
    rw [h0] at h
    have hGt : (geodCurve (cov := cov) hmet (r' n) (hr'nn n) (y n) (u n) (hu1 n)) t
        = GExp (cov := cov) hmet (y n) (t • u n) :=
      (GExp_eq_geodCurve (cov := cov) hmet (hu1 n) (hr'nn n) (r := t) htpos.le (ht_r' n)).symm
    rw [hGt] at h
    simpa using h
  have hzp_eq : ∀ n, Manifold.riemannianEDist I (GExp (cov := cov) hmet (y n) (t • u n)) p
      = ENNReal.ofReal (r' n - t) := by
    intro n
    have hGr : (geodCurve (cov := cov) hmet (r' n) (hr'nn n) (y n) (u n) (hu1 n)) (r' n) = p := by
      rw [← GExp_eq_geodCurve (cov := cov) hmet (hu1 n) (hr'nn n) (r := r' n) (hr'nn n) le_rfl]
      exact (hpG n).symm
    have hmin : Manifold.riemannianEDist I (y n)
        ((geodCurve (cov := cov) hmet (r' n) (hr'nn n) (y n) (u n) (hu1 n)) (r' n))
        = ENNReal.ofReal (r' n) := by rw [hGr]; exact hdist n
    have hsub := geodCurve_sub_arc_minimising' (cov := cov) hmet (hr'nn n) (hu1 n) (s := r' n)
      (hr'nn n) le_rfl hmin
    have h := hsub t ⟨htpos.le, ht_r' n⟩ (r' n) ⟨hr'nn n, le_refl _⟩ (ht_r' n)
    rw [hGr] at h
    have hGt : (geodCurve (cov := cov) hmet (r' n) (hr'nn n) (y n) (u n) (hu1 n)) t
        = GExp (cov := cov) hmet (y n) (t • u n) :=
      (GExp_eq_geodCurve (cov := cov) hmet (hu1 n) (hr'nn n) (r := t) htpos.le (ht_r' n)).symm
    rw [hGt] at h
    simpa using h
  -- `‖w‖ = 1`
  have hgcont : ContinuousAt (fun q : M × E => chartGram (I := I) x₀ q.1 q.2 q.2) (x₀, w) :=
    continuousAt_chartGram_prod (I := I) x₀ (mem_chart_source H x₀) w
  have hxwpair : Tendsto (fun n => (y (φ n), ws (φ n))) atTop (𝓝 (x₀, w)) := by
    rw [nhds_prod_eq]
    exact hytend.prodMk hwtend
  have hlim : Tendsto (fun n => chartGram (I := I) x₀ (y (φ n)) (ws (φ n)) (ws (φ n))) atTop
      (𝓝 (chartGram (I := I) x₀ x₀ w w)) :=
    (hgcont.tendsto).comp hxwpair
  have hone : Tendsto (fun n => chartGram (I := I) x₀ (y (φ n)) (ws (φ n)) (ws (φ n))) atTop
      (𝓝 1) := by simp only [hgram1]; exact tendsto_const_nhds
  have hgrams : chartGram (I := I) x₀ x₀ w w = 1 := tendsto_nhds_unique hlim hone
  -- the fibre norm of `w` is `1` (`chartGram` at the base point is the Riemannian metric)
  have hw1fib : @norm (TangentSpace I x₀)
      (@NormedAddCommGroup.toNorm (TangentSpace I x₀)
        (instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal x₀))
      w = 1 := by
    have h2 : (@norm (TangentSpace I x₀)
        (@NormedAddCommGroup.toNorm (TangentSpace I x₀)
          (instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal x₀))
        w) ^ 2 = 1 := by
      calc (@norm (TangentSpace I x₀)
            (@NormedAddCommGroup.toNorm (TangentSpace I x₀)
              (instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal x₀))
            w) ^ 2
          = chartGram (I := I) x₀ x₀ w w :=
            (Submission.GSDisk.chartGram_self_fibre (I := I) x₀ (w : TangentSpace I x₀)).symm
        _ = 1 := hgrams
    have h3 : ((@norm (TangentSpace I x₀)
          (@NormedAddCommGroup.toNorm (TangentSpace I x₀)
            (instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal x₀))
          w) - 1)
        * ((@norm (TangentSpace I x₀)
          (@NormedAddCommGroup.toNorm (TangentSpace I x₀)
            (instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal x₀))
          w) + 1) = 0 := by nlinarith [h2]
    rcases mul_eq_zero.mp h3 with h | h
    · linarith
    · have hnn : (0 : ℝ) ≤ @norm (TangentSpace I x₀)
          (@NormedAddCommGroup.toNorm (TangentSpace I x₀)
            (instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal x₀))
          w := norm_nonneg _
      linarith
  have hwne : w ≠ 0 := by
    intro h
    have h1 : Lam * ‖w‖ ^ 2 = 0 := by rw [h, norm_zero]; ring
    have h2 : chartGram (I := I) x₀ x₀ w w ≤ Lam * ‖w‖ ^ 2 := (hbnd x₀ hx₀Z w).2
    rw [hgrams, h1] at h2
    norm_num at h2
  have hwle_norm : ∀ n, ‖ws n‖ ≤ (Real.sqrt lam)⁻¹ := by
    intro n
    have h := hwle n
    rw [Metric.mem_closedBall, dist_zero_right, div_eq_inv_mul, mul_one] at h
    exact h
  have hwlt : ‖w‖ ≤ (Real.sqrt lam)⁻¹ :=
    le_of_tendsto ((continuous_norm.tendsto w).comp hwtend)
      (Eventually.of_forall fun n => hwle_norm (φ n))
  -- `zₙ → GExp x₀ (t • w)`
  have hz_tend : Tendsto (fun n => GExp (cov := cov) hmet (y (φ n)) (t • u (φ n))) atTop
      (𝓝 (GExp (cov := cov) hmet x₀ (t • w))) := by
    have hK : ((extChartAt I x₀) x₀, flowScale D • (t • w))
        ∈ chartData (I := I) x₀ Z := by
      refine ⟨⟨x₀, hx₀Z, rfl⟩, ?_⟩
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos (flowScale_pos D), norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
      have h1 : flowScale D * t ≤ Real.sqrt lam := by
        have h2 : flowScale D * (Real.sqrt lam * (flowScale D)⁻¹) = Real.sqrt lam := by
          rw [mul_comm (Real.sqrt lam) ((flowScale D)⁻¹), ← mul_assoc,
            mul_inv_cancel₀ (flowScale_ne_zero D), one_mul]
        calc flowScale D * t ≤ flowScale D * (Real.sqrt lam * (flowScale D)⁻¹) :=
              mul_le_mul_of_nonneg_left ht_le_c (flowScale_pos D).le
          _ = Real.sqrt lam := h2
      calc flowScale D * (t * ‖w‖) = (flowScale D * t) * ‖w‖ := by ring
        _ ≤ Real.sqrt lam * (Real.sqrt lam)⁻¹ :=
              mul_le_mul h1 hwlt (norm_nonneg w) (le_of_lt hsl)
        _ = 1 := mul_inv_cancel₀ (ne_of_gt hsl)
    have hcont := GExp_frameVector_continuousAt (cov := cov) D hmet hx₀src
      (show t • w ≠ 0 from smul_ne_zero (ne_of_gt htpos) hwne) hK
    have hpair : Tendsto (fun n => (y (φ n), t • ws (φ n))) atTop (𝓝 (x₀, t • w)) := by
      simpa only [nhds_prod_eq] using hytend.prodMk (hwtend.const_smul t)
    have h1 : Tendsto (fun n => GExp (cov := cov) hmet (y (φ n))
        (frameVector (I := I) x₀ (y (φ n)) (t • ws (φ n)))) atTop
        (𝓝 (GExp (cov := cov) hmet x₀ (frameVector (I := I) x₀ x₀ (t • w)))) :=
      hcont.tendsto.comp hpair
    rw [Submission.Gauss.frameVector_self] at h1
    refine h1.congr' (Eventually.of_forall (fun n => ?_))
    rw [frameVector_smul, hws (φ n)]
  -- `d z p = ofReal (r - t)`
  have hzp_lim : Manifold.riemannianEDist I (GExp (cov := cov) hmet x₀ (t • w)) p
      = ENNReal.ofReal (r - t) := by
    have hrt : Tendsto (fun n => r' (φ n) - t) atTop (𝓝 (r - t)) := by
      have h3 : Tendsto (fun n => Manifold.riemannianEDist I (y (φ n)) p) atTop
          (𝓝 (ENNReal.ofReal r)) := by
        have h4 := ((Submission.HopfRinow.continuous_riemannianEDist_right (I := I) p).tendsto
          x₀).comp hytend
        rwa [hr_eq] at h4
      have h5 : Tendsto (fun n => (Manifold.riemannianEDist I (y (φ n)) p).toReal) atTop
          (𝓝 r) := by
        have h6 := (ENNReal.tendsto_toReal ENNReal.ofReal_ne_top).comp h3
        rwa [ENNReal.toReal_ofReal hrpos.le] at h6
      have h7 : (fun n => r' (φ n) - t)
          = fun n => (Manifold.riemannianEDist I (y (φ n)) p).toReal - t := by
        funext n
        rw [hdist (φ n), ENNReal.toReal_ofReal (hr'nn (φ n))]
      rw [h7]
      exact h5.sub_const t
    have h8 : Tendsto (fun n => ENNReal.ofReal (r' (φ n) - t)) atTop
        (𝓝 (ENNReal.ofReal (r - t))) :=
      (ENNReal.continuous_ofReal.tendsto _).comp hrt
    have h9 : Tendsto (fun n => Manifold.riemannianEDist I
        (GExp (cov := cov) hmet (y (φ n)) (t • u (φ n))) p) atTop
        (𝓝 (Manifold.riemannianEDist I (GExp (cov := cov) hmet x₀ (t • w)) p)) :=
      ((Submission.HopfRinow.continuous_riemannianEDist_right (I := I) p).tendsto
        (GExp (cov := cov) hmet x₀ (t • w))).comp hz_tend
    exact tendsto_nhds_unique h9 (h8.congr' (Eventually.of_forall (fun n => (hzp_eq (φ n)).symm)))
  -- `d x₀ z = ofReal t`
  have hz_le : Manifold.riemannianEDist I x₀ (GExp (cov := cov) hmet x₀ (t • w))
      ≤ ENNReal.ofReal t :=
    edist_GExp_smul_le_zero (cov := cov) hmet x₀ hw1fib htpos.le
  have hz_eq_t : Manifold.riemannianEDist I x₀ (GExp (cov := cov) hmet x₀ (t • w))
      = ENNReal.ofReal t := by
    refine le_antisymm hz_le ?_
    have htri := Manifold.riemannianEDist_triangle (I := I) (x := x₀)
      (y := GExp (cov := cov) hmet x₀ (t • w)) (z := p)
    rw [hr_eq, hzp_lim] at htri
    have hsum : ENNReal.ofReal t + ENNReal.ofReal (r - t) = ENNReal.ofReal r := by
      rw [← ENNReal.ofReal_add htpos.le (by linarith : (0 : ℝ) ≤ r - t)]
      norm_num
    rw [← hsum] at htri
    exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).mp htri
  -- the angle
  have hangle : 0 ≤ inner ℝ (frameVector (I := I) x₀ x₀ vv) w := by
    have hlim : Tendsto (fun n => chartGram (I := I) x₀ (y (φ n)) vv (ws (φ n))) atTop
        (𝓝 (chartGram (I := I) x₀ x₀ vv w)) := by
      have hfun : (fun n => chartGram (I := I) x₀ (y (φ n)) vv (ws (φ n)))
          = fun n => (chartGram (I := I) x₀ (y (φ n)) (vv + ws (φ n)) (vv + ws (φ n))
              - chartGram (I := I) x₀ (y (φ n)) vv vv
              - chartGram (I := I) x₀ (y (φ n)) (ws (φ n)) (ws (φ n))) / 2 := by
        funext n; exact chartGram_polar x₀ (y (φ n)) vv (ws (φ n))
      rw [hfun]
      have hxwA : Tendsto (fun n => (y (φ n), vv + ws (φ n))) atTop (𝓝 (x₀, vv + w)) := by
        rw [nhds_prod_eq]
        exact hytend.prodMk (hwtend.const_add vv)
      have hxvv : Tendsto (fun n => (y (φ n), vv)) atTop (𝓝 (x₀, vv)) := by
        rw [nhds_prod_eq]
        exact hytend.prodMk tendsto_const_nhds
      have hA : Tendsto (fun n => chartGram (I := I) x₀ (y (φ n)) (vv + ws (φ n)) (vv + ws (φ n)))
          atTop (𝓝 (chartGram (I := I) x₀ x₀ (vv + w) (vv + w))) :=
        ((continuousAt_chartGram_prod (I := I) x₀ (mem_chart_source H x₀) (vv + w)).tendsto).comp hxwA
      have hB : Tendsto (fun n => chartGram (I := I) x₀ (y (φ n)) vv vv) atTop
          (𝓝 (chartGram (I := I) x₀ x₀ vv vv)) :=
        ((continuousAt_chartGram_prod (I := I) x₀ (mem_chart_source H x₀) vv).tendsto).comp hxvv
      have hC := hlim
      have hcomb := (((hA.sub hB).sub hC).div_const 2)
      have hval : (chartGram (I := I) x₀ x₀ (vv + w) (vv + w) - chartGram (I := I) x₀ x₀ vv vv
            - chartGram (I := I) x₀ x₀ w w) / 2 = chartGram (I := I) x₀ x₀ vv w := by
        rw [chartGram_polar x₀ x₀ vv w]
      rw [← hval]
      exact hcomb
    have hnn : ∀ n, 0 ≤ chartGram (I := I) x₀ (y (φ n)) vv (ws (φ n)) := fun n => by
      rw [chartGram_apply, hws (φ n)]
      exact hinner (φ n)
    have hlim0 : (0 : ℝ) ≤ chartGram (I := I) x₀ x₀ vv w :=
      ge_of_tendsto hlim (Eventually.of_forall hnn)
    have hconv : chartGram (I := I) x₀ x₀ vv w
        = inner ℝ (frameVector (I := I) x₀ x₀ vv) w := by
      rw [chartGram_apply]
      exact congrArg (fun z => inner ℝ (frameVector (I := I) x₀ x₀ vv) z)
        (Submission.Gauss.frameVector_self (I := I) x₀ w)
    rwa [hconv] at hlim0
  -- the no-corner lemma and the contradiction
  have hcrux := eq_GExp_of_minimising_broken (cov := cov) hmet htor hw1fib (le_of_lt hrpos) htpos
    ht_lt_r hz_eq_t hzp_lim hr_eq
  have hneg : inner ℝ (frameVector (I := I) x₀ x₀ vv) w < 0 :=
    hv r w (le_of_lt hrpos) hw1fib hcrux hr_eq
  linarith

end

end Submission.GSField

/-
# The local inward push on a `9`-manifold with boundary

Let `M` be a charted space over the model half-space `H = EuclideanHalfSpace 9 ⊆ E = ℝ⁹` which is a
`C¹` manifold with boundary (`IsManifold (modelWithCornersEuclideanHalfSpace 9) 1 M`).

The interior `int M = {x | x ∉ (𝓡∂ 9).boundary M}` of `M` is the set of points whose chart image
lies in the interior `{z | 0 < z 0}` of the model half-space.  The aim of this file is to produce,
for every `x : M`, a *local* continuous map which pushes the points of a neighbourhood of `x`
strictly into the interior, together with the fact that this map preserves the interior.  These
local maps are then composed (in `interiorHomology`) into a deformation retraction of `M` onto
`int M`, which is the standard proof that `int M ↪ M` is a homology equivalence.

## Contents

* `Work.ThomBordism.RelDuality.nrm`, `pushE`, `pushH` — the inward push in the model space:
  `pushE y s = y + max s 0 • e₀` shifts the first coordinate up by `max s 0`, so that it preserves
  the half-space and never decreases the first coordinate;
* `Work.ThomBordism.RelDuality.isCompact_halfClosedBall` — the closed half-ball of the model
  half-space is compact;
* `Work.ThomBordism.RelDuality.PushDatum` — the data of a local push: a chart of the atlas, an
  ambient centre and a radius whose closed ball lies in the chart target;
* `PushDatum.region`, `PushDatum.amountE`, `PushDatum.localMap` — the region in which the push acts,
  the (clamped) amount of the shift and the local push itself;
* `PushDatum.ofPoint` — the datum at a point, with the chart at that point (so that every point of
  `M` lies in the region of its own datum);
* `PushDatum.isOpen_region`, `PushDatum.localMap_zero`, `PushDatum.localMap_eq_self_of_not_mem`,
  `PushDatum.localMap_push`, `PushDatum.localMap_preserves_interior`,
  `PushDatum.continuous_localMap` — the API of the local push.
-/
import Mathlib
import Submission.Work.Cohomology.homologyContractible

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open scoped Topology Manifold
open Function Set
open Classical

namespace Work.ThomBordism.RelDuality

noncomputable section

/-! ## The model half-space -/

/-- The ambient Euclidean space `ℝ⁹` of the model. -/
abbrev E9 : Type := EuclideanSpace ℝ (Fin 9)

/-- The model half-space `{z : ℝ⁹ | 0 ≤ z 0}`. -/
abbrev H9 : Type := EuclideanHalfSpace 9

/-- **The inward unit normal** of the model half-space: the first unit vector of `ℝ⁹`. -/
def nrm : E9 := PiLp.single 2 (0 : Fin 9) 1

theorem nrm_apply_zero : nrm 0 = 1 := by
  rw [nrm, PiLp.single_eq_same]

theorem nrm_apply_ne {k : Fin 9} (hk : k ≠ 0) : nrm k = 0 := by
  rw [nrm]
  exact PiLp.single_eq_of_ne (p := 2) hk 1

theorem norm_nrm : ‖nrm‖ = 1 := by
  have h0 : nrm.ofLp 0 = 1 := nrm_apply_zero
  have hs : ∀ k : Fin 8, nrm.ofLp k.succ = 0 := fun k => nrm_apply_ne (Fin.succ_ne_zero k)
  have hsum : (∑ i : Fin 9, ‖nrm.ofLp i‖ ^ 2) = 1 := by
    rw [Fin.sum_univ_succ]
    simp [h0, hs]
  rw [EuclideanSpace.norm_eq, hsum, Real.sqrt_one]

/-! ## The inward push of the model space -/

/-- **The inward push of the ambient space**: add `max s 0` to the first coordinate. -/
def pushE (y : E9) (s : ℝ) : E9 := y + max s 0 • nrm

theorem pushE_apply_zero (y : E9) (s : ℝ) : pushE y s 0 = y 0 + max s 0 := by
  simp [pushE, nrm]

theorem pushE_apply_ne {k : Fin 9} (hk : k ≠ 0) (y : E9) (s : ℝ) : pushE y s k = y k := by
  simp [pushE, nrm_apply_ne hk, smul_eq_mul]

theorem pushE_eq_self_of_nonpos (y : E9) (s : ℝ) (hs : s ≤ 0) : pushE y s = y := by
  have h : max s 0 = 0 := le_antisymm (max_le hs le_rfl) (le_max_right s 0)
  rw [pushE, h, zero_smul, add_zero]

@[simp] theorem pushE_eq_self_zero (y : E9) : pushE y 0 = y :=
  pushE_eq_self_of_nonpos y 0 le_rfl

theorem continuous_pushE : Continuous fun p : E9 × ℝ => pushE p.1 p.2 := by
  have h : Continuous fun p : E9 × ℝ => max p.2 0 • nrm :=
    (continuous_snd.max continuous_const).smul continuous_const
  exact continuous_fst.add h

theorem dist_pushE_le (y : E9) (s : ℝ) (c : E9) :
    dist (pushE y s) c ≤ dist y c + max s 0 := by
  have hsub : pushE y s - c = (y - c) + max s 0 • nrm := by
    simp only [pushE]
    abel
  have hn : ‖(max s 0) • nrm‖ = max s 0 := by
    rw [norm_smul, Real.norm_of_nonneg (le_max_right s 0), norm_nrm, mul_one]
  rw [dist_eq_norm, dist_eq_norm, hsub]
  calc ‖(y - c) + max s 0 • nrm‖ ≤ ‖y - c‖ + ‖(max s 0) • nrm‖ := norm_add_le _ _
    _ = ‖y - c‖ + max s 0 := by rw [hn]

/-- **The inward push of the model half-space**: the ambient push, which preserves the half-space
because it only increases the first coordinate. -/
def pushH (y : H9) (s : ℝ) : H9 :=
  ⟨pushE y.1 s, by
    rw [pushE_apply_zero]
    exact add_nonneg y.2 (le_max_right s 0)⟩

@[simp] theorem pushH_coe (y : H9) (s : ℝ) : (pushH y s).1 = pushE y.1 s := rfl

theorem pushH_coord_zero (y : H9) (s : ℝ) :
    (pushH y s).1 0 = y.1 0 + max s 0 := by
  rw [pushH_coe, pushE_apply_zero]

@[simp] theorem pushH_eq_self_zero (y : H9) : pushH y 0 = y := by
  apply Subtype.ext
  rw [pushH_coe, pushE_eq_self_zero]

theorem pushH_eq_self_of_nonpos (y : H9) (s : ℝ) (hs : s ≤ 0) : pushH y s = y := by
  apply Subtype.ext
  rw [pushH_coe, pushE_eq_self_of_nonpos _ _ hs]

theorem continuous_pushH : Continuous fun p : H9 × ℝ => pushH p.1 p.2 :=
  Continuous.subtype_mk
    (continuous_pushE.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)) _

theorem dist_pushH_le (y : H9) (s : ℝ) (c : E9) :
    dist (pushH y s).1 c ≤ dist y.1 c + max s 0 := by
  rw [pushH_coe]
  exact dist_pushE_le _ _ _

/-- **The closed half-ball of the model half-space is compact.** -/
theorem isCompact_halfClosedBall (c : E9) (r : ℝ) :
    IsCompact {y : H9 | dist y.1 c ≤ r} := by
  have hclosed : IsClosed {x : E9 | 0 ≤ x 0} := isClosed_le continuous_const (by fun_prop)
  have hemb : Topology.IsClosedEmbedding (Subtype.val : H9 → E9) :=
    IsClosed.isClosedEmbedding_subtypeVal hclosed
  exact hemb.isCompact_preimage (isCompact_closedBall c r)


/-! ## Local push data -/

/-- **The data of a local inward push** on a charted space over `EuclideanHalfSpace 9`: a chart of
the atlas, an ambient centre and a radius whose closed ball lands in the chart target. -/
structure PushDatum (M : Type*) [TopologicalSpace M] [ChartedSpace H9 M] where
  chart : OpenPartialHomeomorph M H9
  chart_mem_atlas : chart ∈ atlas H9 M
  center : E9
  radius : ℝ
  radius_pos : 0 < radius
  closedBall_subset : ∀ y : H9, dist y.1 center ≤ radius → y ∈ chart.target

/-! ## The chart criterion for interior points -/

/-- **Interior points in a chart.**  For a chart `e` of the atlas of a `C¹` manifold with boundary
modelled on the half-space `EuclideanHalfSpace 9`, a point `y` of the source of `e` is an interior
point of `M` if and only if the first coordinate of its chart image is positive. -/
theorem isInteriorPoint_iff_chart_coord {M : Type*} [TopologicalSpace M] [ChartedSpace H9 M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 9) 1 M]
    {e : OpenPartialHomeomorph M H9} (he : e ∈ atlas H9 M) {y : M} (hy : y ∈ e.source) :
    (modelWithCornersEuclideanHalfSpace 9).IsInteriorPoint y ↔ 0 < (e y).1 0 := by
  have hn : (1 : WithTop ℕ∞) ≠ 0 := by simp
  rw [ModelWithCorners.isInteriorPoint_iff_of_mem_atlas
    (I := modelWithCornersEuclideanHalfSpace 9) hn he hy]
  constructor
  · intro h
    have h' := (OpenPartialHomeomorph.interior_extend_target_subset_interior_range
      (I := modelWithCornersEuclideanHalfSpace 9) e) h
    rw [interior_range_modelWithCornersEuclideanHalfSpace] at h'
    simpa [OpenPartialHomeomorph.extend_coe, modelWithCornersEuclideanHalfSpace_toFun] using h'
  · intro h
    refine OpenPartialHomeomorph.mem_interior_extend_target e (e.map_source hy) ?_
    rw [interior_range_modelWithCornersEuclideanHalfSpace]
    simpa [modelWithCornersEuclideanHalfSpace_toFun] using h

namespace PushDatum

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H9 M]

theorem ball_subset (D : PushDatum M) {y : H9} (hy : dist y.1 D.center < D.radius) :
    y ∈ D.chart.target :=
  D.closedBall_subset y (le_of_lt hy)

/-- **The region in which the local push acts**: the points of the chart source whose chart image
lies in the open ball. -/
def region (D : PushDatum M) : Set M :=
  D.chart.source ∩ {x : M | dist (D.chart x).1 D.center < D.radius}

theorem mem_region {D : PushDatum M} {x : M} : x ∈ D.region ↔
    x ∈ D.chart.source ∧ dist (D.chart x).1 D.center < D.radius := Iff.rfl

theorem isOpen_region (D : PushDatum M) : IsOpen D.region := by
  have h : IsOpen {y : H9 | dist y.1 D.center < D.radius} :=
    Metric.isOpen_ball.preimage continuous_subtype_val
  have h2 := D.chart.isOpen_inter_preimage h
  simpa only [region, Set.preimage_setOf_eq, Set.mem_setOf_eq] using h2

/-- **The amount** by which the push shifts the first chart coordinate. -/
def amountE (D : PushDatum M) (t : ℝ) (z : E9) : ℝ :=
  min t 1 * max 0 ((D.radius - dist z D.center) / 2)

theorem amountE_eq_zero_of_le (D : PushDatum M) (t : ℝ) {z : E9}
    (hz : D.radius ≤ dist z D.center) : D.amountE t z = 0 := by
  have h : max 0 ((D.radius - dist z D.center) / 2) = 0 := by
    rw [max_eq_left (by linarith : (D.radius - dist z D.center) / 2 ≤ 0)]
  rw [amountE, h, mul_zero]

theorem max_amountE_le (D : PushDatum M) {z : E9} (hz : dist z D.center < D.radius) (t : ℝ) :
    max (D.amountE t z) 0 ≤ (D.radius - dist z D.center) / 2 := by
  have h1 : 0 ≤ (D.radius - dist z D.center) / 2 := by linarith
  have h2 : D.amountE t z ≤ (D.radius - dist z D.center) / 2 := by
    rw [amountE]
    calc min t 1 * max 0 ((D.radius - dist z D.center) / 2)
        ≤ 1 * max 0 ((D.radius - dist z D.center) / 2) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (le_max_left _ _)
      _ = (D.radius - dist z D.center) / 2 := by rw [one_mul, max_eq_right h1]
  exact max_le h2 h1

/-- **The local push at time `t`**: inside the region, shift the first chart coordinate inward by
the clamped amount; outside the region, the identity. -/
def localMap (D : PushDatum M) (t : ℝ) (x : M) : M :=
  if x ∈ D.region then D.chart.symm (pushH (D.chart x) (D.amountE t (D.chart x).1)) else x

theorem localMap_eq_self_of_not_mem (D : PushDatum M) {x : M} (hx : x ∉ D.region) (t : ℝ) :
    D.localMap t x = x := by
  rw [localMap, if_neg hx]

theorem localMap_zero (D : PushDatum M) (x : M) : D.localMap 0 x = x := by
  classical
  by_cases h : x ∈ D.region
  · rw [localMap, if_pos h]
    have h0 : D.amountE 0 (D.chart x).1 = 0 := by
      rw [amountE, min_eq_left (by norm_num : (0:ℝ) ≤ 1), zero_mul]
    rw [h0, pushH_eq_self_zero, D.chart.left_inv h.1]
  · exact D.localMap_eq_self_of_not_mem h 0

theorem dist_push_lt (D : PushDatum M) {x : M} (hx : x ∈ D.region) (t : ℝ) :
    dist (pushH (D.chart x) (D.amountE t (D.chart x).1)).1 D.center < D.radius := by
  obtain ⟨-, hlt⟩ := mem_region.mp hx
  have h := dist_pushH_le (D.chart x) (D.amountE t (D.chart x).1) D.center
  have h2 := D.max_amountE_le hlt t
  linarith

/-- The push of a chart coordinate of the source lands in the chart target. -/
theorem push_mem_target (D : PushDatum M) {x : M} (hx : x ∈ D.chart.source) (t : ℝ) :
    pushH (D.chart x) (D.amountE t (D.chart x).1) ∈ D.chart.target := by
  by_cases h : dist (D.chart x).1 D.center < D.radius
  · exact D.ball_subset (D.dist_push_lt ⟨hx, h⟩ t)
  · rw [D.amountE_eq_zero_of_le t (not_lt.mp h), pushH_eq_self_zero]
    exact D.chart.map_source hx

/-- Inside the source of the chart, the local push is given by the chart formula. -/
theorem localMap_eq_formula (D : PushDatum M) {x : M} (hx : x ∈ D.chart.source) (t : ℝ) :
    D.localMap t x = D.chart.symm (pushH (D.chart x) (D.amountE t (D.chart x).1)) := by
  classical
  by_cases h : x ∈ D.region
  · rw [localMap, if_pos h]
  · rw [localMap, if_neg h]
    have hge : D.radius ≤ dist (D.chart x).1 D.center := by
      by_contra hc
      exact h ⟨hx, not_le.mp hc⟩
    rw [D.amountE_eq_zero_of_le t hge, pushH_eq_self_zero, D.chart.left_inv hx]

/-- **A closed ambient ball inside a chart target.**  For any chart `e` and any point `y` of its
target there is a radius `r > 0` such that every point of the half-space at ambient distance `≤ r`
from `y` lies in the target of `e`. -/
theorem exists_closedBall_subset_target {e : OpenPartialHomeomorph M H9} {y : H9}
    (hy : y ∈ e.target) :
    ∃ r : ℝ, 0 < r ∧ ∀ z : H9, dist z.1 y.1 ≤ r → z ∈ e.target := by
  have hmem : e.target ∈ 𝓝 (⟨y.1, y.2⟩ : H9) := e.open_target.mem_nhds hy
  rw [nhds_subtype_eq_comap (p := fun z : E9 => 0 ≤ z 0) (x := y.1) (h := y.2)] at hmem
  obtain ⟨U, hU, hsub⟩ := Filter.mem_comap.mp hmem
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨ε / 2, by linarith, fun z hz => hsub ?_⟩
  exact hball (by rw [Metric.mem_ball]; linarith)

/-- **The push datum at a point** `x` of `M`: the chart at `x`, centred at the image of `x`, with a
radius so small that the closed ambient ball around the centre lands in the chart target. -/
def ofPoint (x : M) : PushDatum M :=
  let e := chartAt H9 x
  let w := exists_closedBall_subset_target (e := e) (mem_chart_target H9 x)
  { chart := e
    chart_mem_atlas := ChartedSpace.chart_mem_atlas x
    center := (e x).1
    radius := Classical.choose w
    radius_pos := (Classical.choose_spec w).1
    closedBall_subset := fun z hz => (Classical.choose_spec w).2 z hz }

@[simp] theorem ofPoint_chart (x : M) : (ofPoint x).chart = chartAt H9 x := rfl

@[simp] theorem ofPoint_center (x : M) : (ofPoint x).center = ((chartAt H9 x) x).1 := rfl

theorem ofPoint_radius_pos (x : M) : 0 < (ofPoint x).radius := (ofPoint x).radius_pos

/-- **Every point lies in the region of its own push datum.** -/
theorem mem_region_ofPoint (x : M) : x ∈ (ofPoint x).region := by
  refine ⟨?_, ?_⟩
  · show x ∈ (ofPoint x).chart.source
    rw [ofPoint_chart]
    exact mem_chart_source H9 x
  · show dist (((ofPoint x).chart x)).1 ((ofPoint x).center) < (ofPoint x).radius
    rw [ofPoint_chart, ofPoint_center, dist_self]
    linarith [(ofPoint x).radius_pos]

theorem region_subset_symm_image (D : PushDatum M) :
    D.region ⊆ D.chart.symm '' {y : H9 | dist y.1 D.center ≤ D.radius} := by
  intro x hx
  obtain ⟨hsrc, hlt⟩ := mem_region.mp hx
  exact ⟨D.chart x, le_of_lt hlt, D.chart.left_inv hsrc⟩

/-- The `chart.symm`-image of the closed ball is contained in the chart source. -/
theorem symm_image_subset_source (D : PushDatum M) :
    D.chart.symm '' {y : H9 | dist y.1 D.center ≤ D.radius} ⊆ D.chart.source := by
  rintro z ⟨y, hy, rfl⟩
  exact D.chart.map_target (D.closedBall_subset y hy)

/-! ## Continuity of the local push -/

theorem continuous_pushH_amount (D : PushDatum M) :
    Continuous fun q : H9 × ℝ => pushH q.1 (D.amountE q.2 q.1.1) := by
  refine Continuous.subtype_mk ?_ _
  have h1 : Continuous fun q : H9 × ℝ => q.1.1 := continuous_subtype_val.comp continuous_fst
  have h2 : Continuous fun q : H9 × ℝ => D.amountE q.2 q.1.1 := by
    have hdist : Continuous fun q : H9 × ℝ => dist q.1.1 D.center :=
      continuous_dist.comp (h1.prodMk continuous_const)
    rw [show (fun q : H9 × ℝ => D.amountE q.2 q.1.1) = fun q : H9 × ℝ =>
        min q.2 1 * max 0 ((D.radius - dist q.1.1 D.center) / 2) from rfl]
    fun_prop
  exact continuous_pushE.comp (h1.prodMk h2)

theorem continuousOn_formula (D : PushDatum M) :
    ContinuousOn (fun p : M × ℝ => D.chart.symm
      (pushH (D.chart p.1) (D.amountE p.2 (D.chart p.1).1)))
      (D.chart.source ×ˢ (univ : Set ℝ)) := by
  have hchart : ContinuousOn (fun p : M × ℝ => D.chart p.1) (D.chart.source ×ˢ univ) :=
    ContinuousOn.comp (g := fun x : M => D.chart x) (t := D.chart.source)
      D.chart.continuousOn continuousOn_fst (by intro p hp; exact hp.1)
  have hcore : ContinuousOn (fun p : M × ℝ => (D.chart p.1, p.2)) (D.chart.source ×ˢ univ) :=
    hchart.prodMk continuousOn_snd
  have hpush : ContinuousOn (fun p : M × ℝ =>
      pushH (D.chart p.1) (D.amountE p.2 (D.chart p.1).1)) (D.chart.source ×ˢ univ) :=
    Continuous.comp_continuousOn D.continuous_pushH_amount hcore
  have hmap : MapsTo (fun p : M × ℝ => pushH (D.chart p.1) (D.amountE p.2 (D.chart p.1).1))
      (D.chart.source ×ˢ univ) D.chart.target := by
    intro p hp
    exact D.push_mem_target hp.1 p.2
  exact ContinuousOn.comp D.chart.symm.continuousOn hpush hmap

/-- **The local push is jointly continuous.** -/
theorem continuous_localMap_uncurry (D : PushDatum M) :
    Continuous fun p : M × ℝ => D.localMap p.2 p.1 := by
  classical
  rw [continuous_iff_continuousAt]
  rintro ⟨x₀, t₀⟩
  by_cases hx : x₀ ∈ D.chart.source
  · have hmem : D.chart.source ×ˢ (univ : Set ℝ) ∈ 𝓝 (x₀, t₀) :=
      (D.chart.open_source.prod isOpen_univ).mem_nhds ⟨hx, trivial⟩
    have heq : (fun p : M × ℝ => D.chart.symm
        (pushH (D.chart p.1) (D.amountE p.2 (D.chart p.1).1))) =ᶠ[𝓝 (x₀, t₀)]
        (fun p : M × ℝ => D.localMap p.2 p.1) := by
      filter_upwards [hmem] with p hp
      exact (D.localMap_eq_formula hp.1 p.2).symm
    exact (D.continuousOn_formula.continuousAt hmem).congr heq
  · have hA : IsCompact (D.chart.symm '' {y : H9 | dist y.1 D.center ≤ D.radius}) :=
      (isCompact_halfClosedBall D.center D.radius).image_of_continuousOn
        (D.chart.symm.continuousOn.mono (fun y hy => D.closedBall_subset y hy))
    have hclosed : IsClosed (D.chart.symm '' {y : H9 | dist y.1 D.center ≤ D.radius}) :=
      hA.isClosed
    have hx₀ : x₀ ∉ D.chart.symm '' {y : H9 | dist y.1 D.center ≤ D.radius} :=
      fun h => hx (D.symm_image_subset_source h)
    have hopen : IsOpen ((D.chart.symm '' {y : H9 | dist y.1 D.center ≤ D.radius})ᶜ) :=
      @IsClosed.isOpen_compl _ _ _ hclosed
    have hmem : ((D.chart.symm '' {y : H9 | dist y.1 D.center ≤ D.radius})ᶜ
        ×ˢ (univ : Set ℝ)) ∈ 𝓝 (x₀, t₀) :=
      (hopen.prod isOpen_univ).mem_nhds ⟨hx₀, trivial⟩
    have heq : (fun p : M × ℝ => D.localMap p.2 p.1) =ᶠ[𝓝 (x₀, t₀)] Prod.fst := by
      filter_upwards [hmem] with p hp
      have hp' : p.1 ∉ D.region := fun hr => hp.1 (D.region_subset_symm_image hr)
      exact D.localMap_eq_self_of_not_mem hp' p.2
    exact continuous_fst.continuousAt.congr heq.symm

theorem continuous_localMap (D : PushDatum M) (t : ℝ) : Continuous (D.localMap t) :=
  D.continuous_localMap_uncurry.comp
    (continuous_id.prodMk (continuous_const : Continuous fun _ : M => t))

/-- **The local push moves the points of its region strictly into the interior.** -/
theorem isInteriorPoint_localMap [IsManifold (modelWithCornersEuclideanHalfSpace 9) 1 M]
    (D : PushDatum M) {x : M} (hx : x ∈ D.region) {t : ℝ} (ht : 0 < t) :
    (modelWithCornersEuclideanHalfSpace 9).IsInteriorPoint (D.localMap t x) := by
  obtain ⟨hsrc, hdist⟩ := mem_region.mp hx
  have hmem : pushH (D.chart x) (D.amountE t (D.chart x).1) ∈ D.chart.target :=
    D.push_mem_target hsrc t
  rw [D.localMap_eq_formula hsrc t]
  refine (isInteriorPoint_iff_chart_coord D.chart_mem_atlas (D.chart.map_target hmem)).mpr ?_
  rw [D.chart.right_inv hmem, pushH_coord_zero]
  have hpos : 0 < D.amountE t (D.chart x).1 := by
    rw [amountE]
    refine mul_pos (lt_min ht zero_lt_one) ?_
    rw [lt_max_iff]
    right
    linarith
  rw [max_eq_left (le_of_lt hpos)]
  linarith [(D.chart x).2]

/-- **The local push preserves the interior.** -/
theorem isInteriorPoint_localMap_of_isInteriorPoint
    [IsManifold (modelWithCornersEuclideanHalfSpace 9) 1 M]
    (D : PushDatum M) {x : M} (hx : (modelWithCornersEuclideanHalfSpace 9).IsInteriorPoint x)
    (t : ℝ) : (modelWithCornersEuclideanHalfSpace 9).IsInteriorPoint (D.localMap t x) := by
  classical
  by_cases h : x ∈ D.region
  · obtain ⟨hsrc, hdist⟩ := mem_region.mp h
    have hmem : pushH (D.chart x) (D.amountE t (D.chart x).1) ∈ D.chart.target :=
      D.push_mem_target hsrc t
    rw [D.localMap_eq_formula hsrc t]
    refine (isInteriorPoint_iff_chart_coord D.chart_mem_atlas (D.chart.map_target hmem)).mpr ?_
    rw [D.chart.right_inv hmem, pushH_coord_zero]
    have hpos : 0 < (D.chart x).1 0 :=
      (isInteriorPoint_iff_chart_coord D.chart_mem_atlas hsrc).mp hx
    linarith [le_max_right (D.amountE t (D.chart x).1) 0]
  · rw [D.localMap_eq_self_of_not_mem h t]
    exact hx

end PushDatum

end

end Work.ThomBordism.RelDuality

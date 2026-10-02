import Mathlib
import Submission.Work.PTGeometric.SourceRegion
import Submission.Work.ThomBordism.Transversality.Preimage.BoundaryCoord
import Submission.Work.PTGeometric.exists_chart_at_interior_zero
import Submission.Work.PTGeometric.regionNhdBoundaryZero

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The region-charting theorem

`Work.PTGeometric.RegionManifoldTheorem k` (see `Submission/Work/PTGeometric/SourceRegion.lean`)
says: for a smooth function `Φ` on a compact smooth manifold with boundary `A`, a submersion
(Mathlib's local-normal-form `IsSubmersionAt`) at every zero, and *one-sided* at the boundary zeros
(`{Φ = 0}` tangent to `∂A` there, as in the `hΦ_one` hypothesis), the region `{Φ ≤ 0}` is a compact
`T2` smooth manifold with boundary, the inclusion is smooth, submersivity is transported, and the
boundary is `(∂A ∪ {Φ = 0}) ∩ {Φ ≤ 0}`.

This file proves it.  The manifold structure is transported to the region `{x // Φ x ≤ 0}` itself
(the homeomorphism `e` is the identity): at every point `m` of the region we produce an ambient
maximal-atlas chart `dom m` of `A` and a linear isomorphism `lin m` of the model space, such that
the map
  `chartVec m w = lin m (dom m.extend w - off m)`
restricted to the region is a chart into the half-space.  Three cases:

* `m ∈ ∂A` or `Φ m < 0` (the "big" case): the region contains a neighbourhood of `m`
  (`regionNhdBoundaryZero` for the boundary zeros; continuity otherwise), and the chart is the
  ambient chart itself (`lin m = 1`, `off m = 0`);
* `m ∈ int A` with `Φ m = 0`: the region is locally the affine half-space cut out by the
  normal-form functional (`exists_chart_at_interior_zero`).

The transitions between these charts are the ambient changes of extended charts
(`contDiffOn_extendCoordChange`) composed with linear automorphisms, so they are smooth; this gives
`ChartedSpace` and `IsManifold`. -/

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter ModelWithCorners Classical

namespace Work.PTGeometric

noncomputable section

/-- A chart of the maximal atlas whose source lies in a prescribed open set. -/
theorem exists_chart_source_subset {n : ℕ} [NeZero n] (A : Type*) [TopologicalSpace A]
    [ChartedSpace (EuclideanHalfSpace n) A] [IsManifold (𝓡∂ n) ∞ A]
    {U : Set A} (hU : IsOpen U) {x : A} (hx : x ∈ U) :
    ∃ e : OpenPartialHomeomorph A (EuclideanHalfSpace n),
      e ∈ IsManifold.maximalAtlas (𝓡∂ n) ∞ A ∧ x ∈ e.source ∧ e.source ⊆ U := by
  refine ⟨(chartAt (EuclideanHalfSpace n) x).restr U, ?_, ?_, ?_⟩
  · exact restr_mem_maximalAtlas (contDiffGroupoid ∞ (𝓡∂ n))
      (IsManifold.chart_mem_maximalAtlas (I := 𝓡∂ n) x) hU
  · rw [OpenPartialHomeomorph.restr_source, hU.interior_eq]
    exact ⟨mem_chart_source _ x, hx⟩
  · rw [OpenPartialHomeomorph.restr_source, hU.interior_eq]
    exact inter_subset_right


/-- The model space of the ambient manifold. -/
abbrev Mod (k : ℕ) : Type := EuclideanSpace ℝ (Fin (8 + k + 1))

/-- The half-space model of the ambient manifold. -/
abbrev Half (k : ℕ) : Type := EuclideanHalfSpace (8 + k + 1)

/-- **The data of the region-charting theorem**: a compact `T2` smooth `(8+k+1)`-manifold `A` with
boundary, a smooth `Φ : A → ℝ` which is a submersion at its zeros and one-sided at the boundary
zeros. -/
structure RegionSetup (k : ℕ) where
  /-- the ambient manifold -/
  A : Type
  [topologicalSpace : TopologicalSpace A]
  [chartedSpace : ChartedSpace (EuclideanHalfSpace (8 + k + 1)) A]
  [isManifold : IsManifold (𝓡∂ (8 + k + 1)) ∞ A]
  [t2Space : T2Space A]
  /-- the defining function -/
  Φ : A → ℝ
  hΦ : ContMDiff (𝓡∂ (8 + k + 1)) (𝓘(ℝ, ℝ)) ∞ Φ
  hsub : ∀ x : A, Φ x = 0 → IsSubmersionAt (𝓡∂ (8 + k + 1)) (𝓘(ℝ, ℝ)) ∞ Φ x
  hone : ∀ x ∈ (𝓡∂ (8 + k + 1)).boundary A, Φ x = 0 →
    ∃ (e : OpenPartialHomeomorph A (EuclideanHalfSpace (8 + k + 1))) (c : ℝ),
      e ∈ IsManifold.maximalAtlas (𝓡∂ (8 + k + 1)) ∞ A ∧ x ∈ e.source ∧ c < 0 ∧
      (∀ y ∈ e.source, (e y).1 0 = 0 ↔ y ∈ (𝓡∂ (8 + k + 1)).boundary A) ∧
      mfderiv (𝓡∂ (8 + k + 1)) (𝓘(ℝ, ℝ)) Φ x
        = c • mfderiv (𝓡∂ (8 + k + 1)) (𝓘(ℝ, ℝ)) (fun y : A => (e y).1 0) x
  /-- **the region is compact.**  This replaces the compactness of the ambient manifold: the region
  theorem is needed on the half-space `EuclideanHalfSpace N`, which is not compact, and the only place
  where compactness of the ambient was used is the compactness of the region. -/
  hK : IsCompact {x : A | Φ x ≤ 0}

attribute [instance] RegionSetup.topologicalSpace RegionSetup.chartedSpace RegionSetup.isManifold
  RegionSetup.t2Space

namespace RegionSetup

variable {k : ℕ} (S : RegionSetup k)

/-- The region `{x | Φ x ≤ 0}`, as a subtype of the ambient manifold. -/
abbrev Region : Type := {x : S.A // S.Φ x ≤ 0}

variable {S}

theorem isOpen_region_of_neg {x : S.A} (h : S.Φ x < 0) : {y : S.A | S.Φ y ≤ 0} ∈ 𝓝 x :=
  Filter.mem_of_superset
    (show S.Φ ⁻¹' Iio 0 ∈ 𝓝 x from
      (S.hΦ.continuous.isOpen_preimage _ isOpen_Iio).mem_nhds h)
    (fun y hy => le_of_lt (show S.Φ y < 0 from hy))

theorem mem_regionSet_of_boundary_zero {x : S.A}
    (hxb : x ∈ (𝓡∂ (8 + k + 1)).boundary S.A) (hx0 : S.Φ x = 0) :
    {y : S.A | S.Φ y ≤ 0} ∈ 𝓝 x :=
  regionNhdBoundaryZero S.A S.Φ S.hΦ S.hsub S.hone hxb hx0


/-- The dichotomy at a point of the region: either the region contains a neighbourhood of it
(`m ∈ ∂A` or `Φ m < 0`), or `m` is a zero of `Φ` in the interior of `A`. -/
def bigCase (m : S.Region) : Prop := m.1 ∈ (𝓡∂ (8 + k + 1)).boundary S.A ∨ S.Φ m.1 < 0

theorem interior_of_not_bigCase (m : S.Region) (h : ¬ S.bigCase m) :
    m.1 ∈ (𝓡∂ (8 + k + 1)).interior S.A := by
  rcases (𝓡∂ (8 + k + 1)).isInteriorPoint_or_isBoundaryPoint m.1 with hi | hb
  · exact hi
  · exact absurd (Or.inl hb) h

theorem zero_of_not_bigCase (m : S.Region) (h : ¬ S.bigCase m) : S.Φ m.1 = 0 :=
  le_antisymm m.2 (not_lt.mp fun hlt => h (Or.inr hlt))

theorem eventually_region (m : S.Region) (h : S.bigCase m) : ∀ᶠ y in 𝓝 m.1, S.Φ y ≤ 0 := by
  rcases h with hb | hlt
  · rcases lt_or_eq_of_le m.2 with hlt' | heq
    · exact S.isOpen_region_of_neg hlt'
    · exact S.mem_regionSet_of_boundary_zero hb heq
  · exact S.isOpen_region_of_neg hlt

theorem exists_open_regionNhd (m : S.Region) (h : S.bigCase m) :
    ∃ U : Set S.A, IsOpen U ∧ m.1 ∈ U ∧ U ⊆ {y : S.A | S.Φ y ≤ 0} := by
  have hmem : {y : S.A | S.Φ y ≤ 0} ∈ 𝓝 m.1 := S.eventually_region m h
  obtain ⟨U, hUsub, hUopen, hUm⟩ := mem_nhds_iff.mp hmem
  exact ⟨U, hUopen, hUm, hUsub⟩

/-- The open neighbourhood of `m` on which the region contains a neighbourhood (`bigCase`). -/
noncomputable def regionNhd (m : S.Region) (h : S.bigCase m) : Set S.A :=
  Classical.choose (S.exists_open_regionNhd m h)

theorem isOpen_regionNhd (m : S.Region) (h : S.bigCase m) : IsOpen (S.regionNhd m h) :=
  (Classical.choose_spec (S.exists_open_regionNhd m h)).1

theorem mem_regionNhd (m : S.Region) (h : S.bigCase m) : m.1 ∈ S.regionNhd m h :=
  (Classical.choose_spec (S.exists_open_regionNhd m h)).2.1

theorem regionNhd_subset (m : S.Region) (h : S.bigCase m) :
    S.regionNhd m h ⊆ {y : S.A | S.Φ y ≤ 0} :=
  (Classical.choose_spec (S.exists_open_regionNhd m h)).2.2

/-- The ambient chart in the `bigCase`: its source lies in the region. -/
noncomputable def chartI (m : S.Region) (h : S.bigCase m) :
    OpenPartialHomeomorph S.A (Half k) :=
  Classical.choose (exists_chart_source_subset S.A (U := S.regionNhd m h)
    (S.isOpen_regionNhd m h) (S.mem_regionNhd m h))

theorem chartI_maximalAtlas (m : S.Region) (h : S.bigCase m) :
    S.chartI m h ∈ IsManifold.maximalAtlas (𝓡∂ (8 + k + 1)) ∞ S.A :=
  (Classical.choose_spec (exists_chart_source_subset S.A (U := S.regionNhd m h)
    (S.isOpen_regionNhd m h) (S.mem_regionNhd m h))).1

theorem mem_chartI_source (m : S.Region) (h : S.bigCase m) : m.1 ∈ (S.chartI m h).source :=
  (Classical.choose_spec (exists_chart_source_subset S.A (U := S.regionNhd m h)
    (S.isOpen_regionNhd m h) (S.mem_regionNhd m h))).2.1

theorem chartI_source_subset (m : S.Region) (h : S.bigCase m) :
    (S.chartI m h).source ⊆ {y : S.A | S.Φ y ≤ 0} := fun y hy =>
  S.regionNhd_subset m h
    ((Classical.choose_spec (exists_chart_source_subset S.A (U := S.regionNhd m h)
      (S.isOpen_regionNhd m h) (S.mem_regionNhd m h))).2.2 hy)

theorem exists_chartII (m : S.Region) (h : ¬ S.bigCase m) :
    ∃ (e : OpenPartialHomeomorph S.A (Half k)) (T : Mod k ≃L[ℝ] Mod k),
      e ∈ IsManifold.maximalAtlas (𝓡∂ (8 + k + 1)) ∞ S.A ∧ m.1 ∈ e.source ∧
      e.source ⊆ (𝓡∂ (8 + k + 1)).interior S.A ∧
      (∀ y ∈ e.source, S.Φ y ≤ 0 ↔ 0 ≤ (T ((e.extend (𝓡∂ (8 + k + 1))) y
        - (e.extend (𝓡∂ (8 + k + 1))) m.1)) 0) ∧
      (∀ y ∈ e.source, S.Φ y = 0 ↔ (T ((e.extend (𝓡∂ (8 + k + 1))) y
        - (e.extend (𝓡∂ (8 + k + 1))) m.1)) 0 = 0) :=
  exists_chart_at_interior_zero S.A S.Φ (S.interior_of_not_bigCase m h)
    (S.zero_of_not_bigCase m h) (S.hsub m.1 (S.zero_of_not_bigCase m h))

/-- The straightened (affine) chart at an interior zero. -/
noncomputable def chartII (m : S.Region) (h : ¬ S.bigCase m) :
    OpenPartialHomeomorph S.A (Half k) :=
  Classical.choose (S.exists_chartII m h)

/-- The linear isomorphism of the straightened chart at an interior zero. -/
noncomputable def linII (m : S.Region) (h : ¬ S.bigCase m) : Mod k ≃L[ℝ] Mod k :=
  Classical.choose (Classical.choose_spec (S.exists_chartII m h))

theorem chartII_maximalAtlas (m : S.Region) (h : ¬ S.bigCase m) :
    S.chartII m h ∈ IsManifold.maximalAtlas (𝓡∂ (8 + k + 1)) ∞ S.A :=
  (Classical.choose_spec (Classical.choose_spec (S.exists_chartII m h))).1

theorem mem_chartII_source (m : S.Region) (h : ¬ S.bigCase m) :
    m.1 ∈ (S.chartII m h).source :=
  (Classical.choose_spec (Classical.choose_spec (S.exists_chartII m h))).2.1

theorem chartII_source_interior (m : S.Region) (h : ¬ S.bigCase m) :
    (S.chartII m h).source ⊆ (𝓡∂ (8 + k + 1)).interior S.A :=
  (Classical.choose_spec (Classical.choose_spec (S.exists_chartII m h))).2.2.1

theorem chartII_iff (m : S.Region) (h : ¬ S.bigCase m) :
    ∀ y ∈ (S.chartII m h).source, S.Φ y ≤ 0 ↔
      0 ≤ (S.linII m h (((S.chartII m h).extend (𝓡∂ (8 + k + 1))) y
        - ((S.chartII m h).extend (𝓡∂ (8 + k + 1))) m.1)) 0 :=
  (Classical.choose_spec (Classical.choose_spec (S.exists_chartII m h))).2.2.2.1

theorem chartII_iff_zero (m : S.Region) (h : ¬ S.bigCase m) :
    ∀ y ∈ (S.chartII m h).source, S.Φ y = 0 ↔
      (S.linII m h (((S.chartII m h).extend (𝓡∂ (8 + k + 1))) y
        - ((S.chartII m h).extend (𝓡∂ (8 + k + 1))) m.1)) 0 = 0 :=
  (Classical.choose_spec (Classical.choose_spec (S.exists_chartII m h))).2.2.2.2

/-- The ambient chart used at `m`. -/
noncomputable def dom (m : S.Region) : OpenPartialHomeomorph S.A (Half k) :=
  if h : S.bigCase m then S.chartI m h else S.chartII m h

/-- The linear comparison map used at `m`. -/
noncomputable def lin (m : S.Region) : (Mod k) ≃L[ℝ] (Mod k) :=
  if h : S.bigCase m then ContinuousLinearEquiv.refl ℝ (Mod k) else S.linII m h

/-- The affine offset: at an interior zero, the chart value of the base point. -/
noncomputable def off (m : S.Region) : Mod k :=
  if h : S.bigCase m then 0 else (S.chartII m h).extend (𝓡∂ (8 + k + 1)) m.1

theorem dom_maximalAtlas (m : S.Region) :
    S.dom m ∈ IsManifold.maximalAtlas (𝓡∂ (8 + k + 1)) ∞ S.A := by
  by_cases h : S.bigCase m
  · simpa only [dom, dif_pos h] using S.chartI_maximalAtlas m h
  · simpa only [dom, dif_neg h] using S.chartII_maximalAtlas m h

theorem mem_dom_source (m : S.Region) : m.1 ∈ (S.dom m).source := by
  by_cases h : S.bigCase m
  · simpa only [dom, dif_pos h] using S.mem_chartI_source m h
  · simpa only [dom, dif_neg h] using S.mem_chartII_source m h

theorem dom_subset_region (m : S.Region) (h : S.bigCase m) :
    (S.dom m).source ⊆ {y : S.A | S.Φ y ≤ 0} := by
  simpa only [dom, dif_pos h] using S.chartI_source_subset m h

theorem dom_eq_chartI (m : S.Region) (h : S.bigCase m) : S.dom m = S.chartI m h := by
  simp only [dom, dif_pos h]

theorem dom_eq_chartII (m : S.Region) (h : ¬ S.bigCase m) : S.dom m = S.chartII m h := by
  simp only [dom, dif_neg h]

theorem off_eq (m : S.Region) (h : ¬ S.bigCase m) :
    S.off m = (S.chartII m h).extend (𝓡∂ (8 + k + 1)) m.1 := by
  simp only [off, dif_neg h]

theorem lin_eq (m : S.Region) (h : ¬ S.bigCase m) : S.lin m = S.linII m h := by
  simp only [lin, dif_neg h]

theorem lin_eq_big (m : S.Region) (h : S.bigCase m) :
    S.lin m = ContinuousLinearEquiv.refl ℝ (Mod k) := by
  simp only [lin, dif_pos h]

theorem off_eq_big (m : S.Region) (h : S.bigCase m) : S.off m = 0 := by
  simp only [off, dif_pos h]

/-- The underlying vector of the chart of the region at `m`, evaluated at `w`. -/
noncomputable def chartVec (m : S.Region) (w : S.A) : Mod k :=
  S.lin m ((S.dom m).extend (𝓡∂ (8 + k + 1)) w - S.off m)

/-- In the `bigCase`, the chart vector is the ambient chart value. -/
theorem chartVec_of_bigCase (m : S.Region) (h : S.bigCase m) (w : S.A) :
    S.chartVec m w = ((S.dom m).extend (𝓡∂ (8 + k + 1))) w := by
  rw [chartVec, S.lin_eq_big m h, ContinuousLinearEquiv.refl_apply, off, dif_pos h, sub_zero]

/-- The chart vector lies in the half-space on the region. -/
theorem chartVec_nonneg (m : S.Region) {w : S.A} (hw : w ∈ (S.dom m).source)
    (hΦw : S.Φ w ≤ 0) : 0 ≤ (S.chartVec m w) 0 := by
  by_cases h : S.bigCase m
  · rw [S.chartVec_of_bigCase m h w]
    exact Work.ThomBordism.Transversality.Preimage.zero_le_extend_apply_coord (S.dom m) hw
  · have hw' : w ∈ (S.chartII m h).source := by rwa [S.dom_eq_chartII m h] at hw
    rw [chartVec, S.dom_eq_chartII m h, S.lin_eq m h, S.off_eq m h]
    exact (S.chartII_iff m h w hw').mp hΦw

/-- The chart vector determines the value of `Φ`. -/
theorem le_of_chartVec_nonneg (m : S.Region) {w : S.A} (hw : w ∈ (S.dom m).source)
    (h : 0 ≤ (S.chartVec m w) 0) : S.Φ w ≤ 0 := by
  by_cases hb : S.bigCase m
  · exact S.dom_subset_region m hb hw
  · have hw' : w ∈ (S.chartII m hb).source := by rwa [S.dom_eq_chartII m hb] at hw
    rw [chartVec, S.dom_eq_chartII m hb, S.lin_eq m hb, S.off_eq m hb] at h
    exact (S.chartII_iff m hb w hw').mpr h

/-- The chart vector of the base point vanishes in the interior-zero case. -/
theorem chartVec_self (m : S.Region) (h : ¬ S.bigCase m) : S.chartVec m m.1 = 0 := by
  rw [chartVec, S.dom_eq_chartII m h, S.lin_eq m h, S.off_eq m h, sub_self, map_zero]

/-- In the `bigCase`, the boundary is read off the zeroth coordinate of the chart vector. -/
theorem chartVec_coord_zero_iff_bigCase (m : S.Region) (h : S.bigCase m) :
    (S.chartVec m m.1) 0 = 0 ↔ m.1 ∈ (𝓡∂ (8 + k + 1)).boundary S.A := by
  rw [S.chartVec_of_bigCase m h m.1]
  exact (Work.ThomBordism.Transversality.Preimage.mem_boundary_iff_extend_apply_coord_eq_zero
    (m := 8 + k + 1) (S.dom_maximalAtlas m) (S.mem_dom_source m)).symm


/-- The target of the extended chart is the image of the source. -/
theorem extend_target_eq_image (m : S.Region) :
    ((S.dom m).extend (𝓡∂ (8 + k + 1))).target
      = ((S.dom m).extend (𝓡∂ (8 + k + 1))) '' (S.dom m).source := by
  have h := PartialEquiv.image_source_eq_target ((S.dom m).extend (𝓡∂ (8 + k + 1)))
  rw [OpenPartialHomeomorph.extend_source (I := 𝓡∂ (8 + k + 1)) (f := S.dom m)] at h
  exact h.symm

/-- The image of the source of the ambient chart, packaged so that no `isOpenMap` is needed: `v`
lies in the image of the chart iff the corresponding ambient point is a chart value. -/
noncomputable def chartImageSet (m : S.Region) : Set (Mod k) :=
  {v : Mod k | (S.lin m).symm (v + (S.lin m) (S.off m))
    ∈ ((S.dom m).extend (𝓡∂ (8 + k + 1))) '' (S.dom m).source}

/-- The target of the chart of the region at `m`. -/
noncomputable def chartTarget (m : S.Region) : Set (Half k) :=
  {u : Half k | u.1 ∈ S.chartImageSet m}

/-- The ambient point whose chart vector is `u`. -/
noncomputable def chartInvVal (m : S.Region) (u : Half k) : S.A :=
  ((S.dom m).extend (𝓡∂ (8 + k + 1))).symm ((S.lin m).symm (u.1 + (S.lin m) (S.off m)))

theorem mem_target_extend_of_mem_image (m : S.Region) {v : Mod k}
    (hv : v ∈ ((S.dom m).extend (𝓡∂ (8 + k + 1))) '' (S.dom m).source) :
    v ∈ ((S.dom m).extend (𝓡∂ (8 + k + 1))).target := by
  rw [S.extend_target_eq_image m]
  exact hv

theorem chartVec_mem_chartImageSet (m : S.Region) {w : S.A} (hw : w ∈ (S.dom m).source) :
    S.chartVec m w ∈ S.chartImageSet m := by
  have h : (S.lin m).symm ((S.lin m) (((S.dom m).extend (𝓡∂ (8 + k + 1))) w - S.off m)
      + (S.lin m) (S.off m)) = ((S.dom m).extend (𝓡∂ (8 + k + 1))) w := by
    rw [← map_add, sub_add_cancel, ContinuousLinearEquiv.symm_apply_apply]
  show (S.lin m).symm (S.chartVec m w + (S.lin m) (S.off m))
    ∈ ((S.dom m).extend (𝓡∂ (8 + k + 1))) '' (S.dom m).source
  rw [chartVec, h]
  exact ⟨w, hw, rfl⟩

theorem chartInvVal_mem_source (m : S.Region) {u : Half k} (hu : u ∈ S.chartTarget m) :
    S.chartInvVal m u ∈ (S.dom m).source := by
  have hz := S.mem_target_extend_of_mem_image m (v := (S.lin m).symm (u.1 + (S.lin m) (S.off m))) hu
  have h := PartialEquiv.map_target ((S.dom m).extend (𝓡∂ (8 + k + 1))) hz
  rw [OpenPartialHomeomorph.extend_source (I := 𝓡∂ (8 + k + 1)) (f := S.dom m)] at h
  exact h

theorem chartVec_chartInvVal (m : S.Region) {u : Half k} (hu : u ∈ S.chartTarget m) :
    S.chartVec m (S.chartInvVal m u) = u.1 := by
  have hz := S.mem_target_extend_of_mem_image m (v := (S.lin m).symm (u.1 + (S.lin m) (S.off m))) hu
  have h1 : ((S.dom m).extend (𝓡∂ (8 + k + 1))) (S.chartInvVal m u)
      = (S.lin m).symm (u.1 + (S.lin m) (S.off m)) :=
    PartialEquiv.right_inv _ hz
  rw [chartVec, h1, map_sub, ContinuousLinearEquiv.apply_symm_apply]
  abel

theorem chartInvVal_mem_region (m : S.Region) {u : Half k} (hu : u ∈ S.chartTarget m) :
    S.Φ (S.chartInvVal m u) ≤ 0 :=
  S.le_of_chartVec_nonneg m (S.chartInvVal_mem_source m hu)
    (by rw [S.chartVec_chartInvVal m hu]; exact u.2)

/-- The image of the source of a maximal-atlas chart, when the source lies in the interior. -/
theorem isOpen_extend_image_source (m : S.Region)
    (hint : (S.dom m).source ⊆ (𝓡∂ (8 + k + 1)).interior S.A) :
    IsOpen (((S.dom m).extend (𝓡∂ (8 + k + 1))) '' (S.dom m).source) := by
  obtain ⟨W, hWopen, hW⟩ :=
    Work.ThomBordism.Transversality.Preimage.exists_isOpen_extend_target (e := S.dom m)
  have hpos : ∀ x ∈ ((S.dom m).extend (𝓡∂ (8 + k + 1))) '' (S.dom m).source, 0 < x 0 := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hinty : y ∈ (𝓡∂ (8 + k + 1)).interior S.A := hint hy
    have h1 : ((S.dom m).extend (𝓡∂ (8 + k + 1))) y
        ∈ interior (((S.dom m).extend (𝓡∂ (8 + k + 1))).target) :=
      (Work.ThomBordism.Transversality.Preimage.isInteriorPoint_iff_of_mem_maximalAtlas
        (n := (∞ : WithTop ℕ∞)) (by simp) (S.dom_maximalAtlas m) hy).mp hinty
    have htarget : ((S.dom m).extend (𝓡∂ (8 + k + 1))).target
        ⊆ range (𝓡∂ (8 + k + 1)) := by
      rw [S.extend_target_eq_image m]
      refine subset_trans (image_subset_range _ _) ?_
      rw [OpenPartialHomeomorph.extend_coe (I := 𝓡∂ (8 + k + 1)) (f := S.dom m)]
      exact Set.range_comp_subset_range _ _
    have h2 := interior_mono htarget h1
    rw [interior_range_modelWithCornersEuclideanHalfSpace] at h2
    exact h2
  have hsub : ((S.dom m).extend (𝓡∂ (8 + k + 1))) '' (S.dom m).source
      ⊆ interior (range (𝓡∂ (8 + k + 1))) := by
    intro x hx
    rw [interior_range_modelWithCornersEuclideanHalfSpace]
    exact hpos x hx
  have hWim : ((S.dom m).extend (𝓡∂ (8 + k + 1))) '' (S.dom m).source
      = W ∩ range (𝓡∂ (8 + k + 1)) := by
    rw [← S.extend_target_eq_image m]
    exact hW
  rw [hWim]
  have hEq : W ∩ range (𝓡∂ (8 + k + 1)) = W ∩ interior (range (𝓡∂ (8 + k + 1))) := by
    refine Subset.antisymm (fun x hx => ⟨hx.1, hsub ?_⟩)
      (fun x hx => ⟨hx.1, interior_subset hx.2⟩)
    rw [hWim]
    exact hx
  rw [hEq]
  exact hWopen.inter isOpen_interior

theorem isOpen_chartTarget (m : S.Region) : IsOpen (S.chartTarget m) := by
  by_cases h : S.bigCase m
  · have hset : S.chartImageSet m
        = ((S.dom m).extend (𝓡∂ (8 + k + 1))) '' (S.dom m).source := by
      ext v
      simp only [chartImageSet, Set.mem_setOf_eq, S.lin_eq_big m h, S.off_eq_big m h]
      simp
    obtain ⟨W, hWopen, hW⟩ :=
      Work.ThomBordism.Transversality.Preimage.exists_isOpen_extend_target (e := S.dom m)
    have hWim : ((S.dom m).extend (𝓡∂ (8 + k + 1))) '' (S.dom m).source
        = W ∩ range (𝓡∂ (8 + k + 1)) := by
      rw [← S.extend_target_eq_image m]
      exact hW
    have hfinal : S.chartTarget m = Subtype.val ⁻¹' W := by
      ext u
      simp only [chartTarget, Set.mem_setOf_eq, Set.mem_preimage, hset, hWim, Set.mem_inter_iff]
      constructor
      · intro hu; exact hu.1
      · intro hu
        exact ⟨hu, by rw [range_modelWithCornersEuclideanHalfSpace]; exact u.2⟩
    rw [hfinal]
    exact hWopen.preimage continuous_subtype_val
  · have hopen : IsOpen (((S.dom m).extend (𝓡∂ (8 + k + 1))) '' (S.dom m).source) :=
      S.isOpen_extend_image_source m (fun y hy => by
        rw [S.dom_eq_chartII m h] at hy
        exact S.chartII_source_interior m h hy)
    have hcont : Continuous fun v : Mod k => (S.lin m).symm (v + (S.lin m) (S.off m)) :=
      (S.lin m).symm.continuous.comp (continuous_id.add continuous_const)
    have h2 : IsOpen (S.chartImageSet m) := hopen.preimage hcont
    rw [chartTarget]
    exact h2.preimage continuous_subtype_val

/-- The source of the chart of the region at `m`. -/
def chartSource (m : S.Region) : Set S.Region := {w : S.Region | w.1 ∈ (S.dom m).source}

theorem isOpen_chartSource (m : S.Region) : IsOpen (S.chartSource m) :=
  (S.dom m).open_source.preimage continuous_subtype_val

theorem chartVec_self_mem_target (m : S.Region) : S.chartVec m m.1 ∈ S.chartImageSet m :=
  S.chartVec_mem_chartImageSet m (S.mem_dom_source m)

/-- **The chart of the region at `m`.** -/
noncomputable def chartAt (m : S.Region) : OpenPartialHomeomorph S.Region (Half k) where
  toFun w := if hw : w ∈ S.chartSource m then
      (⟨S.chartVec m w.1, S.chartVec_nonneg m hw w.2⟩ : Half k)
    else (⟨0, by simp⟩ : Half k)
  invFun u := if hu : u ∈ S.chartTarget m then
      (⟨S.chartInvVal m u, S.chartInvVal_mem_region m hu⟩ : S.Region)
    else m
  source := S.chartSource m
  target := S.chartTarget m
  map_source' w hw := by
    rw [dif_pos hw]
    exact S.chartVec_mem_chartImageSet m hw
  map_target' u hu := by
    rw [dif_pos hu]
    exact S.chartInvVal_mem_source m hu
  left_inv' w hw := by
    rw [dif_pos hw]
    have hmem : (⟨S.chartVec m w.1, S.chartVec_nonneg m hw w.2⟩ : Half k) ∈ S.chartTarget m :=
      S.chartVec_mem_chartImageSet m hw
    rw [dif_pos hmem]
    have hz : (S.lin m).symm (S.chartVec m w.1 + (S.lin m) (S.off m))
        = ((S.dom m).extend (𝓡∂ (8 + k + 1))) w.1 := by
      rw [chartVec, map_sub, sub_add_cancel, ContinuousLinearEquiv.symm_apply_apply]
    have hleft := PartialEquiv.left_inv ((S.dom m).extend (𝓡∂ (8 + k + 1)))
      (show w.1 ∈ ((S.dom m).extend (𝓡∂ (8 + k + 1))).source by
        simpa [OpenPartialHomeomorph.extend_source, chartSource] using hw)
    refine Subtype.ext ?_
    show ((S.dom m).extend (𝓡∂ (8 + k + 1))).symm
      ((S.lin m).symm (S.chartVec m w.1 + (S.lin m) (S.off m))) = w.1
    rw [hz]
    exact hleft
  right_inv' u hu := by
    rw [dif_pos hu]
    have hmem : (⟨S.chartInvVal m u, S.chartInvVal_mem_region m hu⟩ : S.Region)
        ∈ S.chartSource m := S.chartInvVal_mem_source m hu
    rw [dif_pos hmem]
    refine Subtype.ext ?_
    exact S.chartVec_chartInvVal m hu
  open_source := S.isOpen_chartSource m
  open_target := S.isOpen_chartTarget m
  continuousOn_toFun := by
    rw [continuousOn_iff_continuous_domRestrict]
    have h1 : Continuous (fun w : ↥(S.chartSource m) =>
        ((S.dom m).extend (𝓡∂ (8 + k + 1))) w.1.1) :=
      (OpenPartialHomeomorph.continuousOn_extend (S.dom m)).comp_continuous
        (by fun_prop)
        (fun w => by
          simp only [OpenPartialHomeomorph.extend_source]
          exact w.2)
    have h2 : Continuous (fun w : ↥(S.chartSource m) => S.chartVec m w.1.1) := by
      simp only [chartVec]
      exact (S.lin m).continuous.comp (h1.sub continuous_const)
    have haux : (S.chartSource m).domRestrict (fun w : S.Region =>
        if hw : w ∈ S.chartSource m then
          (⟨S.chartVec m w.1, S.chartVec_nonneg m hw w.2⟩ : Half k)
        else (⟨0, by simp⟩ : Half k))
        = fun w : ↥(S.chartSource m) => (⟨S.chartVec m w.1.1,
            S.chartVec_nonneg m w.2 w.1.2⟩ : Half k) := by
      funext w
      rw [Set.domRestrict_apply, dif_pos w.2]
    rw [haux]
    exact Continuous.subtype_mk h2 (fun w => S.chartVec_nonneg m w.2 w.1.2)
  continuousOn_invFun := by
    rw [continuousOn_iff_continuous_domRestrict]
    have h1 : Continuous (fun u : ↥(S.chartTarget m) =>
        (S.lin m).symm ((u.1 : Half k).1 + (S.lin m) (S.off m))) := by
      have hsub : Continuous (fun u : ↥(S.chartTarget m) => ((u.1 : Half k).1 : Mod k)) := by
        fun_prop
      exact (S.lin m).symm.continuous.comp (hsub.add continuous_const)
    have h2 : Continuous (fun u : ↥(S.chartTarget m) =>
        ((S.dom m).extend (𝓡∂ (8 + k + 1))).symm
          ((S.lin m).symm ((u.1 : Half k).1 + (S.lin m) (S.off m)))) :=
      (OpenPartialHomeomorph.continuousOn_extend_symm (S.dom m)).comp_continuous h1
        (fun u => S.mem_target_extend_of_mem_image m u.2)
    have haux : (S.chartTarget m).domRestrict (fun u : Half k =>
        if hu : u ∈ S.chartTarget m then
          (⟨S.chartInvVal m u, S.chartInvVal_mem_region m hu⟩ : S.Region)
        else m)
        = fun u : ↥(S.chartTarget m) =>
          (⟨S.chartInvVal m u.1, S.chartInvVal_mem_region m u.2⟩ : S.Region) := by
      funext u
      rw [Set.domRestrict_apply, dif_pos u.2]
    rw [haux]
    exact Continuous.subtype_mk h2 (fun u => S.chartInvVal_mem_region m u.2)

/-- The inverse chart map, as a `Region`-valued function. -/
noncomputable def chartInvFun (m : S.Region) (u : Half k) : S.Region :=
  if hu : u ∈ S.chartTarget m then
    (⟨S.chartInvVal m u, S.chartInvVal_mem_region m hu⟩ : S.Region)
  else m

theorem chartInvFun_of_mem (m : S.Region) {u : Half k} (hu : u ∈ S.chartTarget m) :
    S.chartInvFun m u = (⟨S.chartInvVal m u, S.chartInvVal_mem_region m hu⟩ : S.Region) :=
  dif_pos hu

theorem chartInvFun_mem_source (m : S.Region) {u : Half k} (hu : u ∈ S.chartTarget m) :
    S.chartInvFun m u ∈ S.chartSource m := by
  rw [S.chartInvFun_of_mem m hu]
  exact S.chartInvVal_mem_source m hu

theorem chartInvVal_spec (m : S.Region) {u : Half k} (hu : u ∈ S.chartTarget m) :
    ((S.dom m).extend (𝓡∂ (8 + k + 1))) (S.chartInvVal m u)
      = (S.lin m).symm (u.1 + (S.lin m) (S.off m)) :=
  PartialEquiv.right_inv _ (S.mem_target_extend_of_mem_image m hu)

theorem chartAt_symm_apply (m : S.Region) (u : Half k) :
    (S.chartAt m).symm u = S.chartInvFun m u := rfl

theorem chartAt_apply_of_mem (m : S.Region) {w : S.Region} (hw : w ∈ S.chartSource m) :
    S.chartAt m w = (⟨S.chartVec m w.1, S.chartVec_nonneg m hw w.2⟩ : Half k) := by
  change (if hw' : w ∈ S.chartSource m then
      (⟨S.chartVec m w.1, S.chartVec_nonneg m hw' w.2⟩ : Half k)
    else (⟨0, by simp⟩ : Half k)) = _
  rw [dif_pos hw]

theorem chartAt_trans_apply (m m' : S.Region) (u : Half k) :
    ((S.chartAt m).symm ≫ₕ (S.chartAt m')) u = S.chartAt m' (S.chartInvFun m u) := by
  rw [OpenPartialHomeomorph.trans_apply, S.chartAt_symm_apply m]

/-- The model-level form of the transition between the charts at `m` and `m'`. -/
noncomputable def transAux (m m' : S.Region) (y : Mod k) : Mod k :=
  (S.lin m') (((S.dom m').extend (𝓡∂ (8 + k + 1)))
      (((S.dom m).extend (𝓡∂ (8 + k + 1))).symm
        ((S.lin m).symm (y + (S.lin m) (S.off m)))) - S.off m')

/-- The set on which the model-level transition is defined. -/
def transSource (m m' : S.Region) : Set (Mod k) :=
  {y : Mod k | (S.lin m).symm (y + (S.lin m) (S.off m))
    ∈ ((𝓡∂ (8 + k + 1)).extendCoordChange (S.dom m) (S.dom m')).source}

theorem contDiffOn_transAux (m m' : S.Region) :
    ContDiffOn ℝ ∞ (S.transAux m m') (S.transSource m m') := by
  have h1 : ContDiffOn ℝ ∞ (fun y : Mod k => (S.lin m).symm (y + (S.lin m) (S.off m))) univ :=
    (S.lin m).symm.contDiff.fun_comp_contDiffOn (contDiffOn_id.add contDiffOn_const)
  have h2 : ContDiffOn ℝ ∞ (fun x : Mod k => ((S.dom m').extend (𝓡∂ (8 + k + 1)))
      (((S.dom m).extend (𝓡∂ (8 + k + 1))).symm x))
      ((𝓡∂ (8 + k + 1)).extendCoordChange (S.dom m) (S.dom m')).source :=
    contDiffOn_extendCoordChange (S.dom_maximalAtlas m) (S.dom_maximalAtlas m')
  have h3 : ContDiffOn ℝ ∞ (fun y : Mod k => ((S.dom m').extend (𝓡∂ (8 + k + 1)))
      (((S.dom m).extend (𝓡∂ (8 + k + 1))).symm
        ((S.lin m).symm (y + (S.lin m) (S.off m))))) (S.transSource m m') :=
    h2.comp (h1.mono (Set.subset_univ _)) (fun y hy => hy)
  have h4 : ContDiffOn ℝ ∞ (fun y : Mod k => ((S.dom m').extend (𝓡∂ (8 + k + 1)))
      (((S.dom m).extend (𝓡∂ (8 + k + 1))).symm
        ((S.lin m).symm (y + (S.lin m) (S.off m)))) - S.off m') (S.transSource m m') :=
    h3.sub contDiffOn_const
  exact (S.lin m').contDiff.fun_comp_contDiffOn h4

theorem symm_val_of_mem_range {y : Mod k} (hy : y ∈ range (𝓡∂ (8 + k + 1))) :
    ((𝓡∂ (8 + k + 1)).symm y).1 = y := by
  rw [range_modelWithCornersEuclideanHalfSpace] at hy
  rw [modelWithCornersEuclideanHalfSpace_symm_apply_of_le hy]

theorem transAux_eq_chartAt_trans (m m' : S.Region) {y : Mod k}
    (hy : y ∈ range (𝓡∂ (8 + k + 1))) (hct : (𝓡∂ (8 + k + 1)).symm y ∈ S.chartTarget m)
    (hcs : S.chartInvFun m ((𝓡∂ (8 + k + 1)).symm y) ∈ S.chartSource m') :
    S.transAux m m' y = (𝓡∂ (8 + k + 1))
      (((S.chartAt m).symm ≫ₕ (S.chartAt m')) ((𝓡∂ (8 + k + 1)).symm y)) := by
  have hT : ((S.chartAt m).symm ≫ₕ (S.chartAt m')) ((𝓡∂ (8 + k + 1)).symm y)
      = (⟨S.chartVec m' (S.chartInvFun m ((𝓡∂ (8 + k + 1)).symm y)).1,
          S.chartVec_nonneg m' hcs (S.chartInvFun m ((𝓡∂ (8 + k + 1)).symm y)).2⟩ : Half k) := by
    rw [S.chartAt_trans_apply m m']
    exact S.chartAt_apply_of_mem m' hcs
  have hkey : ((S.dom m).extend (𝓡∂ (8 + k + 1))).symm
        ((S.lin m).symm (y + (S.lin m) (S.off m)))
      = (S.chartInvFun m ((𝓡∂ (8 + k + 1)).symm y)).1 := by
    rw [show (S.chartInvFun m ((𝓡∂ (8 + k + 1)).symm y)).1
      = S.chartInvVal m ((𝓡∂ (8 + k + 1)).symm y) from
        congrArg Subtype.val (S.chartInvFun_of_mem m hct)]
    rw [chartInvVal, symm_val_of_mem_range hy]
  rw [hT, modelWithCornersEuclideanHalfSpace_apply]
  show S.transAux m m' y = (S.lin m') (((S.dom m').extend (𝓡∂ (8 + k + 1)))
      (S.chartInvFun m ((𝓡∂ (8 + k + 1)).symm y)).1 - S.off m')
  rw [transAux, hkey]

theorem contDiffOn_chartAt_trans (m m' : S.Region) :
    ContDiffOn ℝ ∞ (fun y : Mod k => (𝓡∂ (8 + k + 1))
      (((S.chartAt m).symm ≫ₕ (S.chartAt m')) ((𝓡∂ (8 + k + 1)).symm y)))
      ((𝓡∂ (8 + k + 1)).symm ⁻¹' ((S.chartAt m).symm ≫ₕ (S.chartAt m')).source
        ∩ range (𝓡∂ (8 + k + 1))) := by
  set Sset : Set (Mod k) := (𝓡∂ (8 + k + 1)).symm ⁻¹'
      ((S.chartAt m).symm ≫ₕ (S.chartAt m')).source ∩ range (𝓡∂ (8 + k + 1)) with hSset
  have hct_of : ∀ y ∈ Sset, (𝓡∂ (8 + k + 1)).symm y ∈ S.chartTarget m := by
    intro y hy
    have h := hy.1
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source] at h
    exact h.1
  have hcs_of : ∀ y ∈ Sset, S.chartInvFun m ((𝓡∂ (8 + k + 1)).symm y) ∈ S.chartSource m' := by
    intro y hy
    have h := hy.1
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source] at h
    exact h.2
  have hsub : Sset ⊆ S.transSource m m' := by
    intro y hy
    have hct := hct_of y hy
    have hcs := hcs_of y hy
    show (S.lin m).symm (y + (S.lin m) (S.off m))
      ∈ ((𝓡∂ (8 + k + 1)).extendCoordChange (S.dom m) (S.dom m')).source
    rw [show ((𝓡∂ (8 + k + 1)).extendCoordChange (S.dom m) (S.dom m')).source
        = ((S.dom m).extend (𝓡∂ (8 + k + 1))) ''
            ((S.dom m).source ∩ (S.dom m').source)
      from (OpenPartialHomeomorph.extend_image_source_inter
        (I := 𝓡∂ (8 + k + 1)) (S.dom m) (S.dom m')).symm]
    refine ⟨S.chartInvFun m ((𝓡∂ (8 + k + 1)).symm y),
      ⟨(S.chartInvFun_mem_source m hct), (hcs : (S.chartInvFun m _).1 ∈ (S.dom m').source)⟩, ?_⟩
    rw [show (S.chartInvFun m ((𝓡∂ (8 + k + 1)).symm y)).1
        = S.chartInvVal m ((𝓡∂ (8 + k + 1)).symm y) from
          congrArg Subtype.val (S.chartInvFun_of_mem m hct)]
    rw [S.chartInvVal_spec m hct, symm_val_of_mem_range hy.2]
  have heq : ∀ y ∈ Sset, S.transAux m m' y = (𝓡∂ (8 + k + 1))
      (((S.chartAt m).symm ≫ₕ (S.chartAt m')) ((𝓡∂ (8 + k + 1)).symm y)) :=
    fun y hy => S.transAux_eq_chartAt_trans m m' hy.2 (hct_of y hy) (hcs_of y hy)
  exact ((S.contDiffOn_transAux m m').mono hsub).congr (fun y hy => (heq y hy).symm)

/-- The charted space structure on the region. -/
noncomputable def chartedSpaceOfRegion : ChartedSpace (Half k) S.Region where
  atlas := Set.range (S.chartAt)
  chartAt := S.chartAt
  mem_chart_source m := S.mem_dom_source m
  chart_mem_atlas m := ⟨m, rfl⟩

attribute [instance] chartedSpaceOfRegion

/-- The smooth structure on the region. -/
theorem isManifoldOfRegion : IsManifold (𝓡∂ (8 + k + 1)) ∞ S.Region := by
  refine isManifold_of_contDiffOn (𝓡∂ (8 + k + 1)) ∞ S.Region (fun e e' he he' => ?_)
  obtain ⟨m, rfl⟩ := he
  obtain ⟨m', rfl⟩ := he'
  exact S.contDiffOn_chartAt_trans m m'

/-- The region is compact. -/
theorem compactSpaceOfRegion : CompactSpace S.Region :=
  isCompact_iff_compactSpace.mp S.hK

attribute [instance] isManifoldOfRegion compactSpaceOfRegion

/-- The boundary of the region is the part of `∂A ∪ {Φ = 0}` lying in the region. -/
theorem mem_boundary_iff (m : S.Region) :
    m ∈ (𝓡∂ (8 + k + 1)).boundary S.Region ↔
      (m.1 ∈ (𝓡∂ (8 + k + 1)).boundary S.A ∨ S.Φ m.1 = 0) := by
  have he : S.chartAt m ∈ IsManifold.maximalAtlas (𝓡∂ (8 + k + 1)) ∞ S.Region :=
    IsManifold.chart_mem_maximalAtlas m
  rw [Work.ThomBordism.Transversality.Preimage.mem_boundary_iff_extend_apply_coord_eq_zero
    (m := 8 + k + 1) he (mem_chart_source (Half k) m)]
  have hval : ((S.chartAt m).extend (𝓡∂ (8 + k + 1))) m = S.chartVec m m.1 := by
    rw [OpenPartialHomeomorph.extend_coe, Function.comp_apply,
      S.chartAt_apply_of_mem m (S.mem_dom_source m), modelWithCornersEuclideanHalfSpace_apply]
  rw [hval]
  by_cases h : S.bigCase m
  · rw [S.chartVec_coord_zero_iff_bigCase m h]
    constructor
    · intro hb; exact Or.inl hb
    · rintro (hb | hb)
      · exact hb
      · exact h.resolve_right (by rw [hb]; exact lt_irrefl 0)
  · rw [S.chartVec_self m h]
    constructor
    · intro _; exact Or.inr (S.zero_of_not_bigCase m h)
    · intro _; rfl

/-- The value of the ambient chart of the region at a point of the half-space. -/
theorem extend_symm_val (m : S.Region) {y : Mod k} (hy : y ∈ range (𝓡∂ (8 + k + 1)))
    (hct : (𝓡∂ (8 + k + 1)).symm y ∈ S.chartTarget m) :
    ((S.dom m).extend (𝓡∂ (8 + k + 1)) ∘ Subtype.val
        ∘ ((S.chartAt m).extend (𝓡∂ (8 + k + 1))).symm) y
      = (S.lin m).symm (y + (S.lin m) (S.off m)) := by
  have h2 : ((S.chartInvFun m ((𝓡∂ (8 + k + 1)).symm y)).1 : S.A)
      = S.chartInvVal m ((𝓡∂ (8 + k + 1)).symm y) :=
    congrArg Subtype.val (S.chartInvFun_of_mem m hct)
  show ((S.dom m).extend (𝓡∂ (8 + k + 1))) ((S.chartInvFun m
    ((𝓡∂ (8 + k + 1)).symm y)).1)
      = (S.lin m).symm (y + (S.lin m) (S.off m))
  rw [h2, S.chartInvVal_spec m hct, symm_val_of_mem_range hy]

/-- The preimage of the target of the chart at `m` is a neighbourhood of the base point within the
half-space. -/
theorem chartTarget_mem_nhdsWithin (m : S.Region) :
    (𝓡∂ (8 + k + 1)).symm ⁻¹' S.chartTarget m ∈
      𝓝[range (𝓡∂ (8 + k + 1))] (((S.chartAt m).extend (𝓡∂ (8 + k + 1))) m) := by
  obtain ⟨W, hWopen, hW⟩ := isOpen_induced_iff.mp (S.isOpen_chartTarget m)
  have hmemW : ((S.chartAt m) m) ∈ Subtype.val ⁻¹' W := by
    rw [hW]
    exact (S.chartAt m).map_source (mem_chart_source (Half k) m)
  have hxW : ((S.chartAt m).extend (𝓡∂ (8 + k + 1))) m ∈ W := by
    rw [OpenPartialHomeomorph.extend_coe, Function.comp_apply,
      modelWithCornersEuclideanHalfSpace_apply]
    exact hmemW
  refine mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr ⟨W, hWopen.mem_nhds hxW, ?_⟩
  rintro y ⟨hyW, hyI⟩
  rw [Set.mem_preimage, ← hW, Set.mem_preimage,
    show (((𝓡∂ (8 + k + 1)).symm y : Half k)).1 = y from symm_val_of_mem_range hyI]
  exact hyW

/-- **The inclusion of the region in the ambient manifold is smooth.** -/
theorem contMDiff_val : ContMDiff (𝓡∂ (8 + k + 1)) (𝓡∂ (8 + k + 1)) ∞
    (fun m : S.Region => m.1) := by
  intro m
  have hxI : ((S.chartAt m).extend (𝓡∂ (8 + k + 1))) m ∈ range (𝓡∂ (8 + k + 1)) :=
    ⟨(S.chartAt m) m, rfl⟩
  have h2 : (𝓡∂ (8 + k + 1)).symm (((S.chartAt m).extend (𝓡∂ (8 + k + 1))) m)
      = (S.chartAt m) m := by
    show (𝓡∂ (8 + k + 1)).symm ((𝓡∂ (8 + k + 1)) ((S.chartAt m) m)) = (S.chartAt m) m
    exact ModelWithCorners.left_inv (𝓡∂ (8 + k + 1)) ((S.chartAt m) m)
  have hxct : (𝓡∂ (8 + k + 1)).symm (((S.chartAt m).extend (𝓡∂ (8 + k + 1))) m)
      ∈ S.chartTarget m := by
    rw [h2]
    exact (S.chartAt m).map_source (mem_chart_source (Half k) m)
  rw [contMDiffAt_iff_of_mem_maximalAtlas
    (IsManifold.chart_mem_maximalAtlas (I := 𝓡∂ (8 + k + 1)) m) (S.dom_maximalAtlas m)
    (mem_chart_source (Half k) m) (S.mem_dom_source m)]
  refine ⟨continuous_subtype_val.continuousAt, ?_⟩
  have haff : ContDiff ℝ ∞ (fun y : Mod k => (S.lin m).symm (y + (S.lin m) (S.off m))) :=
    (S.lin m).symm.contDiff.comp (contDiff_id.add contDiff_const)
  refine (haff.contDiffWithinAt).congr_of_eventuallyEq ?_ ?_
  · refine Filter.eventuallyEq_iff_exists_mem.mpr
      ⟨range (𝓡∂ (8 + k + 1)) ∩ ((𝓡∂ (8 + k + 1)).symm ⁻¹' S.chartTarget m), ?_, ?_⟩
    · exact Filter.inter_mem self_mem_nhdsWithin (S.chartTarget_mem_nhdsWithin m)
    · intro y hy
      exact S.extend_symm_val m hy.1 hy.2
  · exact S.extend_symm_val m hxI hxct

/-- The inclusion of the region in the ambient manifold is smooth, on any set. -/
theorem contMDiffOn_val (W : Set S.A) :
    ContMDiffOn (𝓡∂ (8 + k + 1)) (𝓡∂ (8 + k + 1)) ∞ (fun m : S.Region => m.1)
      {m : S.Region | m.1 ∈ W} :=
  S.contMDiff_val.contMDiffOn

/-- **Post-composition with the inclusion of the region.** -/
theorem contMDiffOn_comp_val (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : S.A → F) (W : Set S.A)
    (hf : ContMDiffOn (𝓡∂ (8 + k + 1)) (𝓘(ℝ, F)) ∞ f W) :
    ContMDiffOn (𝓡∂ (8 + k + 1)) (𝓘(ℝ, F)) ∞ (fun m : S.Region => f m.1)
      {m : S.Region | m.1 ∈ W} :=
  hf.comp (S.contMDiffOn_val W) (fun _ hm => hm)

/-- The region is a `T2` space. -/
theorem t2SpaceOfRegion : T2Space S.Region := inferInstance

attribute [instance] t2SpaceOfRegion


/-- The source of the pullback chart of an ambient chart `φ`: the points of the region whose
underlying point lies in the source of `φ` and at which `Φ < 0`. -/
def pullSource (φ : OpenPartialHomeomorph S.A (Half k)) : Set S.Region :=
  {w : S.Region | w.1 ∈ φ.source ∧ S.Φ w.1 < 0}

/-- The target of the pullback chart of `φ`. -/
def pullTarget (φ : OpenPartialHomeomorph S.A (Half k)) : Set (Half k) :=
  φ '' {y : S.A | y ∈ φ.source ∧ S.Φ y < 0}

theorem isOpen_pullSource (φ : OpenPartialHomeomorph S.A (Half k)) :
    IsOpen (S.pullSource φ) :=
  (((φ.open_source).inter (S.hΦ.continuous.isOpen_preimage _ isOpen_Iio)).preimage
    continuous_subtype_val)

theorem pullTarget_subset_target (φ : OpenPartialHomeomorph S.A (Half k)) :
    S.pullTarget φ ⊆ φ.target := by
  rintro u ⟨y, hy, rfl⟩
  exact φ.map_source hy.1

theorem isOpen_pullTarget (φ : OpenPartialHomeomorph S.A (Half k)) :
    IsOpen (S.pullTarget φ) :=
  (φ.isOpen_image_iff_of_subset_source (fun y hy => hy.1)).mpr
    ((φ.open_source).inter (S.hΦ.continuous.isOpen_preimage _ isOpen_Iio))

/-- The ambient point underlying the inverse of the pullback chart. -/
noncomputable def pullInvVal (m : S.Region) (φ : OpenPartialHomeomorph S.A (Half k))
    (u : Half k) : S.A :=
  if hu : u ∈ S.pullTarget φ then φ.symm u else m.1

theorem pullInvVal_of_mem (m : S.Region) (φ : OpenPartialHomeomorph S.A (Half k)) {u : Half k}
    (hu : u ∈ S.pullTarget φ) : S.pullInvVal m φ u = φ.symm u :=
  dif_pos hu

theorem pullInvVal_mem_source (m : S.Region) (φ : OpenPartialHomeomorph S.A (Half k))
    {u : Half k} (hu : u ∈ S.pullTarget φ) : S.pullInvVal m φ u ∈ φ.source := by
  rw [S.pullInvVal_of_mem m φ hu]
  obtain ⟨y, hy, hyu⟩ := hu
  have hsymm : φ.symm u = y := by
    rw [← hyu]
    exact PartialEquiv.left_inv (φ.toPartialEquiv) hy.1
  rw [hsymm]
  exact hy.1

theorem pullInvVal_mem_neg (m : S.Region) (φ : OpenPartialHomeomorph S.A (Half k))
    {u : Half k} (hu : u ∈ S.pullTarget φ) : S.Φ (S.pullInvVal m φ u) < 0 := by
  rw [S.pullInvVal_of_mem m φ hu]
  obtain ⟨y, hy, hyu⟩ := hu
  have hsymm : φ.symm u = y := by
    rw [← hyu]
    exact PartialEquiv.left_inv (φ.toPartialEquiv) hy.1
  rw [hsymm]
  exact hy.2

theorem pullInvVal_mem_region (m : S.Region) (φ : OpenPartialHomeomorph S.A (Half k))
    {u : Half k} (hu : u ∈ S.pullTarget φ) : S.Φ (S.pullInvVal m φ u) ≤ 0 :=
  le_of_lt (S.pullInvVal_mem_neg m φ hu)

/-- The inverse of the pullback chart, as a `Region`-valued function. -/
noncomputable def pullInvFun (m : S.Region) (φ : OpenPartialHomeomorph S.A (Half k))
    (u : Half k) : S.Region :=
  if hu : u ∈ S.pullTarget φ then
    (⟨S.pullInvVal m φ u, S.pullInvVal_mem_region m φ hu⟩ : S.Region)
  else m

theorem pullInvFun_of_mem (m : S.Region) (φ : OpenPartialHomeomorph S.A (Half k)) {u : Half k}
    (hu : u ∈ S.pullTarget φ) :
    S.pullInvFun m φ u
      = (⟨S.pullInvVal m φ u, S.pullInvVal_mem_region m φ hu⟩ : S.Region) :=
  dif_pos hu

theorem pullInvFun_mem_source (m : S.Region) (φ : OpenPartialHomeomorph S.A (Half k))
    {u : Half k} (hu : u ∈ S.pullTarget φ) : S.pullInvFun m φ u ∈ S.pullSource φ := by
  rw [S.pullInvFun_of_mem m φ hu]
  exact ⟨S.pullInvVal_mem_source m φ hu, S.pullInvVal_mem_neg m φ hu⟩

/-- **The pullback chart** of an ambient chart `φ` to the region: on the points of the region where
`Φ < 0` and which lie in the source of `φ`, it is `φ` itself. -/
noncomputable def pullChart (m : S.Region) (φ : OpenPartialHomeomorph S.A (Half k)) :
    OpenPartialHomeomorph S.Region (Half k) where
  toFun w := φ w.1
  invFun := S.pullInvFun m φ
  source := S.pullSource φ
  target := S.pullTarget φ
  map_source' w hw := by
    have hw' : w.1 ∈ φ.source ∧ S.Φ w.1 < 0 := hw
    exact ⟨w.1, hw', rfl⟩
  map_target' u hu := S.pullInvFun_mem_source m φ hu
  left_inv' w hw := by
    have hw' : w.1 ∈ φ.source ∧ S.Φ w.1 < 0 := hw
    have hu : φ w.1 ∈ S.pullTarget φ := ⟨w.1, hw', rfl⟩
    have h1 : (S.pullInvFun m φ (φ w.1)).1 = S.pullInvVal m φ (φ w.1) :=
      congrArg Subtype.val (S.pullInvFun_of_mem m φ hu)
    refine Subtype.ext ?_
    rw [h1, S.pullInvVal_of_mem m φ hu]
    exact PartialEquiv.left_inv (φ.toPartialEquiv) hw'.1
  right_inv' u hu := by
    have h1 : (S.pullInvFun m φ u).1 = S.pullInvVal m φ u :=
      congrArg Subtype.val (S.pullInvFun_of_mem m φ hu)
    rw [h1, S.pullInvVal_of_mem m φ hu]
    obtain ⟨y, hy, hyu⟩ := hu
    have hsymm : φ.symm u = y := by
      rw [← hyu]
      exact PartialEquiv.left_inv (φ.toPartialEquiv) hy.1
    rw [hsymm]
    exact hyu
  open_source := S.isOpen_pullSource φ
  open_target := S.isOpen_pullTarget φ
  continuousOn_toFun := by
    rw [continuousOn_iff_continuous_domRestrict]
    have h1 : Continuous (fun w : ↥(S.pullSource φ) => φ w.1.1) :=
      (φ.continuousOn_toFun).comp_continuous (by fun_prop) (fun w => w.2.1)
    have haux : (S.pullSource φ).domRestrict (fun w : S.Region => φ w.1)
        = fun w : ↥(S.pullSource φ) => φ w.1.1 := rfl
    rw [haux]
    exact h1
  continuousOn_invFun := by
    rw [continuousOn_iff_continuous_domRestrict]
    have haux : (S.pullTarget φ).domRestrict (S.pullInvFun m φ)
        = fun u : ↥(S.pullTarget φ) =>
          (⟨S.pullInvVal m φ u.1, S.pullInvVal_mem_region m φ u.2⟩ : S.Region) := by
      funext u
      rw [Set.domRestrict_apply, S.pullInvFun_of_mem m φ u.2]
    rw [haux]
    refine Continuous.subtype_mk ?_ _
    rw [show (fun u : ↥(S.pullTarget φ) => S.pullInvVal m φ u.1)
        = (fun u : ↥(S.pullTarget φ) => φ.symm u.1) from
      funext fun u => S.pullInvVal_of_mem m φ u.2]
    exact (φ.continuousOn_symm.mono (S.pullTarget_subset_target φ)).comp_continuous
      (by fun_prop) (fun u => u.2)

theorem pullChart_apply_of_mem (m : S.Region) (φ : OpenPartialHomeomorph S.A (Half k))
    {w : S.Region} (hw : w ∈ S.pullSource φ) : S.pullChart m φ w = φ w.1 := rfl

theorem pullChart_symm_apply (m : S.Region) (φ : OpenPartialHomeomorph S.A (Half k))
    (u : Half k) : (S.pullChart m φ).symm u = S.pullInvFun m φ u := rfl

/-- The value of the extended region chart on its source. -/
theorem chartAt_extend_apply (m : S.Region) {w : S.Region} (hw : w ∈ S.chartSource m) :
    ((S.chartAt m).extend (𝓡∂ (8 + k + 1))) w = S.chartVec m w.1 := by
  rw [OpenPartialHomeomorph.extend_coe, Function.comp_apply, S.chartAt_apply_of_mem m hw,
    modelWithCornersEuclideanHalfSpace_apply]

/-- The extended region chart at `m'`, evaluated at the inverse of the pullback chart of `φ`
(which lies in `m'`'s chart source). -/
theorem pullChart_symm_extend_eq (m : S.Region) (φ : OpenPartialHomeomorph S.A (Half k))
    (m' : S.Region) {z : EuclideanSpace ℝ (Fin (8 + k + 1))}
    (hz : (𝓡∂ (8 + k + 1)).symm z ∈ S.pullTarget φ)
    (hzsrc : φ.symm ((𝓡∂ (8 + k + 1)).symm z) ∈ (S.dom m').source) :
    ((S.chartAt m').extend (𝓡∂ (8 + k + 1)))
        (S.pullInvFun m φ ((𝓡∂ (8 + k + 1)).symm z))
      = (S.lin m') ((S.dom m').extend (𝓡∂ (8 + k + 1))
          ((φ.extend (𝓡∂ (8 + k + 1))).symm z) - S.off m') := by
  have h1 : (S.pullInvFun m φ ((𝓡∂ (8 + k + 1)).symm z)).1
      = S.pullInvVal m φ ((𝓡∂ (8 + k + 1)).symm z) :=
    congrArg Subtype.val (S.pullInvFun_of_mem m φ hz)
  have h2 : S.pullInvVal m φ ((𝓡∂ (8 + k + 1)).symm z)
      = φ.symm ((𝓡∂ (8 + k + 1)).symm z) := S.pullInvVal_of_mem m φ hz
  have hregion : S.Φ (φ.symm ((𝓡∂ (8 + k + 1)).symm z)) ≤ 0 := by
    rw [← h2]
    exact S.pullInvVal_mem_region m φ hz
  have hX : S.pullInvFun m φ ((𝓡∂ (8 + k + 1)).symm z)
      = (⟨φ.symm ((𝓡∂ (8 + k + 1)).symm z), hregion⟩ : S.Region) :=
    Subtype.ext (h1.trans h2)
  have hmem : (⟨φ.symm ((𝓡∂ (8 + k + 1)).symm z), hregion⟩ : S.Region)
      ∈ S.chartSource m' := hzsrc
  rw [hX, S.chartAt_extend_apply m' hmem]
  rfl

/-- **The pullback chart of a chart of the maximal atlas of `A` is a chart of the maximal atlas of
the region**: both it and its inverse are smooth. -/
theorem pullChart_mem_maximalAtlas (m : S.Region) (φ : OpenPartialHomeomorph S.A (Half k))
    (hφ : φ ∈ IsManifold.maximalAtlas (𝓡∂ (8 + k + 1)) ∞ S.A) :
    S.pullChart m φ ∈ IsManifold.maximalAtlas (𝓡∂ (8 + k + 1)) ∞ S.Region := by
  refine OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn _ ?_ ?_
  · have h1 : ContMDiffOn (𝓡∂ (8 + k + 1)) (𝓡∂ (8 + k + 1)) ∞
        (fun w : S.Region => φ w.1) (S.pullSource φ) :=
      (contMDiffOn_of_mem_maximalAtlas hφ).comp
        ((S.contMDiffOn_val φ.source).mono (fun w hw => hw.1))
        (fun w hw => hw.1)
    exact h1.congr (fun w _ => rfl)
  · intro u hu
    set m' : S.Region := S.pullInvFun m φ u with hm'
    have hm'val : m'.1 = S.pullInvVal m φ u :=
      congrArg Subtype.val (S.pullInvFun_of_mem m φ hu)
    have hm'φ : m'.1 ∈ φ.source := by
      rw [hm'val]
      exact S.pullInvVal_mem_source m φ hu
    have hm'dom : m'.1 ∈ (S.dom m').source := S.mem_dom_source m'
    have huφtgt : u ∈ φ.target := S.pullTarget_subset_target φ hu
    have hsymm : φ.symm u = m'.1 := by
      rw [hm'val, S.pullInvVal_of_mem m φ hu]
    have hkey : φ m'.1 = u := by
      rw [← hsymm]
      exact PartialEquiv.right_inv (φ.toPartialEquiv) huφtgt
    change ContMDiffWithinAt (𝓡∂ (8 + k + 1)) (𝓡∂ (8 + k + 1)) ∞ (S.pullInvFun m φ)
      (S.pullTarget φ) u
    rw [contMDiffWithinAt_iff_of_mem_maximalAtlas (I := 𝓡∂ (8 + k + 1))
      (I' := 𝓡∂ (8 + k + 1))
      (e := _root_.chartAt (Half k) u) (e' := S.chartAt m')
      (IsManifold.chart_mem_maximalAtlas (I := 𝓡∂ (8 + k + 1)) u)
      (IsManifold.chart_mem_maximalAtlas (I := 𝓡∂ (8 + k + 1)) m')
      (mem_chart_source (Half k) u) (mem_chart_source (Half k) m')]
    refine ⟨((S.pullChart m φ).continuousOn_invFun.continuousWithinAt hu), ?_⟩
    set z₀ : EuclideanSpace ℝ (Fin (8 + k + 1)) := extChartAt (𝓡∂ (8 + k + 1)) u u with hz₀
    have hz₀I : z₀ = (𝓡∂ (8 + k + 1)) u := by rw [hz₀, extChartAt_self_apply]
    have hz₀eq : z₀ = (φ.extend (𝓡∂ (8 + k + 1))) m'.1 := by
      rw [hz₀I, OpenPartialHomeomorph.extend_coe, Function.comp_apply, hkey]
    have hz₀src : z₀ ∈ ((𝓡∂ (8 + k + 1)).extendCoordChange φ (S.dom m')).source := by
      rw [hz₀eq, ← OpenPartialHomeomorph.extend_image_source_inter (I := 𝓡∂ (8 + k + 1))]
      exact ⟨m'.1, ⟨hm'φ, hm'dom⟩, rfl⟩
    have hS₀nhds : ((𝓡∂ (8 + k + 1)).extendCoordChange φ (S.dom m')).source
        ∈ 𝓝[range (𝓡∂ (8 + k + 1))] z₀ := by
      rw [← OpenPartialHomeomorph.extend_image_source_inter (I := 𝓡∂ (8 + k + 1)), hz₀eq,
        ← OpenPartialHomeomorph.map_extend_nhds (f := φ) (I := 𝓡∂ (8 + k + 1)) hm'φ]
      exact Filter.mem_map.mpr (Filter.mem_of_superset
        (Filter.inter_mem (φ.open_source.mem_nhds hm'φ)
          ((S.dom m').open_source.mem_nhds hm'dom))
        (fun y hy => ⟨y, hy, rfl⟩))
    have hF : ContDiffOn ℝ ∞ (fun z => (S.lin m')
        ((S.dom m').extend (𝓡∂ (8 + k + 1)) ((φ.extend (𝓡∂ (8 + k + 1))).symm z)
          - S.off m')) ((𝓡∂ (8 + k + 1)).extendCoordChange φ (S.dom m')).source := by
      have h2 : ContDiffOn ℝ ∞ (fun x : Mod k =>
          (S.dom m').extend (𝓡∂ (8 + k + 1)) ((φ.extend (𝓡∂ (8 + k + 1))).symm x))
          ((𝓡∂ (8 + k + 1)).extendCoordChange φ (S.dom m')).source :=
        contDiffOn_extendCoordChange hφ (S.dom_maximalAtlas m')
      exact (S.lin m').contDiff.fun_comp_contDiffOn (h2.sub contDiffOn_const)
    have hz₀symm : (𝓡∂ (8 + k + 1)).symm z₀ = u := by
      rw [hz₀I]
      exact (𝓡∂ (8 + k + 1)).left_inv u
    have hcont : ContinuousAt (fun z => φ.symm ((𝓡∂ (8 + k + 1)).symm z)) z₀ := by
      have h1 : ContinuousAt (fun z : EuclideanSpace ℝ (Fin (8 + k + 1)) =>
          (𝓡∂ (8 + k + 1)).symm z) z₀ :=
        (𝓡∂ (8 + k + 1)).continuous_symm.continuousAt
      have h2 : ContinuousAt (fun y : Half k => φ.symm y) ((𝓡∂ (8 + k + 1)).symm z₀) := by
        rw [hz₀symm]
        exact φ.continuousOn_symm.continuousAt (φ.open_target.mem_nhds huφtgt)
      exact h2.comp h1
    have hpt : φ.symm ((𝓡∂ (8 + k + 1)).symm z₀) ∈ (S.dom m').source := by
      rw [hz₀symm, hsymm]
      exact hm'dom
    have hV : {z : EuclideanSpace ℝ (Fin (8 + k + 1)) |
        φ.symm ((𝓡∂ (8 + k + 1)).symm z) ∈ (S.dom m').source} ∈ 𝓝 z₀ :=
      hcont.preimage_mem_nhds ((S.dom m').open_source.mem_nhds hpt)
    have hsub : ∀ z ∈ (((_root_.chartAt (Half k) u).extend (𝓡∂ (8 + k + 1))).symm
          ⁻¹' S.pullTarget φ ∩ range (𝓡∂ (8 + k + 1)))
        ∩ {z : EuclideanSpace ℝ (Fin (8 + k + 1)) |
            φ.symm ((𝓡∂ (8 + k + 1)).symm z) ∈ (S.dom m').source},
        z ∈ ((𝓡∂ (8 + k + 1)).extendCoordChange φ (S.dom m')).source := by
      rw [← OpenPartialHomeomorph.extend_image_source_inter (I := 𝓡∂ (8 + k + 1))]
      rintro z ⟨⟨hzT, hzr⟩, hzV⟩
      have hzT' : (𝓡∂ (8 + k + 1)).symm z ∈ S.pullTarget φ := hzT
      have h2 : S.pullInvVal m φ ((𝓡∂ (8 + k + 1)).symm z)
          = φ.symm ((𝓡∂ (8 + k + 1)).symm z) := S.pullInvVal_of_mem m φ hzT'
      have h1 : φ.symm ((𝓡∂ (8 + k + 1)).symm z) ∈ φ.source := by
        rw [← h2]
        exact S.pullInvVal_mem_source m φ hzT'
      have h3 : (𝓡∂ (8 + k + 1)).symm z ∈ φ.target := S.pullTarget_subset_target φ hzT'
      refine ⟨φ.symm ((𝓡∂ (8 + k + 1)).symm z), ⟨h1, hzV⟩, ?_⟩
      show (φ.extend (𝓡∂ (8 + k + 1))) (φ.symm ((𝓡∂ (8 + k + 1)).symm z)) = z
      have h3' : φ (φ.symm ((𝓡∂ (8 + k + 1)).symm z)) = (𝓡∂ (8 + k + 1)).symm z :=
        PartialEquiv.right_inv (φ.toPartialEquiv) h3
      rw [OpenPartialHomeomorph.extend_coe, Function.comp_apply, h3']
      exact (𝓡∂ (8 + k + 1)).right_inv hzr
    have hFct : ContDiffWithinAt ℝ ∞ (fun z => (S.lin m')
        ((S.dom m').extend (𝓡∂ (8 + k + 1)) ((φ.extend (𝓡∂ (8 + k + 1))).symm z)
          - S.off m')) (range (𝓡∂ (8 + k + 1))) z₀ :=
      (hF.contDiffWithinAt hz₀src).mono_of_mem_nhdsWithin hS₀nhds
    have hsubT : (((_root_.chartAt (Half k) u).extend (𝓡∂ (8 + k + 1))).symm
        ⁻¹' S.pullTarget φ ∩ range (𝓡∂ (8 + k + 1))) ⊆ range (𝓡∂ (8 + k + 1)) :=
      fun z hz => hz.2
    have hev : ∀ᶠ z in 𝓝[((_root_.chartAt (Half k) u).extend (𝓡∂ (8 + k + 1))).symm
        ⁻¹' S.pullTarget φ ∩ range (𝓡∂ (8 + k + 1))] z₀,
        φ.symm ((𝓡∂ (8 + k + 1)).symm z) ∈ (S.dom m').source :=
      Filter.Eventually.filter_mono (nhdsWithin_mono z₀ hsubT)
        (Filter.Eventually.filter_mono nhdsWithin_le_nhds hV)
    have hz₀T : (𝓡∂ (8 + k + 1)).symm z₀ ∈ S.pullTarget φ := by
      rw [hz₀symm]
      exact hu
    have hz₀src' : φ.symm ((𝓡∂ (8 + k + 1)).symm z₀) ∈ (S.dom m').source := by
      rw [hz₀symm, hsymm]
      exact hm'dom
    refine (hFct.mono hsubT).congr_of_eventuallyEq ?_ ?_
    · filter_upwards [self_mem_nhdsWithin, hev] with z hzT hzsrc
      exact S.pullChart_symm_extend_eq m φ m' hzT.1 hzsrc
    · exact S.pullChart_symm_extend_eq m φ m' hz₀T hz₀src'

/-- **Submersivity transfers to the region at interior points** (the `sub` conjunct). -/
theorem isSubmersionAt_comp_val {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : S.A → F) (m : S.Region) (hm : m ∉ (𝓡∂ (8 + k + 1)).boundary S.Region)
    (hf : IsSubmersionAt (𝓡∂ (8 + k + 1)) (𝓘(ℝ, F)) ∞ f m.1) :
    IsSubmersionAt (𝓡∂ (8 + k + 1)) (𝓘(ℝ, F)) ∞ (fun y : S.Region => f y.1) m := by
  have hnot : ¬ (m.1 ∈ (𝓡∂ (8 + k + 1)).boundary S.A ∨ S.Φ m.1 = 0) := fun h =>
    hm ((S.mem_boundary_iff m).mpr h)
  have hΦ : S.Φ m.1 < 0 := lt_of_le_of_ne m.2 (fun h => hnot (Or.inr h))
  obtain ⟨Fc, instC, instS, hfc⟩ := hf
  letI : NormedAddCommGroup Fc := instC
  letI : NormedSpace ℝ Fc := instS
  refine ⟨Fc, instC, instS, ?_⟩
  refine IsSubmersionAtOfComplement.mk_of_charts (equiv := hfc.equiv)
    (domChart := S.pullChart m hfc.domChart) (codChart := hfc.codChart)
    ⟨hfc.mem_domChart_source, hΦ⟩ hfc.mem_codChart_source
    (S.pullChart_mem_maximalAtlas m hfc.domChart hfc.domChart_mem_maximalAtlas)
    hfc.codChart_mem_maximalAtlas ?_ ?_
  · intro w hw
    exact hfc.source_subset_preimage_source hw.1
  · intro z hz
    set φ := hfc.domChart with hφ
    set ψ := hfc.codChart with hψ
    have hzr : z ∈ range (𝓡∂ (8 + k + 1)) := by
      rw [← (𝓡∂ (8 + k + 1)).target_eq]
      exact hz.1
    have hzT : (𝓡∂ (8 + k + 1)).symm z ∈ S.pullTarget φ := hz.2
    have hval : S.pullInvVal m φ ((𝓡∂ (8 + k + 1)).symm z)
        = φ.symm ((𝓡∂ (8 + k + 1)).symm z) := S.pullInvVal_of_mem m φ hzT
    have harg : (((S.pullChart m φ).extend (𝓡∂ (8 + k + 1))).symm z).1
        = φ.symm ((𝓡∂ (8 + k + 1)).symm z) :=
      (congrArg Subtype.val (S.pullInvFun_of_mem m φ hzT)).trans hval
    have hz' : z ∈ (φ.extend (𝓡∂ (8 + k + 1))).target := by
      rw [OpenPartialHomeomorph.extend_target]
      exact ⟨S.pullTarget_subset_target φ hzT, hzr⟩
    have h5 := hfc.writtenInCharts hz'
    rw [Function.comp_apply, Function.comp_apply] at h5
    rw [Function.comp_apply, Function.comp_apply]
    rw [← h5, harg]
    rfl

/-! ## The comparison of the boundary of the region with the boundary of `A` -/

/-- The ambient chart used to compare the two boundaries (the chart of the region at `m`). -/
noncomputable def bChi (m : S.Region) : OpenPartialHomeomorph S.A (Half k) := S.dom m

/-- The preferred ambient chart of `A` at `m.1`. -/
noncomputable def bE0 (m : S.Region) : OpenPartialHomeomorph S.A (Half k) :=
  _root_.chartAt (Half k) m.1

/-- An open neighbourhood of `m.1` contained in the region. -/
noncomputable def bV (m : S.Region)
    (he : m.1 ∈ (𝓡∂ (8 + k + 1)).boundary S.A) : Set S.A := S.regionNhd m (Or.inl he)

/-- The open set of `A` on which the comparison of the boundaries is made. -/
def bU (m : S.Region) (he : m.1 ∈ (𝓡∂ (8 + k + 1)).boundary S.A) : Set S.A :=
  (S.bChi m).source ∩ ((S.bE0 m).source ∩ S.bV m he)

theorem mem_bU_iff (m : S.Region) (he : m.1 ∈ (𝓡∂ (8 + k + 1)).boundary S.A) {a : S.A} :
    a ∈ S.bU m he ↔ a ∈ (S.bChi m).source ∧ a ∈ (S.bE0 m).source ∧ a ∈ S.bV m he :=
  Iff.rfl

theorem isOpen_bU (m : S.Region) (he : m.1 ∈ (𝓡∂ (8 + k + 1)).boundary S.A) :
    IsOpen (S.bU m he) :=
  ((S.bChi m).open_source).inter (((S.bE0 m).open_source).inter
    (S.isOpen_regionNhd m (Or.inl he)))

theorem bU_subset_chi (m : S.Region) (he : m.1 ∈ (𝓡∂ (8 + k + 1)).boundary S.A) {a : S.A}
    (ha : a ∈ S.bU m he) : a ∈ (S.bChi m).source := ha.1

theorem bU_subset_e0 (m : S.Region) (he : m.1 ∈ (𝓡∂ (8 + k + 1)).boundary S.A) {a : S.A}
    (ha : a ∈ S.bU m he) : a ∈ (S.bE0 m).source := ha.2.1

theorem bU_subset_V (m : S.Region) (he : m.1 ∈ (𝓡∂ (8 + k + 1)).boundary S.A) {a : S.A}
    (ha : a ∈ S.bU m he) : a ∈ S.bV m he := ha.2.2

theorem bU_subset_region (m : S.Region) (he : m.1 ∈ (𝓡∂ (8 + k + 1)).boundary S.A) {a : S.A}
    (ha : a ∈ S.bU m he) : S.Φ a ≤ 0 :=
  S.regionNhd_subset m (Or.inl he) (S.bU_subset_V m he ha)

theorem mem_bU_self (m : S.Region) (he : m.1 ∈ (𝓡∂ (8 + k + 1)).boundary S.A) :
    m.1 ∈ S.bU m he := by
  refine ⟨?_, ?_, ?_⟩
  · exact S.mem_dom_source m
  · exact mem_chart_source (Half k) m.1
  · exact S.mem_regionNhd m (Or.inl he)

/-- **A point of the boundary of the region whose chart value lies in the chart of the region is
over the boundary of `A`.** -/
theorem bdry_of_mem_chi (m : S.Region)
    (he : m.1 ∈ (𝓡∂ (8 + k + 1)).boundary S.A)
    (y : ↥((𝓡∂ (8 + k + 1)).boundary S.Region)) (hy : y.1.1 ∈ (S.bChi m).source) :
    y.1.1 ∈ (𝓡∂ (8 + k + 1)).boundary S.A := by
  have hbig : S.bigCase m := Or.inl he
  have hycs : y.1 ∈ S.chartSource m := hy
  have h1 : (S.chartVec m y.1.1) 0 = 0 := by
    have hec : S.chartAt m ∈ IsManifold.maximalAtlas (𝓡∂ (8 + k + 1)) ∞ S.Region :=
      IsManifold.chart_mem_maximalAtlas m
    have hx := (Work.ThomBordism.Transversality.Preimage.mem_boundary_iff_extend_apply_coord_eq_zero
      (m := 8 + k + 1) hec hycs).mp y.2
    rwa [OpenPartialHomeomorph.extend_coe, Function.comp_apply, S.chartAt_apply_of_mem m hycs,
      modelWithCornersEuclideanHalfSpace_apply] at hx
  refine (Work.ThomBordism.Transversality.Preimage.mem_boundary_iff_extend_apply_coord_eq_zero
    (m := 8 + k + 1) (S.dom_maximalAtlas m) hy).mpr ?_
  rw [← S.chartVec_of_bigCase m hbig y.1.1]
  exact h1

/-- The boundary identification, as a total (junk off the boundary) map. -/
noncomputable def bjA (m : S.Region) (he : m.1 ∈ (𝓡∂ (8 + k + 1)).boundary S.A) :
    ↥((𝓡∂ (8 + k + 1)).boundary S.Region) → ↥((𝓡∂ (8 + k + 1)).boundary S.A) :=
  fun y => if h : y.1.1 ∈ (𝓡∂ (8 + k + 1)).boundary S.A then ⟨y.1.1, h⟩ else ⟨m.1, he⟩

/-- Its inverse, as a total (junk off the region) map. -/
noncomputable def biA (m : S.Region) (hm : m ∈ (𝓡∂ (8 + k + 1)).boundary S.Region)
    (he : m.1 ∈ (𝓡∂ (8 + k + 1)).boundary S.A) :
    ↥((𝓡∂ (8 + k + 1)).boundary S.A) → ↥((𝓡∂ (8 + k + 1)).boundary S.Region) :=
  fun x => if h : S.Φ x.1 ≤ 0 then
      ⟨⟨x.1, h⟩, (S.mem_boundary_iff ⟨x.1, h⟩).mpr (Or.inl x.2)⟩
    else ⟨m, hm⟩

theorem bjA_coe_of_mem (m : S.Region) (he : m.1 ∈ (𝓡∂ (8 + k + 1)).boundary S.A)
    {y : ↥((𝓡∂ (8 + k + 1)).boundary S.Region)}
    (hy : y.1.1 ∈ (𝓡∂ (8 + k + 1)).boundary S.A) : (S.bjA m he y).1 = y.1.1 := by
  simp only [bjA, dif_pos hy]

theorem biA_coe_of_mem (m : S.Region) (hm : m ∈ (𝓡∂ (8 + k + 1)).boundary S.Region)
    (he : m.1 ∈ (𝓡∂ (8 + k + 1)).boundary S.A)
    {x : ↥((𝓡∂ (8 + k + 1)).boundary S.A)} (hx : S.Φ x.1 ≤ 0) :
    (S.biA m hm he x).1.1 = x.1 := by
  simp only [biA, dif_pos hx]

/-- The source of the comparison: the points of the boundary of the region which lie over `bU`. -/
def bSource (m : S.Region) (he : m.1 ∈ (𝓡∂ (8 + k + 1)).boundary S.A) :
    Set ↥((𝓡∂ (8 + k + 1)).boundary S.Region) := {y | y.1.1 ∈ S.bU m he}

/-- The target of the comparison. -/
def bTarget (m : S.Region) (he : m.1 ∈ (𝓡∂ (8 + k + 1)).boundary S.A) :
    Set ↥((𝓡∂ (8 + k + 1)).boundary S.A) := {x | x.1 ∈ S.bU m he}

theorem isOpen_bSource (m : S.Region) (he : m.1 ∈ (𝓡∂ (8 + k + 1)).boundary S.A) :
    IsOpen (S.bSource m he) :=
  (S.isOpen_bU m he).preimage
    (by fun_prop :
      Continuous fun y : ↥((𝓡∂ (8 + k + 1)).boundary S.Region) => (y.1.1 : S.A))

theorem isOpen_bTarget (m : S.Region) (he : m.1 ∈ (𝓡∂ (8 + k + 1)).boundary S.A) :
    IsOpen (S.bTarget m he) :=
  (S.isOpen_bU m he).preimage
    (by fun_prop :
      Continuous fun x : ↥((𝓡∂ (8 + k + 1)).boundary S.A) => (x.1 : S.A))

theorem mem_bSource_iff (m : S.Region) (he : m.1 ∈ (𝓡∂ (8 + k + 1)).boundary S.A)
    {y : ↥((𝓡∂ (8 + k + 1)).boundary S.Region)} :
    y ∈ S.bSource m he ↔ y.1.1 ∈ S.bU m he := Iff.rfl

theorem mem_bTarget_iff (m : S.Region) (he : m.1 ∈ (𝓡∂ (8 + k + 1)).boundary S.A)
    {x : ↥((𝓡∂ (8 + k + 1)).boundary S.A)} :
    x ∈ S.bTarget m he ↔ x.1 ∈ S.bU m he := Iff.rfl

theorem mem_bSource_self (m : S.Region) (hm : m ∈ (𝓡∂ (8 + k + 1)).boundary S.Region)
    (he : m.1 ∈ (𝓡∂ (8 + k + 1)).boundary S.A) :
    (⟨m, hm⟩ : ↥((𝓡∂ (8 + k + 1)).boundary S.Region)) ∈ S.bSource m he :=
  S.mem_bU_self m he

theorem bjA_mem_bTarget (m : S.Region) (he : m.1 ∈ (𝓡∂ (8 + k + 1)).boundary S.A)
    {y : ↥((𝓡∂ (8 + k + 1)).boundary S.Region)} (hy : y ∈ S.bSource m he) :
    S.bjA m he y ∈ S.bTarget m he := by
  have hbd : y.1.1 ∈ (𝓡∂ (8 + k + 1)).boundary S.A :=
    S.bdry_of_mem_chi m he y (S.bU_subset_chi m he hy)
  rw [S.mem_bTarget_iff m he, S.bjA_coe_of_mem m he hbd]
  exact hy

theorem biA_mem_bSource (m : S.Region) (hm : m ∈ (𝓡∂ (8 + k + 1)).boundary S.Region)
    (he : m.1 ∈ (𝓡∂ (8 + k + 1)).boundary S.A)
    {x : ↥((𝓡∂ (8 + k + 1)).boundary S.A)} (hx : x ∈ S.bTarget m he) :
    S.biA m hm he x ∈ S.bSource m he := by
  have hΦ : S.Φ x.1 ≤ 0 := S.bU_subset_region m he hx
  rw [S.mem_bSource_iff m he, S.biA_coe_of_mem m hm he hΦ]
  exact hx

theorem biA_bjA (m : S.Region) (hm : m ∈ (𝓡∂ (8 + k + 1)).boundary S.Region)
    (he : m.1 ∈ (𝓡∂ (8 + k + 1)).boundary S.A)
    {y : ↥((𝓡∂ (8 + k + 1)).boundary S.Region)} (hy : y ∈ S.bSource m he) :
    S.biA m hm he (S.bjA m he y) = y := by
  have hbd : y.1.1 ∈ (𝓡∂ (8 + k + 1)).boundary S.A :=
    S.bdry_of_mem_chi m he y (S.bU_subset_chi m he hy)
  have hΦ : S.Φ y.1.1 ≤ 0 := y.1.2
  simp only [biA, bjA, dif_pos hbd, dif_pos hΦ]

theorem bjA_biA (m : S.Region) (hm : m ∈ (𝓡∂ (8 + k + 1)).boundary S.Region)
    (he : m.1 ∈ (𝓡∂ (8 + k + 1)).boundary S.A)
    {x : ↥((𝓡∂ (8 + k + 1)).boundary S.A)} (hx : x ∈ S.bTarget m he) :
    S.bjA m he (S.biA m hm he x) = x := by
  have hΦ : S.Φ x.1 ≤ 0 := S.bU_subset_region m he hx
  have hcc : (S.biA m hm he x).1.1 = x.1 := S.biA_coe_of_mem m hm he hΦ
  have hbd : (S.biA m hm he x).1.1 ∈ (𝓡∂ (8 + k + 1)).boundary S.A := by
    rw [hcc]; exact x.2
  apply Subtype.ext
  rw [S.bjA_coe_of_mem m he hbd, hcc]

theorem continuousOn_bjA (m : S.Region) (hm : m ∈ (𝓡∂ (8 + k + 1)).boundary S.Region)
    (he : m.1 ∈ (𝓡∂ (8 + k + 1)).boundary S.A) :
    ContinuousOn (S.bjA m he) (S.bSource m he) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have h2 : Continuous (fun y : ↥(S.bSource m he) =>
      (⟨(y.1.1.1 : S.A), S.bdry_of_mem_chi m he y.1 (S.bU_subset_chi m he y.2)⟩ :
        ↥((𝓡∂ (8 + k + 1)).boundary S.A))) :=
    Continuous.subtype_mk (by fun_prop : Continuous fun y : ↥(S.bSource m he) => (y.1.1.1 : S.A)) _
  refine h2.congr fun y => ?_
  refine Subtype.ext ?_
  simp only [Set.domRestrict_apply, bjA,
    dif_pos (S.bdry_of_mem_chi m he y.1 (S.bU_subset_chi m he y.2))]

theorem continuousOn_biA (m : S.Region) (hm : m ∈ (𝓡∂ (8 + k + 1)).boundary S.Region)
    (he : m.1 ∈ (𝓡∂ (8 + k + 1)).boundary S.A) :
    ContinuousOn (S.biA m hm he) (S.bTarget m he) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have h2 : Continuous (fun x : ↥(S.bTarget m he) =>
      (⟨⟨x.1.1, S.bU_subset_region m he x.2⟩,
        (S.mem_boundary_iff ⟨x.1.1, S.bU_subset_region m he x.2⟩).mpr (Or.inl x.1.2)⟩ :
        ↥((𝓡∂ (8 + k + 1)).boundary S.Region))) :=
    Continuous.subtype_mk (Continuous.subtype_mk
      (by fun_prop : Continuous fun x : ↥(S.bTarget m he) => (x.1.1 : S.A)) _) _
  refine h2.congr fun x => ?_
  simp only [Set.domRestrict_apply, biA, dif_pos (S.bU_subset_region m he x.2)]

/-- **The identification of a neighbourhood of `m` in the boundary of the region with a
neighbourhood of `m.1` in the boundary of `A`.** -/
noncomputable def bJ (m : S.Region) (hm : m ∈ (𝓡∂ (8 + k + 1)).boundary S.Region)
    (he : m.1 ∈ (𝓡∂ (8 + k + 1)).boundary S.A) :
    OpenPartialHomeomorph (↥((𝓡∂ (8 + k + 1)).boundary S.Region))
      (↥((𝓡∂ (8 + k + 1)).boundary S.A)) where
  toFun := S.bjA m he
  invFun := S.biA m hm he
  source := S.bSource m he
  target := S.bTarget m he
  map_source' := fun y hy => S.bjA_mem_bTarget m he hy
  map_target' := fun x hx => S.biA_mem_bSource m hm he hx
  left_inv' := fun y hy => S.biA_bjA m hm he hy
  right_inv' := fun x hx => S.bjA_biA m hm he hx
  continuousOn_toFun := S.continuousOn_bjA m hm he
  continuousOn_invFun := S.continuousOn_biA m hm he
  open_source := S.isOpen_bSource m he
  open_target := S.isOpen_bTarget m he


/-! ## The model-level transition and the comparison maps -/

theorem bChi_maximalAtlas (m : S.Region) :
    S.bChi m ∈ IsManifold.maximalAtlas (𝓡∂ (8 + k + 1)) ∞ S.A := S.dom_maximalAtlas m

/-- The model-level ambient transition between the region chart and the preferred chart at
`m.1`. -/
noncomputable def bT (m : S.Region) : PartialEquiv (Mod k) (Mod k) :=
  (𝓡∂ (8 + k + 1)).extendCoordChange (S.bChi m) (_root_.chartAt (Half k) m.1)

/-- The comparison map on the model. -/
noncomputable def bTheta (m : S.Region) (v : EuclideanSpace ℝ (Fin (8 + k))) :
    EuclideanSpace ℝ (Fin (8 + k)) :=
  Work.Surgery.tailCLM (8 + k) ((S.bT m) ((Work.Surgery.consZeroCLM (8 + k)) v))

/-- The source of the comparison map. -/
def bThetaSource (m : S.Region) : Set (EuclideanSpace ℝ (Fin (8 + k))) :=
  {v | (Work.Surgery.consZeroCLM (8 + k)) v ∈ (S.bT m).source}

/-- The inverse comparison map on the model. -/
noncomputable def bThetaInv (m : S.Region) (w : EuclideanSpace ℝ (Fin (8 + k))) :
    EuclideanSpace ℝ (Fin (8 + k)) :=
  Work.Surgery.tailCLM (8 + k) ((S.bT m).symm ((Work.Surgery.consZeroCLM (8 + k)) w))

/-- The source of the inverse comparison map. -/
def bThetaInvSource (m : S.Region) : Set (EuclideanSpace ℝ (Fin (8 + k))) :=
  {w | (Work.Surgery.consZeroCLM (8 + k)) w ∈
    ((𝓡∂ (8 + k + 1)).extendCoordChange (_root_.chartAt (Half k) m.1) (S.bChi m)).source}

theorem bT_symm (m : S.Region) :
    (S.bT m).symm
      = (𝓡∂ (8 + k + 1)).extendCoordChange (_root_.chartAt (Half k) m.1) (S.bChi m) := by
  rw [bT, ModelWithCorners.extendCoordChange_symm]

theorem contDiffOn_bTheta (m : S.Region) :
    ContDiffOn ℝ ∞ (S.bTheta m) (S.bThetaSource m) := by
  have hT : ContDiffOn ℝ ∞ (fun v : Mod k => (S.bT m) v) (S.bT m).source :=
    (𝓡∂ (8 + k + 1)).contDiffOn_extendCoordChange (S.bChi_maximalAtlas m)
      (IsManifold.chart_mem_maximalAtlas (I := 𝓡∂ (8 + k + 1)) m.1)
  have h1 := hT.comp ((Work.Surgery.consZeroCLM (8 + k)).contDiff.contDiffOn)
    (fun v hv => hv)
  exact (Work.Surgery.tailCLM (8 + k)).contDiff.contDiffOn.comp h1
    (fun _ _ => Set.mem_univ _)

theorem contDiffOn_bThetaInv (m : S.Region) :
    ContDiffOn ℝ ∞ (S.bThetaInv m) (S.bThetaInvSource m) := by
  have hTs : ContDiffOn ℝ ∞ (fun w : Mod k =>
      (𝓡∂ (8 + k + 1)).extendCoordChange (_root_.chartAt (Half k) m.1) (S.bChi m) w)
      ((𝓡∂ (8 + k + 1)).extendCoordChange (_root_.chartAt (Half k) m.1) (S.bChi m)).source :=
    (𝓡∂ (8 + k + 1)).contDiffOn_extendCoordChange
      (IsManifold.chart_mem_maximalAtlas (I := 𝓡∂ (8 + k + 1)) m.1) (S.bChi_maximalAtlas m)
  have h1 := hTs.comp ((Work.Surgery.consZeroCLM (8 + k)).contDiff.contDiffOn)
    (fun w hw => hw)
  have h2 : ContDiffOn ℝ ∞ (fun w : EuclideanSpace ℝ (Fin (8 + k)) =>
      Work.Surgery.tailCLM (8 + k)
        ((𝓡∂ (8 + k + 1)).extendCoordChange (_root_.chartAt (Half k) m.1) (S.bChi m)
          ((Work.Surgery.consZeroCLM (8 + k)) w))) (S.bThetaInvSource m) :=
    (Work.Surgery.tailCLM (8 + k)).contDiff.contDiffOn.comp h1 (fun _ _ => Set.mem_univ _)
  refine h2.congr fun w _ => ?_
  simp only [bThetaInv, bT_symm]

/-- The preferred boundary chart of the region at `m`. -/
noncomputable def bChaR (m : S.Region) (hm : m ∈ (𝓡∂ (8 + k + 1)).boundary S.Region) :
    OpenPartialHomeomorph (↥((𝓡∂ (8 + k + 1)).boundary S.Region))
      (EuclideanSpace ℝ (Fin (8 + k))) :=
  Work.Surgery.boundaryChartAt (⟨m, hm⟩ : ↥((𝓡∂ (8 + k + 1)).boundary S.Region))

/-- The preferred boundary chart of `A` at `m.1`. -/
noncomputable def bChaA (m : S.Region) (he : m.1 ∈ (𝓡∂ (8 + k + 1)).boundary S.A) :
    OpenPartialHomeomorph (↥((𝓡∂ (8 + k + 1)).boundary S.A))
      (EuclideanSpace ℝ (Fin (8 + k))) :=
  Work.Surgery.boundaryChartAt (⟨m.1, he⟩ : ↥((𝓡∂ (8 + k + 1)).boundary S.A))

theorem bChaR_mem_maximalAtlas (m : S.Region)
    (hm : m ∈ (𝓡∂ (8 + k + 1)).boundary S.Region) :
    S.bChaR m hm ∈ IsManifold.maximalAtlas (𝓡 (8 + k)) ∞
      (↥((𝓡∂ (8 + k + 1)).boundary S.Region)) :=
  IsManifold.chart_mem_maximalAtlas (I := 𝓡 (8 + k))
    (⟨m, hm⟩ : ↥((𝓡∂ (8 + k + 1)).boundary S.Region))

theorem bChaA_mem_maximalAtlas (m : S.Region)
    (he : m.1 ∈ (𝓡∂ (8 + k + 1)).boundary S.A) :
    S.bChaA m he ∈ IsManifold.maximalAtlas (𝓡 (8 + k)) ∞
      (↥((𝓡∂ (8 + k + 1)).boundary S.A)) :=
  IsManifold.chart_mem_maximalAtlas (I := 𝓡 (8 + k))
    (⟨m.1, he⟩ : ↥((𝓡∂ (8 + k + 1)).boundary S.A))

theorem bSource_subset_bChaR (m : S.Region)
    (hm : m ∈ (𝓡∂ (8 + k + 1)).boundary S.Region)
    (he : m.1 ∈ (𝓡∂ (8 + k + 1)).boundary S.A) :
    S.bSource m he ⊆ (S.bChaR m hm).source := by
  intro y hy
  rw [bChaR, Work.Surgery.boundaryChartAt_source, extChartAt_source]
  exact S.bU_subset_chi m he hy

theorem bTarget_subset_bChaA (m : S.Region)
    (he : m.1 ∈ (𝓡∂ (8 + k + 1)).boundary S.A) :
    S.bTarget m he ⊆ (S.bChaA m he).source := by
  intro x hx
  rw [bChaA, Work.Surgery.boundaryChartAt_source, extChartAt_source]
  exact S.bU_subset_e0 m he hx

/-- The region's chart, extended, in terms of the ambient chart `bChi`. -/
theorem extChartAt_region_apply (m : S.Region)
    (he : m.1 ∈ (𝓡∂ (8 + k + 1)).boundary S.A)
    (y : ↥((𝓡∂ (8 + k + 1)).boundary S.Region)) (hy : y.1.1 ∈ (S.bChi m).source) :
    (extChartAt (𝓡∂ (8 + k + 1)) m) y.1 = (S.bChi m).extend (𝓡∂ (8 + k + 1)) y.1.1 := by
  have hb : S.bigCase m := Or.inl he
  have hycs : y.1 ∈ S.chartSource m := hy
  have hL : (extChartAt (𝓡∂ (8 + k + 1)) m) y.1 = S.chartVec m y.1.1 := by
    rw [extChartAt, OpenPartialHomeomorph.extend_coe, Function.comp_apply,
      show _root_.chartAt (Half k) m = S.chartAt m from rfl,
      S.chartAt_apply_of_mem m hycs, modelWithCornersEuclideanHalfSpace_apply]
  have hR : (S.bChi m).extend (𝓡∂ (8 + k + 1)) y.1.1 = S.chartVec m y.1.1 := by
    rw [bChi, ← S.chartVec_of_bigCase m hb y.1.1]
  rw [hL, hR]

theorem bChaR_apply_of_mem (m : S.Region)
    (hm : m ∈ (𝓡∂ (8 + k + 1)).boundary S.Region)
    (he : m.1 ∈ (𝓡∂ (8 + k + 1)).boundary S.A)
    {y : ↥((𝓡∂ (8 + k + 1)).boundary S.Region)} (hy : y ∈ S.bSource m he) :
    S.bChaR m hm y
      = Work.Surgery.tailCLM (8 + k) ((S.bChi m).extend (𝓡∂ (8 + k + 1)) y.1.1) := by
  rw [bChaR, Work.Surgery.boundaryChartAt_apply
    (⟨m, hm⟩ : ↥((𝓡∂ (8 + k + 1)).boundary S.Region)) y
    (S.bSource_subset_bChaR m hm he hy)]
  congr 1
  exact S.extChartAt_region_apply m he y (S.bU_subset_chi m he hy)

theorem bChaA_apply_of_mem (m : S.Region)
    (he : m.1 ∈ (𝓡∂ (8 + k + 1)).boundary S.A)
    {x : ↥((𝓡∂ (8 + k + 1)).boundary S.A)} (hx : x ∈ S.bTarget m he) :
    S.bChaA m he x
      = Work.Surgery.tailCLM (8 + k) ((extChartAt (𝓡∂ (8 + k + 1)) m.1) x.1) := by
  rw [bChaA, Work.Surgery.boundaryChartAt_apply
    (⟨m.1, he⟩ : ↥((𝓡∂ (8 + k + 1)).boundary S.A)) x
    (S.bTarget_subset_bChaA m he hx)]


theorem bjA_self (m : S.Region) (hm : m ∈ (𝓡∂ (8 + k + 1)).boundary S.Region)
    (he : m.1 ∈ (𝓡∂ (8 + k + 1)).boundary S.A) :
    S.bjA m he (⟨m, hm⟩ : ↥((𝓡∂ (8 + k + 1)).boundary S.Region)) = ⟨m.1, he⟩ := by
  rw [bjA, dif_pos he]

/-- The comparison of the boundary charts. -/
theorem bChaA_bJ (m : S.Region) (hm : m ∈ (𝓡∂ (8 + k + 1)).boundary S.Region)
    (he : m.1 ∈ (𝓡∂ (8 + k + 1)).boundary S.A)
    {y : ↥((𝓡∂ (8 + k + 1)).boundary S.Region)} (hy : y ∈ S.bSource m he) :
    S.bChaA m he (S.bjA m he y) = S.bTheta m (S.bChaR m hm y) := by
  have hχ : y.1.1 ∈ (S.bChi m).source := S.bU_subset_chi m he hy
  have hbd : y.1.1 ∈ (𝓡∂ (8 + k + 1)).boundary S.A := S.bdry_of_mem_chi m he y hχ
  have hL : S.bChaA m he (S.bjA m he y)
      = Work.Surgery.tailCLM (8 + k) ((extChartAt (𝓡∂ (8 + k + 1)) m.1) y.1.1) := by
    rw [S.bChaA_apply_of_mem m he (S.bjA_mem_bTarget m he hy), S.bjA_coe_of_mem m he hbd]
  have hR : S.bTheta m (S.bChaR m hm y)
      = Work.Surgery.tailCLM (8 + k) ((extChartAt (𝓡∂ (8 + k + 1)) m.1) y.1.1) := by
    rw [S.bChaR_apply_of_mem m hm he hy, bTheta]
    congr 1
    have hw0 : (((S.bChi m).extend (𝓡∂ (8 + k + 1))) y.1.1).ofLp 0 = 0 :=
      (Work.ThomBordism.Transversality.Preimage.mem_boundary_iff_extend_apply_coord_eq_zero
        (S.bChi_maximalAtlas m) hχ).mp hbd
    rw [Work.Surgery.consZeroCLM_tailCLM (8 + k) _ hw0]
    have hχe : y.1.1 ∈ ((S.bChi m).extend (𝓡∂ (8 + k + 1))).source := by
      rw [OpenPartialHomeomorph.extend_source]; exact hχ
    rw [bT]
    show ((_root_.chartAt (Half k) m.1).extend (𝓡∂ (8 + k + 1)))
        (((S.bChi m).extend (𝓡∂ (8 + k + 1))).symm
          ((S.bChi m).extend (𝓡∂ (8 + k + 1)) y.1.1))
      = (extChartAt (𝓡∂ (8 + k + 1)) m.1) y.1.1
    rw [PartialEquiv.left_inv (e := (S.bChi m).extend (𝓡∂ (8 + k + 1))) hχe]
    rfl
  rw [hL, hR]

/-- The comparison of boundary charts, in the inverse direction. -/
theorem bChaR_bJ_symm (m : S.Region) (hm : m ∈ (𝓡∂ (8 + k + 1)).boundary S.Region)
    (he : m.1 ∈ (𝓡∂ (8 + k + 1)).boundary S.A)
    {x : ↥((𝓡∂ (8 + k + 1)).boundary S.A)} (hx : x ∈ S.bTarget m he) :
    S.bChaR m hm ((S.bJ m hm he).symm x) = S.bThetaInv m (S.bChaA m he x) := by
  have he0 : x.1 ∈ (S.bE0 m).source := S.bU_subset_e0 m he hx
  have hbd : x.1 ∈ (𝓡∂ (8 + k + 1)).boundary S.A := x.2
  have hL : S.bChaR m hm ((S.bJ m hm he).symm x)
      = Work.Surgery.tailCLM (8 + k) ((S.bChi m).extend (𝓡∂ (8 + k + 1)) x.1) := by
    have hsym : (S.bJ m hm he).symm x = S.biA m hm he x := rfl
    rw [hsym, S.bChaR_apply_of_mem m hm he (S.biA_mem_bSource m hm he hx)]
    congr 1
    rw [S.biA_coe_of_mem m hm he (S.bU_subset_region m he hx)]
  have hR : S.bThetaInv m (S.bChaA m he x)
      = Work.Surgery.tailCLM (8 + k) ((S.bChi m).extend (𝓡∂ (8 + k + 1)) x.1) := by
    rw [S.bChaA_apply_of_mem m he hx, bThetaInv]
    congr 1
    have hw0 : (((extChartAt (𝓡∂ (8 + k + 1)) m.1) x.1)).ofLp 0 = 0 :=
      (Work.ThomBordism.Transversality.Preimage.mem_boundary_iff_extend_apply_coord_eq_zero
        (IsManifold.chart_mem_maximalAtlas (I := 𝓡∂ (8 + k + 1)) m.1) he0).mp hbd
    rw [Work.Surgery.consZeroCLM_tailCLM (8 + k) _ hw0]
    rw [bT_symm]
    have he0e : x.1 ∈ ((_root_.chartAt (Half k) m.1).extend (𝓡∂ (8 + k + 1))).source := by
      rw [OpenPartialHomeomorph.extend_source]; exact he0
    show ((S.bChi m).extend (𝓡∂ (8 + k + 1)))
        (((_root_.chartAt (Half k) m.1).extend (𝓡∂ (8 + k + 1))).symm
          (((_root_.chartAt (Half k) m.1).extend (𝓡∂ (8 + k + 1))) x.1)) = _
    rw [PartialEquiv.left_inv
      (e := (_root_.chartAt (Half k) m.1).extend (𝓡∂ (8 + k + 1))) he0e]
  rw [hL, hR]

theorem bThetasource_of_mem (m : S.Region) (hm : m ∈ (𝓡∂ (8 + k + 1)).boundary S.Region)
    (he : m.1 ∈ (𝓡∂ (8 + k + 1)).boundary S.A)
    {y : ↥((𝓡∂ (8 + k + 1)).boundary S.Region)} (hy : y ∈ S.bSource m he) :
    (S.bChaR m hm).extend (𝓡 (8 + k)) y ∈ S.bThetaSource m := by
  have hχ : y.1.1 ∈ (S.bChi m).source := S.bU_subset_chi m he hy
  have he0 : y.1.1 ∈ (S.bE0 m).source := S.bU_subset_e0 m he hy
  have hbd : y.1.1 ∈ (𝓡∂ (8 + k + 1)).boundary S.A := S.bdry_of_mem_chi m he y hχ
  have hw0 : (((S.bChi m).extend (𝓡∂ (8 + k + 1))) y.1.1).ofLp 0 = 0 :=
    (Work.ThomBordism.Transversality.Preimage.mem_boundary_iff_extend_apply_coord_eq_zero
      (S.bChi_maximalAtlas m) hχ).mp hbd
  have hval : (S.bChaR m hm).extend (𝓡 (8 + k)) y
      = Work.Surgery.tailCLM (8 + k) ((S.bChi m).extend (𝓡∂ (8 + k + 1)) y.1.1) := by
    simp only [OpenPartialHomeomorph.extend_coe, Function.comp_apply,
      modelWithCornersSelf_coe, id_eq]
    exact S.bChaR_apply_of_mem m hm he hy
  rw [bThetaSource, Set.mem_ofPred_eq, hval, Work.Surgery.consZeroCLM_tailCLM (8 + k) _ hw0]
  rw [bT, ← OpenPartialHomeomorph.extend_image_source_inter (I := 𝓡∂ (8 + k + 1))
    (S.bChi m) (_root_.chartAt (Half k) m.1)]
  exact mem_image_of_mem _ ⟨hχ, he0⟩

theorem bThetainvSource_of_mem (m : S.Region)
    (he : m.1 ∈ (𝓡∂ (8 + k + 1)).boundary S.A)
    {x : ↥((𝓡∂ (8 + k + 1)).boundary S.A)} (hx : x ∈ S.bTarget m he) :
    (S.bChaA m he).extend (𝓡 (8 + k)) x ∈ S.bThetaInvSource m := by
  have hχ : x.1 ∈ (S.bChi m).source := S.bU_subset_chi m he hx
  have he0 : x.1 ∈ (S.bE0 m).source := S.bU_subset_e0 m he hx
  have hbd : x.1 ∈ (𝓡∂ (8 + k + 1)).boundary S.A := x.2
  have hw0 : (((extChartAt (𝓡∂ (8 + k + 1)) m.1) x.1)).ofLp 0 = 0 :=
    (Work.ThomBordism.Transversality.Preimage.mem_boundary_iff_extend_apply_coord_eq_zero
      (IsManifold.chart_mem_maximalAtlas (I := 𝓡∂ (8 + k + 1)) m.1) he0).mp hbd
  have hval : (S.bChaA m he).extend (𝓡 (8 + k)) x
      = Work.Surgery.tailCLM (8 + k) ((extChartAt (𝓡∂ (8 + k + 1)) m.1) x.1) := by
    simp only [OpenPartialHomeomorph.extend_coe, Function.comp_apply,
      modelWithCornersSelf_coe, id_eq]
    exact S.bChaA_apply_of_mem m he hx
  rw [bThetaInvSource, Set.mem_ofPred_eq, hval, Work.Surgery.consZeroCLM_tailCLM (8 + k) _ hw0]
  rw [← OpenPartialHomeomorph.extend_image_source_inter (I := 𝓡∂ (8 + k + 1))
    (_root_.chartAt (Half k) m.1) (S.bChi m)]
  exact mem_image_of_mem _ ⟨he0, hχ⟩


/-! ## Smoothness of the identification -/

theorem contMDiffOn_bJ (m : S.Region) (hm : m ∈ (𝓡∂ (8 + k + 1)).boundary S.Region)
    (he : m.1 ∈ (𝓡∂ (8 + k + 1)).boundary S.A) :
    ContMDiffOn (𝓡 (8 + k)) (𝓡 (8 + k)) ∞ (S.bJ m hm he) (S.bJ m hm he).source := by
  change ContMDiffOn (𝓡 (8 + k)) (𝓡 (8 + k)) ∞ (⇑(S.bJ m hm he)) (S.bSource m he)
  rw [contMDiffOn_iff_of_mem_maximalAtlas (S.bChaR_mem_maximalAtlas m hm)
    (S.bChaA_mem_maximalAtlas m he) (S.bSource_subset_bChaR m hm he)
    (show MapsTo (⇑(S.bJ m hm he)) (S.bJ m hm he).source (S.bChaA m he).source from
      fun y hy => S.bTarget_subset_bChaA m he (S.bjA_mem_bTarget m he hy))]
  constructor
  · exact (S.bJ m hm he).continuousOn_toFun
  · have hΘ : ContDiffOn ℝ ∞ (S.bTheta m)
        ((S.bChaR m hm).extend (𝓡 (8 + k)) '' (S.bJ m hm he).source) :=
      (S.contDiffOn_bTheta m).mono (by
        rintro z ⟨y, hy, rfl⟩
        exact S.bThetasource_of_mem m hm he hy)
    refine hΘ.congr fun z hz => ?_
    obtain ⟨y, hy, rfl⟩ := hz
    have hyS : y ∈ S.bSource m he := hy
    have hye : y ∈ ((S.bChaR m hm).extend (𝓡 (8 + k))).source := by
      rw [OpenPartialHomeomorph.extend_source]
      exact S.bSource_subset_bChaR m hm he hyS
    show (S.bChaA m he).extend (𝓡 (8 + k)) ((S.bJ m hm he)
        (((S.bChaR m hm).extend (𝓡 (8 + k))).symm
          ((S.bChaR m hm).extend (𝓡 (8 + k)) y)))
      = S.bTheta m ((S.bChaR m hm).extend (𝓡 (8 + k)) y)
    rw [PartialEquiv.left_inv (e := (S.bChaR m hm).extend (𝓡 (8 + k))) hye]
    simp only [OpenPartialHomeomorph.extend_coe, Function.comp_apply,
      modelWithCornersSelf_coe, id_eq]
    exact S.bChaA_bJ m hm he hyS

theorem contMDiffOn_bJ_symm (m : S.Region) (hm : m ∈ (𝓡∂ (8 + k + 1)).boundary S.Region)
    (he : m.1 ∈ (𝓡∂ (8 + k + 1)).boundary S.A) :
    ContMDiffOn (𝓡 (8 + k)) (𝓡 (8 + k)) ∞ (S.bJ m hm he).symm (S.bJ m hm he).target := by
  change ContMDiffOn (𝓡 (8 + k)) (𝓡 (8 + k)) ∞ (⇑(S.bJ m hm he).symm) (S.bTarget m he)
  rw [contMDiffOn_iff_of_mem_maximalAtlas (S.bChaA_mem_maximalAtlas m he)
    (S.bChaR_mem_maximalAtlas m hm) (S.bTarget_subset_bChaA m he)
    (show MapsTo (⇑(S.bJ m hm he).symm) (S.bJ m hm he).target (S.bChaR m hm).source from
      fun x hx => S.bSource_subset_bChaR m hm he ((S.bJ m hm he).map_target' hx))]
  constructor
  · exact (S.bJ m hm he).continuousOn_invFun
  · have hΘ : ContDiffOn ℝ ∞ (S.bThetaInv m)
        ((S.bChaA m he).extend (𝓡 (8 + k)) '' (S.bJ m hm he).target) :=
      (S.contDiffOn_bThetaInv m).mono (by
        rintro z ⟨x, hx, rfl⟩
        exact S.bThetainvSource_of_mem m he hx)
    refine hΘ.congr fun z hz => ?_
    obtain ⟨x, hx, rfl⟩ := hz
    have hxT : x ∈ S.bTarget m he := hx
    have hxe : x ∈ ((S.bChaA m he).extend (𝓡 (8 + k))).source := by
      rw [OpenPartialHomeomorph.extend_source]
      exact S.bTarget_subset_bChaA m he hxT
    show (S.bChaR m hm).extend (𝓡 (8 + k)) ((S.bJ m hm he).symm
        (((S.bChaA m he).extend (𝓡 (8 + k))).symm
          ((S.bChaA m he).extend (𝓡 (8 + k)) x)))
      = S.bThetaInv m ((S.bChaA m he).extend (𝓡 (8 + k)) x)
    rw [PartialEquiv.left_inv (e := (S.bChaA m he).extend (𝓡 (8 + k))) hxe]
    simp only [OpenPartialHomeomorph.extend_coe, Function.comp_apply,
      modelWithCornersSelf_coe, id_eq]
    exact S.bChaR_bJ_symm m hm he hxT


/-! ## The transport of submersivity to the boundary of the region -/

theorem bJ_self_apply (m : S.Region) (hm : m ∈ (𝓡∂ (8 + k + 1)).boundary S.Region)
    (he : m.1 ∈ (𝓡∂ (8 + k + 1)).boundary S.A) :
    (S.bJ m hm he) (⟨m, hm⟩ : ↥((𝓡∂ (8 + k + 1)).boundary S.Region)) = ⟨m.1, he⟩ :=
  S.bjA_self m hm he

/-- A point of the target of a chart is in the target of its extension (identity model). -/
theorem mem_extend_target_self {α : Type*} [TopologicalSpace α]
    {f : OpenPartialHomeomorph α (EuclideanSpace ℝ (Fin (8 + k)))}
    {z : EuclideanSpace ℝ (Fin (8 + k))} (hz : z ∈ f.target) :
    z ∈ (f.extend (𝓡 (8 + k))).target := by
  rw [OpenPartialHomeomorph.extend_target]
  exact ⟨hz, by simp⟩

theorem bJ_self_mem_source (m : S.Region) (hm : m ∈ (𝓡∂ (8 + k + 1)).boundary S.Region)
    (he : m.1 ∈ (𝓡∂ (8 + k + 1)).boundary S.A) :
    (⟨m, hm⟩ : ↥((𝓡∂ (8 + k + 1)).boundary S.Region)) ∈ (S.bJ m hm he).source :=
  S.mem_bSource_self m hm he

theorem isSubmersionAt_comp_val_boundary (f : S.A → EuclideanSpace ℝ (Fin k))
    (m : S.Region) (hm : m ∈ (𝓡∂ (8 + k + 1)).boundary S.Region)
    (he : m.1 ∈ (𝓡∂ (8 + k + 1)).boundary S.A)
    (hf : IsSubmersionAt (𝓡 (8 + k)) (𝓡 k) ∞
      (fun y : ↥((𝓡∂ (8 + k + 1)).boundary S.A) => f y) ⟨m.1, he⟩) :
    IsSubmersionAt (𝓡 (8 + k)) (𝓡 k) ∞
      (fun y : ↥((𝓡∂ (8 + k + 1)).boundary S.Region) => f y.1) ⟨m, hm⟩ := by
  obtain ⟨Fc, instC, instS, hfc⟩ := hf
  letI : NormedAddCommGroup Fc := instC
  letI : NormedSpace ℝ Fc := instS
  refine ⟨Fc, instC, instS, ?_⟩
  refine IsSubmersionAtOfComplement.mk_of_charts (equiv := hfc.equiv)
    (domChart := S.bJ m hm he ≫ₕ hfc.domChart) (codChart := hfc.codChart)
    ?_ ?_ ?_ ?_ ?_ ?_
  · rw [OpenPartialHomeomorph.trans_source]
    refine ⟨S.bJ_self_mem_source m hm he, ?_⟩
    rw [Set.mem_preimage, S.bJ_self_apply m hm he]
    exact hfc.mem_domChart_source
  · exact hfc.mem_codChart_source
  · rw [IsManifold.mem_maximalAtlas_iff_contMDiffOn]
    constructor
    · have hbJ : ContMDiffOn (𝓡 (8 + k)) (𝓡 (8 + k)) ∞ (⇑(S.bJ m hm he))
          (S.bJ m hm he ≫ₕ hfc.domChart).source :=
        (S.contMDiffOn_bJ m hm he).mono (by
          rw [OpenPartialHomeomorph.trans_source]
          exact Set.inter_subset_left)
      have h1 : ContMDiffOn (𝓡 (8 + k)) (𝓡 (8 + k)) ∞ (hfc.domChart ∘ S.bJ m hm he)
          (S.bJ m hm he ≫ₕ hfc.domChart).source :=
        (contMDiffOn_of_mem_maximalAtlas hfc.domChart_mem_maximalAtlas).comp hbJ
          (by rw [OpenPartialHomeomorph.trans_source]; exact Set.inter_subset_right)
      refine h1.congr fun y hy => ?_
      rw [OpenPartialHomeomorph.trans_apply, Function.comp_apply]
    · have hψs : ContMDiffOn (𝓡 (8 + k)) (𝓡 (8 + k)) ∞ (⇑hfc.domChart.symm)
          (S.bJ m hm he ≫ₕ hfc.domChart).target :=
        (contMDiffOn_symm_of_mem_maximalAtlas hfc.domChart_mem_maximalAtlas).mono (by
          rw [OpenPartialHomeomorph.trans_target]
          exact Set.inter_subset_left)
      have h2 : ContMDiffOn (𝓡 (8 + k)) (𝓡 (8 + k)) ∞
          ((S.bJ m hm he).symm ∘ hfc.domChart.symm)
          (S.bJ m hm he ≫ₕ hfc.domChart).target :=
        (S.contMDiffOn_bJ_symm m hm he).comp hψs
          (by rw [OpenPartialHomeomorph.trans_target]; exact Set.inter_subset_right)
      refine h2.congr fun z hz => ?_
      show ((S.bJ m hm he).symm ∘ hfc.domChart.symm) z
        = (S.bJ m hm he ≫ₕ hfc.domChart).symm z
      rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
        OpenPartialHomeomorph.trans_apply, Function.comp_apply]
  · exact hfc.codChart_mem_maximalAtlas
  · intro y hy
    rw [OpenPartialHomeomorph.trans_source] at hy
    have hyS : y ∈ S.bSource m he := hy.1
    have hbd : y.1.1 ∈ (𝓡∂ (8 + k + 1)).boundary S.A :=
      S.bdry_of_mem_chi m he y (S.bU_subset_chi m he hyS)
    have hj : (S.bJ m hm he y).1 = y.1.1 := S.bjA_coe_of_mem m he hbd
    show f ↑↑y ∈ hfc.codChart.source
    rw [← hj]
    exact hfc.source_subset_preimage_source hy.2
  · intro z hz
    have hzt : z ∈ (S.bJ m hm he ≫ₕ hfc.domChart).target := by
      have h' := hz
      rw [OpenPartialHomeomorph.extend_target] at h'
      exact h'.1
    rw [OpenPartialHomeomorph.trans_target] at hzt
    have hsymm : (((S.bJ m hm he ≫ₕ hfc.domChart)).extend (𝓡 (8 + k))).symm z
        = (S.bJ m hm he).symm (hfc.domChart.symm z) := by
      rw [OpenPartialHomeomorph.extend_coe_symm, Function.comp_apply,
        modelWithCornersSelf_coe_symm, id_eq,
        OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
        OpenPartialHomeomorph.trans_apply]
    have hext : ((hfc.domChart).extend (𝓡 (8 + k))).symm z = hfc.domChart.symm z := by
      rw [OpenPartialHomeomorph.extend_coe_symm, Function.comp_apply,
        modelWithCornersSelf_coe_symm, id_eq]
    have h5 := hfc.writtenInCharts (mem_extend_target_self (f := hfc.domChart) hzt.1)
    rw [Function.comp_apply, Function.comp_apply, hext] at h5
    rw [Function.comp_apply, Function.comp_apply, hsymm]
    rw [← h5]
    congr 1
    show f ↑↑((S.bJ m hm he).symm (hfc.domChart.symm z)) = f ↑(hfc.domChart.symm z)
    exact congrArg f (S.biA_coe_of_mem m hm he (S.bU_subset_region m he hzt.2))


end RegionSetup

/-- **The region-charting theorem.** -/
theorem regionManifoldTheorem (k : ℕ) : Work.PTGeometric.RegionManifoldTheorem k := by
  intro A _ _ _ _ _ Φ hΦ hsub hone
  have hK : IsCompact {x : A | Φ x ≤ 0} :=
    (isClosed_Iic.preimage hΦ.continuous).isCompact
  let S : RegionSetup k := { A := A, Φ := Φ, hΦ := hΦ, hsub := hsub, hone := hone, hK := hK }
  refine ⟨S.Region, inferInstance, S.chartedSpaceOfRegion, S.isManifoldOfRegion,
    S.compactSpaceOfRegion, S.t2SpaceOfRegion, Homeomorph.refl S.Region, ?_, ?_, ?_, ?_, ?_⟩
  · intro m
    exact S.mem_boundary_iff m
  · intro F _ _ f hf
    intro m
    exact S.contMDiffOn_comp_val F f univ hf.contMDiffOn m (Set.mem_univ m)
  · intro F _ _ f W hf
    exact S.contMDiffOn_comp_val F f W hf
  · intro F _ _ f m hm hf
    exact S.isSubmersionAt_comp_val f m hm hf
  · intro f m hm he hf
    exact S.isSubmersionAt_comp_val_boundary f m hm he hf

end

end Work.PTGeometric
import Mathlib
import Submission.Work.Surgery.BoundaryInstances

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The boundary hyperplane in a chart of the maximal atlas

Mathlib knows (`ModelWithCorners.isBoundaryPoint_iff_of_mem_atlas`) that a point of a manifold with
boundary is a boundary point if and only if some chart *of the atlas* sends it to the frontier of
the model.  The charts produced by the submersion normal form of `Φ ∘ F` lie in the *maximal*
atlas, so we need the same statement for maximal-atlas charts.  The proof of the Mathlib statement
only ever uses its hypotheses through `IsManifold.subset_maximalAtlas`, so we reproduce it verbatim
with the hypothesis strengthened to maximal-atlas membership.

The end product is `mem_boundary_iff_extend_apply_coord_eq_zero`: for a chart `e` of the maximal
atlas around `x`, the point `x` is a boundary point of `M` exactly when the zeroth coordinate of
`e x` vanishes.
-/

open scoped Manifold Topology ContDiff
open Function Set
open ModelWithCorners

namespace Work.ThomBordism.Transversality.Preimage

noncomputable section

variable {𝕜 E H M : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M] [ChartedSpace H M]
  {n : WithTop ℕ∞}

/-- For any two charts `e`, `e'` of the *maximal* atlas around a point `x` in a C¹ manifold, `e`
maps `x` to the interior of its target iff `e'` does.  (Same proof as
`ModelWithCorners.mem_interior_range_of_mem_interior_range_of_mem_atlas`, whose hypotheses are used
only through `IsManifold.subset_maximalAtlas`.) -/
theorem mem_interior_range_of_mem_interior_range_of_mem_maximalAtlas [IsManifold I n M]
    (hn : n ≠ 0) {e e' : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I n M) (he' : e' ∈ IsManifold.maximalAtlas I n M)
    {x : M} (hex : x ∈ e.source) (hex' : x ∈ e'.source)
    (hx : e.extend I x ∈ interior (e.extend I).target) :
    e'.extend I x ∈ interior (e'.extend I).target := by
  let φ := I.extendCoordChange e e'
  have hφ : ContDiffOn 𝕜 n φ φ.source := contDiffOn_extendCoordChange he he'
  suffices h : Function.Surjective (fderivWithin 𝕜 φ φ.source (e.extend I x)) →
      e'.extend I x ∈ interior (range I) by
    refine e'.mem_interior_extend_target (by simp [hex']) <| h ?_
    exact (isInvertible_fderivWithin_extendCoordChange hn he he' <| by simp [hex, hex']).surjective
  intro hφx'
  wlog _ : IsRCLikeNormedField 𝕜
  · simp [I.range_eq_univ_of_not_isRCLikeNormedField ‹_›]
  let _ := IsRCLikeNormedField.rclike 𝕜
  let _ : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  have hφx : φ.source ∈ 𝓝 (e.extend I x) := by
    simp_rw [φ, extendCoordChange, PartialEquiv.trans_source, PartialEquiv.symm_source,
      Filter.inter_mem_iff, mem_interior_iff_mem_nhds.1 hx, true_and, e'.extend_source]
    exact e.extend_preimage_mem_nhds hex <| e'.open_source.mem_nhds hex'
  rw [← ContinuousLinearMap.coe_restrictScalars' (R := ℝ),
    (hφ.differentiableOn hn _ (by simp [φ, hex, hex'])).restrictScalars_fderivWithin (𝕜 := ℝ)
      (uniqueDiffWithinAt_of_mem_nhds hφx), fderivWithin_of_mem_nhds <| hφx] at hφx'
  rw [show e'.extend I x = φ (e.extend I x) by simp [φ, hex]]
  replace hφ := ((hφ.restrict_scalars ℝ).differentiableOn hn).differentiableAt hφx
  exact hφ.mem_interior_convex_of_surjective_fderiv hφx I.convex_range I.isClosed_range
    I.nonempty_interior (φ.mapsTo.mono_right <| by simp [φ, inter_assoc]) hφx'

/-- Interior points are chart-independent, for charts of the maximal atlas. -/
theorem mem_interior_range_iff_of_mem_maximalAtlas [IsManifold I n M]
    (hn : n ≠ 0) {e e' : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I n M) (he' : e' ∈ IsManifold.maximalAtlas I n M)
    {x : M} (hex : x ∈ e.source) (hex' : x ∈ e'.source) :
    e.extend I x ∈ interior (e.extend I).target ↔
    e'.extend I x ∈ interior (e'.extend I).target :=
  ⟨fun h => mem_interior_range_of_mem_interior_range_of_mem_maximalAtlas hn he he' hex hex' h,
   fun h => mem_interior_range_of_mem_interior_range_of_mem_maximalAtlas hn he' he hex' hex h⟩

/-- A point is an interior point iff any maximal-atlas chart sends it to the interior of its
target. -/
theorem isInteriorPoint_iff_of_mem_maximalAtlas [IsManifold I n M]
    (hn : n ≠ 0) {e : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I n M) {x : M} (hx : x ∈ e.source) :
    I.IsInteriorPoint x ↔ e.extend I x ∈ interior (e.extend I).target := by
  rw [isInteriorPoint_iff]
  exact mem_interior_range_iff_of_mem_maximalAtlas hn (IsManifold.chart_mem_maximalAtlas x) he
    (mem_chart_source H x) hx

/-- A point is a boundary point iff any maximal-atlas chart sends it to the frontier of its
target. -/
theorem isBoundaryPoint_iff_of_mem_maximalAtlas [IsManifold I n M]
    (hn : n ≠ 0) {e : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I n M) {x : M} (hx : x ∈ e.source) :
    I.IsBoundaryPoint x ↔ e.extend I x ∈ frontier (e.extend I).target := by
  rw [← not_iff_not, ← I.isInteriorPoint_iff_not_isBoundaryPoint,
    isInteriorPoint_iff_of_mem_maximalAtlas hn he hx, mem_interior_iff_notMem_frontier]
  exact (e.extend I).mapsTo <| e.extend_source (I := I) ▸ hx

/-- **The frontier of a set which is open in a closed set.**  If `T = W ∩ S` with `W` open and `S`
closed, then for `z ∈ T` the frontier of `T` and the frontier of `S` cut out the same subset of
`T`. -/
theorem frontier_inter_of_isClosed_of_isOpen_in {E : Type*} [TopologicalSpace E] {S T : Set E}
    (hS : IsClosed S) (hT : ∃ W : Set E, IsOpen W ∧ T = W ∩ S) {z : E} (hz : z ∈ T) :
    z ∈ frontier T ↔ z ∈ frontier S := by
  obtain ⟨W, hW, rfl⟩ := hT
  have hint : interior (W ∩ S) = (W ∩ S) ∩ interior S := by
    apply Set.Subset.antisymm
    · intro a ha
      exact Set.mem_inter (interior_subset ha) (interior_mono inter_subset_right ha)
    · rintro a ⟨⟨haW, haS⟩, haI⟩
      rw [mem_interior_iff_mem_nhds]
      exact Filter.inter_mem (hW.mem_nhds haW)
        (Filter.mem_of_superset (isOpen_interior.mem_nhds haI) interior_subset)
  have hcl : z ∈ closure (W ∩ S) := subset_closure hz
  rw [frontier, frontier, mem_sdiff, mem_sdiff, hS.closure_eq, hint]
  constructor
  · rintro ⟨-, h⟩
    exact ⟨hz.2, fun hc => h ⟨hz, hc⟩⟩
  · rintro ⟨-, h⟩
    exact ⟨hcl, fun hc => h hc.2⟩

section HalfSpace

variable {m : ℕ} [NeZero m] {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace m) M] [IsManifold (𝓡∂ m) (∞ : WithTop ℕ∞) M]

/-- The target of an extended chart is open in the range of the model. -/
theorem exists_isOpen_extend_target (e : OpenPartialHomeomorph M (EuclideanHalfSpace m)) :
    ∃ (W : Set (EuclideanSpace ℝ (Fin m))), IsOpen W ∧
      (e.extend (𝓡∂ m)).target = W ∩ range (𝓡∂ m) := by
  refine ⟨(𝓡∂ m).symm ⁻¹' e.target, ?_, ?_⟩
  · exact e.open_target.preimage (𝓡∂ m).continuous_symm
  · exact OpenPartialHomeomorph.extend_target e

/-- The zeroth coordinate of an extended chart is nonnegative. -/
theorem zero_le_extend_apply_coord (e : OpenPartialHomeomorph M (EuclideanHalfSpace m))
    {x : M} (hx : x ∈ e.source) : 0 ≤ ((e.extend (𝓡∂ m)) x) 0 := by
  have hmem : (e.extend (𝓡∂ m)) x ∈ (e.extend (𝓡∂ m)).target :=
    PartialEquiv.map_source _ (by simpa using hx)
  have hmem' : (e.extend (𝓡∂ m)) x ∈ range (𝓡∂ m) := by
    rw [OpenPartialHomeomorph.extend_target] at hmem
    exact hmem.2
  rw [Work.Surgery.range_halfModel] at hmem'
  exact hmem'

/-- **The boundary hyperplane in a chart of the maximal atlas.**  For a chart `e` of the maximal
atlas around `x`, the point `x` lies on the boundary of `M` exactly when the zeroth coordinate of
`e x` (in the model space) vanishes. -/
theorem mem_boundary_iff_extend_apply_coord_eq_zero
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace m)}
    (he : e ∈ IsManifold.maximalAtlas (𝓡∂ m) (∞ : WithTop ℕ∞) M) {x : M} (hx : x ∈ e.source) :
    x ∈ (𝓡∂ m).boundary M ↔ ((e.extend (𝓡∂ m)) x) 0 = 0 := by
  have hmem : (e.extend (𝓡∂ m)) x ∈ (e.extend (𝓡∂ m)).target :=
    PartialEquiv.map_source _ (by simpa using hx)
  rw [show x ∈ (𝓡∂ m).boundary M ↔ (𝓡∂ m).IsBoundaryPoint x from Iff.rfl,
    isBoundaryPoint_iff_of_mem_maximalAtlas (n := (∞ : WithTop ℕ∞)) (by simp) he hx,
    frontier_inter_of_isClosed_of_isOpen_in (𝓡∂ m).isClosed_range (exists_isOpen_extend_target e) hmem,
    Work.Surgery.frontier_range_halfModel]
  exact Work.Surgery.mem_hyperplane_iff

end HalfSpace

end

end Work.ThomBordism.Transversality.Preimage

import Mathlib
import Submission.Work.ThomBordism.doubleDefs
import Submission.Work.ThomBordism.doubleCharted

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Every seam point of the double lies in the closure of the interior of the first copy

The double `D = M ∪_∂M M` of a `C¹` manifold with boundary (`Work.ThomBordism.Double`) contains the
image `doubleιM '' M` of the first copy.  This file shows that a point `doubleιM b.1` of the *seam*
(a boundary point of `M`) is a limit of points of the interior of the first copy, i.e. lies in the
closure of `Set.range (interiorEmb)`.

The mathematical content is that the interior of a `C¹` manifold with boundary is dense: a boundary
point is a limit of interior points (`boundary_mem_closure_interior`).  For a boundary point `b` the
preferred chart at `b` sends a neighbourhood of `b` to a neighbourhood of `b`'s image in the model
half-space; the extended chart of `b` therefore meets the half-space `{0 < x 0}` (the model interior)
in points arbitrarily close to the image of `b`.  The `C¹` hypothesis is used through
`ModelWithCorners.isInteriorPoint_iff_of_mem_atlas`, which makes the notion of interior point
chart-independent.
-/

open scoped Manifold Topology
open Function Set

namespace Work.ThomBordism.doubleFC

/-- **A general topological lemma.**  If `f` is continuous within `t` at `x`, `x` lies in the
closure of `s` and `s ⊆ t`, then `f x` lies in the closure of `f '' s`.

(Continuity is only assumed *within* `t`, which need not be a neighbourhood of `x`; the point is that
`s` is dense enough near `x` to supply the points at which continuity within `t` is used.) -/
theorem continuousWithinAt_mem_closure_image_of_subset {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] {f : α → β} {s t : Set α} {x : α}
    (h : ContinuousWithinAt f t x) (hx : x ∈ closure s) (hst : s ⊆ t) :
    f x ∈ closure (f '' s) := by
  rw [mem_closure_iff] at hx ⊢
  intro V hV hfxV
  obtain ⟨u, hu, hxu, husub⟩ := mem_nhdsWithin.mp (h.preimage_mem_nhdsWithin (hV.mem_nhds hfxV))
  obtain ⟨y, hyu, hys⟩ := hx u hu hxu
  exact ⟨f y, husub ⟨hyu, hst hys⟩, y, hys, rfl⟩

/-- **The interior of a `C¹` manifold with boundary is dense**: every boundary point is a limit of
interior points. -/
theorem boundary_mem_closure_interior (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 M]
    (b : (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M) :
    b.1 ∈ closure ((modelWithCornersEuclideanHalfSpace (n + 1)).interior M) := by
  set e : OpenPartialHomeomorph M (EuclideanHalfSpace (n + 1)) :=
    chartAt (EuclideanHalfSpace (n + 1)) b.1 with he
  set φ : PartialEquiv M (EuclideanSpace ℝ (Fin (n + 1))) :=
    extChartAt (𝓡∂ (n + 1)) b.1 with hφ
  set x : EuclideanSpace ℝ (Fin (n + 1)) := Subtype.val (e b.1) with hx
  have he_mem : e ∈ atlas (EuclideanHalfSpace (n + 1)) M := by
    rw [he]; exact chart_mem_atlas _ _
  have hφsrc : φ.source = e.source := by
    rw [hφ, he]; exact OpenPartialHomeomorph.extend_source _
  have hφtgt : φ.target = Set.range (↑(𝓡∂ (n + 1))) ∩ (𝓡∂ (n + 1)).symm ⁻¹' e.target := by
    rw [hφ, he, extChartAt_target, Set.inter_comm]
  have hφext : e.extend (𝓡∂ (n + 1)) = φ := by
    rw [he, hφ]; rfl
  have hφb : φ b.1 = x := by
    rw [hx, hφ, he]
    simp only [extChartAt, OpenPartialHomeomorph.extend_coe, Function.comp_apply,
      modelWithCornersEuclideanHalfSpace_toFun]
  have hb_src : b.1 ∈ φ.source := by rw [hφ]; exact mem_extChartAt_source _
  have hxT : x ∈ φ.target := by rw [← hφb]; exact φ.map_source hb_src
  have hxcoord : x 0 = 0 := by
    rw [hx, he]; exact chartAt_self_coord_zero b
  have hx_cl : x ∈ closure {y : EuclideanSpace ℝ (Fin (n + 1)) | 0 < y 0} := by
    rw [closure_open_halfSpace (n := n + 1) 2 0 0]
    simp [hxcoord]
  have hOopen : IsOpen ((𝓡∂ (n + 1)).symm ⁻¹' e.target) :=
    e.open_target.preimage (𝓡∂ (n + 1)).continuous_symm
  have hsymm : (𝓡∂ (n + 1)).symm x = e b.1 := by
    rw [hx]; exact (𝓡∂ (n + 1)).left_inv (e b.1)
  have hxO : x ∈ (𝓡∂ (n + 1)).symm ⁻¹' e.target := by
    rw [Set.mem_preimage, hsymm, he]; exact mem_chart_target _ _
  have hInt : interior φ.target =
      {y : EuclideanSpace ℝ (Fin (n + 1)) | 0 < y 0} ∩ ((𝓡∂ (n + 1)).symm ⁻¹' e.target) := by
    rw [hφtgt, interior_inter, hOopen.interior_eq,
      modelWithCornersEuclideanHalfSpace_toFun, range_euclideanHalfSpace,
      interior_halfSpace (n := n + 1) 2 0 0]
  have hx_cl_intT : x ∈ closure (interior φ.target) := by
    rw [hInt]
    exact hOopen.closure_inter ⟨hx_cl, hxO⟩
  have hTsymm : ∀ z ∈ interior φ.target, ⇑(φ.symm) z ∈ (𝓡∂ (n + 1)).interior M := by
    intro z hz
    have hzT : z ∈ φ.target := interior_subset hz
    have hye : ⇑(φ.symm) z ∈ e.source := by
      have h1 : ⇑(φ.symm) z ∈ φ.source := φ.map_target hzT
      rwa [hφsrc] at h1
    change (𝓡∂ (n + 1)).IsInteriorPoint (⇑(φ.symm) z)
    have hkey := ModelWithCorners.isInteriorPoint_iff_of_mem_atlas (I := 𝓡∂ (n + 1)) (M := M)
      (n := (1 : WithTop ℕ∞)) (by norm_num) (e := e) he_mem hye
    rw [hφext] at hkey
    rw [hkey, φ.right_inv hzT]
    exact hz
  have hcont : ContinuousWithinAt (⇑(φ.symm)) φ.target x := by
    have hcon : ContinuousOn (⇑(φ.symm)) φ.target := by
      rw [hφ]; exact continuousOn_extChartAt_symm b.1
    exact hcon.continuousWithinAt hxT
  have hb1 : ⇑(φ.symm) x = b.1 := by
    rw [← hφb]
    exact φ.left_inv hb_src
  have hmem : b.1 ∈ closure (⇑(φ.symm) '' interior φ.target) := by
    rw [← hb1]
    exact continuousWithinAt_mem_closure_image_of_subset hcont hx_cl_intT interior_subset
  have hsub : ⇑(φ.symm) '' interior φ.target ⊆ (𝓡∂ (n + 1)).interior M := by
    rintro y ⟨z, hz, rfl⟩
    exact hTsymm z hz
  exact closure_mono hsub hmem

/-- **Every seam point of the double is in the closure of the interior of the first copy.**

(The `[IsManifold]` hypothesis is needed: the boundary/interior dichotomy of a half-space-charted
space is chart-independent only for `C¹` manifolds.)  Route: it suffices that `interior M` is dense
in `M`.  For `y` near a boundary point, use `Work.ThomBordism.chartMemHyperplane` and the extended
chart at `b`: points of the chart's source whose image has positive first coordinate are interior
points, and they approach `b`; conclude with the continuity of `doubleιM`. -/
theorem seam_mem_closure_interior (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 M]
    (b : (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M) :
    doubleιM (n := n) (M := M) b.1 ∈ closure (Set.range (interiorEmb (n := n) (M := M))) := by
  have hb : b.1 ∈ closure ((𝓡∂ (n + 1)).interior M) :=
    boundary_mem_closure_interior n M b
  have himg : Set.range (interiorEmb (n := n) (M := M))
      = doubleιM (n := n) (M := M) '' ((𝓡∂ (n + 1)).interior M) := by
    ext z
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨u.1, by rw [← ModelWithCorners.compl_boundary]; exact u.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, by rw [ModelWithCorners.compl_boundary]; exact hy⟩, rfl⟩
  rw [himg]
  exact image_closure_subset_closure_image (continuous_doubleιM (n := n) (M := M))
    ⟨b.1, hb, rfl⟩

end Work.ThomBordism.doubleFC

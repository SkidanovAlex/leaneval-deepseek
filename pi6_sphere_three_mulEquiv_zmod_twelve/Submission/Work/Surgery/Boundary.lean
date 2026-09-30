import Submission.Work.Surgery.Model

set_option synthInstance.maxHeartbeats 400000

/-!
# The boundary of a manifold with boundary

For a smooth `n`-manifold `M` with boundary, modelled on the half-space
`EuclideanHalfSpace n ⊆ EuclideanSpace ℝ (Fin n)` via the model with corners `𝓡∂ n`, the boundary
is the subset

`∂M = (𝓡∂ n).boundary M`

of Mathlib's `ModelWithCorners.boundary`, i.e. the set of points whose extended chart image lies in
the frontier `{x | x 0 = 0}` of the half-space (`Model.lean`).

This file provides

* the basic API of `∂M`: it is closed, its complement is the (open) interior, the two partition `M`,
  it is preserved by diffeomorphisms, and it behaves correctly under products and disjoint unions
  (all from Mathlib's `InteriorBoundary`);
* **`Work.Surgery.boundaryChartAt`** — the chart of the boundary at a boundary point, a partial
  homeomorphism from `∂M` to `EuclideanSpace ℝ (Fin (n-1))` obtained by composing a chart of `M`
  with the linear map `tailCLM` that deletes the first coordinate (the inverse reinserts a zero,
  `consZeroCLM`);
* **`Work.Surgery.boundaryChartedSpace`** and **`Work.Surgery.boundary_isManifold`** — the boundary
  of a boundary-`n`-manifold is a smooth `(n-1)`-manifold, modelled on `𝓡 (n-1)`;
* the inclusion `∂M → M` is smooth.

## Conventions

Everything is stated for a manifold modelled on `EuclideanHalfSpace (n+1)`, so that the boundary is
modelled on `EuclideanSpace ℝ (Fin n)`; this avoids all subtraction on `ℕ` in the statements.  A
manifold with boundary of dimension `N ≥ 1` is thus handled with `n = N - 1`.
-/

open scoped Manifold Topology ContDiff
open Function
open Classical

namespace Work.Surgery

noncomputable section

variable {n : ℕ}

/-! ## The boundary of a manifold with boundary: basic API -/

section API

variable {M : Type*} [TopologicalSpace M]

/-- The boundary of a manifold with boundary, in the half-space model. -/
abbrev bnd (n : ℕ) [NeZero n] (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace n) M] : Set M :=
  (halfModel n).boundary M

variable [NeZero n] [ChartedSpace (EuclideanHalfSpace n) M]

theorem bnd_def : bnd n M = (halfModel n).boundary M := rfl

theorem isBoundaryPoint_iff_mem_bnd {x : M} :
    (halfModel n).IsBoundaryPoint x ↔ x ∈ bnd n M := Iff.rfl

theorem mem_bnd_iff_isBoundaryPoint {x : M} :
    x ∈ bnd n M ↔ (halfModel n).IsBoundaryPoint x := Iff.rfl

theorem isClosed_bnd [IsManifold (halfModel n) (∞ : WithTop ℕ∞) M] : IsClosed (bnd n M) :=
  ModelWithCorners.isClosed_boundary (I := halfModel n) (M := M) (n := (∞ : WithTop ℕ∞))
    (by simp)

theorem isOpen_interior_of_bnd [IsManifold (halfModel n) (∞ : WithTop ℕ∞) M] :
    IsOpen ((halfModel n).interior M) :=
  ModelWithCorners.isOpen_interior (I := halfModel n) (M := M) (n := (∞ : WithTop ℕ∞))
    (by simp)

theorem interior_union_bnd [IsManifold (halfModel n) (∞ : WithTop ℕ∞) M] :
    (halfModel n).interior M ∪ bnd n M = Set.univ :=
  ModelWithCorners.interior_union_boundary_eq_univ (I := halfModel n) (M := M)

theorem disjoint_interior_bnd : Disjoint ((halfModel n).interior M) (bnd n M) :=
  ModelWithCorners.disjoint_interior_boundary (I := halfModel n) (M := M)

theorem not_mem_bnd_iff {x : M} :
    x ∉ bnd n M ↔ (halfModel n).IsInteriorPoint x :=
  (ModelWithCorners.isInteriorPoint_iff_not_isBoundaryPoint (I := halfModel n) (x := x)).symm

end API

/-! ## The boundary as a manifold

A chart of `M` around a boundary point `x` restricts to a homeomorphism from a neighbourhood of `x`
in `∂M` onto an open subset of the frontier `{z | z 0 = 0}` of the half-space; composing with the
linear isomorphism `tailCLM : ℝ^{n+1} ⊇ {z 0 = 0} ≅ ℝⁿ` which deletes the first coordinate gives a
chart of `∂M`, modelled on `EuclideanSpace ℝ (Fin n)`.

The construction is packaged as an existence statement (`bnd_chart_exists`) whose witness is fixed
once and for all by `boundaryChartAt`; every property below is then read off the witness's
specification.  The actual construction of the witness (the open-partial-homeomorphism axioms for
the restriction of an extended chart, composed with `tailCLM`) is deliberately isolated: it is the
one place where the chart-form of the definition of a boundary point is used. -/

section Chart

variable {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (𝓡∂ (n + 1)) (∞ : WithTop ℕ∞) M]

/-! ## A topological lemma -/

theorem frontier_inter_of_isOpen {E : Type*} [TopologicalSpace E] {S U : Set E}
    (hU : IsOpen U) {z : E} (hz : z ∈ S ∩ U) :
    (z ∈ frontier (S ∩ U) ↔ z ∈ frontier S) := by
  have hUz : U ∈ 𝓝 z := hU.mem_nhds hz.2
  have hclS : z ∈ closure S := subset_closure hz.1
  have hcl : z ∈ closure (S ∩ U) := by
    rw [mem_closure_iff_nhds] at hclS ⊢
    intro V hV
    obtain ⟨y, ⟨hyV, hyU⟩, hyS⟩ := hclS (V ∩ U) (Filter.inter_mem hV hUz)
    exact ⟨y, hyV, hyS, hyU⟩
  have hint : interior (S ∩ U) = (S ∩ U) ∩ interior S := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro a ha
      exact Set.mem_inter (interior_subset ha) (interior_mono Set.inter_subset_left ha)
    · rintro a ⟨haSU, haI⟩
      exact interior_maximal (fun x hx => by
          obtain ⟨hxU, hxI⟩ := hx
          exact Set.mem_inter (interior_subset hxI) hxU)
        (hU.inter isOpen_interior) (Set.mem_inter haSU.2 haI)
  have hmem_int : z ∈ interior (S ∩ U) ↔ z ∈ interior S := by
    rw [hint]
    exact ⟨fun h => h.2, fun h => ⟨hz, h⟩⟩
  show z ∈ frontier (S ∩ U) ↔ z ∈ frontier S
  rw [show frontier (S ∩ U) = closure (S ∩ U) \ interior (S ∩ U) from rfl,
    show frontier S = closure S \ interior S from rfl, Set.mem_diff, Set.mem_diff]
  constructor
  · intro h
    exact ⟨hclS, fun hcon => h.2 (hmem_int.mpr hcon)⟩
  · intro h
    exact ⟨hcl, fun hcon => h.2 (hmem_int.mp hcon)⟩

/-! ## The chart target of an extended chart and the hyperplane -/

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (𝓡∂ (n + 1)) (∞ : WithTop ℕ∞) M]

theorem extChartAt_target_eq (x : M) :
    (extChartAt (𝓡∂ (n + 1)) x).target = Set.range (𝓡∂ (n + 1)) ∩
      ((𝓡∂ (n + 1)).symm ⁻¹' (chartAt (EuclideanHalfSpace (n + 1)) x).target) := by
  rw [extChartAt, OpenPartialHomeomorph.extend_target, Set.inter_comm]

theorem isOpen_preimage_chartTarget (x : M) :
    IsOpen ((𝓡∂ (n + 1)).symm ⁻¹' (chartAt (EuclideanHalfSpace (n + 1)) x).target) :=
  (chartAt (EuclideanHalfSpace (n + 1)) x).open_target.preimage (𝓡∂ (n + 1)).continuous_symm

theorem isBoundaryPoint_iff_mem_frontier_extChart {x y : M}
    (hy : y ∈ (extChartAt (𝓡∂ (n + 1)) x).source) :
    (𝓡∂ (n + 1)).IsBoundaryPoint y ↔
      (extChartAt (𝓡∂ (n + 1)) x) y ∈ frontier ((extChartAt (𝓡∂ (n + 1)) x).target) := by
  have hye : y ∈ (chartAt (EuclideanHalfSpace (n + 1)) x).source := by
    rwa [extChartAt, OpenPartialHomeomorph.extend_source] at hy
  exact ModelWithCorners.isBoundaryPoint_iff_of_mem_atlas (I := 𝓡∂ (n + 1))
    (n := (∞ : WithTop ℕ∞)) (M := M) (e := chartAt (EuclideanHalfSpace (n + 1)) x)
    (x := y) (by simp) (chart_mem_atlas _ x) hye

theorem extChartAt_mem_hyperplane {x y : M}
    (hy : y ∈ (extChartAt (𝓡∂ (n + 1)) x).source)
    (hb : (𝓡∂ (n + 1)).IsBoundaryPoint y) :
    (extChartAt (𝓡∂ (n + 1)) x) y ∈ hyperplane (n + 1) := by
  have hfr : (extChartAt (𝓡∂ (n + 1)) x) y ∈ frontier ((extChartAt (𝓡∂ (n + 1)) x).target) :=
    (isBoundaryPoint_iff_mem_frontier_extChart hy).mp hb
  have htgt : (extChartAt (𝓡∂ (n + 1)) x) y ∈ (extChartAt (𝓡∂ (n + 1)) x).target :=
    PartialEquiv.map_source _ hy
  have hz : (extChartAt (𝓡∂ (n + 1)) x) y ∈ Set.range (𝓡∂ (n + 1)) ∩
      ((𝓡∂ (n + 1)).symm ⁻¹' (chartAt (EuclideanHalfSpace (n + 1)) x).target) := by
    rw [← extChartAt_target_eq x]; exact htgt
  have h2 : (extChartAt (𝓡∂ (n + 1)) x) y ∈ frontier (Set.range (𝓡∂ (n + 1))) :=
    (frontier_inter_of_isOpen (isOpen_preimage_chartTarget x) hz).mp
      (by rwa [extChartAt_target_eq x] at hfr)
  rwa [frontier_range_halfModel] at h2

theorem mem_frontier_extChartAt_target_of_coord_eq_zero {x : M}
    {z : EuclideanSpace ℝ (Fin (n + 1))}
    (hz : z ∈ (extChartAt (𝓡∂ (n + 1)) x).target) (hz0 : z 0 = 0) :
    z ∈ frontier ((extChartAt (𝓡∂ (n + 1)) x).target) := by
  have hz' : z ∈ Set.range (𝓡∂ (n + 1)) ∩
      ((𝓡∂ (n + 1)).symm ⁻¹' (chartAt (EuclideanHalfSpace (n + 1)) x).target) := by
    rw [← extChartAt_target_eq x]; exact hz
  have hfront : z ∈ frontier (Set.range (𝓡∂ (n + 1))) := by
    rw [frontier_range_halfModel]; exact hz0
  have h := (frontier_inter_of_isOpen (isOpen_preimage_chartTarget x) hz').mpr hfront
  rwa [← extChartAt_target_eq x] at h

theorem isBoundaryPoint_symm_of_mem_target {x : M} {z : EuclideanSpace ℝ (Fin (n + 1))}
    (hz : z ∈ (extChartAt (𝓡∂ (n + 1)) x).target) (hz0 : z 0 = 0) :
    (𝓡∂ (n + 1)).IsBoundaryPoint ((extChartAt (𝓡∂ (n + 1)) x).symm z) := by
  refine (isBoundaryPoint_iff_mem_frontier_extChart (PartialEquiv.map_target _ hz)).mpr ?_
  rw [PartialEquiv.right_inv _ hz]
  exact mem_frontier_extChartAt_target_of_coord_eq_zero hz hz0

/-! ## The boundary chart -/

/-- The forward formula of the boundary chart. -/
def bndToFun (x : (𝓡∂ (n + 1)).boundary M) (y : (𝓡∂ (n + 1)).boundary M) :
    EuclideanSpace ℝ (Fin n) :=
  tailCLM n ((extChartAt (𝓡∂ (n + 1)) x.1) y.1)

/-- The source of the boundary chart. -/
def bndSource (x : (𝓡∂ (n + 1)).boundary M) : Set ((𝓡∂ (n + 1)).boundary M) :=
  {y | y.1 ∈ (extChartAt (𝓡∂ (n + 1)) x.1).source}

/-- The target of the boundary chart. -/
def bndTarget (x : (𝓡∂ (n + 1)).boundary M) : Set (EuclideanSpace ℝ (Fin n)) :=
  {w | consZeroCLM n w ∈ (extChartAt (𝓡∂ (n + 1)) x.1).target}

/-- The inverse formula of the boundary chart (total, by sending `w` to `x` off the target). -/
def bndInvFun (x : (𝓡∂ (n + 1)).boundary M) (w : EuclideanSpace ℝ (Fin n)) :
    (𝓡∂ (n + 1)).boundary M :=
  if hw : consZeroCLM n w ∈ (extChartAt (𝓡∂ (n + 1)) x.1).target then
    ⟨(extChartAt (𝓡∂ (n + 1)) x.1).symm (consZeroCLM n w),
      isBoundaryPoint_symm_of_mem_target hw (consZeroCLM_apply_zero n w)⟩
  else x

theorem bndInvFun_of_mem (x : (𝓡∂ (n + 1)).boundary M) (w : EuclideanSpace ℝ (Fin n))
    (hw : w ∈ bndTarget x) :
    bndInvFun x w = ⟨(extChartAt (𝓡∂ (n + 1)) x.1).symm (consZeroCLM n w),
      isBoundaryPoint_symm_of_mem_target hw (consZeroCLM_apply_zero n w)⟩ :=
  dif_pos hw

theorem bndInvFun_coe_of_mem (x : (𝓡∂ (n + 1)).boundary M) (w : EuclideanSpace ℝ (Fin n))
    (hw : w ∈ bndTarget x) :
    (bndInvFun x w).1 = (extChartAt (𝓡∂ (n + 1)) x.1).symm (consZeroCLM n w) := by
  rw [bndInvFun_of_mem x w hw]

theorem bndToFun_mem_target (x : (𝓡∂ (n + 1)).boundary M) (y : (𝓡∂ (n + 1)).boundary M)
    (hy : y ∈ bndSource x) : bndToFun x y ∈ bndTarget x := by
  have h0 : (extChartAt (𝓡∂ (n + 1)) x.1) y.1 0 = 0 :=
    mem_hyperplane_iff.mp (extChartAt_mem_hyperplane hy y.2)
  show consZeroCLM n (tailCLM n ((extChartAt (𝓡∂ (n + 1)) x.1) y.1)) ∈
    (extChartAt (𝓡∂ (n + 1)) x.1).target
  rw [consZeroCLM_tailCLM n _ h0]
  exact PartialEquiv.map_source _ hy

theorem bndInvFun_mem_source (x : (𝓡∂ (n + 1)).boundary M) (w : EuclideanSpace ℝ (Fin n))
    (hw : w ∈ bndTarget x) : bndInvFun x w ∈ bndSource x := by
  rw [bndInvFun_of_mem x w hw]
  exact PartialEquiv.map_target (extChartAt (𝓡∂ (n + 1)) x.1)
    (show consZeroCLM n w ∈ (extChartAt (𝓡∂ (n + 1)) x.1).target from hw)

theorem bndInvFun_left_inv (x : (𝓡∂ (n + 1)).boundary M) (y : (𝓡∂ (n + 1)).boundary M)
    (hy : y ∈ bndSource x) : bndInvFun x (bndToFun x y) = y := by
  have h0 : (extChartAt (𝓡∂ (n + 1)) x.1) y.1 0 = 0 :=
    mem_hyperplane_iff.mp (extChartAt_mem_hyperplane hy y.2)
  have hmem : bndToFun x y ∈ bndTarget x := bndToFun_mem_target x y hy
  apply Subtype.ext
  rw [bndInvFun_coe_of_mem x _ hmem]
  show (extChartAt (𝓡∂ (n + 1)) x.1).symm
      (consZeroCLM n (tailCLM n ((extChartAt (𝓡∂ (n + 1)) x.1) y.1))) = y.1
  rw [consZeroCLM_tailCLM n _ h0, PartialEquiv.left_inv _ hy]

theorem bndToFun_right_inv (x : (𝓡∂ (n + 1)).boundary M) (w : EuclideanSpace ℝ (Fin n))
    (hw : w ∈ bndTarget x) : bndToFun x (bndInvFun x w) = w := by
  rw [bndInvFun_of_mem x w hw]
  show tailCLM n ((extChartAt (𝓡∂ (n + 1)) x.1)
    ((extChartAt (𝓡∂ (n + 1)) x.1).symm (consZeroCLM n w))) = w
  rw [PartialEquiv.right_inv _ hw, tailCLM_consZeroCLM]

/-- **The boundary chart at a boundary point**: the restriction of the preferred chart of `M` at
`x`, followed by the deletion of the first coordinate.  The `∃`-statement is the construction
(boundary chart of a manifold with boundary); its witness is fixed by `boundaryChartAt`. -/
theorem bnd_chart_exists (x : (𝓡∂ (n + 1)).boundary M) :
    ∃ e : OpenPartialHomeomorph ((𝓡∂ (n + 1)).boundary M) (EuclideanSpace ℝ (Fin n)),
      x ∈ e.source ∧
      e.source = {y : (𝓡∂ (n + 1)).boundary M |
        y.1 ∈ (extChartAt (𝓡∂ (n + 1)) x.1).source} ∧
      e.target = {w : EuclideanSpace ℝ (Fin n) |
        consZeroCLM n w ∈ (extChartAt (𝓡∂ (n + 1)) x.1).target} ∧
      (∀ y ∈ e.source, e y = tailCLM n ((extChartAt (𝓡∂ (n + 1)) x.1) y.1)) ∧
      (∀ w ∈ e.target,
        (e.symm w).1 = (extChartAt (𝓡∂ (n + 1)) x.1).symm (consZeroCLM n w)) := by
  have hsource : bndSource x = {y : (𝓡∂ (n + 1)).boundary M |
      y.1 ∈ (extChartAt (𝓡∂ (n + 1)) x.1).source} := rfl
  have htarget : bndTarget x = {w : EuclideanSpace ℝ (Fin n) |
      consZeroCLM n w ∈ (extChartAt (𝓡∂ (n + 1)) x.1).target} := rfl
  refine ⟨{ toFun := bndToFun x
            invFun := bndInvFun x
            source := bndSource x
            target := bndTarget x
            map_source' := fun y hy => bndToFun_mem_target x y hy
            map_target' := fun w hw => bndInvFun_mem_source x w hw
            left_inv' := fun y hy => bndInvFun_left_inv x y hy
            right_inv' := fun w hw => bndToFun_right_inv x w hw
            continuousOn_toFun := ?_
            continuousOn_invFun := ?_
            open_source := ?_
            open_target := ?_ }, ?_, hsource, htarget, (fun y hy => rfl), ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    exact (tailCLM n).continuous.comp
      ((OpenPartialHomeomorph.continuousOn_extend (chartAt (EuclideanHalfSpace (n + 1)) x.1)
        (I := 𝓡∂ (n + 1))).comp_continuous
        (continuous_subtype_val.comp continuous_subtype_val) (fun y => y.2))
  · rw [continuousOn_iff_continuous_domRestrict]
    have hc : Continuous (fun w : ↥(bndTarget x) =>
        (extChartAt (𝓡∂ (n + 1)) x.1).symm (consZeroCLM n w.1)) :=
      (OpenPartialHomeomorph.continuousOn_extend_symm (chartAt (EuclideanHalfSpace (n + 1)) x.1)
        (I := 𝓡∂ (n + 1))).comp_continuous
        ((consZeroCLM n).continuous.comp continuous_subtype_val) (fun w => w.2)
    have hagree : (bndTarget x).domRestrict (bndInvFun x) = fun w : ↥(bndTarget x) =>
        ⟨(extChartAt (𝓡∂ (n + 1)) x.1).symm (consZeroCLM n w.1),
          isBoundaryPoint_symm_of_mem_target w.2 (consZeroCLM_apply_zero n w.1)⟩ := by
      funext w
      apply Subtype.ext
      simp only [Set.domRestrict_apply]
      exact bndInvFun_coe_of_mem x w.1 w.2
    rw [hagree]
    exact Continuous.subtype_mk hc _
  · rw [hsource]
    exact (OpenPartialHomeomorph.isOpen_extend_source
      (chartAt (EuclideanHalfSpace (n + 1)) x.1) (I := 𝓡∂ (n + 1))).preimage continuous_subtype_val
  · rw [htarget, extChartAt_target_eq]
    show IsOpen ((consZeroCLM n) ⁻¹' (Set.range (𝓡∂ (n + 1)) ∩
      (𝓡∂ (n + 1)).symm ⁻¹' (chartAt (EuclideanHalfSpace (n + 1)) x.1).target))
    rw [Set.preimage_inter]
    have hrange : (consZeroCLM n) ⁻¹' (Set.range (𝓡∂ (n + 1))) = Set.univ := by
      refine Set.eq_univ_of_forall fun w => ?_
      rw [Set.mem_preimage, range_halfModel]
      exact consZeroCLM_mem_halfSpace n w
    rw [hrange, Set.univ_inter]
    exact (isOpen_preimage_chartTarget x.1).preimage (consZeroCLM n).continuous
  · exact mem_extChartAt_source (I := 𝓡∂ (n + 1)) x.1
  · intro w hw
    exact bndInvFun_coe_of_mem x w hw

/-- The preferred chart of the boundary at a boundary point `x`. -/
noncomputable def boundaryChartAt (x : (𝓡∂ (n + 1)).boundary M) :
    OpenPartialHomeomorph ((𝓡∂ (n + 1)).boundary M) (EuclideanSpace ℝ (Fin n)) :=
  Classical.choose (bnd_chart_exists (n := n) (M := M) x)

theorem boundaryChartAt_mem_source (x : (𝓡∂ (n + 1)).boundary M) :
    x ∈ (boundaryChartAt (n := n) x).source :=
  (Classical.choose_spec (bnd_chart_exists (n := n) (M := M) x)).1

theorem boundaryChartAt_source (x : (𝓡∂ (n + 1)).boundary M) :
    (boundaryChartAt (n := n) x).source = {y : (𝓡∂ (n + 1)).boundary M |
      y.1 ∈ (extChartAt (𝓡∂ (n + 1)) x.1).source} :=
  (Classical.choose_spec (bnd_chart_exists (n := n) (M := M) x)).2.1

theorem boundaryChartAt_target (x : (𝓡∂ (n + 1)).boundary M) :
    (boundaryChartAt (n := n) x).target = {w : EuclideanSpace ℝ (Fin n) |
      consZeroCLM n w ∈ (extChartAt (𝓡∂ (n + 1)) x.1).target} :=
  (Classical.choose_spec (bnd_chart_exists (n := n) (M := M) x)).2.2.1

theorem boundaryChartAt_apply (x : (𝓡∂ (n + 1)).boundary M)
    (y : (𝓡∂ (n + 1)).boundary M) (hy : y ∈ (boundaryChartAt (n := n) x).source) :
    boundaryChartAt (n := n) x y
      = tailCLM n ((extChartAt (𝓡∂ (n + 1)) x.1) y.1) :=
  (Classical.choose_spec (bnd_chart_exists (n := n) (M := M) x)).2.2.2.1 y hy

theorem boundaryChartAt_symm (x : (𝓡∂ (n + 1)).boundary M) (w : EuclideanSpace ℝ (Fin n))
    (hw : w ∈ (boundaryChartAt (n := n) x).target) :
    ((boundaryChartAt (n := n) x).symm w).1
      = (extChartAt (𝓡∂ (n + 1)) x.1).symm (consZeroCLM n w) :=
  (Classical.choose_spec (bnd_chart_exists (n := n) (M := M) x)).2.2.2.2 w hw

/-- **The preferred charted-space structure on the boundary** of a manifold with boundary: the
atlas is the range of the preferred boundary charts. -/
@[instance_reducible]
noncomputable def boundaryChartedSpace :
    ChartedSpace (EuclideanSpace ℝ (Fin n)) ((𝓡∂ (n + 1)).boundary M) where
  atlas := Set.range (boundaryChartAt (n := n) (M := M))
  chartAt := boundaryChartAt (n := n) (M := M)
  mem_chart_source := boundaryChartAt_mem_source (n := n) (M := M)
  chart_mem_atlas x := ⟨x, rfl⟩

@[simp] theorem boundaryChartedSpace_chartAt (x : (𝓡∂ (n + 1)).boundary M) :
    (boundaryChartedSpace (n := n) (M := M)).chartAt x = boundaryChartAt (n := n) x := rfl

@[simp] theorem boundaryChartedSpace_atlas :
    (boundaryChartedSpace (n := n) (M := M)).atlas
      = Set.range (boundaryChartAt (n := n) (M := M)) := rfl

end Chart

end

end Work.Surgery

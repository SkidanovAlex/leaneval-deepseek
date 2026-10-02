import Mathlib
import Submission.Work.ThomBordism.doubleDefs
import Submission.Work.Surgery.Gluing
import Submission.Work.Surgery.GluingPointSet

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The double `M ∪_∂M M` of a manifold with boundary is a charted space

For a `C¹` manifold `M` with boundary, modelled on the half-space `EuclideanHalfSpace (n+1)`,
the double `Work.ThomBordism.Double n M = M ∪_∂M M` (gluing two copies of `M` along the identity
of the boundary, `Submission/Work/ThomBordism/doubleDefs.lean`) carries a charted-space structure
modelled on the boundaryless model `EuclideanSpace ℝ (Fin (n+1))`.

This is the point-set part of the statement that the double of a manifold with boundary is a
manifold without boundary.  The charts are of two kinds:

* at an **interior** point of `M`, the interior chart of `M` (`extChartAt` cut down so that its
  target lies in the interior of the half-space), pushed forward along the open embedding of the
  interior of `M` into the double;
* at a **boundary** point `x`, the *seam chart*: the chart `e = chartAt _ x` of `M` at `x` is
  thickened to an open subset `T` of the ambient model space (a ball-like open set, symmetric
  under the reflection `flipEucl` of the first coordinate, whose positive half is the target of
  `e`), and the double is read through `e` on the first half and `flipEucl ∘ e` on the second half.
  The two formulas agree on the seam because a chart sends boundary points to the hyperplane
  `{x | x 0 = 0}` (`Work.ThomBordism.chartMemHyperplane`), where `flipEucl` is the identity.

## Contents

* `Work.ThomBordism.chartMemHyperplane` — a chart of the atlas sends boundary points of `M` into
  the hyperplane;
* `Work.ThomBordism.intChartD` — the interior charts of the double;
* `Work.ThomBordism.seamChart` — the seam charts of the double, and its source/target/evaluation
  API;
* `Work.ThomBordism.doubleChartedSpace` — the charted space structure, and
  `Work.ThomBordism.doubleCharted` — its `Nonempty` form, the statement of this file.
-/

open scoped Manifold Topology
open Function Set
open Classical

namespace Work.ThomBordism

noncomputable section

/-- The half-space model `𝓡∂ (n+1)` at dimension `n+1`. -/
abbrev hModel (n : ℕ) :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin (n + 1))) (EuclideanHalfSpace (n + 1)) :=
  modelWithCornersEuclideanHalfSpace (n + 1)

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 M]

/-! ## The boundary of a `C¹` manifold with boundary -/

/-- The boundary `∂M` of a `C¹` manifold with boundary is closed. -/
theorem isClosed_boundary_one :
    IsClosed ((hModel n).boundary M) :=
  ModelWithCorners.isClosed_boundary (I := hModel n) (M := M)
    (n := (1 : WithTop ℕ∞)) (by norm_num)

/-- The interior of a `C¹` manifold with boundary is open. -/
theorem isOpen_interior_one : IsOpen ((hModel n).interior M) :=
  ModelWithCorners.isOpen_interior (I := hModel n) (M := M)
    (n := (1 : WithTop ℕ∞)) (by norm_num)

/-- **A chart of the atlas sends boundary points to the hyperplane.**  If `e` is a chart in the
atlas of `M`, `y ∈ e.source` is a boundary point of `M`, then the first coordinate of `e y` (read
in the ambient model space `ℝ^{n+1}`) vanishes. -/
theorem chartMemHyperplane {e : OpenPartialHomeomorph M (EuclideanHalfSpace (n + 1))}
    (he : e ∈ atlas (EuclideanHalfSpace (n + 1)) M) {y : M} (hy : y ∈ e.source)
    (hb : (hModel n).IsBoundaryPoint y) :
    Subtype.val (e y) ∈ Work.Surgery.hyperplane (n + 1) := by
  have hfr0 : (e.extend (hModel n)) y ∈ frontier ((e.extend (hModel n)).target) :=
    (ModelWithCorners.isBoundaryPoint_iff_of_mem_atlas (I := hModel n) (M := M)
      (n := (1 : WithTop ℕ∞)) (by norm_num) he hy).mp hb
  have htgt : (e.extend (hModel n)) y ∈ (e.extend (hModel n)).target :=
    PartialEquiv.map_source _ (by rw [OpenPartialHomeomorph.extend_source]; exact hy)
  have hset : Set.range (↑(hModel n)) ∩ (hModel n).symm ⁻¹' e.target =
      (e.extend (hModel n)).target := by
    rw [OpenPartialHomeomorph.extend_target, Set.inter_comm]
  have hfr : (e.extend (hModel n)) y ∈
      frontier (Set.range (↑(hModel n)) ∩ (hModel n).symm ⁻¹' e.target) := by
    rw [hset]; exact hfr0
  have htgt' : (e.extend (hModel n)) y ∈
      Set.range (↑(hModel n)) ∩ (hModel n).symm ⁻¹' e.target := by
    rw [hset]; exact htgt
  have hopen : IsOpen ((hModel n).symm ⁻¹' e.target) :=
    e.open_target.preimage (hModel n).continuous_symm
  have h2 : (e.extend (hModel n)) y ∈ frontier (Set.range (↑(hModel n))) :=
    (Work.Surgery.frontier_inter_of_isOpen (S := Set.range (↑(hModel n)))
      (U := (hModel n).symm ⁻¹' e.target) hopen htgt').mp hfr
  rw [Work.Surgery.frontier_range_halfModel] at h2
  simpa only [OpenPartialHomeomorph.extend_coe, Function.comp_apply,
    modelWithCornersEuclideanHalfSpace_toFun] using h2

/-- **Boundary points of the source of the preferred chart at `x` map to the hyperplane.** -/
theorem chartAt_mem_hyperplane (x : (hModel n).boundary M) {y : M}
    (hy : y ∈ (chartAt (EuclideanHalfSpace (n + 1)) x.1).source)
    (hb : (hModel n).IsBoundaryPoint y) :
    (Subtype.val ((chartAt (EuclideanHalfSpace (n + 1)) x.1) y) :
      EuclideanSpace ℝ (Fin (n + 1))) 0 = 0 := by
  have h := chartMemHyperplane (n := n) (M := M)
    (chart_mem_atlas (EuclideanHalfSpace (n + 1)) x.1) hy hb
  rw [Work.Surgery.mem_hyperplane_iff] at h
  exact h

/-- The preferred chart at a boundary point, evaluated at the point itself, lies in the
hyperplane. -/
theorem chartAt_self_coord_zero (x : (hModel n).boundary M) :
    (Subtype.val ((chartAt (EuclideanHalfSpace (n + 1)) x.1) x.1) :
      EuclideanSpace ℝ (Fin (n + 1))) 0 = 0 :=
  chartAt_mem_hyperplane x (mem_chart_source _ _) x.2

/-! ## The interior charts of the double -/

/-- **The interior chart of `M` at an interior point `x`**: the extended chart at `x`, cut down so
that its target lies in the interior of the half-space.  Its target is open in the *boundaryless*
model space `ℝ^{n+1}`. -/
def intChartM (x : M) (hx : x ∉ (hModel n).boundary M) :
    OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (n + 1))) where
  toFun := extChartAt (hModel n) x
  invFun := (extChartAt (hModel n) x).symm
  source := (extChartAt (hModel n) x).source ∩
    (extChartAt (hModel n) x) ⁻¹' interior (Set.range (hModel n))
  target := (extChartAt (hModel n) x).target ∩ interior (Set.range (hModel n))
  map_source' := fun y hy => ⟨PartialEquiv.map_source _ hy.1, hy.2⟩
  map_target' := fun z hz =>
    ⟨PartialEquiv.map_target _ hz.1,
      by
        simp only [Set.mem_preimage]
        rw [PartialEquiv.right_inv _ hz.1]
        exact hz.2⟩
  left_inv' := fun y hy => (extChartAt (hModel n) x).left_inv hy.1
  right_inv' := fun z hz => (extChartAt (hModel n) x).right_inv hz.1
  continuousOn_toFun :=
    (continuousOn_extChartAt (I := hModel n) x).mono Set.inter_subset_left
  continuousOn_invFun :=
    (continuousOn_extChartAt_symm (I := hModel n) x).mono Set.inter_subset_left
  open_source := isOpen_extChartAt_preimage' (I := hModel n) x isOpen_interior
  open_target := by
    rw [extChartAt_target, Set.inter_assoc,
      Set.inter_eq_right.mpr (interior_subset (s := Set.range (hModel n)))]
    exact (((chartAt (EuclideanHalfSpace (n + 1)) x).open_target).preimage
      (hModel n).continuous_symm).inter isOpen_interior

/-- The base point belongs to the source of its interior chart. -/
theorem intChartM_mem_source (x : M) (hx : x ∉ (hModel n).boundary M) :
    x ∈ (intChartM x hx).source :=
  ⟨mem_extChartAt_source (I := hModel n) x,
    (ModelWithCorners.isInteriorPoint_iff_not_isBoundaryPoint (I := hModel n) x).mpr hx⟩

/-- **The embedding of the interior of `M` into its double.** -/
def interiorEmb : Set.Elem ((hModel n).boundary M)ᶜ → Double n M := fun u => doubleιM u.1

/-- **The inclusion of the interior of `M` into its double is an open map.** -/
theorem isOpenMap_interior_doubleιM : IsOpenMap (interiorEmb (n := n) (M := M)) := by
  intro W hW
  have hcompl : IsOpen (((hModel n).boundary M)ᶜ) :=
    (isClosed_boundary_one (n := n) (M := M)).isOpen_compl
  have himg : interiorEmb (n := n) (M := M) '' W
      = doubleιM (n := n) (M := M) '' (Subtype.val '' W) :=
    Set.image_comp (doubleιM (n := n) (M := M))
      (Subtype.val : Set.Elem ((hModel n).boundary M)ᶜ → M) W
  have hopen : IsOpen ((Sum.inl : M → M ⊕ M) ''
      ((Subtype.val : Set.Elem ((hModel n).boundary M)ᶜ → M) '' W)) := by
    have h1 : IsOpenMap (Subtype.val : Set.Elem ((hModel n).boundary M)ᶜ → M) :=
      IsOpen.isOpenMap_subtype_val hcompl
    have h2 : IsOpenMap (Sum.inl : M → M ⊕ M) :=
      (Topology.IsOpenEmbedding.inl (X := M) (Y := M)).isOpenMap
    have h3 := h2.comp h1 W hW
    rwa [Set.image_comp] at h3
  rw [isOpen_coinduced, himg]
  have h : Quotient.mk' (s := (doubleData n M).setoid) ⁻¹'
      (doubleιM (n := n) (M := M) '' (Subtype.val '' W)) = Sum.inl '' (Subtype.val '' W) :=
    Work.Surgery.GlueData.preimage_image_interior_ιM (doubleData n M) W
  rw [h]
  exact hopen

/-- **The embedding of the interior of `M` into its double is an open embedding.** -/
theorem isOpenEmbedding_interiorEmb :
    Topology.IsOpenEmbedding (interiorEmb (n := n) (M := M)) :=
  Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    ((continuous_doubleιM (n := n) (M := M)).comp continuous_subtype_val)
    (fun _ _ h => Subtype.ext (doubleιM_injective h))
    isOpenMap_interior_doubleιM

/-- The interior of `M`, as an open subset. -/
def interiorOpens : TopologicalSpace.Opens M :=
  ⟨((hModel n).boundary M)ᶜ, (isClosed_boundary_one (n := n) (M := M)).isOpen_compl⟩

/-- **The interior chart of the double at an interior point `x` of `M`.** -/
def intChartD (x : M) (hx : x ∉ (hModel n).boundary M) :
    OpenPartialHomeomorph (Double n M) (EuclideanSpace ℝ (Fin (n + 1))) :=
  OpenPartialHomeomorph.lift_openEmbedding
    ((intChartM x hx).subtypeRestr (s := interiorOpens (n := n) (M := M)) ⟨⟨x, hx⟩⟩)
    (isOpenEmbedding_interiorEmb (n := n) (M := M))

theorem intChartD_source (x : M) (hx : x ∉ (hModel n).boundary M) :
    (intChartD x hx).source =
      interiorEmb (n := n) (M := M) ''
        ((intChartM x hx).subtypeRestr (s := interiorOpens (n := n) (M := M))
          ⟨⟨x, hx⟩⟩).source :=
  OpenPartialHomeomorph.lift_openEmbedding_source _ _

/-- The image of an interior point of `M` lies in the source of its interior chart of the
double. -/
theorem intChartD_mem_source_self (x : M) (hx : x ∉ (hModel n).boundary M) :
    doubleιM (n := n) (M := M) x ∈ (intChartD x hx).source := by
  rw [intChartD_source]
  refine ⟨⟨x, hx⟩, ?_, rfl⟩
  rw [OpenPartialHomeomorph.subtypeRestr_source]
  exact intChartM_mem_source x hx


/-- **The embedding of the interior of the second copy of `M` into its double.** -/
def interiorEmbN : Set.Elem ((hModel n).boundary M)ᶜ → Double n M := fun u => doubleιN u.1

/-- The second inclusion is an open map on the interior. -/
theorem isOpenMap_interior_doubleιN : IsOpenMap (interiorEmbN (n := n) (M := M)) := by
  intro W hW
  have hcompl : IsOpen (((hModel n).boundary M)ᶜ) :=
    (isClosed_boundary_one (n := n) (M := M)).isOpen_compl
  have himg : interiorEmbN (n := n) (M := M) '' W
      = doubleιN (n := n) (M := M) '' (Subtype.val '' W) :=
    Set.image_comp (doubleιN (n := n) (M := M))
      (Subtype.val : Set.Elem ((hModel n).boundary M)ᶜ → M) W
  have hopen : IsOpen ((Sum.inr : M → M ⊕ M) ''
      ((Subtype.val : Set.Elem ((hModel n).boundary M)ᶜ → M) '' W)) := by
    have h1 : IsOpenMap (Subtype.val : Set.Elem ((hModel n).boundary M)ᶜ → M) :=
      IsOpen.isOpenMap_subtype_val hcompl
    have h2 : IsOpenMap (Sum.inr : M → M ⊕ M) :=
      (Topology.IsOpenEmbedding.inr (X := M) (Y := M)).isOpenMap
    have h3 := h2.comp h1 W hW
    rwa [Set.image_comp] at h3
  rw [isOpen_coinduced, himg]
  have h : Quotient.mk' (s := (doubleData n M).setoid) ⁻¹'
      (doubleιN (n := n) (M := M) '' (Subtype.val '' W)) = Sum.inr '' (Subtype.val '' W) :=
    Work.Surgery.GlueData.preimage_image_interior_ιN (doubleData n M) W
  rw [h]
  exact hopen

theorem isOpenEmbedding_interiorEmbN :
    Topology.IsOpenEmbedding (interiorEmbN (n := n) (M := M)) :=
  Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    ((continuous_doubleιN (n := n) (M := M)).comp continuous_subtype_val)
    (fun _ _ h => Subtype.ext (doubleιN_injective h))
    isOpenMap_interior_doubleιN

/-- **The interior chart of the double at an interior point of the second copy of `M`.** -/
def intChartDN (x : M) (hx : x ∉ (hModel n).boundary M) :
    OpenPartialHomeomorph (Double n M) (EuclideanSpace ℝ (Fin (n + 1))) :=
  OpenPartialHomeomorph.lift_openEmbedding
    ((intChartM x hx).subtypeRestr (s := interiorOpens (n := n) (M := M)) ⟨⟨x, hx⟩⟩)
    (isOpenEmbedding_interiorEmbN (n := n) (M := M))

theorem intChartDN_source (x : M) (hx : x ∉ (hModel n).boundary M) :
    (intChartDN x hx).source =
      interiorEmbN (n := n) (M := M) ''
        ((intChartM x hx).subtypeRestr (s := interiorOpens (n := n) (M := M))
          ⟨⟨x, hx⟩⟩).source :=
  OpenPartialHomeomorph.lift_openEmbedding_source _ _

/-- The image of an interior point of `M` in the second copy lies in the source of the interior
chart of the double attached to that copy. -/
theorem intChartDN_mem_source_self (x : M) (hx : x ∉ (hModel n).boundary M) :
    doubleιN (n := n) (M := M) x ∈ (intChartDN x hx).source := by
  rw [intChartDN_source]
  refine ⟨⟨x, hx⟩, ?_, rfl⟩
  rw [OpenPartialHomeomorph.subtypeRestr_source]
  exact intChartM_mem_source x hx

/-! ## The seam charts of the double

Fix a boundary point `x` of `M`.  The chart `seamChartAt x = chartAt _ x.1` of `M` at `x` sends a
neighbourhood of `x` onto an open subset of the half-space; we thicken it to an open subset
`seamTarget x` of the ambient model space, symmetric under the reflection
`Work.Surgery.flipEucl n` of the first coordinate, whose positive half is the chart's target.  The
double is then read through this chart on the first half (using `seamProj x`) and through the
reflection of it on the second half.  The two formulas agree on the seam because a chart sends
boundary points to the hyperplane (`chartAt_mem_hyperplane`), where the reflection is the identity.
-/

/-! ### The level-`1` boundary charts -/

/-- A point of the source of the extended chart at `x` is a boundary point if and only if its image
lies in the frontier of the chart's target. -/
theorem isBoundaryPoint_iff_mem_frontier_extChart_one {x y : M}
    (hy : y ∈ (extChartAt (hModel n) x).source) :
    (hModel n).IsBoundaryPoint y ↔
      (extChartAt (hModel n) x) y ∈ frontier ((extChartAt (hModel n) x).target) := by
  have hye : y ∈ (chartAt (EuclideanHalfSpace (n + 1)) x).source := by
    rwa [extChartAt_source] at hy
  exact ModelWithCorners.isBoundaryPoint_iff_of_mem_atlas (I := hModel n)
    (n := (1 : WithTop ℕ∞)) (M := M) (e := chartAt (EuclideanHalfSpace (n + 1)) x)
    (x := y) (by norm_num) (chart_mem_atlas _ x) hye

/-- **A point of the target of the extended chart at `x` whose first coordinate vanishes lies in the
frontier of the target.** -/
theorem mem_frontier_extChart_target_of_coord_eq_zero_one {x : M}
    {z : EuclideanSpace ℝ (Fin (n + 1))}
    (hz : z ∈ (extChartAt (hModel n) x).target) (hz0 : z 0 = 0) :
    z ∈ frontier ((extChartAt (hModel n) x).target) := by
  have hz' : z ∈ (hModel n).symm ⁻¹'
      (chartAt (EuclideanHalfSpace (n + 1)) x).target ∩ Set.range (↑(hModel n)) := by
    rw [← extChartAt_target]; exact hz
  have hz'' : z ∈ Set.range (↑(hModel n)) ∩ (hModel n).symm ⁻¹'
      (chartAt (EuclideanHalfSpace (n + 1)) x).target := by
    rw [Set.inter_comm]; exact hz'
  have hopen : IsOpen ((hModel n).symm ⁻¹'
      (chartAt (EuclideanHalfSpace (n + 1)) x).target) :=
    (chartAt (EuclideanHalfSpace (n + 1)) x).open_target.preimage (hModel n).continuous_symm
  have hmem : z ∈ frontier (Set.range (↑(hModel n)) ∩ (hModel n).symm ⁻¹'
      (chartAt (EuclideanHalfSpace (n + 1)) x).target) :=
    (Work.Surgery.frontier_inter_of_isOpen (S := Set.range (↑(hModel n)))
      (U := (hModel n).symm ⁻¹' (chartAt (EuclideanHalfSpace (n + 1)) x).target)
      hopen hz'').mpr (by
        rw [Work.Surgery.frontier_range_halfModel]
        exact Work.Surgery.mem_hyperplane_iff.mpr hz0)
  rwa [show Set.range (↑(hModel n)) ∩ (hModel n).symm ⁻¹'
      (chartAt (EuclideanHalfSpace (n + 1)) x).target = (extChartAt (hModel n) x).target from by
        rw [extChartAt_target, Set.inter_comm]] at hmem

/-- **The inverse of a chart sends points of the hyperplane back to the boundary.** -/
theorem isBoundaryPoint_symm_of_mem_target_one {x : M} {z : EuclideanSpace ℝ (Fin (n + 1))}
    (hz : z ∈ (extChartAt (hModel n) x).target) (hz0 : z 0 = 0) :
    (hModel n).IsBoundaryPoint ((extChartAt (hModel n) x).symm z) := by
  refine (isBoundaryPoint_iff_mem_frontier_extChart_one (PartialEquiv.map_target _ hz)).mpr ?_
  rw [PartialEquiv.right_inv _ hz]
  exact mem_frontier_extChart_target_of_coord_eq_zero_one hz hz0

/-- **The reflection of the first coordinate fixes the hyperplane.** -/
theorem flipEucl_eq_self_of_coord_zero {p : EuclideanSpace ℝ (Fin (n + 1))} (h : p 0 = 0) :
    Work.Surgery.flipEucl n p = p := by
  refine PiLp.ext fun i => ?_
  show (Work.Surgery.flipEucl n p).ofLp i = p.ofLp i
  rw [Work.Surgery.flipEucl_ofLp]
  simp only [Work.Surgery.flipLin_apply]
  induction i using Fin.cases with
  | zero => rw [Work.Surgery.flipCLM_apply_zero]; simp [h]
  | succ k => rw [Work.Surgery.flipCLM_apply_succ]

/-! ### The thickened chart target -/

/-- The chart of `M` at a boundary point. -/
abbrev seamChartAt (x : (hModel n).boundary M) :
    OpenPartialHomeomorph M (EuclideanHalfSpace (n + 1)) :=
  chartAt (EuclideanHalfSpace (n + 1)) x.1

/-- The chart of `M` at `x`, read in the ambient model space `ℝ^{n+1}`. -/
abbrev seamProj (x : (hModel n).boundary M) : M → EuclideanSpace ℝ (Fin (n + 1)) :=
  ⇑(extChartAt (hModel n) x.1)

/-- The inverse of `seamProj x`, as a function on the ambient model space. -/
abbrev seamEmb (x : (hModel n).boundary M) : EuclideanSpace ℝ (Fin (n + 1)) → M :=
  ⇑(extChartAt (hModel n) x.1).symm

theorem seamProj_eq (x : (hModel n).boundary M) :
    seamProj x = Subtype.val ∘ ⇑(seamChartAt x) := by
  funext y
  exact congrFun (OpenPartialHomeomorph.extend_coe (seamChartAt x) (I := hModel n)) y

/-- The first coordinate of `seamProj x y` is nonnegative. -/
theorem seamProj_nonneg (x : (hModel n).boundary M) (y : M) : 0 ≤ (seamProj x y) 0 := by
  rw [seamProj_eq]
  exact (seamChartAt x y).2

/-- **An open subset of the ambient model space whose trace on the half-space is the target of the
chart at `x`.** -/
noncomputable def chartOpen (x : (hModel n).boundary M) : Set (EuclideanSpace ℝ (Fin (n + 1))) :=
  (isOpen_induced_iff.mp (show IsOpen[TopologicalSpace.induced
      (Subtype.val : EuclideanHalfSpace (n + 1) → EuclideanSpace ℝ (Fin (n + 1))) _]
      (seamChartAt x).target from (seamChartAt x).open_target)).choose

theorem chartOpen_spec (x : (hModel n).boundary M) :
    IsOpen (chartOpen x) ∧
      (Subtype.val : EuclideanHalfSpace (n + 1) → EuclideanSpace ℝ (Fin (n + 1))) ⁻¹'
        chartOpen x = (seamChartAt x).target :=
  (isOpen_induced_iff.mp (show IsOpen[TopologicalSpace.induced
      (Subtype.val : EuclideanHalfSpace (n + 1) → EuclideanSpace ℝ (Fin (n + 1))) _]
      (seamChartAt x).target from (seamChartAt x).open_target)).choose_spec

theorem isOpen_chartOpen (x : (hModel n).boundary M) : IsOpen (chartOpen x) :=
  (chartOpen_spec x).1

/-- Membership in `chartOpen x` in terms of the chart of `M`. -/
theorem mem_chartOpen_iff (x : (hModel n).boundary M) (z : EuclideanHalfSpace (n + 1)) :
    (Subtype.val z : EuclideanSpace ℝ (Fin (n + 1))) ∈ chartOpen x ↔
      z ∈ (seamChartAt x).target :=
  Set.ext_iff.mp (chartOpen_spec x).2 z

/-- **The thickened chart target**: the chart target, symmetrised under the reflection of the first
coordinate.  It is an open subset of the ambient model space, invariant under the reflection, whose
positive half is the chart's target. -/
noncomputable def seamTarget (x : (hModel n).boundary M) :
    Set (EuclideanSpace ℝ (Fin (n + 1))) :=
  chartOpen x ∩ Work.Surgery.flipEucl n '' chartOpen x

theorem isOpen_seamTarget (x : (hModel n).boundary M) : IsOpen (seamTarget x) :=
  (isOpen_chartOpen x).inter ((Work.Surgery.flipEucl n).isOpenMap _ (isOpen_chartOpen x))

theorem seamTarget_subset_chartOpen (x : (hModel n).boundary M) :
    seamTarget x ⊆ chartOpen x := Set.inter_subset_left

/-- **The thickened target is invariant under the reflection.** -/
theorem flipEucl_image_seamTarget (x : (hModel n).boundary M) :
    Work.Surgery.flipEucl n '' seamTarget x = seamTarget x := by
  have hinj : Injective (Work.Surgery.flipEucl n) := (Work.Surgery.flipEucl_involutive n).injective
  have hff : Work.Surgery.flipEucl n '' Work.Surgery.flipEucl n '' chartOpen x = chartOpen x := by
    rw [← Set.image_comp]
    have hcomp : (Work.Surgery.flipEucl n ∘ Work.Surgery.flipEucl n :
        EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))) = id :=
      funext (Work.Surgery.flipEucl_involutive n)
    rw [hcomp, Set.image_id]
  rw [seamTarget, Set.image_inter hinj, hff, Set.inter_comm]

/-- A point of the thickened target with nonnegative first coordinate lies in the chart target. -/
theorem mem_target_of_mem_seamTarget (x : (hModel n).boundary M)
    {p : EuclideanSpace ℝ (Fin (n + 1))} (hp : p ∈ seamTarget x) (h0 : 0 ≤ p 0) :
    (⟨p, h0⟩ : EuclideanHalfSpace (n + 1)) ∈ (seamChartAt x).target :=
  (mem_chartOpen_iff x ⟨p, h0⟩).mp (seamTarget_subset_chartOpen x hp)

/-- The same point, in the extended chart's target. -/
theorem mem_extChartAt_target_of_mem_seamTarget (x : (hModel n).boundary M)
    {p : EuclideanSpace ℝ (Fin (n + 1))} (hp : p ∈ seamTarget x) (h0 : 0 ≤ p 0) :
    p ∈ (extChartAt (hModel n) x.1).target := by
  have hmem : (⟨p, h0⟩ : EuclideanHalfSpace (n + 1)) ∈ (seamChartAt x).target :=
    mem_target_of_mem_seamTarget x hp h0
  rw [extChartAt_target]
  refine ⟨?_, ?_⟩
  · have hinv : (hModel n).invFun p = (⟨p, h0⟩ : EuclideanHalfSpace (n + 1)) :=
      Subtype.ext (ModelWithCorners.right_inv (hModel n) (by
        rw [Work.Surgery.range_halfModel]; exact h0))
    show (hModel n).invFun p ∈ (seamChartAt x).target
    rw [hinv]
    exact hmem
  · rw [Work.Surgery.range_halfModel]; exact h0

/-- **The part of `M` that the seam chart of `x` reads.** -/
noncomputable def seamU (x : (hModel n).boundary M) : Set M :=
  (seamChartAt x).source ∩ (seamProj x) ⁻¹' seamTarget x

theorem seamU_subset_source (x : (hModel n).boundary M) : seamU x ⊆ (seamChartAt x).source :=
  Set.inter_subset_left

theorem mem_seamU_iff (x : (hModel n).boundary M) {y : M} :
    y ∈ seamU x ↔ y ∈ (seamChartAt x).source ∧ seamProj x y ∈ seamTarget x := Iff.rfl

theorem isOpen_seamU (x : (hModel n).boundary M) : IsOpen (seamU x) := by
  rw [seamU]
  have hpre : IsOpen ((Subtype.val : EuclideanHalfSpace (n + 1) →
      EuclideanSpace ℝ (Fin (n + 1))) ⁻¹' seamTarget x) :=
    isOpen_induced_iff.mpr ⟨seamTarget x, isOpen_seamTarget x, rfl⟩
  have h := (seamChartAt x).continuousOn.isOpen_inter_preimage (seamChartAt x).open_source hpre
  have hproj : (seamProj x) ⁻¹' seamTarget x = ⇑(seamChartAt x) ⁻¹'
      (Subtype.val ⁻¹' seamTarget x) := by
    rw [seamProj_eq, Set.preimage_comp]
  rwa [← hproj] at h

theorem seamU_subset_extChartAt_source (x : (hModel n).boundary M) :
    seamU x ⊆ (extChartAt (hModel n) x.1).source := by
  rw [extChartAt_source]
  exact seamU_subset_source x

theorem continuousOn_seamProj (x : (hModel n).boundary M) :
    ContinuousOn (seamProj x) (seamU x) :=
  (continuousOn_extChartAt (I := hModel n) x.1).mono (seamU_subset_extChartAt_source x)

/-- The point of `M` underlying a point of the extended chart's target. -/
theorem seamProj_seamEmb (x : (hModel n).boundary M)
    {p : EuclideanSpace ℝ (Fin (n + 1))} (hp : p ∈ (extChartAt (hModel n) x.1).target) :
    seamProj x (seamEmb x p) = p :=
  PartialEquiv.right_inv _ hp

/-- The inverse of `seamProj x` on the source of the chart. -/
theorem seamEmb_seamProj (x : (hModel n).boundary M) {y : M}
    (hy : y ∈ (seamChartAt x).source) : seamEmb x (seamProj x y) = y := by
  refine PartialEquiv.left_inv _ ?_
  rw [extChartAt_source]
  exact hy

theorem seamEmb_mem_source (x : (hModel n).boundary M)
    {p : EuclideanSpace ℝ (Fin (n + 1))} (hp : p ∈ (extChartAt (hModel n) x.1).target) :
    seamEmb x p ∈ (seamChartAt x).source := by
  have h := PartialEquiv.map_target (extChartAt (hModel n) x.1) hp
  rwa [extChartAt_source] at h

/-- For `y ∈ seamU x`, the chart value `seamProj x y` lies in the extended chart's target. -/
theorem seamProj_mem_extChartAt_target (x : (hModel n).boundary M) {y : M}
    (hy : y ∈ seamU x) : seamProj x y ∈ (extChartAt (hModel n) x.1).target :=
  mem_extChartAt_target_of_mem_seamTarget x hy.2 (seamProj_nonneg x y)

theorem flip_seamProj_coord (x : (hModel n).boundary M) (y : M) :
    (Work.Surgery.flipEucl n (seamProj x y)) 0 = -((seamProj x y) 0) :=
  Work.Surgery.flipEucl_apply_zero n (seamProj x y)

theorem flip_seamProj_nonpos (x : (hModel n).boundary M) (y : M) :
    (Work.Surgery.flipEucl n (seamProj x y)) 0 ≤ 0 := by
  rw [flip_seamProj_coord]
  linarith [seamProj_nonneg x y]

theorem flip_mem_seamTarget (x : (hModel n).boundary M) {p : EuclideanSpace ℝ (Fin (n + 1))}
    (hp : p ∈ seamTarget x) : Work.Surgery.flipEucl n p ∈ seamTarget x := by
  rw [← flipEucl_image_seamTarget x]
  exact ⟨p, hp, rfl⟩

/-- The reflection fixes the chart value of a boundary point. -/
theorem flip_seamProj_eq_self (x : (hModel n).boundary M) {y : M}
    (hy : y ∈ seamU x) (hb : (hModel n).IsBoundaryPoint y) :
    Work.Surgery.flipEucl n (seamProj x y) = seamProj x y := by
  refine flipEucl_eq_self_of_coord_zero ?_
  show (Subtype.val ((chartAt (EuclideanHalfSpace (n + 1)) x.1) y) :
    EuclideanSpace ℝ (Fin (n + 1))) 0 = 0
  exact chartAt_mem_hyperplane x (seamU_subset_source x hy) hb

/-! ### The maps of the seam chart -/

/-- The source of the seam chart, inside `M ⊕ M`. -/
def seamSumSource (x : (hModel n).boundary M) : Set (M ⊕ M) :=
  Sum.inl '' seamU x ∪ Sum.inr '' seamU x

theorem isOpen_seamSumSource (x : (hModel n).boundary M) : IsOpen (seamSumSource x) :=
  ((Topology.IsOpenEmbedding.inl (X := M) (Y := M)).isOpenMap _ (isOpen_seamU x)).union
    ((Topology.IsOpenEmbedding.inr (X := M) (Y := M)).isOpenMap _ (isOpen_seamU x))

/-- The source of the seam chart, in the double. -/
def seamSource (x : (hModel n).boundary M) : Set (Double n M) :=
  doubleQ '' seamSumSource x

/-- The gluing relation identifies exactly the seam, so the preimage of the seam source is the
seam source upstairs. -/
theorem preimage_seamSumSource (x : (hModel n).boundary M) :
    doubleQ (n := n) (M := M) ⁻¹' (doubleQ (n := n) (M := M) '' seamSumSource x) =
      seamSumSource x := by
  ext a
  refine ⟨fun h => ?_, fun h => ⟨a, h, rfl⟩⟩
  obtain ⟨b, hb, hba⟩ := h
  rcases a with y | y <;> rcases b with y' | y' <;>
    rw [seamSumSource] at hb ⊢
  · -- inl/inl
    have h1 : y' = y := doubleιM_injective hba
    subst h1
    rcases hb with hb | hb
    · obtain ⟨z, hz, hzy⟩ := hb
      exact Or.inl ⟨z, hz, hzy⟩
    · obtain ⟨z, _, hzy⟩ := hb
      exact absurd hzy (by simp)
  · -- inl/inr
    obtain ⟨q, hq, hqq⟩ :=
      doubleιM_eq_ιN_iff.mp (by simpa only [doubleQ_inl, doubleQ_inr] using hba.symm)
    subst hq; subst hqq
    rcases hb with hb | hb
    · obtain ⟨z, _, hzy⟩ := hb
      exact absurd hzy (by simp)
    · obtain ⟨z, hz, hzy⟩ := hb
      exact Or.inl ⟨z, hz, by simpa using hzy⟩
  · -- inr/inl
    obtain ⟨q, hq, hqq⟩ :=
      doubleιM_eq_ιN_iff.mp (by simpa only [doubleQ_inl, doubleQ_inr] using hba)
    subst hq; subst hqq
    rcases hb with hb | hb
    · obtain ⟨z, hz, hzy⟩ := hb
      exact Or.inr ⟨z, hz, by simpa using hzy⟩
    · obtain ⟨z, _, hzy⟩ := hb
      exact absurd hzy (by simp)
  · -- inr/inr
    have h1 : y' = y := doubleιN_injective hba
    subst h1
    rcases hb with hb | hb
    · obtain ⟨z, _, hzy⟩ := hb
      exact absurd hzy (by simp)
    · obtain ⟨z, hz, hzy⟩ := hb
      exact Or.inr ⟨z, hz, hzy⟩

theorem preimage_seamSource (x : (hModel n).boundary M) :
    Quotient.mk' (s := (doubleData n M).setoid) ⁻¹' seamSource x = seamSumSource x :=
  preimage_seamSumSource x

theorem isOpen_seamSource (x : (hModel n).boundary M) : IsOpen (seamSource x) := by
  rw [isOpen_coinduced]
  rw [preimage_seamSource x]
  exact isOpen_seamSumSource x

/-- The forward map of the seam chart, on `M ⊕ M`. -/
def seamG (x : (hModel n).boundary M) : M ⊕ M → EuclideanSpace ℝ (Fin (n + 1)) :=
  fun a => match a with
    | Sum.inl y => if y ∈ seamU x then seamProj x y else 0
    | Sum.inr y => if y ∈ seamU x then Work.Surgery.flipEucl n (seamProj x y) else 0

@[simp] theorem seamG_inl (x : (hModel n).boundary M) (y : M) :
    seamG x (Sum.inl y) = if y ∈ seamU x then seamProj x y else 0 := rfl

@[simp] theorem seamG_inr (x : (hModel n).boundary M) (y : M) :
    seamG x (Sum.inr y) = if y ∈ seamU x then Work.Surgery.flipEucl n (seamProj x y) else 0 := rfl

theorem seamG_apply_inl (x : (hModel n).boundary M) {y : M} (hy : y ∈ seamU x) :
    seamG x (Sum.inl y) = seamProj x y := by
  rw [seamG_inl, if_pos hy]

theorem seamG_apply_inr (x : (hModel n).boundary M) {y : M} (hy : y ∈ seamU x) :
    seamG x (Sum.inr y) = Work.Surgery.flipEucl n (seamProj x y) := by
  rw [seamG_inr, if_pos hy]

theorem seamG_apply_inl_of_notMem (x : (hModel n).boundary M) {y : M} (hy : y ∉ seamU x) :
    seamG x (Sum.inl y) = 0 := by
  rw [seamG_inl, if_neg hy]

theorem seamG_apply_inr_of_notMem (x : (hModel n).boundary M) {y : M} (hy : y ∉ seamU x) :
    seamG x (Sum.inr y) = 0 := by
  rw [seamG_inr, if_neg hy]

/-- The two formulas agree on the seam: glueing two boundary points by the identity, the chart
value has vanishing first coordinate, where the reflection is the identity. -/
theorem seamG_wellDefined (x : (hModel n).boundary M) {a b : M ⊕ M}
    (h : (doubleData n M).setoid.r a b) : seamG x a = seamG x b := by
  have hq : doubleQ (n := n) (M := M) a = doubleQ (n := n) (M := M) b := Quotient.sound' h
  rcases a with y | y <;> rcases b with y' | y'
  · have h1 : y = y' := doubleιM_injective (by simpa only [doubleQ_inl] using hq)
    subst h1; rfl
  · obtain ⟨p, hp, hp'⟩ := doubleιM_eq_ιN_iff.mp (by simpa only [doubleQ_inl, doubleQ_inr] using hq)
    subst hp; subst hp'
    by_cases hU : p.1 ∈ seamU x
    · rw [seamG_apply_inl (x := x) (y := p.1) hU, ← flip_seamProj_eq_self x hU p.2,
        seamG_apply_inr (x := x) (y := p.1) hU]
    · rw [seamG_apply_inl_of_notMem (x := x) (y := p.1) hU,
        seamG_apply_inr_of_notMem (x := x) (y := p.1) hU]
  · obtain ⟨p, hp, hp'⟩ :=
      doubleιM_eq_ιN_iff.mp (by simpa only [doubleQ_inl, doubleQ_inr] using hq.symm)
    subst hp; subst hp'
    by_cases hU : p.1 ∈ seamU x
    · rw [seamG_apply_inr (x := x) (y := p.1) hU, flip_seamProj_eq_self x hU p.2,
        seamG_apply_inl (x := x) (y := p.1) hU]
    · rw [seamG_apply_inl_of_notMem (x := x) (y := p.1) hU, seamG_apply_inr_of_notMem (x := x) (y := p.1) hU]
  · have h1 : y = y' := doubleιN_injective (by simpa only [doubleQ_inr] using hq)
    subst h1; rfl

/-- The forward map of the seam chart. -/
def seamF (x : (hModel n).boundary M) : Double n M → EuclideanSpace ℝ (Fin (n + 1)) :=
  Quotient.lift (s := (doubleData n M).setoid) (seamG x)
    (fun _ _ hab => seamG_wellDefined x hab)

theorem seamF_inl (x : (hModel n).boundary M) (y : M) :
    seamF x (doubleιM (n := n) (M := M) y) = seamG x (Sum.inl y) :=
  Quotient.lift_mk (s := (doubleData n M).setoid) (seamG x)
    (fun _ _ hab => seamG_wellDefined x hab) (Sum.inl y)

theorem seamF_inr (x : (hModel n).boundary M) (y : M) :
    seamF x (doubleιN (n := n) (M := M) y) = seamG x (Sum.inr y) :=
  Quotient.lift_mk (s := (doubleData n M).setoid) (seamG x)
    (fun _ _ hab => seamG_wellDefined x hab) (Sum.inr y)

/-- The inverse map of the seam chart. -/
def seamInv (x : (hModel n).boundary M) : EuclideanSpace ℝ (Fin (n + 1)) → Double n M :=
  fun p => if 0 ≤ p 0 then doubleιM (seamEmb x p)
           else doubleιN (seamEmb x (Work.Surgery.flipEucl n p))

theorem seamInv_of_nonneg (x : (hModel n).boundary M) {p : EuclideanSpace ℝ (Fin (n + 1))}
    (h : 0 ≤ p 0) : seamInv x p = doubleιM (seamEmb x p) := by rw [seamInv, if_pos h]

theorem seamInv_of_neg (x : (hModel n).boundary M) {p : EuclideanSpace ℝ (Fin (n + 1))}
    (h : ¬ 0 ≤ p 0) : seamInv x p = doubleιN (seamEmb x (Work.Surgery.flipEucl n p)) := by
  rw [seamInv, if_neg h]


/-- The first coordinate of the reflection of a vector, in the form used below. -/
theorem flipEucl_coord (p : EuclideanSpace ℝ (Fin (n + 1))) :
    (Work.Surgery.flipEucl n p) 0 = -(p 0) :=
  Work.Surgery.flipEucl_apply_zero n p

/-! ### The round trips of the seam chart -/

/-- The forward map of the seam chart sends its source into its target. -/
theorem seamF_mem_seamTarget (x : (hModel n).boundary M) {z : Double n M}
    (hz : z ∈ seamSource x) : seamF x z ∈ seamTarget x := by
  obtain ⟨a, ha, rfl⟩ := hz
  rw [seamSumSource] at ha
  rcases ha with ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩
  · change seamF x (doubleιM (n := n) (M := M) y) ∈ seamTarget x
    rw [seamF_inl, seamG_apply_inl (x := x) (y := y) hy]
    exact hy.2
  · change seamF x (doubleιN (n := n) (M := M) y) ∈ seamTarget x
    rw [seamF_inr, seamG_apply_inr (x := x) (y := y) hy]
    exact flip_mem_seamTarget x hy.2

/-- The inverse map of the seam chart sends its target into its source. -/
theorem seamInv_mem_seamSource (x : (hModel n).boundary M)
    {p : EuclideanSpace ℝ (Fin (n + 1))} (hp : p ∈ seamTarget x) :
    seamInv x p ∈ seamSource x := by
  rcases le_or_gt (0 : ℝ) (p 0) with h0 | h0
  · rw [seamInv_of_nonneg x h0]
    refine ⟨Sum.inl (seamEmb x p), ?_, rfl⟩
    refine Or.inl ⟨seamEmb x p, ⟨?_, ?_⟩, rfl⟩
    · exact seamEmb_mem_source x (mem_extChartAt_target_of_mem_seamTarget x hp h0)
    · show seamProj x (seamEmb x p) ∈ seamTarget x
      rw [seamProj_seamEmb x (mem_extChartAt_target_of_mem_seamTarget x hp h0)]
      exact hp
  · have h0' : 0 ≤ (Work.Surgery.flipEucl n p) 0 := by
      rw [flipEucl_coord]; linarith
    rw [seamInv_of_neg x (not_le.mpr h0)]
    refine ⟨Sum.inr (seamEmb x (Work.Surgery.flipEucl n p)), ?_, rfl⟩
    refine Or.inr ⟨seamEmb x (Work.Surgery.flipEucl n p), ⟨?_, ?_⟩, rfl⟩
    · exact seamEmb_mem_source x
        (mem_extChartAt_target_of_mem_seamTarget x (flip_mem_seamTarget x hp) h0')
    · show seamProj x (seamEmb x (Work.Surgery.flipEucl n p)) ∈ seamTarget x
      rw [seamProj_seamEmb x
        (mem_extChartAt_target_of_mem_seamTarget x (flip_mem_seamTarget x hp) h0')]
      exact flip_mem_seamTarget x hp

/-- The inverse of the forward map is the identity on the source. -/
theorem seamInv_seamF (x : (hModel n).boundary M) {z : Double n M}
    (hz : z ∈ seamSource x) : seamInv x (seamF x z) = z := by
  obtain ⟨a, ha, rfl⟩ := hz
  rw [seamSumSource] at ha
  rcases ha with ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩
  · change seamInv x (seamF x (doubleιM (n := n) (M := M) y)) =
      doubleιM (n := n) (M := M) y
    rw [seamF_inl, seamG_apply_inl (x := x) (y := y) hy,
      seamInv_of_nonneg x (seamProj_nonneg x y), seamEmb_seamProj x (seamU_subset_source x hy)]
  · change seamInv x (seamF x (doubleιN (n := n) (M := M) y)) =
      doubleιN (n := n) (M := M) y
    have hflip0 : (Work.Surgery.flipEucl n (seamProj x y)) 0 ≤ 0 := by
      rw [flipEucl_coord]; linarith [seamProj_nonneg x y]
    rcases lt_or_eq_of_le hflip0 with hlt | heq
    · rw [seamF_inr, seamG_apply_inr (x := x) (y := y) hy,
        seamInv_of_neg x (not_le.mpr hlt)]
      refine congrArg doubleιN ?_
      rw [Work.Surgery.flipEucl_involutive, seamEmb_seamProj x (seamU_subset_source x hy)]
    · -- the point is on the seam: the chart value has vanishing first coordinate
      have hcoord : (seamProj x y) 0 = 0 := by
        rw [flipEucl_coord] at heq; linarith
      have hb : (hModel n).IsBoundaryPoint y := by
        have hsymm : seamEmb x (seamProj x y) = y :=
          seamEmb_seamProj x (seamU_subset_source x hy)
        have hthis := isBoundaryPoint_symm_of_mem_target_one
          (mem_extChartAt_target_of_mem_seamTarget x hy.2 (seamProj_nonneg x y)) hcoord
        change (hModel n).IsBoundaryPoint (seamEmb x (seamProj x y)) at hthis
        rwa [hsymm] at hthis
      rw [seamF_inr, seamG_apply_inr (x := x) (y := y) hy,
        seamInv_of_nonneg x (le_of_eq heq.symm), flipEucl_eq_self_of_coord_zero hcoord,
        seamEmb_seamProj x (seamU_subset_source x hy),
        doubleιM_eq_ιN_iff.mpr ⟨⟨y, hb⟩, rfl, rfl⟩]

/-- The forward map of the inverse is the identity on the target. -/
theorem seamF_seamInv (x : (hModel n).boundary M)
    {p : EuclideanSpace ℝ (Fin (n + 1))} (hp : p ∈ seamTarget x) :
    seamF x (seamInv x p) = p := by
  rcases le_or_gt (0 : ℝ) (p 0) with h0 | h0
  · rw [seamInv_of_nonneg x h0]
    have hmem : seamEmb x p ∈ seamU x :=
      ⟨seamEmb_mem_source x (mem_extChartAt_target_of_mem_seamTarget x hp h0), by
        show seamProj x (seamEmb x p) ∈ seamTarget x
        rw [seamProj_seamEmb x (mem_extChartAt_target_of_mem_seamTarget x hp h0)]
        exact hp⟩
    rw [seamF_inl, seamG_apply_inl (x := x) (y := seamEmb x p) hmem,
      seamProj_seamEmb x (mem_extChartAt_target_of_mem_seamTarget x hp h0)]
  · have h0' : 0 ≤ (Work.Surgery.flipEucl n p) 0 := by
      rw [flipEucl_coord]; linarith
    rw [seamInv_of_neg x (not_le.mpr h0)]
    have hmem : seamEmb x (Work.Surgery.flipEucl n p) ∈ seamU x :=
      ⟨seamEmb_mem_source x
          (mem_extChartAt_target_of_mem_seamTarget x (flip_mem_seamTarget x hp) h0'),
        by
          show seamProj x (seamEmb x (Work.Surgery.flipEucl n p)) ∈ seamTarget x
          rw [seamProj_seamEmb x
            (mem_extChartAt_target_of_mem_seamTarget x (flip_mem_seamTarget x hp) h0')]
          exact flip_mem_seamTarget x hp⟩
    rw [seamF_inr, seamG_apply_inr (x := x) (y := seamEmb x (Work.Surgery.flipEucl n p)) hmem,
      seamProj_seamEmb x (mem_extChartAt_target_of_mem_seamTarget x (flip_mem_seamTarget x hp) h0'),
      Work.Surgery.flipEucl_involutive]

/-! ### Continuity of the seam chart -/

/-- The forward map of the seam chart, transported to `M ⊕ M`, is continuous. -/
theorem continuousOn_seamG (x : (hModel n).boundary M) :
    ContinuousOn (seamG x) (seamSumSource x) := by
  rw [continuousOn_open_iff (isOpen_seamSumSource x)]
  intro W hW
  have hpre : IsOpen ((Subtype.val : EuclideanHalfSpace (n + 1) →
      EuclideanSpace ℝ (Fin (n + 1))) ⁻¹' W) :=
    isOpen_induced_iff.mpr ⟨W, hW, rfl⟩
  have hproj : (seamProj x) ⁻¹' W = ⇑(seamChartAt x) ⁻¹' (Subtype.val ⁻¹' W) := by
    rw [seamProj_eq, Set.preimage_comp]
  have hT : IsOpen ((seamProj x) ⁻¹' W ∩ seamU x) := by
    rw [Set.inter_comm]
    exact (continuousOn_seamProj x).isOpen_inter_preimage (isOpen_seamU x) hW
  have hT' : IsOpen ((seamProj x) ⁻¹' (Work.Surgery.flipEucl n ⁻¹' W) ∩ seamU x) := by
    rw [Set.inter_comm]
    exact (continuousOn_seamProj x).isOpen_inter_preimage (isOpen_seamU x)
      (hW.preimage (Work.Surgery.flipEucl n).continuous)
  have hset : seamSumSource x ∩ (seamG x) ⁻¹' W =
      Sum.inl '' ((seamProj x) ⁻¹' W ∩ seamU x) ∪
        Sum.inr '' ((seamProj x) ⁻¹' (Work.Surgery.flipEucl n ⁻¹' W) ∩ seamU x) := by
    ext a
    rcases a with y | y <;> rw [seamSumSource]
    · constructor
      · intro h
        rw [Set.mem_inter_iff, Set.mem_preimage, Set.mem_union] at h
        obtain ⟨hin, hmem⟩ := h
        rcases hin with ⟨z, hz, hzy⟩ | ⟨z, hz, hzy⟩
        · have hzy' : z = y := Sum.inl.inj hzy
          rw [hzy'] at hz
          rw [seamG_apply_inl (x := x) (y := y) hz] at hmem
          exact Or.inl ⟨y, ⟨hmem, hz⟩, rfl⟩
        · exact absurd hzy (by simp)
      · intro h
        rcases h with ⟨z, ⟨hzW, hzU⟩, hzy⟩ | h
        · have hzy' : z = y := Sum.inl.inj hzy
          rw [hzy'] at hzW hzU
          refine ⟨Or.inl ⟨y, hzU, rfl⟩, ?_⟩
          show seamG x (Sum.inl y) ∈ W
          rw [seamG_apply_inl (x := x) (y := y) hzU]
          exact hzW
        · obtain ⟨z, _, hzy⟩ := h
          exact absurd hzy (by simp)
    · constructor
      · intro h
        rw [Set.mem_inter_iff, Set.mem_preimage, Set.mem_union] at h
        obtain ⟨hin, hmem⟩ := h
        rcases hin with ⟨z, hz, hzy⟩ | ⟨z, hz, hzy⟩
        · exact absurd hzy (by simp)
        · have hzy' : z = y := Sum.inr.inj hzy
          rw [hzy'] at hz
          rw [seamG_apply_inr (x := x) (y := y) hz] at hmem
          exact Or.inr ⟨y, ⟨hmem, hz⟩, rfl⟩
      · intro h
        rcases h with h | ⟨z, ⟨hzW, hzU⟩, hzy⟩
        · obtain ⟨z, _, hzy⟩ := h
          exact absurd hzy (by simp)
        · have hzy' : z = y := Sum.inr.inj hzy
          rw [hzy'] at hzW hzU
          refine ⟨Or.inr ⟨y, hzU, rfl⟩, ?_⟩
          show seamG x (Sum.inr y) ∈ W
          rw [seamG_apply_inr (x := x) (y := y) hzU]
          exact hzW
  rw [hset]
  exact ((Topology.IsOpenEmbedding.inl (X := M) (Y := M)).isOpenMap _ hT).union
    ((Topology.IsOpenEmbedding.inr (X := M) (Y := M)).isOpenMap _ hT')

/-- The forward map of the seam chart is continuous on its source. -/
theorem continuousOn_seamF (x : (hModel n).boundary M) :
    ContinuousOn (seamF x) (seamSource x) := by
  have hcomp : (seamF x ∘ Quotient.mk' (s := (doubleData n M).setoid)) = seamG x := by
    funext a
    rcases a with y | y
    · exact seamF_inl x y
    · exact seamF_inr x y
  rw [Topology.IsQuotientMap.continuousOn_isOpen_iff
    (f := Quotient.mk' (s := (doubleData n M).setoid)) isQuotientMap_quotient_mk'
    (isOpen_seamSource x), preimage_seamSource x, hcomp]
  exact continuousOn_seamG x

/-- The inverse map of the seam chart is continuous on its target. -/
theorem continuousOn_seamInv (x : (hModel n).boundary M) :
    ContinuousOn (seamInv x) (seamTarget x) := by
  rw [continuousOn_iff_continuous_domRestrict]
  set P := seamTarget x with hPdef
  set s : Set ↥P := Subtype.val ⁻¹' {p : EuclideanSpace ℝ (Fin (n + 1)) | 0 ≤ p 0} with hsdef
  set t : Set ↥P := Subtype.val ⁻¹' {p : EuclideanSpace ℝ (Fin (n + 1)) | p 0 ≤ 0} with htdef
  have hsc : IsClosed s :=
    IsClosed.preimage continuous_subtype_val (isClosed_le continuous_const (by fun_prop))
  have htc : IsClosed t :=
    IsClosed.preimage continuous_subtype_val (isClosed_le (by fun_prop) continuous_const)
  have hcov : s ∪ t = univ := by
    ext q
    simp only [hsdef, htdef, Set.mem_union, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_univ,
      iff_true]
    exact le_total (0 : ℝ) (q.1 0)
  have hmemP : ∀ q : ↥P, q.1 ∈ seamTarget x := fun q => hPdef ▸ q.2
  have hmaps : MapsTo (fun q : ↥P => q.1) s (extChartAt (hModel n) x.1).target := by
    intro q hq
    simp only [hsdef, Set.mem_preimage, Set.mem_setOf_eq] at hq
    exact mem_extChartAt_target_of_mem_seamTarget x (hmemP q) hq
  have hcont1 : ContinuousOn (fun q : ↥P => seamEmb x q.1) s :=
    (continuousOn_extChartAt_symm (I := hModel n) x.1).comp
      (Continuous.continuousOn continuous_subtype_val) hmaps
  have h1 : ContinuousOn (P.domRestrict (seamInv x)) s :=
    (continuous_doubleιM (n := n) (M := M)).comp_continuousOn hcont1 |>.congr (fun q hq => by
      simp only [hsdef, Set.mem_preimage, Set.mem_setOf_eq] at hq
      exact (seamInv_of_nonneg x hq).trans rfl)
  have hmaps2 : MapsTo (fun q : ↥P => Work.Surgery.flipEucl n q.1) t
      (extChartAt (hModel n) x.1).target := by
    intro q hq
    simp only [htdef, Set.mem_preimage, Set.mem_setOf_eq] at hq
    exact mem_extChartAt_target_of_mem_seamTarget x (flip_mem_seamTarget x (hmemP q))
      (by rw [flipEucl_coord]; linarith)
  have hcont2 : ContinuousOn (fun q : ↥P => seamEmb x (Work.Surgery.flipEucl n q.1)) t :=
    (continuousOn_extChartAt_symm (I := hModel n) x.1).comp
      (Continuous.continuousOn ((Work.Surgery.flipEucl n).continuous.comp continuous_subtype_val))
      hmaps2
  have h2 : ContinuousOn (P.domRestrict (seamInv x)) t :=
    (continuous_doubleιN (n := n) (M := M)).comp_continuousOn hcont2 |>.congr (fun q hq => by
      simp only [htdef, Set.mem_preimage, Set.mem_setOf_eq] at hq
      rcases lt_or_eq_of_le hq with hlt | heq
      · exact (seamInv_of_neg x (not_le.mpr hlt)).trans rfl
      · show seamInv x q.1 = doubleιN (seamEmb x (Work.Surgery.flipEucl n q.1))
        rw [seamInv_of_nonneg x (le_of_eq heq.symm), flipEucl_eq_self_of_coord_zero heq]
        have hbnd : (hModel n).IsBoundaryPoint (seamEmb x q.1) :=
          isBoundaryPoint_symm_of_mem_target_one
            (mem_extChartAt_target_of_mem_seamTarget x (hmemP q) (le_of_eq heq.symm)) heq
        exact doubleιM_eq_ιN_iff.mpr ⟨⟨seamEmb x q.1, hbnd⟩, rfl, rfl⟩)
  have h3 := h1.union_of_isClosed h2 hsc htc
  rwa [hcov, continuousOn_univ] at h3

/-! ### The seam chart -/

/-- **The seam chart of the double at a boundary point `x` of `M`.** -/
noncomputable def seamChart (x : (hModel n).boundary M) :
    OpenPartialHomeomorph (Double n M) (EuclideanSpace ℝ (Fin (n + 1))) where
  toFun := seamF x
  invFun := seamInv x
  source := seamSource x
  target := seamTarget x
  map_source' := fun _z hz => seamF_mem_seamTarget x hz
  map_target' := fun _p hp => seamInv_mem_seamSource x hp
  left_inv' := fun _z hz => seamInv_seamF x hz
  right_inv' := fun _p hp => seamF_seamInv x hp
  open_source := isOpen_seamSource x
  open_target := isOpen_seamTarget x
  continuousOn_toFun := continuousOn_seamF x
  continuousOn_invFun := continuousOn_seamInv x

theorem seamChart_source (x : (hModel n).boundary M) :
    (seamChart x).source = seamSource x := rfl

theorem seamChart_target (x : (hModel n).boundary M) :
    (seamChart x).target = seamTarget x := rfl

/-- The seam chart contains the image of its base point. -/
theorem seamChart_mem_source_self (x : (hModel n).boundary M) :
    doubleιM (n := n) (M := M) x.1 ∈ (seamChart x).source := by
  rw [seamChart_source]
  refine ⟨Sum.inl x.1, Or.inl ⟨x.1, ⟨mem_chart_source _ _, ?_⟩, rfl⟩, rfl⟩
  have hcx : seamProj x x.1 ∈ chartOpen x := by
    have h1 := (mem_chartOpen_iff x ((chartAt (EuclideanHalfSpace (n + 1)) x.1) x.1)).mpr
      (mem_chart_target (EuclideanHalfSpace (n + 1)) x.1)
    simpa [seamProj] using h1
  exact ⟨hcx, ⟨seamProj x x.1, hcx, flipEucl_eq_self_of_coord_zero (chartAt_self_coord_zero x)⟩⟩


end

/-! ## The charted space structure on the double -/

section Assembly

variable (n : ℕ) {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 M]

/-- The chart attached to a point of `M ⊕ M`: an interior chart of the double if the point lies in
the interior of `M`, and a seam chart otherwise.  It is invariant under the gluing relation, so it
descends to the double. -/
noncomputable def doubleChartSum (a : M ⊕ M) :
    OpenPartialHomeomorph (Double n M) (EuclideanSpace ℝ (Fin (n + 1))) :=
  match a with
  | Sum.inl x => if hx : x ∈ (hModel n).boundary M then seamChart (n := n) ⟨x, hx⟩
      else intChartD (n := n) x hx
  | Sum.inr y => if hy : y ∈ (hModel n).boundary M then seamChart (n := n) ⟨y, hy⟩
      else intChartDN (n := n) y hy

/-- The chart is invariant under the gluing relation: two identified points of `M ⊕ M` — two copies
of the same boundary point of `M` — give the same chart. -/
theorem doubleChartSum_wellDefined {a b : M ⊕ M}
    (h : (doubleData n M).setoid.r a b) : doubleChartSum n a = doubleChartSum n b := by
  have hq : doubleQ (n := n) (M := M) a = doubleQ (n := n) (M := M) b := Quotient.sound' h
  rcases a with x | x <;> rcases b with y | y
  · have h1 : x = y := doubleιM_injective (by simpa only [doubleQ_inl] using hq)
    subst h1; rfl
  · obtain ⟨p, hp, hp'⟩ := doubleιM_eq_ιN_iff.mp (by simpa only [doubleQ_inl, doubleQ_inr] using hq)
    subst hp; subst hp'
    simp only [doubleChartSum, dif_pos p.2]
  · obtain ⟨p, hp, hp'⟩ :=
      doubleιM_eq_ιN_iff.mp (by simpa only [doubleQ_inl, doubleQ_inr] using hq.symm)
    subst hp; subst hp'
    simp only [doubleChartSum, dif_pos p.2]
  · have h1 : x = y := doubleιN_injective (by simpa only [doubleQ_inr] using hq)
    subst h1; rfl

/-- The invariance of `doubleChartSum` under the gluing relation, as the hypothesis of
`Quotient.lift`. -/
theorem doubleChartSumHyp : ∀ a b : M ⊕ M, (doubleData n M).setoid a b →
    doubleChartSum n a = doubleChartSum n b :=
  fun _ _ hab => doubleChartSum_wellDefined n hab

/-- **The preferred chart of the double at a point.** -/
noncomputable def doubleChartAt (z : Double n M) :
    OpenPartialHomeomorph (Double n M) (EuclideanSpace ℝ (Fin (n + 1))) :=
  Quotient.lift (s := (doubleData n M).setoid) (doubleChartSum n) (doubleChartSumHyp n) z

theorem doubleChartAt_inl (x : M) :
    doubleChartAt n (Quotient.mk (s := (doubleData n M).setoid) (Sum.inl x)) =
    (if hx : x ∈ (hModel n).boundary M then seamChart (n := n) ⟨x, hx⟩
      else intChartD (n := n) x hx) :=
  Quotient.lift_mk (s := (doubleData n M).setoid) (doubleChartSum n) (doubleChartSumHyp n) (Sum.inl x)

theorem doubleChartAt_inr (y : M) :
    doubleChartAt n (Quotient.mk (s := (doubleData n M).setoid) (Sum.inr y)) =
    (if hy : y ∈ (hModel n).boundary M then seamChart (n := n) ⟨y, hy⟩
      else intChartDN (n := n) y hy) :=
  Quotient.lift_mk (s := (doubleData n M).setoid) (doubleChartSum n) (doubleChartSumHyp n) (Sum.inr y)

/-- The preferred chart of the double at a point contains that point. -/
theorem doubleChartAt_mem_source (z : Double n M) : z ∈ (doubleChartAt n z).source := by
  obtain ⟨a, ha⟩ := Quotient.exists_rep z
  subst ha
  rcases a with x | x
  · by_cases hx : x ∈ (hModel n).boundary M
    · rw [doubleChartAt_inl, dif_pos hx]
      exact seamChart_mem_source_self (n := n) ⟨x, hx⟩
    · rw [doubleChartAt_inl, dif_neg hx]
      exact intChartD_mem_source_self (n := n) x hx
  · by_cases hx : x ∈ (hModel n).boundary M
    · rw [doubleChartAt_inr, dif_pos hx]
      have h1 : Quotient.mk (s := (doubleData n M).setoid) (Sum.inr x) =
          doubleιM (n := n) (M := M) x :=
        (doubleιM_eq_ιN_iff.mpr ⟨⟨x, hx⟩, rfl, rfl⟩).symm
      rw [h1]
      exact seamChart_mem_source_self (n := n) ⟨x, hx⟩
    · rw [doubleChartAt_inr, dif_neg hx]
      exact intChartDN_mem_source_self (n := n) x hx

/-- **The charted space structure on the double of `M`.** -/
noncomputable instance doubleChartedSpace :
    ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) (Double n M) where
  atlas := Set.univ
  chartAt := doubleChartAt n
  mem_chart_source := doubleChartAt_mem_source n
  chart_mem_atlas := fun _ => Set.mem_univ _

end Assembly

/-- **The double of a `C¹` manifold with boundary carries a charted space structure** modelled on
the boundaryless model `ℝ^{n+1}`, i.e. it is a manifold without boundary at the level of charts.

The charts are the interior charts of `M` pushed forward along the open embedding of the interior,
and the *seam charts*: at a boundary point `x`, the chart `chartAt _ x` of `M` is thickened to an
open subset `seamTarget x` of `ℝ^{n+1}` invariant under the reflection `flipEucl n` of the first
coordinate, whose positive half is the chart's target; the double is then read through this chart on
the first copy of `M` and through the reflection of it on the second copy.  The two formulas agree
on the seam because a chart sends boundary points to the hyperplane, where the reflection is the
identity. -/
theorem doubleCharted (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 M] :
    Nonempty (ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) (Work.ThomBordism.Double n M)) :=
  ⟨doubleChartedSpace (n := n) (M := M)⟩

end Work.ThomBordism

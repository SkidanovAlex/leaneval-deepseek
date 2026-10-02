import Mathlib
import Submission.Work.Orient.Defs
import Submission.Work.Orient.Boundary

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The boundary collapse of a compact manifold with boundary (general dimension)

`Work.PTGeometric.exists_boundaryCollapse_gen`: for every compact `(n+1)`-manifold `W` with
nonempty boundary `∂W` there is a compact `K ⊆ int W` and a self-map `ψ` of `W` such that

* `ψ` sends the complement of `K` into `∂W`,
* `ψ` fixes `∂W` pointwise,
* `ψ` is homotopic to the identity through maps sending `∂W` into itself.

This is the dimension-generic form of `Work.ThomBordism.RelDuality.exists_boundaryCollapse` (the
`9`-dimensional statement proved in `.../RelDuality/relClass_lift.lean` from the chart pieces of
`.../RelDuality/collapsePiece.lean`).  The `9`-dimensional files are hard-coded to dimension `9`
(their abbreviations `E9`, `H9`, `BoundaryCollapse`, `ColDatum` and all their intermediate
derivations mention the numeral `9`), so the chart-piece construction is reproduced here with the
model half-space `EuclideanHalfSpace (n + 1)` in place of `EuclideanHalfSpace 9`.

## The construction

A *collapse piece* is a chart `e : W → H` at a point of the boundary together with an ambient centre
`c` lying on the boundary hyperplane of the chart, a core radius `r > 0` and an outer radius
`R > r` whose closed ambient ball lies in the chart target.  In the chart it multiplies the first
coordinate by the bump `λ = max 0 (min 1 ((dist · c - r)/(R - r)))`:

* `λ = 0` on the closed `r`-ball (the *core*), so at time `1` the piece sends the core into `∂W`;
* `λ = 1` outside the open `R`-ball, so the piece is the identity there (this is what makes the
  pieces glue);
* `λ ∈ [0,1]`, so (because `c` lies on the boundary hyperplane) the piece does not increase the
  distance to `c` and hence stays inside the chart target — and it *fixes* the boundary hyperplane
  pointwise, at every time of the homotopy `λ(t) = (1 - t) + t λ`.

Composing the pieces of a finite list `L` of boundary points (each first piece applied first) gives
the map `colComp L`, and the compact set is

`K := (colGood L)ᶜ`, where `colGood` is the set of points which at some stage of the iteration lie
in the interior of the core of the piece applied at that stage.

Then `colComp L (·,1)` sends `colGood L` into `∂W` by construction, `K` lies in the interior because
the interiors of the cores cover `∂W` (compactness of `∂W`), and `∂W` is fixed pointwise at all
times.  The finite cover of `∂W` by the interiors of the cores is produced by
`IsCompact.elim_finite_subcover` from `ColDatum.ofPoint_mem_interior_core`.

## Main statements

* `Work.PTGeometric.exists_boundaryCollapse_gen` — the target;
* the chart-piece API `Work.PTGeometric.colLam`, `Work.PTGeometric.ColDatum`,
  `ColDatum.localMap_spec`, `ColDatum.ofPoint_mem_interior_core`, and the iterated collapse
  `Work.PTGeometric.colComp`, `colGood` together with their characteristic lemmas.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open scoped Topology Manifold
open Classical
open Function Set

namespace Work.PTGeometric

noncomputable section

section Gen

variable {n : ℕ}

/-! ## The model space, the chart criterion, and the model collapse pieces -/
def nrm : EuclideanSpace ℝ (Fin (n + 1)) := PiLp.single 2 (0 : Fin (n + 1)) 1

theorem nrm_apply_zero : nrm (0 : Fin (n + 1)) = 1 := by
  rw [nrm, PiLp.single_eq_same]

theorem nrm_apply_ne {k : Fin (n + 1)} (hk : k ≠ 0) : nrm k = 0 := by
  rw [nrm]
  exact PiLp.single_eq_of_ne (p := 2) hk 1

theorem isCompact_halfClosedBall (c : EuclideanSpace ℝ (Fin (n + 1))) (r : ℝ) :
    IsCompact {y : (EuclideanHalfSpace (n + 1)) | dist y.1 c ≤ r} := by
  have hclosed : IsClosed {x : EuclideanSpace ℝ (Fin (n + 1)) | 0 ≤ x 0} := isClosed_le continuous_const (by fun_prop)
  have hemb : Topology.IsClosedEmbedding (Subtype.val : (EuclideanHalfSpace (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))) :=
    IsClosed.isClosedEmbedding_subtypeVal hclosed
  exact hemb.isCompact_preimage (isCompact_closedBall c r)

theorem isInteriorPoint_iff_chart_coord {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 M]
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace (n + 1))} (he : e ∈ atlas (EuclideanHalfSpace (n + 1)) M) {y : M} (hy : y ∈ e.source) :
    (modelWithCornersEuclideanHalfSpace (n + 1)).IsInteriorPoint y ↔ 0 < (e y).1 0 := by
  have hn : (1 : WithTop ℕ∞) ≠ 0 := by simp
  rw [ModelWithCorners.isInteriorPoint_iff_of_mem_atlas
    (I := modelWithCornersEuclideanHalfSpace (n + 1)) hn he hy]
  constructor
  · intro h
    have h' := (OpenPartialHomeomorph.interior_extend_target_subset_interior_range
      (I := modelWithCornersEuclideanHalfSpace (n + 1)) e) h
    rw [interior_range_modelWithCornersEuclideanHalfSpace] at h'
    simpa [OpenPartialHomeomorph.extend_coe, modelWithCornersEuclideanHalfSpace_toFun] using h'
  · intro h
    refine OpenPartialHomeomorph.mem_interior_extend_target e (e.map_source hy) ?_
    rw [interior_range_modelWithCornersEuclideanHalfSpace]
    simpa [modelWithCornersEuclideanHalfSpace_toFun] using h

/-- **The interior of `M` is the complement of its boundary.** -/
theorem isInteriorPoint_iff_not_mem_boundary {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] (z : M) :
    (modelWithCornersEuclideanHalfSpace (n + 1)).IsInteriorPoint z ↔
      z ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M := by
  show z ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).interior M ↔ _
  rw [← ModelWithCorners.compl_boundary]
  exact Iff.rfl

theorem exists_closedBall_subset_target_gen {M : Type*} [TopologicalSpace M]
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace (n + 1))} {y : (EuclideanHalfSpace (n + 1))}
    (hy : y ∈ e.target) :
    ∃ r : ℝ, 0 < r ∧ ∀ z : (EuclideanHalfSpace (n + 1)), dist z.1 y.1 ≤ r → z ∈ e.target := by
  have hmem : e.target ∈ 𝓝 (⟨y.1, y.2⟩ : (EuclideanHalfSpace (n + 1))) := e.open_target.mem_nhds hy
  rw [nhds_subtype_eq_comap (p := fun z : EuclideanSpace ℝ (Fin (n + 1)) => 0 ≤ z 0) (x := y.1) (h := y.2)] at hmem
  obtain ⟨U, hU, hsub⟩ := Filter.mem_comap.mp hmem
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨ε / 2, by linarith, fun z hz => hsub ?_⟩
  exact hball (by rw [Metric.mem_ball]; linarith)


def colE (lam : EuclideanSpace ℝ (Fin (n + 1)) × ℝ → ℝ) (p : EuclideanSpace ℝ (Fin (n + 1)) × ℝ) : EuclideanSpace ℝ (Fin (n + 1)) :=
  p.1 + ((lam p - 1) * (p.1 : EuclideanSpace ℝ (Fin (n + 1))) 0) • nrm

/-- The first coordinate of `σ_λ` is `λ` times the first coordinate of the point. -/
theorem colE_apply_zero (lam : EuclideanSpace ℝ (Fin (n + 1)) × ℝ → ℝ) (p : EuclideanSpace ℝ (Fin (n + 1)) × ℝ) :
    colE lam p 0 = lam p * (p.1 : EuclideanSpace ℝ (Fin (n + 1))) 0 := by
  have h : colE lam p 0 = (p.1 : EuclideanSpace ℝ (Fin (n + 1))) 0 + ((lam p - 1) * (p.1 : EuclideanSpace ℝ (Fin (n + 1))) 0) * nrm (0 : Fin (n + 1)) := by
    simp [colE]
  rw [h, nrm_apply_zero]
  ring

/-- The other coordinates of `σ_λ` are unchanged. -/
theorem colE_apply_ne (lam : EuclideanSpace ℝ (Fin (n + 1)) × ℝ → ℝ) (p : EuclideanSpace ℝ (Fin (n + 1)) × ℝ) {k : Fin (n + 1)} (hk : k ≠ 0) :
    colE lam p k = (p.1 : EuclideanSpace ℝ (Fin (n + 1))) k := by
  simp [colE, nrm_apply_ne (n := n) hk]

/-- `σ_λ` is continuous whenever `λ` is. -/
theorem continuous_colE {lam : EuclideanSpace ℝ (Fin (n + 1)) × ℝ → ℝ} (h : Continuous lam) : Continuous (colE lam) := by
  have h2 : Continuous fun p : EuclideanSpace ℝ (Fin (n + 1)) × ℝ => ((p.1 : EuclideanSpace ℝ (Fin (n + 1))) 0) :=
    (PiLp.continuous_apply (p := 2) (i := (0 : Fin (n + 1))) (β := fun _ : Fin (n + 1) => ℝ)).comp
      continuous_fst
  have h3 : Continuous fun p : EuclideanSpace ℝ (Fin (n + 1)) × ℝ => (lam p - 1) * (p.1 : EuclideanSpace ℝ (Fin (n + 1))) 0 :=
    (h.sub continuous_const).mul h2
  exact continuous_fst.add (h3.smul continuous_const)

/-- `σ_λ` fixes the boundary hyperplane `{y | y 0 = 0}`. -/
theorem colE_eq_self_of_zero (lam : EuclideanSpace ℝ (Fin (n + 1)) × ℝ → ℝ) {p : EuclideanSpace ℝ (Fin (n + 1)) × ℝ} (h : (p.1 : EuclideanSpace ℝ (Fin (n + 1))) 0 = 0) :
    colE lam p = (p.1 : EuclideanSpace ℝ (Fin (n + 1))) := by
  have hz : (lam p - 1) * (p.1 : EuclideanSpace ℝ (Fin (n + 1))) 0 = 0 := by rw [h, mul_zero]
  simp [colE, hz]

/-- `σ_λ` is the identity where `λ = 1`. -/
theorem colE_eq_self_of_lam_eq_one (lam : EuclideanSpace ℝ (Fin (n + 1)) × ℝ → ℝ) {p : EuclideanSpace ℝ (Fin (n + 1)) × ℝ} (h : lam p = 1) :
    colE lam p = (p.1 : EuclideanSpace ℝ (Fin (n + 1))) := by
  have hz : (lam p - 1) * (p.1 : EuclideanSpace ℝ (Fin (n + 1))) 0 = 0 := by rw [h, sub_self, zero_mul]
  simp [colE, hz]

/-- For `λ = 0` the image lies in the boundary hyperplane. -/
theorem colE_zero_of_lam_eq_zero (lam : EuclideanSpace ℝ (Fin (n + 1)) × ℝ → ℝ) {p : EuclideanSpace ℝ (Fin (n + 1)) × ℝ} (h : lam p = 0) :
    colE lam p 0 = 0 := by
  rw [colE_apply_zero, h, zero_mul]

/-- `σ_λ` is the identity at `λ = 0` on the boundary hyperplane. -/
theorem colE_comm (lam : EuclideanSpace ℝ (Fin (n + 1)) × ℝ → ℝ) (p : EuclideanSpace ℝ (Fin (n + 1)) × ℝ) :
    colE lam p = (p.1 : EuclideanSpace ℝ (Fin (n + 1))) + ((lam p - 1) * (p.1 : EuclideanSpace ℝ (Fin (n + 1))) 0) • (nrm : EuclideanSpace ℝ (Fin (n + 1))) := rfl

/-! ## The half-space version -/

/-- **The model collapse map of the half-space**: `σ_λ` preserves `H = {y | 0 ≤ y 0}` for
`0 ≤ λ`. -/
def colH (lam : (EuclideanHalfSpace (n + 1)) × ℝ → ℝ) (h0 : ∀ p : (EuclideanHalfSpace (n + 1)) × ℝ, 0 ≤ lam p) (p : (EuclideanHalfSpace (n + 1)) × ℝ) : (EuclideanHalfSpace (n + 1)) :=
  ⟨(p.1 : (EuclideanHalfSpace (n + 1))).1 + ((lam p - 1) * ((p.1 : (EuclideanHalfSpace (n + 1))).1 0)) • nrm, by
    have h : (((p.1 : (EuclideanHalfSpace (n + 1))).1 + ((lam p - 1) * ((p.1 : (EuclideanHalfSpace (n + 1))).1 0)) • nrm : EuclideanSpace ℝ (Fin (n + 1)))) 0
        = (p.1 : (EuclideanHalfSpace (n + 1))).1 0 + ((lam p - 1) * ((p.1 : (EuclideanHalfSpace (n + 1))).1 0)) * nrm (0 : Fin (n + 1)) := by simp
    rw [h, nrm_apply_zero, mul_one]
    have : (p.1 : (EuclideanHalfSpace (n + 1))).1 0 + (lam p - 1) * (p.1 : (EuclideanHalfSpace (n + 1))).1 0 = lam p * (p.1 : (EuclideanHalfSpace (n + 1))).1 0 := by ring
    rw [this]
    exact mul_nonneg (h0 p) (p.1 : (EuclideanHalfSpace (n + 1))).2⟩

@[simp] theorem colH_coe (lam : (EuclideanHalfSpace (n + 1)) × ℝ → ℝ) (h0 : ∀ p : (EuclideanHalfSpace (n + 1)) × ℝ, 0 ≤ lam p) (p : (EuclideanHalfSpace (n + 1)) × ℝ) :
    (colH lam h0 p).1
      = (p.1 : (EuclideanHalfSpace (n + 1))).1 + ((lam p - 1) * ((p.1 : (EuclideanHalfSpace (n + 1))).1 0)) • (nrm : EuclideanSpace ℝ (Fin (n + 1))) := rfl

/-- The first coordinate of the half-space collapse. -/
theorem colH_coord_zero (lam : (EuclideanHalfSpace (n + 1)) × ℝ → ℝ) (h0 : ∀ p : (EuclideanHalfSpace (n + 1)) × ℝ, 0 ≤ lam p) (p : (EuclideanHalfSpace (n + 1)) × ℝ) :
    (colH lam h0 p).1 0 = lam p * (p.1 : (EuclideanHalfSpace (n + 1))).1 0 := by
  rw [colH_coe]
  have h : (((p.1 : (EuclideanHalfSpace (n + 1))).1 + ((lam p - 1) * ((p.1 : (EuclideanHalfSpace (n + 1))).1 0)) • nrm : EuclideanSpace ℝ (Fin (n + 1)))) 0
      = (p.1 : (EuclideanHalfSpace (n + 1))).1 0 + ((lam p - 1) * ((p.1 : (EuclideanHalfSpace (n + 1))).1 0)) * nrm (0 : Fin (n + 1)) := by simp
  rw [h, nrm_apply_zero]
  ring

/-- The half-space collapse fixes the boundary hyperplane pointwise. -/
theorem colH_eq_self_of_coord_zero (lam : (EuclideanHalfSpace (n + 1)) × ℝ → ℝ) (h0 : ∀ p : (EuclideanHalfSpace (n + 1)) × ℝ, 0 ≤ lam p)
    {p : (EuclideanHalfSpace (n + 1)) × ℝ} (h : (p.1 : (EuclideanHalfSpace (n + 1))).1 0 = 0) : colH lam h0 p = p.1 := by
  apply Subtype.ext
  rw [colH_coe]
  have hz : (lam p - 1) * ((p.1 : (EuclideanHalfSpace (n + 1))).1 0) = 0 := by rw [h, mul_zero]
  simp [hz]

/-- Where `λ = 0`, the half-space collapse lands on the boundary hyperplane. -/
theorem colH_coord_zero_of_lam_eq_zero (lam : (EuclideanHalfSpace (n + 1)) × ℝ → ℝ) (h0 : ∀ p : (EuclideanHalfSpace (n + 1)) × ℝ, 0 ≤ lam p)
    {p : (EuclideanHalfSpace (n + 1)) × ℝ} (h : lam p = 0) : (colH lam h0 p).1 0 = 0 := by
  rw [colH_coord_zero, h, zero_mul]

/-- The half-space collapse is the identity where `λ = 1`. -/
theorem colH_eq_self_of_lam_eq_one (lam : (EuclideanHalfSpace (n + 1)) × ℝ → ℝ) (h0 : ∀ p : (EuclideanHalfSpace (n + 1)) × ℝ, 0 ≤ lam p)
    {p : (EuclideanHalfSpace (n + 1)) × ℝ} (h : lam p = 1) : colH lam h0 p = p.1 := by
  apply Subtype.ext
  rw [colH_coe]
  have hz : (lam p - 1) * ((p.1 : (EuclideanHalfSpace (n + 1))).1 0) = 0 := by rw [h, sub_self, zero_mul]
  simp [hz]

/-- The half-space collapse is jointly continuous. -/
theorem continuous_colH (lam : (EuclideanHalfSpace (n + 1)) × ℝ → ℝ) (h : Continuous lam)
    (h0 : ∀ p : (EuclideanHalfSpace (n + 1)) × ℝ, 0 ≤ lam p) : Continuous (colH lam h0) := by
  have hcoord : Continuous fun p : (EuclideanHalfSpace (n + 1)) × ℝ => (p.1 : (EuclideanHalfSpace (n + 1))).1 0 :=
    (PiLp.continuous_apply (p := 2) (i := (0 : Fin (n + 1))) (β := fun _ : Fin (n + 1) => ℝ)).comp
      ((continuous_subtype_val : Continuous (Subtype.val : (EuclideanHalfSpace (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))).comp continuous_fst)
  have hterm : Continuous fun p : (EuclideanHalfSpace (n + 1)) × ℝ => ((lam p - 1) * (p.1 : (EuclideanHalfSpace (n + 1))).1 0) • (nrm : EuclideanSpace ℝ (Fin (n + 1))) :=
    ((h.sub continuous_const).mul hcoord).smul continuous_const
  have hbase : Continuous fun p : (EuclideanHalfSpace (n + 1)) × ℝ => (p.1 : (EuclideanHalfSpace (n + 1))).1 :=
    (continuous_subtype_val : Continuous (Subtype.val : (EuclideanHalfSpace (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))).comp continuous_fst
  exact Continuous.subtype_mk (hbase.add hterm) _

/-! ## The chart piece on a manifold with boundary -/

section Chart

variable {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 M] [CompactSpace M]

/-- **The chart piece fixes the boundary.**  If `x` is in the source of the atlas chart `e` and on
`∂M`, then `e ⁻¹ (σ_λ (e x)) = x`: in the chart `x` has vanishing first coordinate, where `σ_λ` is
the identity. -/
theorem chartPiece_eq_self_of_boundary {e : OpenPartialHomeomorph M (EuclideanHalfSpace (n + 1))} (he : e ∈ atlas (EuclideanHalfSpace (n + 1)) M)
    {lam : (EuclideanHalfSpace (n + 1)) × ℝ → ℝ} (h0 : ∀ p : (EuclideanHalfSpace (n + 1)) × ℝ, 0 ≤ lam p)
    {x : M} (hx : x ∈ e.source)
    (hxb : x ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M) :
    e.symm (colH lam h0 (e x, 1)) = x := by
  have hcoord : (e x).1 0 = 0 := by
    have hnot : ¬ (0 < (e x).1 0) := fun h =>
      ((isInteriorPoint_iff_not_mem_boundary x).mp
        ((isInteriorPoint_iff_chart_coord (M := M) he hx).mpr h)) hxb
    linarith [not_lt.mp hnot, (e x).2]
  rw [colH_eq_self_of_coord_zero lam h0 hcoord, e.left_inv hx]

/-- **The chart piece collapses the `λ = 0` zone onto the boundary**: if the chart image of `x` has
`λ = 0`, then `e ⁻¹ (σ_λ (e x))` is a boundary point (`σ_λ` sends it to the hyperplane `{y 0 = 0}`,
and the chart criterion `isInteriorPoint_iff_chart_coord` converts that into `∂M`). -/
theorem chartPiece_mem_boundary_of_lam_eq_zero {e : OpenPartialHomeomorph M (EuclideanHalfSpace (n + 1))}
    (he : e ∈ atlas (EuclideanHalfSpace (n + 1)) M) {lam : (EuclideanHalfSpace (n + 1)) × ℝ → ℝ} (h0 : ∀ p : (EuclideanHalfSpace (n + 1)) × ℝ, 0 ≤ lam p)
    (ht : ∀ y ∈ e.target, colH lam h0 (y, 1) ∈ e.target)
    {x : M} (hx : x ∈ e.source) (hlam : lam (e x, 1) = 0) :
    e.symm (colH lam h0 (e x, 1)) ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M := by
  have htarget : colH lam h0 (e x, 1) ∈ e.target := ht (e x) (e.map_source hx)
  have hsrc : e.symm (colH lam h0 (e x, 1)) ∈ e.source := e.map_target htarget
  have hni : ¬ (modelWithCornersEuclideanHalfSpace (n + 1)).IsInteriorPoint
      (e.symm (colH lam h0 (e x, 1))) := by
    intro hInt
    have hlt : 0 < (e (e.symm (colH lam h0 (e x, 1)))).1 0 :=
      (isInteriorPoint_iff_chart_coord (M := M) he hsrc).mp hInt
    rw [e.right_inv htarget, colH_coord_zero lam h0 (e x, 1), hlam, zero_mul] at hlt
    exact lt_irrefl 0 hlt
  exact of_not_not ((isInteriorPoint_iff_not_mem_boundary _).not.mp hni)

end Chart

/-! ## The interpolation function `λ` of a collapse piece

Each collapse piece carries a `λ : (EuclideanHalfSpace (n + 1)) × ℝ → ℝ` which is `0` on its core, `1` near its frontier, and
takes values in `[0,1]`.  In the ambient chart coordinates such a `λ` is produced by the model bump
below, attached to an *ambient* ball (`PushDatum.region` is defined by the ambient distance
`dist (chart x).1 center < radius`, so the ambient ball is the right carrier). -/

/-- **The model bump of a collapse piece**: `0` on the closed ball of radius `r` about `c`, `1`
outside the ball of radius `R`, and continuous in between (`0 < r < R`). -/
def colLam (c : EuclideanSpace ℝ (Fin (n + 1))) (r R : ℝ) (y : EuclideanSpace ℝ (Fin (n + 1))) : ℝ :=
  max 0 (min 1 ((dist y c - r) / (R - r)))

theorem continuous_colLam (c : EuclideanSpace ℝ (Fin (n + 1))) (r R : ℝ) : Continuous (colLam c r R) := by
  unfold colLam
  fun_prop

theorem colLam_nonneg (c : EuclideanSpace ℝ (Fin (n + 1))) (r R : ℝ) (y : EuclideanSpace ℝ (Fin (n + 1))) : 0 ≤ colLam c r R y :=
  le_max_left _ _

theorem colLam_le_one (c : EuclideanSpace ℝ (Fin (n + 1))) (r R : ℝ) (y : EuclideanSpace ℝ (Fin (n + 1))) : colLam c r R y ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

/-- The bump vanishes on the inner ball (the core of the piece). -/
theorem colLam_eq_zero {c : EuclideanSpace ℝ (Fin (n + 1))} {r R : ℝ} (hr : r < R) {y : EuclideanSpace ℝ (Fin (n + 1))} (h : dist y c ≤ r) :
    colLam c r R y = 0 := by
  have hR : 0 < R - r := by linarith
  have hq : (dist y c - r) / (R - r) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt hR)
  rw [colLam, max_eq_left (le_trans (min_le_right _ _) hq)]

/-- The bump equals one outside the outer ball (so the piece is the identity past its frontier). -/
theorem colLam_eq_one {c : EuclideanSpace ℝ (Fin (n + 1))} {r R : ℝ} (hr : r < R) {y : EuclideanSpace ℝ (Fin (n + 1))} (h : R ≤ dist y c) :
    colLam c r R y = 1 := by
  have hR : 0 < R - r := by linarith
  have h1 : 1 ≤ (dist y c - r) / (R - r) := by
    rw [le_div_iff₀ hR]
    linarith
  rw [colLam, min_eq_left h1, max_eq_right zero_le_one]

/-! ## The datum of a collapse piece -/

/-- **The datum of one collapse piece**: an atlas chart, an ambient centre, a *core* radius `r` and
an *outer* radius `R > r` whose closed ambient ball lies in the chart target.  Everything is stated
in *ambient* chart coordinates (as for `PushDatum`), so no metric instance on `(EuclideanHalfSpace (n + 1))` is ever needed.

The piece acts on `region` (its chart source intersected with the open `R`-ball), is the identity
outside it, sends `core` (the closed `r`-ball part) onto the boundary, and interpolates in between. -/
structure ColDatum (n : ℕ) (M : Type) [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace (n + 1)) M] where
  /-- the chart of the piece -/
  chart : OpenPartialHomeomorph M (EuclideanHalfSpace (n + 1))
  /-- the chart is in the atlas (so `isInteriorPoint_iff_chart_coord` applies) -/
  chart_mem_atlas : chart ∈ atlas (EuclideanHalfSpace (n + 1)) M
  /-- the ambient centre of the piece -/
  center : EuclideanSpace ℝ (Fin (n + 1))
  /-- the radius of the core (where `λ = 0`) -/
  r : ℝ
  /-- the outer radius of the piece (where `λ = 1`) -/
  R : ℝ
  /-- the core radius is positive -/
  hr_pos : 0 < r
  /-- the core radius is smaller than the outer radius (the interpolation annulus is nondegenerate) -/
  hrR : r < R
  /-- the closed ambient `R`-ball lies in the chart target -/
  closedBall_subset : ∀ y : (EuclideanHalfSpace (n + 1)), dist y.1 center ≤ R → y ∈ chart.target

namespace ColDatum

variable {M : Type} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]

/-- The interpolation function of the piece, in ambient coordinates. -/
def lam (D : ColDatum n M) : EuclideanSpace ℝ (Fin (n + 1)) → ℝ := colLam D.center D.r D.R

/-- **The region of the piece**: the points of the chart source whose chart image lies in the open
ambient `R`-ball.  The piece is the identity outside its region. -/
def region (D : ColDatum n M) : Set M :=
  D.chart.source ∩ {x : M | dist (D.chart x).1 D.center < D.R}

/-- **The core of the piece**: the points of the chart source whose chart image lies in the closed
ambient `r`-ball.  The piece collapses the core onto the boundary (`λ = 0` there). -/
def core (D : ColDatum n M) : Set M :=
  D.chart.source ∩ {x : M | dist (D.chart x).1 D.center ≤ D.r}

theorem mem_region {D : ColDatum n M} {x : M} :
    x ∈ D.region ↔ x ∈ D.chart.source ∧ dist (D.chart x).1 D.center < D.R := Iff.rfl

theorem mem_core {D : ColDatum n M} {x : M} :
    x ∈ D.core ↔ x ∈ D.chart.source ∧ dist (D.chart x).1 D.center ≤ D.r := Iff.rfl

theorem lam_nonneg (D : ColDatum n M) (y : EuclideanSpace ℝ (Fin (n + 1))) : 0 ≤ D.lam y := colLam_nonneg _ _ _ y

theorem lam_le_one (D : ColDatum n M) (y : EuclideanSpace ℝ (Fin (n + 1))) : D.lam y ≤ 1 := colLam_le_one _ _ _ y

/-- On the core the interpolation function vanishes. -/
theorem lam_eq_zero_of_mem_core (D : ColDatum n M) {x : M} (hx : x ∈ D.core) :
    D.lam (D.chart x).1 = 0 :=
  colLam_eq_zero D.hrR (mem_core.mp hx).2

/-- Off the region (inside the chart source) the interpolation function equals one, so the piece is
the identity there and pieces with disjoint regions glue. -/
theorem lam_eq_one_of_not_mem_region (D : ColDatum n M) {x : M} (hx : x ∈ D.chart.source)
    (h : x ∉ D.region) : D.lam (D.chart x).1 = 1 :=
  colLam_eq_one D.hrR (not_lt.mp fun hlt => h (mem_region.mpr ⟨hx, hlt⟩))

/-- The region of a piece is open. -/
theorem isOpen_region (D : ColDatum n M) : IsOpen D.region := by
  have h : IsOpen {y : (EuclideanHalfSpace (n + 1)) | dist y.1 D.center < D.R} :=
    Metric.isOpen_ball.preimage continuous_subtype_val
  have h2 := D.chart.isOpen_inter_preimage h
  simpa only [region, Set.preimage_setOf_eq, Set.mem_setOf_eq] using h2

end ColDatum

/-! ## Target stability of the model collapse

The collapse `σ_λ` keeps every coordinate except the first, which it multiplies by `λ`.  Hence, for a
centre `c` on the hyperplane `{y | y 0 = 0}`, it never *increases* the distance to `c`: the first
coordinate contributes `(λ y₀)² ≤ y₀²`, and all the other contributions are unchanged.  This is what
keeps a chart piece inside its chart target (`ColDatum.closedBall_subset`) with no extra hypothesis.
-/

theorem dist_colE_le {lam : EuclideanSpace ℝ (Fin (n + 1)) × ℝ → ℝ} (h0 : ∀ p : EuclideanSpace ℝ (Fin (n + 1)) × ℝ, 0 ≤ lam p)
    (h1 : ∀ p : EuclideanSpace ℝ (Fin (n + 1)) × ℝ, lam p ≤ 1) {c : EuclideanSpace ℝ (Fin (n + 1))} (hc : c 0 = 0) (p : EuclideanSpace ℝ (Fin (n + 1)) × ℝ)
    (hp : 0 ≤ (p.1 : EuclideanSpace ℝ (Fin (n + 1))) 0) :
    dist (colE lam p) c ≤ dist (p.1 : EuclideanSpace ℝ (Fin (n + 1))) c := by
  have hv0 : (colE lam p - c) 0 = lam p * (p.1 : EuclideanSpace ℝ (Fin (n + 1))) 0 := by
    have h : (colE lam p - c) 0
        = (p.1 : EuclideanSpace ℝ (Fin (n + 1))) 0 + ((lam p - 1) * (p.1 : EuclideanSpace ℝ (Fin (n + 1))) 0) * nrm (0 : Fin (n + 1)) - c 0 := by
      simp [colE]
    rw [h, nrm_apply_zero, hc]
    ring
  have hw0 : ((p.1 : EuclideanSpace ℝ (Fin (n + 1))) - c) 0 = (p.1 : EuclideanSpace ℝ (Fin (n + 1))) 0 := by
    have h : ((p.1 : EuclideanSpace ℝ (Fin (n + 1))) - c) 0 = (p.1 : EuclideanSpace ℝ (Fin (n + 1))) 0 - c 0 := by simp
    rw [h, hc, sub_zero]
  have hne : ∀ i : Fin (n + 1), i ≠ 0 → (colE lam p - c) i = ((p.1 : EuclideanSpace ℝ (Fin (n + 1))) - c) i := by
    intro i hi
    have h : (colE lam p - c) i
        = (p.1 : EuclideanSpace ℝ (Fin (n + 1))) i + ((lam p - 1) * (p.1 : EuclideanSpace ℝ (Fin (n + 1))) 0) * nrm i - c i := by
      simp [colE]
    have h2 : ((p.1 : EuclideanSpace ℝ (Fin (n + 1))) - c) i = (p.1 : EuclideanSpace ℝ (Fin (n + 1))) i - c i := by simp
    rw [h, nrm_apply_ne hi, h2]
    ring
  rw [dist_eq_norm, dist_eq_norm, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  refine Finset.sum_le_sum (fun i _ => ?_)
  rcases eq_or_ne i 0 with rfl | hi
  · rw [hv0, hw0, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
    have h1'' : |lam p| ≤ 1 := by
      rw [abs_of_nonneg (h0 p)]
      exact h1 p
    have h2'' : 0 ≤ |(p.1 : EuclideanSpace ℝ (Fin (n + 1))) 0| := abs_nonneg _
    nlinarith [mul_le_mul_of_nonneg_right h1'' h2'',
      mul_nonneg (abs_nonneg (lam p)) h2'', sq_nonneg (|lam p| * |(p.1 : EuclideanSpace ℝ (Fin (n + 1))) 0|)]
  · rw [hne i hi]

/-! ## Obligation 2: the local map of a piece and its continuity ingredients

The homotopy of a piece interpolates `λ` from `1` (the identity) at time `0` to `λ` at time `1`.  The
time is *clamped* into `[0,1]` so that the family stays `[0,1]`-valued for every real time, which is
what `colH` needs; clamping also makes the map the identity for `t ≤ 0`. -/

/-- The clamped time of the homotopy. -/
def colT (t : ℝ) : ℝ := max 0 (min t 1)

theorem colT_nonneg (t : ℝ) : 0 ≤ colT t := le_max_left _ _

theorem colT_le_one (t : ℝ) : colT t ≤ 1 := max_le zero_le_one (min_le_right _ _)

theorem continuous_colT : Continuous colT := by
  unfold colT
  fun_prop

theorem colT_zero : colT 0 = 0 := by simp [colT]

theorem colT_one : colT 1 = 1 := by simp [colT]

namespace ColDatum

variable {M : Type} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 M] [CompactSpace M]

/-- **The interpolated interpolation function of a piece**, ambient form: `1` at time `0` and
`D.lam` at time `1`.  It is defined on the *whole* `EuclideanSpace ℝ (Fin (n + 1)) × ℝ` because `D.lam = colLam center r R`
carries no half-space condition — this is what lets `dist_colE_le` (which is about `EuclideanSpace ℝ (Fin (n + 1)) × ℝ`) consume
it directly. -/
def lamT (D : ColDatum n M) (p : EuclideanSpace ℝ (Fin (n + 1)) × ℝ) : ℝ :=
  (1 - colT p.2) + colT p.2 * D.lam p.1

/-- The half-space restriction of `lamT`, which is what `colH` consumes. -/
def lamTH (D : ColDatum n M) (p : (EuclideanHalfSpace (n + 1)) × ℝ) : ℝ := D.lamT ((p.1 : (EuclideanHalfSpace (n + 1))).1, p.2)

theorem lamT_nonneg (D : ColDatum n M) (p : EuclideanSpace ℝ (Fin (n + 1)) × ℝ) : 0 ≤ D.lamT p := by
  have h0 : 0 ≤ colT p.2 := colT_nonneg p.2
  have h1 : colT p.2 ≤ 1 := colT_le_one p.2
  have hl0 : 0 ≤ D.lam p.1 := D.lam_nonneg _
  have hl1 : D.lam p.1 ≤ 1 := D.lam_le_one _
  rw [lamT]
  nlinarith [mul_nonneg (sub_nonneg.mpr h1) hl0, mul_nonneg h0 hl0]

theorem lamT_le_one (D : ColDatum n M) (p : EuclideanSpace ℝ (Fin (n + 1)) × ℝ) : D.lamT p ≤ 1 := by
  have h0 : 0 ≤ colT p.2 := colT_nonneg p.2
  have h1 : colT p.2 ≤ 1 := colT_le_one p.2
  have hl0 : 0 ≤ D.lam p.1 := D.lam_nonneg _
  have hl1 : D.lam p.1 ≤ 1 := D.lam_le_one _
  rw [lamT]
  nlinarith [mul_le_mul_of_nonneg_left hl1 h0, h0, hl0]

theorem lamTH_nonneg (D : ColDatum n M) (p : (EuclideanHalfSpace (n + 1)) × ℝ) : 0 ≤ D.lamTH p :=
  D.lamT_nonneg _

/-- At time `0` the interpolated function is `1` (the identity). -/
theorem lamT_zero (D : ColDatum n M) (y : EuclideanSpace ℝ (Fin (n + 1))) : D.lamT (y, 0) = 1 := by
  rw [lamT, colT_zero]
  ring

theorem lamTH_zero (D : ColDatum n M) (y : (EuclideanHalfSpace (n + 1))) : D.lamTH (y, 0) = 1 :=
  lamT_zero D _

theorem continuous_lam (D : ColDatum n M) : Continuous D.lam :=
  continuous_colLam D.center D.r D.R

theorem continuous_lamT (D : ColDatum n M) : Continuous D.lamT := by
  unfold lamT
  have h1 : Continuous fun p : EuclideanSpace ℝ (Fin (n + 1)) × ℝ => colT p.2 := continuous_colT.comp continuous_snd
  have h2 : Continuous fun p : EuclideanSpace ℝ (Fin (n + 1)) × ℝ => D.lam p.1 := D.continuous_lam.comp continuous_fst
  exact (continuous_const.sub h1).add (h1.mul h2)

theorem continuous_lamTH (D : ColDatum n M) : Continuous D.lamTH := by
  unfold lamTH
  have h1 : Continuous fun p : (EuclideanHalfSpace (n + 1)) × ℝ => colT p.2 := continuous_colT.comp continuous_snd
  have h2 : Continuous fun p : (EuclideanHalfSpace (n + 1)) × ℝ => D.lam (p.1 : (EuclideanHalfSpace (n + 1))).1 :=
    D.continuous_lam.comp
      ((continuous_subtype_val : Continuous (Subtype.val : (EuclideanHalfSpace (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))).comp continuous_fst)
  have h3 : Continuous fun p : (EuclideanHalfSpace (n + 1)) × ℝ => D.lamT ((p.1 : (EuclideanHalfSpace (n + 1))).1, p.2) := by
    unfold lamT
    have h4 : Continuous fun p : (EuclideanHalfSpace (n + 1)) × ℝ => colT p.2 := continuous_colT.comp continuous_snd
    exact (continuous_const.sub h4).add (h4.mul h2)
  exact h3

/-- **The local map of the piece at time `t`**: on the region it is the chart conjugate of the
model collapse `colH`, off the region it is the identity.  (The hypothesis `hctr : (D.center) 0 = 0`
is kept because the *proofs* of the map's correctness — that the image lands in the chart target and
hence in `∂M` on the core — go through `dist_colE_le`, whose `hctr` hypothesis is exactly this.) -/
def localMap (D : ColDatum n M) (hctr : (D.center) 0 = 0) (t : ℝ) (x : M) : M :=
  if _hx : x ∈ D.region then
    D.chart.symm (colH D.lamTH D.lamTH_nonneg (D.chart x, t))
  else x

/-- **The `MapsTo` obligation for the continuity of `localMap`**: on the region, the chart
conjugate of the piece formula lands in the chart target.  This is where the ambient form `lamT` pays
off — `dist_colE_le` applies to it directly. -/
theorem colH_mem_target (D : ColDatum n M) (hctr : (D.center) 0 = 0) {x : M}
    (hx : x ∈ D.region) (t : ℝ) :
    colH D.lamTH D.lamTH_nonneg (D.chart x, t) ∈ D.chart.target := by
  refine D.closedBall_subset _ ?_
  have h := dist_colE_le D.lamT_nonneg D.lamT_le_one hctr ((D.chart x : (EuclideanHalfSpace (n + 1))).1, t) (D.chart x).2
  have heq : (colH D.lamTH D.lamTH_nonneg (D.chart x, t)).1
      = colE D.lamT ((D.chart x : (EuclideanHalfSpace (n + 1))).1, t) := rfl
  rw [heq]
  exact le_trans h (le_of_lt (mem_region.mp hx).2)

/-- **The two-case `MapsTo` for the piece formula**: on the whole chart source (with all times), the
formula lands in the chart target.  Off the region `λ = 1` makes the formula the identity, so the
chart itself provides the target membership; on the region this is `colH_mem_target`. -/
theorem mapsTo_formula (D : ColDatum n M) (hctr : (D.center) 0 = 0) :
    Set.MapsTo (fun p : M × ℝ => colH D.lamTH D.lamTH_nonneg (D.chart p.1, p.2))
      (D.chart.source ×ˢ (Set.univ : Set ℝ)) D.chart.target := by
  rintro ⟨x, t⟩ hp
  have hx : x ∈ D.chart.source := hp.1
  show colH D.lamTH D.lamTH_nonneg (D.chart x, t) ∈ D.chart.target
  by_cases hreg : x ∈ D.region
  · exact D.colH_mem_target hctr hreg t
  · have h1 : D.lamTH (D.chart x, t) = 1 := by
      have h := D.lam_eq_one_of_not_mem_region hx hreg
      simp only [lamTH, lamT, h, mul_one]
      ring
    rw [colH_eq_self_of_lam_eq_one D.lamTH D.lamTH_nonneg h1]
    exact D.chart.map_source hx

/-- **The formula of the piece is continuous on the chart source** (at all times): the
`ContinuousOn.comp` step, from `continuous_colH` and the two-case `mapsTo_formula`. -/
theorem continuousOn_formula (D : ColDatum n M) (hctr : (D.center) 0 = 0) :
    ContinuousOn
      (fun p : M × ℝ => D.chart.symm (colH D.lamTH D.lamTH_nonneg (D.chart p.1, p.2)))
      (D.chart.source ×ˢ (Set.univ : Set ℝ)) := by
  have hchart : ContinuousOn (fun p : M × ℝ => D.chart p.1) (D.chart.source ×ˢ univ) :=
    ContinuousOn.comp (g := fun x : M => D.chart x) (t := D.chart.source)
      D.chart.continuousOn continuousOn_fst (fun p hp => hp.1)
  have hcore : ContinuousOn (fun p : M × ℝ => (D.chart p.1, p.2)) (D.chart.source ×ˢ univ) :=
    hchart.prodMk continuousOn_snd
  have hcolHcont : Continuous fun q : (EuclideanHalfSpace (n + 1)) × ℝ => colH D.lamTH D.lamTH_nonneg q :=
    continuous_colH D.lamTH D.continuous_lamTH D.lamTH_nonneg
  have hpush : ContinuousOn (fun p : M × ℝ => colH D.lamTH D.lamTH_nonneg (D.chart p.1, p.2))
      (D.chart.source ×ˢ univ) :=
    hcolHcont.comp_continuousOn hcore
  exact ContinuousOn.comp D.chart.symm.continuousOn hpush (mapsTo_formula D hctr)

theorem localMap_eq_self_of_not_mem_region (D : ColDatum n M) (hctr : (D.center) 0 = 0) {x : M}
    (hx : x ∉ D.region) (t : ℝ) : D.localMap hctr t x = x := by
  rw [localMap, dif_neg hx]

/-- At time `0` the local map is the identity. -/
theorem localMap_zero (D : ColDatum n M) (hctr : (D.center) 0 = 0) (x : M) :
    D.localMap hctr 0 x = x := by
  by_cases hx : x ∈ D.region
  · rw [localMap, dif_pos hx]
    have hlt : D.lamTH (D.chart x, 0) = 1 := lamTH_zero D (D.chart x)
    have hfix : colH D.lamTH D.lamTH_nonneg (D.chart x, 0) = D.chart x :=
      colH_eq_self_of_lam_eq_one _ _ hlt
    rw [hfix, D.chart.left_inv (mem_region.mp hx).1]
  · exact localMap_eq_self_of_not_mem_region D hctr hx 0

/-- **The region lies in the image of the closed ambient ball**: this is what turns
`x ∉ D.region` into "`x` is outside a closed set", hence — with `isCompact_symm_image` — into a
*neighbourhood* on which `localMap` is the identity (the gluing step of the continuity proof). -/
theorem region_subset_symm_image (D : ColDatum n M) :
    D.region ⊆ D.chart.symm '' {y : (EuclideanHalfSpace (n + 1)) | dist y.1 D.center ≤ D.R} := by
  intro x hx
  obtain ⟨hsrc, hlt⟩ := mem_region.mp hx
  exact ⟨D.chart x, le_of_lt hlt, D.chart.left_inv hsrc⟩

/-- The image of the closed ambient ball is contained in the chart source. -/
theorem symm_image_subset_source (D : ColDatum n M) :
    D.chart.symm '' {y : (EuclideanHalfSpace (n + 1)) | dist y.1 D.center ≤ D.R} ⊆ D.chart.source := by
  rintro z ⟨y, hy, rfl⟩
  exact D.chart.map_target (D.closedBall_subset y hy)

/-- **The image of the closed ambient ball is compact** (the closed half-ball is compact by
`isCompact_halfClosedBall`, and the chart inverse is continuous on it). -/
theorem isCompact_symm_image (D : ColDatum n M) :
    IsCompact (D.chart.symm '' {y : (EuclideanHalfSpace (n + 1)) | dist y.1 D.center ≤ D.R}) :=
  (isCompact_halfClosedBall D.center D.R).image_of_continuousOn
    (D.chart.symm.continuousOn.mono (fun y hy => D.closedBall_subset y hy))

/-- Off the (closed) image of the ball, `localMap` is the identity — the neighbourhood form used in
the glueing of `PushDatum.continuous_localMap_uncurry`. -/
theorem localMap_eq_self_of_not_mem_symm_image (D : ColDatum n M) (hctr : (D.center) 0 = 0) {x : M}
    (hx : x ∉ D.chart.symm '' {y : (EuclideanHalfSpace (n + 1)) | dist y.1 D.center ≤ D.R}) (t : ℝ) :
    D.localMap hctr t x = x :=
  D.localMap_eq_self_of_not_mem_region hctr
    (fun h => hx (D.region_subset_symm_image h)) t

/-- **The formula of the piece agrees with `localMap` on the whole chart source**: on the region this
is by definition, and off it `λ = 1` makes the formula collapse to the identity, which is also the
off-region value of `localMap`. -/
theorem localMap_eq_formula (D : ColDatum n M) (hctr : (D.center) 0 = 0) {x : M}
    (hx : x ∈ D.chart.source) (t : ℝ) :
    D.localMap hctr t x = D.chart.symm (colH D.lamTH D.lamTH_nonneg (D.chart x, t)) := by
  by_cases hreg : x ∈ D.region
  · rw [localMap, dif_pos hreg]
  · rw [localMap, dif_neg hreg]
    have h1 : D.lamTH (D.chart x, t) = 1 := by
      have h := D.lam_eq_one_of_not_mem_region hx hreg
      simp only [lamTH, lamT, h, mul_one]
      ring
    rw [colH_eq_self_of_lam_eq_one D.lamTH D.lamTH_nonneg h1, D.chart.left_inv hx]

/-- **Joint continuity of the local map of a piece** (the `PushDatum.continuous_localMap_uncurry`
template): on the open chart-source neighbourhood the formula applies and is continuous by
`continuousOn_formula`; off the chart source, `symm_image_subset_source` puts the point outside the
*closed* image, giving an open neighbourhood on which the map is the identity. -/
theorem continuous_localMap_uncurry (D : ColDatum n M) (hctr : (D.center) 0 = 0) :
    Continuous fun p : M × ℝ => D.localMap hctr p.2 p.1 := by
  classical
  rw [continuous_iff_continuousAt]
  rintro ⟨x₀, t₀⟩
  by_cases hx : x₀ ∈ D.chart.source
  · have hmem : D.chart.source ×ˢ (univ : Set ℝ) ∈ 𝓝 (x₀, t₀) :=
      (D.chart.open_source.prod isOpen_univ).mem_nhds ⟨hx, trivial⟩
    have heq : (fun p : M × ℝ =>
          D.chart.symm (colH D.lamTH D.lamTH_nonneg (D.chart p.1, p.2)))
        =ᶠ[𝓝 (x₀, t₀)] (fun p : M × ℝ => D.localMap hctr p.2 p.1) := by
      filter_upwards [hmem] with p hp
      exact (D.localMap_eq_formula hctr hp.1 p.2).symm
    exact (D.continuousOn_formula hctr).continuousAt hmem |>.congr heq
  · have hnotmem : x₀ ∉ D.chart.symm '' {y : (EuclideanHalfSpace (n + 1)) | dist y.1 D.center ≤ D.R} :=
      fun h => hx (D.symm_image_subset_source h)
    have hopen : IsOpen (D.chart.symm '' {y : (EuclideanHalfSpace (n + 1)) | dist y.1 D.center ≤ D.R})ᶜ :=
      D.isCompact_symm_image.isClosed.isOpen_compl
    have hmem : ((D.chart.symm '' {y : (EuclideanHalfSpace (n + 1)) | dist y.1 D.center ≤ D.R})ᶜ ×ˢ (univ : Set ℝ))
        ∈ 𝓝 (x₀, t₀) := (hopen.prod isOpen_univ).mem_nhds ⟨hnotmem, trivial⟩
    have heq : (fun p : M × ℝ => D.localMap hctr p.2 p.1) =ᶠ[𝓝 (x₀, t₀)] Prod.fst := by
      filter_upwards [hmem] with p hp
      exact D.localMap_eq_self_of_not_mem_symm_image hctr hp.1 p.2
    exact continuous_fst.continuousAt.congr heq.symm

/-- **The model collapse fixes points whose chart image lies on the boundary hyperplane, at every
time** (so it fixes `∂M` pointwise, at every time of the homotopy). -/
theorem chart_formula_eq_self_of_mem_boundary (D : ColDatum n M) {x : M} (hsrc : x ∈ D.chart.source)
    (hxb : x ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M) (t : ℝ) :
    D.chart.symm (colH D.lamTH D.lamTH_nonneg (D.chart x, t)) = x := by
  have hcoord : (D.chart x).1 0 = 0 := by
    have hnot : ¬ (0 < (D.chart x).1 0) := fun h =>
      ((isInteriorPoint_iff_not_mem_boundary x).mp
        ((isInteriorPoint_iff_chart_coord (M := M) D.chart_mem_atlas hsrc).mpr h)) hxb
    linarith [not_lt.mp hnot, (D.chart x).2]
  rw [colH_eq_self_of_coord_zero D.lamTH D.lamTH_nonneg hcoord, D.chart.left_inv hsrc]

/-- **The piece fixes `∂M` at every time.** -/
theorem localMap_eq_self_of_mem_boundary (D : ColDatum n M) (hctr : (D.center) 0 = 0) {x : M}
    (hxb : x ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M) (t : ℝ) :
    D.localMap hctr t x = x := by
  by_cases hsrc : x ∈ D.chart.source
  · rw [D.localMap_eq_formula hctr hsrc t]
    exact D.chart_formula_eq_self_of_mem_boundary hsrc hxb t
  · rw [localMap, dif_neg (fun hreg => hsrc (mem_region.mp hreg).1)]

/-- **The piece preserves `∂M` at every time.**  Immediate from the fact that it *fixes* `∂M`
pointwise at every time (`localMap_eq_self_of_mem_boundary`). -/
theorem localMap_mem_boundary_of_mem_boundary (D : ColDatum n M) (hctr : (D.center) 0 = 0) {x : M}
    (hxb : x ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M) (t : ℝ) :
    D.localMap hctr t x ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M := by
  rw [D.localMap_eq_self_of_mem_boundary hctr hxb t]
  exact hxb

/-- **The piece collapses its core onto `∂M` at time `1`**: for `x ∈ D.core` the interpolation
function vanishes at time `1` (`lam_eq_zero_of_mem_core` with `colT 1 = 1`), so the chart image of the
formula has first coordinate `0`, and the chart criterion puts it in `∂M`. -/
theorem localMap_mem_boundary_of_mem_core (D : ColDatum n M) (hctr : (D.center) 0 = 0) {x : M}
    (hx : x ∈ D.core) :
    D.localMap hctr 1 x ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M := by
  obtain ⟨hsrc, hdist⟩ := mem_core.mp hx
  have h1 : D.lamTH (D.chart x, 1) = 0 := by
    rw [lamTH, lamT, colT_one, D.lam_eq_zero_of_mem_core hx]
    ring
  have hcoord : (colH D.lamTH D.lamTH_nonneg (D.chart x, 1)).1 0 = 0 := by
    rw [colH_coord_zero, h1, zero_mul]
  have htarget : colH D.lamTH D.lamTH_nonneg (D.chart x, 1) ∈ D.chart.target := by
    refine D.closedBall_subset _ ?_
    have h := dist_colE_le D.lamT_nonneg D.lamT_le_one hctr ((D.chart x : (EuclideanHalfSpace (n + 1))).1, (1 : ℝ))
      (D.chart x).2
    rw [show (colH D.lamTH D.lamTH_nonneg (D.chart x, 1)).1
        = colE D.lamT ((D.chart x : (EuclideanHalfSpace (n + 1))).1, (1 : ℝ)) from rfl]
    exact le_trans (le_trans h hdist) (le_of_lt D.hrR)
  have hsrc' : D.chart.symm (colH D.lamTH D.lamTH_nonneg (D.chart x, 1)) ∈ D.chart.source :=
    D.chart.map_target htarget
  rw [D.localMap_eq_formula hctr hsrc 1]
  by_contra hnb
  have hInt : (modelWithCornersEuclideanHalfSpace (n + 1)).IsInteriorPoint
      (D.chart.symm (colH D.lamTH D.lamTH_nonneg (D.chart x, 1))) :=
    (isInteriorPoint_iff_not_mem_boundary _).mpr hnb
  have hlt : 0 < (D.chart (D.chart.symm (colH D.lamTH D.lamTH_nonneg (D.chart x, 1)))).1 0 :=
    (isInteriorPoint_iff_chart_coord (M := M) D.chart_mem_atlas hsrc').mp hInt
  rw [D.chart.right_inv htarget, hcoord] at hlt
  exact lt_irrefl 0 hlt

/-- **The specification of the piece's local map** — the full `colDatumLocalMap` statement, with the
witness `Ψ p := D.localMap hctr p.2 p.1`: continuous, the identity at time `0`, fixing and preserving
`∂M` at every time, collapsing the core into `∂M` at time `1`, and the identity off the region. -/
theorem localMap_spec (D : ColDatum n M) (hctr : (D.center) 0 = 0) :
    ∃ Ψ : M × ℝ → M, Continuous Ψ ∧ (∀ x : M, Ψ (x, 0) = x) ∧
      (∀ x : M, x ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M →
        ∀ t : ℝ, Ψ (x, t) = x) ∧
      (∀ x : M, x ∈ D.core →
        Ψ (x, 1) ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M) ∧
      (∀ x : M, ¬ (x ∈ D.chart.source ∧ dist (D.chart x).1 D.center < D.R) →
        ∀ t : ℝ, Ψ (x, t) = x) :=
  ⟨fun p : M × ℝ => D.localMap hctr p.2 p.1, D.continuous_localMap_uncurry hctr,
   fun x => D.localMap_zero hctr x,
   fun x hxb t => D.localMap_eq_self_of_mem_boundary hctr hxb t,
   fun x hx => D.localMap_mem_boundary_of_mem_core hctr hx,
   fun x hx t => D.localMap_eq_self_of_not_mem_region hctr hx t⟩

/-- **The piece datum at a point** `x`: the chart at `x`, centre the image of `x`, and a core radius
half of an outer radius that keeps the closed ambient ball inside the chart target (via
`exists_closedBall_subset_target_gen`). -/
def ofPoint (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] (x : M) :
    ColDatum n M :=
  let e := chartAt (EuclideanHalfSpace (n + 1)) x
  let w := exists_closedBall_subset_target_gen (e := e) (mem_chart_target (EuclideanHalfSpace (n + 1)) x)
  { chart := e
    chart_mem_atlas := ChartedSpace.chart_mem_atlas x
    center := (e x).1
    r := Classical.choose w / 2
    R := Classical.choose w
    hr_pos := by linarith [(Classical.choose_spec w).1]
    hrR := by linarith [(Classical.choose_spec w).1]
    closedBall_subset := fun y hy => (Classical.choose_spec w).2 y hy }

theorem ofPoint_chart (x : M) : (ofPoint n M x).chart = chartAt (EuclideanHalfSpace (n + 1)) x := rfl

theorem ofPoint_center (x : M) : (ofPoint n M x).center = ((chartAt (EuclideanHalfSpace (n + 1)) x) x).1 := rfl

/-- The centre of the datum at a **boundary** point lies on the boundary hyperplane of its chart —
so the datum satisfies `hctr`, which is what `localMap_spec` needs. -/
theorem ofPoint_center_zero (x : M)
    (hxb : x ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M) :
    (ofPoint n M x).center 0 = 0 := by
  rw [ofPoint_center]
  have hnot : ¬ (0 < ((chartAt (EuclideanHalfSpace (n + 1)) x) x).1 0) := fun h =>
    ((isInteriorPoint_iff_not_mem_boundary x).mp
      ((isInteriorPoint_iff_chart_coord (M := M) (ChartedSpace.chart_mem_atlas x)
        (mem_chart_source (EuclideanHalfSpace (n + 1)) x)).mpr h)) hxb
  linarith [not_lt.mp hnot, ((chartAt (EuclideanHalfSpace (n + 1)) x) x).2]

/-- **Every boundary point lies in the core of its own piece datum** — the ingredient of the finite
cover of `∂M` by cores. -/
theorem ofPoint_mem_core (x : M)
    (hxb : x ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M) :
    x ∈ (ofPoint n M x).core := by
  refine mem_core.mpr ⟨?_, ?_⟩
  · rw [ofPoint_chart]
    exact mem_chart_source (EuclideanHalfSpace (n + 1)) x
  · rw [ofPoint_chart, ofPoint_center, dist_self]
    show (0 : ℝ) ≤ (Classical.choose (exists_closedBall_subset_target_gen
      (e := chartAt (EuclideanHalfSpace (n + 1)) x) (mem_chart_target (EuclideanHalfSpace (n + 1)) x))) / 2
    have h := (Classical.choose_spec (exists_closedBall_subset_target_gen
      (e := chartAt (EuclideanHalfSpace (n + 1)) x) (mem_chart_target (EuclideanHalfSpace (n + 1)) x))).1
    linarith

/-- **Every boundary point lies in the *interior* of the core of its own datum** — the form needed by
`IsCompact.elim_finite_subcover`, which requires the covering family to be open.  The open set is the
shrunken region `{dist (chart y) center < r/2} ∩ chart.source`, which sits inside the core. -/
theorem ofPoint_mem_interior_core (x : M)
    (hxb : x ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M) :
    x ∈ interior (ofPoint n M x).core := by
  have hAopen : IsOpen ((ofPoint n M x).chart.source ∩
      {y : M | dist ((ofPoint n M x).chart y).1 (ofPoint n M x).center < (ofPoint n M x).r / 2}) := by
    have h : IsOpen {y : (EuclideanHalfSpace (n + 1)) | dist y.1 (ofPoint n M x).center < (ofPoint n M x).r / 2} :=
      Metric.isOpen_ball.preimage continuous_subtype_val
    have h2 := (ofPoint n M x).chart.isOpen_inter_preimage h
    simpa only [Set.preimage_setOf_eq, Set.mem_setOf_eq] using h2
  have hA : x ∈ (ofPoint n M x).chart.source ∩
      {y : M | dist ((ofPoint n M x).chart y).1 (ofPoint n M x).center < (ofPoint n M x).r / 2} := by
    refine ⟨?_, ?_⟩
    · rw [ofPoint_chart]
      exact mem_chart_source (EuclideanHalfSpace (n + 1)) x
    · rw [ofPoint_chart, ofPoint_center]
      have hd : dist ((chartAt (EuclideanHalfSpace (n + 1)) x) x).1 ((chartAt (EuclideanHalfSpace (n + 1)) x) x).1 < (ofPoint n M x).r / 2 := by
        rw [dist_self]
        linarith [(ofPoint n M x).hr_pos]
      exact hd
  have hsub : (ofPoint n M x).chart.source ∩
      {y : M | dist ((ofPoint n M x).chart y).1 (ofPoint n M x).center < (ofPoint n M x).r / 2}
      ⊆ (ofPoint n M x).core := by
    rintro y ⟨hys, hyd⟩
    exact mem_core.mpr ⟨hys, le_of_lt (lt_of_lt_of_le hyd (by linarith [(ofPoint n M x).hr_pos]))⟩
  exact interior_maximal hsub hAopen hA

/-- **Finitely many piece cores cover `∂M`** (taken as *interiors*, so that
`IsCompact.elim_finite_subcover` — which requires an open family — applies). -/
theorem exists_finset_core_cover :
    ∃ S : Finset M, ∀ x : M,
      x ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M →
        x ∈ ⋃ y ∈ S, interior (ofPoint n M y).core := by
  classical
  have hbdry_closed : IsClosed ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary M) :=
    (modelWithCornersEuclideanHalfSpace (n + 1)).isClosed_boundary (n := (1 : WithTop ℕ∞))
      (by norm_num)
  have hbdry_compact : IsCompact ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary M) :=
    hbdry_closed.isCompact
  obtain ⟨S, hS⟩ := hbdry_compact.elim_finite_subcover
    (fun x : M => interior (ofPoint n M x).core)
    (fun _ => isOpen_interior)
    (fun x hx => Set.mem_iUnion.mpr ⟨x, ofPoint_mem_interior_core x hx⟩)
  exact ⟨S, fun x hx => hS hx⟩

/-- **The complement `K` of the finitely many *interiors* of the cores**: it is closed (the union of
closed sets' interiors is open) hence compact, and it lies in `int M` — because `∂M` is covered by
those interiors, so `K ∩ ∂M = ∅`. -/
theorem isCompact_compl_iUnion_interior_core (S : Finset M)
    (hS : ∀ x : M, x ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M →
      x ∈ ⋃ y ∈ S, interior (ofPoint n M y).core) :
    IsCompact ((⋃ y ∈ S, interior (ofPoint n M y).core)ᶜ) ∧
      ((⋃ y ∈ S, interior (ofPoint n M y).core)ᶜ) ⊆
        {x : M | x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M} := by
  refine ⟨?_, ?_⟩
  · exact (isClosed_compl_iff.mpr (isOpen_biUnion fun _ _ => isOpen_interior)).isCompact
  · intro x hx hxb
    exact hx (hS x hxb)

end ColDatum


/-! ## The iterated collapse of a finite list of chart pieces -/

variable {M : Type} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 M] [CompactSpace M]

/-- The *piece datum* at a boundary point: the chart-wise collapse piece centred at the point,
whose centre lies on the boundary hyperplane of its chart. -/
def bdryDatum (y : {x : M // x ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M}) :
    ColDatum n M :=
  ColDatum.ofPoint n M y.1

theorem bdryDatum_center_zero
    (y : {x : M // x ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M}) :
    (bdryDatum y).center 0 = 0 :=
  ColDatum.ofPoint_center_zero y.1 y.2

/-- The map of the collapse piece at the boundary point `y`, at time `t`. -/
def bdryMap (y : {x : M // x ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M}) (t : ℝ)
    (x : M) : M :=
  (bdryDatum y).localMap (bdryDatum_center_zero y) t x

theorem continuous_bdryMap
    (y : {x : M // x ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M}) :
    Continuous fun p : M × ℝ => bdryMap y p.2 p.1 :=
  (bdryDatum y).continuous_localMap_uncurry (bdryDatum_center_zero y)

/-- The piece at a boundary point is continuous at time `1`. -/
theorem continuous_bdryMap_one
    (y : {x : M // x ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M}) :
    Continuous (fun x : M => bdryMap y 1 x) :=
  (continuous_bdryMap y).comp
    (continuous_id.prodMk (continuous_const : Continuous fun _ : M => (1 : ℝ)))

theorem bdryMap_zero
    (y : {x : M // x ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M}) (x : M) :
    bdryMap y 0 x = x :=
  (bdryDatum y).localMap_zero (bdryDatum_center_zero y) x

theorem bdryMap_eq_self_of_mem_boundary
    (y : {x : M // x ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M}) {x : M}
    (hxb : x ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M) (t : ℝ) :
    bdryMap y t x = x :=
  (bdryDatum y).localMap_eq_self_of_mem_boundary (bdryDatum_center_zero y) hxb t

/-- **A piece collapses its core onto the boundary** at time `1`. -/
theorem bdryMap_mem_boundary_of_mem_core
    (y : {x : M // x ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M}) {x : M}
    (hx : x ∈ (bdryDatum y).core) :
    bdryMap y 1 x ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M :=
  (bdryDatum y).localMap_mem_boundary_of_mem_core (bdryDatum_center_zero y) hx

/-- **The iterated collapse map** of a list of pieces: `colComp [y₁,…,yₙ] (x,t)` applies the piece
at `y₁` first and the piece at `yₙ` last, all at time `t`. -/
def colComp :
    List {x : M // x ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M} → M × ℝ → M
  | [] => fun p => p.1
  | y :: L => fun p => colComp L (bdryMap y p.2 p.1, p.2)

/-- **The collapsed set** of a list of pieces: the points which, at some stage of the iteration, are
in the interior of the core of the piece applied at that stage.  The collapse `colComp L (·,1)` maps
this set into `∂M`; its complement is the compact `K` of the boundary collapse datum. -/
def colGood :
    List {x : M // x ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M} → Set M
  | [] => ∅
  | y :: L => interior (bdryDatum y).core ∪ bdryMap y 1 ⁻¹' (colGood L)

theorem continuous_colComp
    (L : List {x : M // x ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M}) :
    Continuous (colComp L) := by
  induction L with
  | nil => exact continuous_fst
  | cons y L ih =>
    exact ih.comp ((continuous_bdryMap y).prodMk continuous_snd)

theorem colComp_zero
    (L : List {x : M // x ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M}) :
    ∀ x : M, colComp L (x, 0) = x := by
  induction L with
  | nil => intro x; rfl
  | cons y L ih =>
    intro x
    show colComp L (bdryMap y 0 x, 0) = x
    rw [bdryMap_zero y x, ih x]

/-- **The iterated collapse fixes `∂M` pointwise at every time.** -/
theorem colComp_eq_self_of_mem_boundary
    (L : List {x : M // x ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M}) :
    ∀ x : M, x ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M →
      ∀ t : ℝ, colComp L (x, t) = x := by
  induction L with
  | nil => intro x _ t; rfl
  | cons y L ih =>
    intro x hxb t
    show colComp L (bdryMap y t x, t) = x
    rw [bdryMap_eq_self_of_mem_boundary y hxb t, ih x hxb t]

theorem isOpen_colGood
    (L : List {x : M // x ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M}) :
    IsOpen (colGood L) := by
  induction L with
  | nil => exact isOpen_empty
  | cons y L ih =>
    exact isOpen_interior.union (ih.preimage (continuous_bdryMap_one y))

/-- **The key property of the iterated collapse**: at time `1` it maps the collapsed set into the
boundary. -/
theorem colComp_mem_boundary_of_mem_colGood
    (L : List {x : M // x ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M}) :
    ∀ x : M, x ∈ colGood L →
      colComp L (x, 1) ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M := by
  induction L with
  | nil => intro x hx; exact absurd hx (by simp [colGood])
  | cons y L ih =>
    intro x hx
    rcases hx with hx | hx
    · have hcore : x ∈ (bdryDatum y).core := interior_subset hx
      have hb : bdryMap y 1 x ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M :=
        bdryMap_mem_boundary_of_mem_core y hcore
      show colComp L (bdryMap y 1 x, 1) ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M
      rw [colComp_eq_self_of_mem_boundary L (bdryMap y 1 x) hb 1]
      exact hb
    · exact ih (bdryMap y 1 x) hx

/-- **Every boundary point inside the union of the cores is collapsed**: the iterated collapse
sends the boundary points which lie in the interior of a core of one of its pieces into `∂M`. -/
theorem mem_colGood_of_mem_boundary_core
    (L : List {x : M // x ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M}) :
    ∀ x : M, x ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M →
      (∃ y ∈ L, x ∈ interior (bdryDatum y).core) → x ∈ colGood L := by
  induction L with
  | nil => intro x _ hx; exact absurd hx (by simp)
  | cons a L ih =>
    intro x hxb hx
    rcases hx with ⟨z, hz, hxz⟩
    rcases List.mem_cons.mp hz with hza | hzL
    · rw [hza] at hxz
      exact Or.inl hxz
    · refine Or.inr ?_
      show bdryMap a 1 x ∈ colGood L
      rw [bdryMap_eq_self_of_mem_boundary a hxb 1]
      exact ih x hxb ⟨z, hzL, hxz⟩

end Gen

/-- **The boundary collapse datum in every dimension.** -/
theorem exists_boundaryCollapse_gen {n : ℕ} (W : TopCat.{0}) [CompactSpace W] [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 W]
    (hB : ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W).Nonempty) :
    ∃ (K : Set W) (hKc : IsCompact K)
      (hKint : K ⊆ {x : W | x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W})
      (ψ : ContinuousMap W W),
      (∀ x : W, x ∉ K → ψ x ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) ∧
      (∀ x : W, x ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W → ψ x = x) ∧
      (∃ H : (ContinuousMap.id W).Homotopy ψ,
        ∀ (t : unitInterval) (x : W),
          x ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W →
            H.toContinuousMap (t, x) ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) := by
  classical
  have hbdry_closed : IsClosed ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) :=
    (modelWithCornersEuclideanHalfSpace (n + 1)).isClosed_boundary (n := (1 : WithTop ℕ∞))
      (by norm_num)
  obtain ⟨S, hS⟩ := hbdry_closed.isCompact.elim_finite_subcover
    (fun y : {x : W // x ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W} =>
      interior (bdryDatum y).core)
    (fun _ => isOpen_interior)
    (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, ColDatum.ofPoint_mem_interior_core x hx⟩)
  let L : List {x : W // x ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W} := S.toList
  have hL : ∀ x : W, x ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W →
      ∃ y ∈ L, x ∈ interior (bdryDatum y).core := by
    intro x hx
    have h := hS hx
    rw [Set.mem_iUnion] at h
    obtain ⟨y, h⟩ := h
    rw [Set.mem_iUnion] at h
    obtain ⟨hy, hxy⟩ := h
    exact ⟨y, by simpa [L] using hy, hxy⟩
  have hgood : ∀ x : W, x ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W →
      x ∈ colGood L :=
    fun x hx => mem_colGood_of_mem_boundary_core L x hx (hL x hx)
  refine ⟨(colGood L)ᶜ, (isOpen_colGood L).isClosed_compl.isCompact, ?_,
    ⟨fun x => colComp L (x, 1),
      (continuous_colComp L).comp (continuous_id.prodMk continuous_const)⟩, ?_, ?_, ?_, ?_⟩
  · intro x hx hxb
    exact hx (hgood x hxb)
  · intro x hx
    exact colComp_mem_boundary_of_mem_colGood L x (by simpa using hx)
  · intro x hxb
    exact colComp_eq_self_of_mem_boundary L x hxb 1
  · exact ContinuousMap.Homotopy.mk
      ⟨fun q : unitInterval × W => colComp L (q.2, (q.1 : ℝ)),
        (continuous_colComp L).comp (Continuous.prodMk continuous_snd
          (continuous_subtype_val.comp continuous_fst))⟩
      (fun x => colComp_zero L x) (fun x => rfl)
  · intro t x hxb
    show colComp L (x, (t : ℝ)) ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W
    rw [colComp_eq_self_of_mem_boundary L x hxb (t : ℝ)]
    exact hxb

end

end Work.PTGeometric

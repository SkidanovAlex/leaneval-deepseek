import Mathlib
import Submission.Work.ThomBordism.RelDuality.interiorPushDefs
import Submission.Work.ThomBordism.RelDuality.interiorHomology

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The model collapse map `σ_λ` and its chart piece

This file starts the chart-wise construction of a `BoundaryCollapse` (the alternative to the collar
neighbourhood theorem `Work.Surgery.HasCollar`).  The local piece is the *model scaling map*

`σ_λ (y, t) = y + ((λ (y,t) - 1) * y 0) • e₀`,

i.e. "replace the first coordinate `y 0` by `λ (y,t) * y 0`, keep the other coordinates".  Compared
with the inward push `pushE`/`pushH` of `interiorPushDefs` it has the two properties the collapse
needs and the push does not have:

* it **fixes the boundary hyperplane** `{y | y 0 = 0}` pointwise (`colE_eq_self_of_zero`), hence
  fixes `∂M` and preserves it (`isInteriorPoint_iff_chart_coord`);
* for `λ = 0` it **lands in** the boundary hyperplane (`colE_zero_of_lam_zero`), whereas the push
  always moves strictly into the interior.

With `0 ≤ λ ≤ 1` it preserves the half-space, it is continuous in `(y,t)` whenever `λ` is, and it is
the identity where `λ = 1` — which is what makes the pieces glue along their frontiers.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped Topology Manifold
open Function Set Classical

namespace Work.ThomBordism.RelDuality

noncomputable section

/-! ## The model scaling map -/

/-- **The model collapse map** (time-dependent form): replace the first coordinate of `p.1` by
`λ p * (p.1) 0`, leaving all other coordinates unchanged. -/
def colE (lam : E9 × ℝ → ℝ) (p : E9 × ℝ) : E9 :=
  p.1 + ((lam p - 1) * (p.1 : E9) 0) • nrm

/-- The first coordinate of `σ_λ` is `λ` times the first coordinate of the point. -/
theorem colE_apply_zero (lam : E9 × ℝ → ℝ) (p : E9 × ℝ) :
    colE lam p 0 = lam p * (p.1 : E9) 0 := by
  have h : colE lam p 0 = (p.1 : E9) 0 + ((lam p - 1) * (p.1 : E9) 0) * nrm 0 := by
    simp [colE]
  rw [h, nrm_apply_zero]
  ring

/-- The other coordinates of `σ_λ` are unchanged. -/
theorem colE_apply_ne (lam : E9 × ℝ → ℝ) (p : E9 × ℝ) {k : Fin 9} (hk : k ≠ 0) :
    colE lam p k = (p.1 : E9) k := by
  simp [colE, nrm_apply_ne hk]

/-- `σ_λ` is continuous whenever `λ` is. -/
theorem continuous_colE {lam : E9 × ℝ → ℝ} (h : Continuous lam) : Continuous (colE lam) := by
  have h2 : Continuous fun p : E9 × ℝ => ((p.1 : E9) 0) :=
    (PiLp.continuous_apply (p := 2) (i := (0 : Fin 9)) (β := fun _ : Fin 9 => ℝ)).comp
      continuous_fst
  have h3 : Continuous fun p : E9 × ℝ => (lam p - 1) * (p.1 : E9) 0 :=
    (h.sub continuous_const).mul h2
  exact continuous_fst.add (h3.smul continuous_const)

/-- `σ_λ` fixes the boundary hyperplane `{y | y 0 = 0}`. -/
theorem colE_eq_self_of_zero (lam : E9 × ℝ → ℝ) {p : E9 × ℝ} (h : (p.1 : E9) 0 = 0) :
    colE lam p = (p.1 : E9) := by
  have hz : (lam p - 1) * (p.1 : E9) 0 = 0 := by rw [h, mul_zero]
  simp [colE, hz]

/-- `σ_λ` is the identity where `λ = 1`. -/
theorem colE_eq_self_of_lam_eq_one (lam : E9 × ℝ → ℝ) {p : E9 × ℝ} (h : lam p = 1) :
    colE lam p = (p.1 : E9) := by
  have hz : (lam p - 1) * (p.1 : E9) 0 = 0 := by rw [h, sub_self, zero_mul]
  simp [colE, hz]

/-- For `λ = 0` the image lies in the boundary hyperplane. -/
theorem colE_zero_of_lam_eq_zero (lam : E9 × ℝ → ℝ) {p : E9 × ℝ} (h : lam p = 0) :
    colE lam p 0 = 0 := by
  rw [colE_apply_zero, h, zero_mul]

/-- `σ_λ` is the identity at `λ = 0` on the boundary hyperplane. -/
theorem colE_comm (lam : E9 × ℝ → ℝ) (p : E9 × ℝ) :
    colE lam p = (p.1 : E9) + ((lam p - 1) * (p.1 : E9) 0) • nrm := rfl

/-! ## The half-space version -/

/-- **The model collapse map of the half-space**: `σ_λ` preserves `H = {y | 0 ≤ y 0}` for
`0 ≤ λ`. -/
def colH (lam : H9 × ℝ → ℝ) (h0 : ∀ p : H9 × ℝ, 0 ≤ lam p) (p : H9 × ℝ) : H9 :=
  ⟨(p.1 : H9).1 + ((lam p - 1) * ((p.1 : H9).1 0)) • nrm, by
    have h : (((p.1 : H9).1 + ((lam p - 1) * ((p.1 : H9).1 0)) • nrm : E9)) 0
        = (p.1 : H9).1 0 + ((lam p - 1) * ((p.1 : H9).1 0)) * nrm 0 := by simp
    rw [h, nrm_apply_zero, mul_one]
    have : (p.1 : H9).1 0 + (lam p - 1) * (p.1 : H9).1 0 = lam p * (p.1 : H9).1 0 := by ring
    rw [this]
    exact mul_nonneg (h0 p) (p.1 : H9).2⟩

@[simp] theorem colH_coe (lam : H9 × ℝ → ℝ) (h0 : ∀ p : H9 × ℝ, 0 ≤ lam p) (p : H9 × ℝ) :
    (colH lam h0 p).1
      = (p.1 : H9).1 + ((lam p - 1) * ((p.1 : H9).1 0)) • nrm := rfl

/-- The first coordinate of the half-space collapse. -/
theorem colH_coord_zero (lam : H9 × ℝ → ℝ) (h0 : ∀ p : H9 × ℝ, 0 ≤ lam p) (p : H9 × ℝ) :
    (colH lam h0 p).1 0 = lam p * (p.1 : H9).1 0 := by
  rw [colH_coe]
  have h : (((p.1 : H9).1 + ((lam p - 1) * ((p.1 : H9).1 0)) • nrm : E9)) 0
      = (p.1 : H9).1 0 + ((lam p - 1) * ((p.1 : H9).1 0)) * nrm 0 := by simp
  rw [h, nrm_apply_zero]
  ring

/-- The half-space collapse fixes the boundary hyperplane pointwise. -/
theorem colH_eq_self_of_coord_zero (lam : H9 × ℝ → ℝ) (h0 : ∀ p : H9 × ℝ, 0 ≤ lam p)
    {p : H9 × ℝ} (h : (p.1 : H9).1 0 = 0) : colH lam h0 p = p.1 := by
  apply Subtype.ext
  rw [colH_coe]
  have hz : (lam p - 1) * ((p.1 : H9).1 0) = 0 := by rw [h, mul_zero]
  simp [hz]

/-- Where `λ = 0`, the half-space collapse lands on the boundary hyperplane. -/
theorem colH_coord_zero_of_lam_eq_zero (lam : H9 × ℝ → ℝ) (h0 : ∀ p : H9 × ℝ, 0 ≤ lam p)
    {p : H9 × ℝ} (h : lam p = 0) : (colH lam h0 p).1 0 = 0 := by
  rw [colH_coord_zero, h, zero_mul]

/-- The half-space collapse is the identity where `λ = 1`. -/
theorem colH_eq_self_of_lam_eq_one (lam : H9 × ℝ → ℝ) (h0 : ∀ p : H9 × ℝ, 0 ≤ lam p)
    {p : H9 × ℝ} (h : lam p = 1) : colH lam h0 p = p.1 := by
  apply Subtype.ext
  rw [colH_coe]
  have hz : (lam p - 1) * ((p.1 : H9).1 0) = 0 := by rw [h, sub_self, zero_mul]
  simp [hz]

/-- The half-space collapse is jointly continuous. -/
theorem continuous_colH (lam : H9 × ℝ → ℝ) (h : Continuous lam)
    (h0 : ∀ p : H9 × ℝ, 0 ≤ lam p) : Continuous (colH lam h0) := by
  have hcoord : Continuous fun p : H9 × ℝ => (p.1 : H9).1 0 :=
    (PiLp.continuous_apply (p := 2) (i := (0 : Fin 9)) (β := fun _ : Fin 9 => ℝ)).comp
      ((continuous_subtype_val : Continuous (Subtype.val : H9 → E9)).comp continuous_fst)
  have hterm : Continuous fun p : H9 × ℝ => ((lam p - 1) * (p.1 : H9).1 0) • nrm :=
    ((h.sub continuous_const).mul hcoord).smul continuous_const
  have hbase : Continuous fun p : H9 × ℝ => (p.1 : H9).1 :=
    (continuous_subtype_val : Continuous (Subtype.val : H9 → E9)).comp continuous_fst
  exact Continuous.subtype_mk (hbase.add hterm) _

/-! ## The chart piece on a manifold with boundary -/

section Chart

variable {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanHalfSpace 9) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace 9) 1 M] [CompactSpace M]

/-- **The chart piece fixes the boundary.**  If `x` is in the source of the atlas chart `e` and on
`∂M`, then `e ⁻¹ (σ_λ (e x)) = x`: in the chart `x` has vanishing first coordinate, where `σ_λ` is
the identity. -/
theorem chartPiece_eq_self_of_boundary {e : OpenPartialHomeomorph M H9} (he : e ∈ atlas H9 M)
    {lam : H9 × ℝ → ℝ} (h0 : ∀ p : H9 × ℝ, 0 ≤ lam p)
    {x : M} (hx : x ∈ e.source)
    (hxb : x ∈ (modelWithCornersEuclideanHalfSpace 9).boundary M) :
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
theorem chartPiece_mem_boundary_of_lam_eq_zero {e : OpenPartialHomeomorph M H9}
    (he : e ∈ atlas H9 M) {lam : H9 × ℝ → ℝ} (h0 : ∀ p : H9 × ℝ, 0 ≤ lam p)
    (ht : ∀ y ∈ e.target, colH lam h0 (y, 1) ∈ e.target)
    {x : M} (hx : x ∈ e.source) (hlam : lam (e x, 1) = 0) :
    e.symm (colH lam h0 (e x, 1)) ∈ (modelWithCornersEuclideanHalfSpace 9).boundary M := by
  have htarget : colH lam h0 (e x, 1) ∈ e.target := ht (e x) (e.map_source hx)
  have hsrc : e.symm (colH lam h0 (e x, 1)) ∈ e.source := e.map_target htarget
  have hni : ¬ (modelWithCornersEuclideanHalfSpace 9).IsInteriorPoint
      (e.symm (colH lam h0 (e x, 1))) := by
    intro hInt
    have hlt : 0 < (e (e.symm (colH lam h0 (e x, 1)))).1 0 :=
      (isInteriorPoint_iff_chart_coord (M := M) he hsrc).mp hInt
    rw [e.right_inv htarget, colH_coord_zero lam h0 (e x, 1), hlam, zero_mul] at hlt
    exact lt_irrefl 0 hlt
  exact of_not_not ((isInteriorPoint_iff_not_mem_boundary _).not.mp hni)

end Chart

/-! ## The interpolation function `λ` of a collapse piece

Each collapse piece carries a `λ : H9 × ℝ → ℝ` which is `0` on its core, `1` near its frontier, and
takes values in `[0,1]`.  In the ambient chart coordinates such a `λ` is produced by the model bump
below, attached to an *ambient* ball (`PushDatum.region` is defined by the ambient distance
`dist (chart x).1 center < radius`, so the ambient ball is the right carrier). -/

/-- **The model bump of a collapse piece**: `0` on the closed ball of radius `r` about `c`, `1`
outside the ball of radius `R`, and continuous in between (`0 < r < R`). -/
def colLam (c : E9) (r R : ℝ) (y : E9) : ℝ :=
  max 0 (min 1 ((dist y c - r) / (R - r)))

theorem continuous_colLam (c : E9) (r R : ℝ) : Continuous (colLam c r R) := by
  unfold colLam
  fun_prop

theorem colLam_nonneg (c : E9) (r R : ℝ) (y : E9) : 0 ≤ colLam c r R y :=
  le_max_left _ _

theorem colLam_le_one (c : E9) (r R : ℝ) (y : E9) : colLam c r R y ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

/-- The bump vanishes on the inner ball (the core of the piece). -/
theorem colLam_eq_zero {c : E9} {r R : ℝ} (hr : r < R) {y : E9} (h : dist y c ≤ r) :
    colLam c r R y = 0 := by
  have hR : 0 < R - r := by linarith
  have hq : (dist y c - r) / (R - r) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt hR)
  rw [colLam, max_eq_left (le_trans (min_le_right _ _) hq)]

/-- The bump equals one outside the outer ball (so the piece is the identity past its frontier). -/
theorem colLam_eq_one {c : E9} {r R : ℝ} (hr : r < R) {y : E9} (h : R ≤ dist y c) :
    colLam c r R y = 1 := by
  have hR : 0 < R - r := by linarith
  have h1 : 1 ≤ (dist y c - r) / (R - r) := by
    rw [le_div_iff₀ hR]
    linarith
  rw [colLam, min_eq_left h1, max_eq_right zero_le_one]

/-! ## The datum of a collapse piece -/

/-- **The datum of one collapse piece**: an atlas chart, an ambient centre, a *core* radius `r` and
an *outer* radius `R > r` whose closed ambient ball lies in the chart target.  Everything is stated
in *ambient* chart coordinates (as for `PushDatum`), so no metric instance on `H9` is ever needed.

The piece acts on `region` (its chart source intersected with the open `R`-ball), is the identity
outside it, sends `core` (the closed `r`-ball part) onto the boundary, and interpolates in between. -/
structure ColDatum (M : Type) [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 9) M] where
  /-- the chart of the piece -/
  chart : OpenPartialHomeomorph M H9
  /-- the chart is in the atlas (so `isInteriorPoint_iff_chart_coord` applies) -/
  chart_mem_atlas : chart ∈ atlas H9 M
  /-- the ambient centre of the piece -/
  center : E9
  /-- the radius of the core (where `λ = 0`) -/
  r : ℝ
  /-- the outer radius of the piece (where `λ = 1`) -/
  R : ℝ
  /-- the core radius is positive -/
  hr_pos : 0 < r
  /-- the core radius is smaller than the outer radius (the interpolation annulus is nondegenerate) -/
  hrR : r < R
  /-- the closed ambient `R`-ball lies in the chart target -/
  closedBall_subset : ∀ y : H9, dist y.1 center ≤ R → y ∈ chart.target

namespace ColDatum

variable {M : Type} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanHalfSpace 9) M]

/-- The interpolation function of the piece, in ambient coordinates. -/
def lam (D : ColDatum M) : E9 → ℝ := colLam D.center D.r D.R

/-- **The region of the piece**: the points of the chart source whose chart image lies in the open
ambient `R`-ball.  The piece is the identity outside its region. -/
def region (D : ColDatum M) : Set M :=
  D.chart.source ∩ {x : M | dist (D.chart x).1 D.center < D.R}

/-- **The core of the piece**: the points of the chart source whose chart image lies in the closed
ambient `r`-ball.  The piece collapses the core onto the boundary (`λ = 0` there). -/
def core (D : ColDatum M) : Set M :=
  D.chart.source ∩ {x : M | dist (D.chart x).1 D.center ≤ D.r}

theorem mem_region {D : ColDatum M} {x : M} :
    x ∈ D.region ↔ x ∈ D.chart.source ∧ dist (D.chart x).1 D.center < D.R := Iff.rfl

theorem mem_core {D : ColDatum M} {x : M} :
    x ∈ D.core ↔ x ∈ D.chart.source ∧ dist (D.chart x).1 D.center ≤ D.r := Iff.rfl

theorem lam_nonneg (D : ColDatum M) (y : E9) : 0 ≤ D.lam y := colLam_nonneg _ _ _ y

theorem lam_le_one (D : ColDatum M) (y : E9) : D.lam y ≤ 1 := colLam_le_one _ _ _ y

/-- On the core the interpolation function vanishes. -/
theorem lam_eq_zero_of_mem_core (D : ColDatum M) {x : M} (hx : x ∈ D.core) :
    D.lam (D.chart x).1 = 0 :=
  colLam_eq_zero D.hrR (mem_core.mp hx).2

/-- Off the region (inside the chart source) the interpolation function equals one, so the piece is
the identity there and pieces with disjoint regions glue. -/
theorem lam_eq_one_of_not_mem_region (D : ColDatum M) {x : M} (hx : x ∈ D.chart.source)
    (h : x ∉ D.region) : D.lam (D.chart x).1 = 1 :=
  colLam_eq_one D.hrR (not_lt.mp fun hlt => h (mem_region.mpr ⟨hx, hlt⟩))

/-- The region of a piece is open. -/
theorem isOpen_region (D : ColDatum M) : IsOpen D.region := by
  have h : IsOpen {y : H9 | dist y.1 D.center < D.R} :=
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

theorem dist_colE_le {lam : E9 × ℝ → ℝ} (h0 : ∀ p : E9 × ℝ, 0 ≤ lam p)
    (h1 : ∀ p : E9 × ℝ, lam p ≤ 1) {c : E9} (hc : c 0 = 0) (p : E9 × ℝ)
    (hp : 0 ≤ (p.1 : E9) 0) :
    dist (colE lam p) c ≤ dist (p.1 : E9) c := by
  have hv0 : (colE lam p - c) 0 = lam p * (p.1 : E9) 0 := by
    have h : (colE lam p - c) 0
        = (p.1 : E9) 0 + ((lam p - 1) * (p.1 : E9) 0) * nrm 0 - c 0 := by
      simp [colE]
    rw [h, nrm_apply_zero, hc]
    ring
  have hw0 : ((p.1 : E9) - c) 0 = (p.1 : E9) 0 := by
    have h : ((p.1 : E9) - c) 0 = (p.1 : E9) 0 - c 0 := by simp
    rw [h, hc, sub_zero]
  have hne : ∀ i : Fin 9, i ≠ 0 → (colE lam p - c) i = ((p.1 : E9) - c) i := by
    intro i hi
    have h : (colE lam p - c) i
        = (p.1 : E9) i + ((lam p - 1) * (p.1 : E9) 0) * nrm i - c i := by
      simp [colE]
    have h2 : ((p.1 : E9) - c) i = (p.1 : E9) i - c i := by simp
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
    have h2'' : 0 ≤ |(p.1 : E9) 0| := abs_nonneg _
    nlinarith [mul_le_mul_of_nonneg_right h1'' h2'',
      mul_nonneg (abs_nonneg (lam p)) h2'', sq_nonneg (|lam p| * |(p.1 : E9) 0|)]
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
  [ChartedSpace (EuclideanHalfSpace 9) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace 9) 1 M] [CompactSpace M]

/-- **The interpolated interpolation function of a piece**, ambient form: `1` at time `0` and
`D.lam` at time `1`.  It is defined on the *whole* `E9 × ℝ` because `D.lam = colLam center r R`
carries no half-space condition — this is what lets `dist_colE_le` (which is about `E9 × ℝ`) consume
it directly. -/
def lamT (D : ColDatum M) (p : E9 × ℝ) : ℝ :=
  (1 - colT p.2) + colT p.2 * D.lam p.1

/-- The half-space restriction of `lamT`, which is what `colH` consumes. -/
def lamTH (D : ColDatum M) (p : H9 × ℝ) : ℝ := D.lamT ((p.1 : H9).1, p.2)

theorem lamT_nonneg (D : ColDatum M) (p : E9 × ℝ) : 0 ≤ D.lamT p := by
  have h0 : 0 ≤ colT p.2 := colT_nonneg p.2
  have h1 : colT p.2 ≤ 1 := colT_le_one p.2
  have hl0 : 0 ≤ D.lam p.1 := D.lam_nonneg _
  have hl1 : D.lam p.1 ≤ 1 := D.lam_le_one _
  rw [lamT]
  nlinarith [mul_nonneg (sub_nonneg.mpr h1) hl0, mul_nonneg h0 hl0]

theorem lamT_le_one (D : ColDatum M) (p : E9 × ℝ) : D.lamT p ≤ 1 := by
  have h0 : 0 ≤ colT p.2 := colT_nonneg p.2
  have h1 : colT p.2 ≤ 1 := colT_le_one p.2
  have hl0 : 0 ≤ D.lam p.1 := D.lam_nonneg _
  have hl1 : D.lam p.1 ≤ 1 := D.lam_le_one _
  rw [lamT]
  nlinarith [mul_le_mul_of_nonneg_left hl1 h0, h0, hl0]

theorem lamTH_nonneg (D : ColDatum M) (p : H9 × ℝ) : 0 ≤ D.lamTH p :=
  D.lamT_nonneg _

/-- At time `0` the interpolated function is `1` (the identity). -/
theorem lamT_zero (D : ColDatum M) (y : E9) : D.lamT (y, 0) = 1 := by
  rw [lamT, colT_zero]
  ring

theorem lamTH_zero (D : ColDatum M) (y : H9) : D.lamTH (y, 0) = 1 :=
  lamT_zero D _

theorem continuous_lam (D : ColDatum M) : Continuous D.lam :=
  continuous_colLam D.center D.r D.R

theorem continuous_lamT (D : ColDatum M) : Continuous D.lamT := by
  unfold lamT
  have h1 : Continuous fun p : E9 × ℝ => colT p.2 := continuous_colT.comp continuous_snd
  have h2 : Continuous fun p : E9 × ℝ => D.lam p.1 := D.continuous_lam.comp continuous_fst
  exact (continuous_const.sub h1).add (h1.mul h2)

theorem continuous_lamTH (D : ColDatum M) : Continuous D.lamTH := by
  unfold lamTH
  have h1 : Continuous fun p : H9 × ℝ => colT p.2 := continuous_colT.comp continuous_snd
  have h2 : Continuous fun p : H9 × ℝ => D.lam (p.1 : H9).1 :=
    D.continuous_lam.comp
      ((continuous_subtype_val : Continuous (Subtype.val : H9 → E9)).comp continuous_fst)
  have h3 : Continuous fun p : H9 × ℝ => D.lamT ((p.1 : H9).1, p.2) := by
    unfold lamT
    have h4 : Continuous fun p : H9 × ℝ => colT p.2 := continuous_colT.comp continuous_snd
    exact (continuous_const.sub h4).add (h4.mul h2)
  exact h3

/-- **The local map of the piece at time `t`**: on the region it is the chart conjugate of the
model collapse `colH`, off the region it is the identity.  (The hypothesis `hctr : (D.center) 0 = 0`
is kept because the *proofs* of the map's correctness — that the image lands in the chart target and
hence in `∂M` on the core — go through `dist_colE_le`, whose `hctr` hypothesis is exactly this.) -/
def localMap (D : ColDatum M) (hctr : (D.center) 0 = 0) (t : ℝ) (x : M) : M :=
  if _hx : x ∈ D.region then
    D.chart.symm (colH D.lamTH D.lamTH_nonneg (D.chart x, t))
  else x

/-- **The `MapsTo` obligation for the continuity of `localMap`**: on the region, the chart
conjugate of the piece formula lands in the chart target.  This is where the ambient form `lamT` pays
off — `dist_colE_le` applies to it directly. -/
theorem colH_mem_target (D : ColDatum M) (hctr : (D.center) 0 = 0) {x : M}
    (hx : x ∈ D.region) (t : ℝ) :
    colH D.lamTH D.lamTH_nonneg (D.chart x, t) ∈ D.chart.target := by
  refine D.closedBall_subset _ ?_
  have h := dist_colE_le D.lamT_nonneg D.lamT_le_one hctr ((D.chart x : H9).1, t) (D.chart x).2
  have heq : (colH D.lamTH D.lamTH_nonneg (D.chart x, t)).1
      = colE D.lamT ((D.chart x : H9).1, t) := rfl
  rw [heq]
  exact le_trans h (le_of_lt (mem_region.mp hx).2)

/-- **The two-case `MapsTo` for the piece formula**: on the whole chart source (with all times), the
formula lands in the chart target.  Off the region `λ = 1` makes the formula the identity, so the
chart itself provides the target membership; on the region this is `colH_mem_target`. -/
theorem mapsTo_formula (D : ColDatum M) (hctr : (D.center) 0 = 0) :
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
theorem continuousOn_formula (D : ColDatum M) (hctr : (D.center) 0 = 0) :
    ContinuousOn
      (fun p : M × ℝ => D.chart.symm (colH D.lamTH D.lamTH_nonneg (D.chart p.1, p.2)))
      (D.chart.source ×ˢ (Set.univ : Set ℝ)) := by
  have hchart : ContinuousOn (fun p : M × ℝ => D.chart p.1) (D.chart.source ×ˢ univ) :=
    ContinuousOn.comp (g := fun x : M => D.chart x) (t := D.chart.source)
      D.chart.continuousOn continuousOn_fst (fun p hp => hp.1)
  have hcore : ContinuousOn (fun p : M × ℝ => (D.chart p.1, p.2)) (D.chart.source ×ˢ univ) :=
    hchart.prodMk continuousOn_snd
  have hcolHcont : Continuous fun q : H9 × ℝ => colH D.lamTH D.lamTH_nonneg q :=
    continuous_colH D.lamTH D.continuous_lamTH D.lamTH_nonneg
  have hpush : ContinuousOn (fun p : M × ℝ => colH D.lamTH D.lamTH_nonneg (D.chart p.1, p.2))
      (D.chart.source ×ˢ univ) :=
    hcolHcont.comp_continuousOn hcore
  exact ContinuousOn.comp D.chart.symm.continuousOn hpush (mapsTo_formula D hctr)

theorem localMap_eq_self_of_not_mem_region (D : ColDatum M) (hctr : (D.center) 0 = 0) {x : M}
    (hx : x ∉ D.region) (t : ℝ) : D.localMap hctr t x = x := by
  rw [localMap, dif_neg hx]

/-- At time `0` the local map is the identity. -/
theorem localMap_zero (D : ColDatum M) (hctr : (D.center) 0 = 0) (x : M) :
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
theorem region_subset_symm_image (D : ColDatum M) :
    D.region ⊆ D.chart.symm '' {y : H9 | dist y.1 D.center ≤ D.R} := by
  intro x hx
  obtain ⟨hsrc, hlt⟩ := mem_region.mp hx
  exact ⟨D.chart x, le_of_lt hlt, D.chart.left_inv hsrc⟩

/-- The image of the closed ambient ball is contained in the chart source. -/
theorem symm_image_subset_source (D : ColDatum M) :
    D.chart.symm '' {y : H9 | dist y.1 D.center ≤ D.R} ⊆ D.chart.source := by
  rintro z ⟨y, hy, rfl⟩
  exact D.chart.map_target (D.closedBall_subset y hy)

/-- **The image of the closed ambient ball is compact** (the closed half-ball is compact by
`isCompact_halfClosedBall`, and the chart inverse is continuous on it). -/
theorem isCompact_symm_image (D : ColDatum M) :
    IsCompact (D.chart.symm '' {y : H9 | dist y.1 D.center ≤ D.R}) :=
  (isCompact_halfClosedBall D.center D.R).image_of_continuousOn
    (D.chart.symm.continuousOn.mono (fun y hy => D.closedBall_subset y hy))

/-- Off the (closed) image of the ball, `localMap` is the identity — the neighbourhood form used in
the glueing of `PushDatum.continuous_localMap_uncurry`. -/
theorem localMap_eq_self_of_not_mem_symm_image (D : ColDatum M) (hctr : (D.center) 0 = 0) {x : M}
    (hx : x ∉ D.chart.symm '' {y : H9 | dist y.1 D.center ≤ D.R}) (t : ℝ) :
    D.localMap hctr t x = x :=
  D.localMap_eq_self_of_not_mem_region hctr
    (fun h => hx (D.region_subset_symm_image h)) t

/-- **The formula of the piece agrees with `localMap` on the whole chart source**: on the region this
is by definition, and off it `λ = 1` makes the formula collapse to the identity, which is also the
off-region value of `localMap`. -/
theorem localMap_eq_formula (D : ColDatum M) (hctr : (D.center) 0 = 0) {x : M}
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
theorem continuous_localMap_uncurry (D : ColDatum M) (hctr : (D.center) 0 = 0) :
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
  · have hnotmem : x₀ ∉ D.chart.symm '' {y : H9 | dist y.1 D.center ≤ D.R} :=
      fun h => hx (D.symm_image_subset_source h)
    have hopen : IsOpen (D.chart.symm '' {y : H9 | dist y.1 D.center ≤ D.R})ᶜ :=
      D.isCompact_symm_image.isClosed.isOpen_compl
    have hmem : ((D.chart.symm '' {y : H9 | dist y.1 D.center ≤ D.R})ᶜ ×ˢ (univ : Set ℝ))
        ∈ 𝓝 (x₀, t₀) := (hopen.prod isOpen_univ).mem_nhds ⟨hnotmem, trivial⟩
    have heq : (fun p : M × ℝ => D.localMap hctr p.2 p.1) =ᶠ[𝓝 (x₀, t₀)] Prod.fst := by
      filter_upwards [hmem] with p hp
      exact D.localMap_eq_self_of_not_mem_symm_image hctr hp.1 p.2
    exact continuous_fst.continuousAt.congr heq.symm

/-- **The model collapse fixes points whose chart image lies on the boundary hyperplane, at every
time** (so it fixes `∂M` pointwise, at every time of the homotopy). -/
theorem chart_formula_eq_self_of_mem_boundary (D : ColDatum M) {x : M} (hsrc : x ∈ D.chart.source)
    (hxb : x ∈ (modelWithCornersEuclideanHalfSpace 9).boundary M) (t : ℝ) :
    D.chart.symm (colH D.lamTH D.lamTH_nonneg (D.chart x, t)) = x := by
  have hcoord : (D.chart x).1 0 = 0 := by
    have hnot : ¬ (0 < (D.chart x).1 0) := fun h =>
      ((isInteriorPoint_iff_not_mem_boundary x).mp
        ((isInteriorPoint_iff_chart_coord (M := M) D.chart_mem_atlas hsrc).mpr h)) hxb
    linarith [not_lt.mp hnot, (D.chart x).2]
  rw [colH_eq_self_of_coord_zero D.lamTH D.lamTH_nonneg hcoord, D.chart.left_inv hsrc]

/-- **The piece fixes `∂M` at every time.** -/
theorem localMap_eq_self_of_mem_boundary (D : ColDatum M) (hctr : (D.center) 0 = 0) {x : M}
    (hxb : x ∈ (modelWithCornersEuclideanHalfSpace 9).boundary M) (t : ℝ) :
    D.localMap hctr t x = x := by
  by_cases hsrc : x ∈ D.chart.source
  · rw [D.localMap_eq_formula hctr hsrc t]
    exact D.chart_formula_eq_self_of_mem_boundary hsrc hxb t
  · rw [localMap, dif_neg (fun hreg => hsrc (mem_region.mp hreg).1)]

/-- **The piece preserves `∂M` at every time.**  Immediate from the fact that it *fixes* `∂M`
pointwise at every time (`localMap_eq_self_of_mem_boundary`). -/
theorem localMap_mem_boundary_of_mem_boundary (D : ColDatum M) (hctr : (D.center) 0 = 0) {x : M}
    (hxb : x ∈ (modelWithCornersEuclideanHalfSpace 9).boundary M) (t : ℝ) :
    D.localMap hctr t x ∈ (modelWithCornersEuclideanHalfSpace 9).boundary M := by
  rw [D.localMap_eq_self_of_mem_boundary hctr hxb t]
  exact hxb

/-- **The piece collapses its core onto `∂M` at time `1`**: for `x ∈ D.core` the interpolation
function vanishes at time `1` (`lam_eq_zero_of_mem_core` with `colT 1 = 1`), so the chart image of the
formula has first coordinate `0`, and the chart criterion puts it in `∂M`. -/
theorem localMap_mem_boundary_of_mem_core (D : ColDatum M) (hctr : (D.center) 0 = 0) {x : M}
    (hx : x ∈ D.core) :
    D.localMap hctr 1 x ∈ (modelWithCornersEuclideanHalfSpace 9).boundary M := by
  obtain ⟨hsrc, hdist⟩ := mem_core.mp hx
  have h1 : D.lamTH (D.chart x, 1) = 0 := by
    rw [lamTH, lamT, colT_one, D.lam_eq_zero_of_mem_core hx]
    ring
  have hcoord : (colH D.lamTH D.lamTH_nonneg (D.chart x, 1)).1 0 = 0 := by
    rw [colH_coord_zero, h1, zero_mul]
  have htarget : colH D.lamTH D.lamTH_nonneg (D.chart x, 1) ∈ D.chart.target := by
    refine D.closedBall_subset _ ?_
    have h := dist_colE_le D.lamT_nonneg D.lamT_le_one hctr ((D.chart x : H9).1, (1 : ℝ))
      (D.chart x).2
    rw [show (colH D.lamTH D.lamTH_nonneg (D.chart x, 1)).1
        = colE D.lamT ((D.chart x : H9).1, (1 : ℝ)) from rfl]
    exact le_trans (le_trans h hdist) (le_of_lt D.hrR)
  have hsrc' : D.chart.symm (colH D.lamTH D.lamTH_nonneg (D.chart x, 1)) ∈ D.chart.source :=
    D.chart.map_target htarget
  rw [D.localMap_eq_formula hctr hsrc 1]
  by_contra hnb
  have hInt : (modelWithCornersEuclideanHalfSpace 9).IsInteriorPoint
      (D.chart.symm (colH D.lamTH D.lamTH_nonneg (D.chart x, 1))) :=
    (isInteriorPoint_iff_not_mem_boundary _).mpr hnb
  have hlt : 0 < (D.chart (D.chart.symm (colH D.lamTH D.lamTH_nonneg (D.chart x, 1)))).1 0 :=
    (isInteriorPoint_iff_chart_coord (M := M) D.chart_mem_atlas hsrc').mp hInt
  rw [D.chart.right_inv htarget, hcoord] at hlt
  exact lt_irrefl 0 hlt

/-- **The specification of the piece's local map** — the full `colDatumLocalMap` statement, with the
witness `Ψ p := D.localMap hctr p.2 p.1`: continuous, the identity at time `0`, fixing and preserving
`∂M` at every time, collapsing the core into `∂M` at time `1`, and the identity off the region. -/
theorem localMap_spec (D : ColDatum M) (hctr : (D.center) 0 = 0) :
    ∃ Ψ : M × ℝ → M, Continuous Ψ ∧ (∀ x : M, Ψ (x, 0) = x) ∧
      (∀ x : M, x ∈ (modelWithCornersEuclideanHalfSpace 9).boundary M →
        ∀ t : ℝ, Ψ (x, t) = x) ∧
      (∀ x : M, x ∈ D.core →
        Ψ (x, 1) ∈ (modelWithCornersEuclideanHalfSpace 9).boundary M) ∧
      (∀ x : M, ¬ (x ∈ D.chart.source ∧ dist (D.chart x).1 D.center < D.R) →
        ∀ t : ℝ, Ψ (x, t) = x) :=
  ⟨fun p : M × ℝ => D.localMap hctr p.2 p.1, D.continuous_localMap_uncurry hctr,
   fun x => D.localMap_zero hctr x,
   fun x hxb t => D.localMap_eq_self_of_mem_boundary hctr hxb t,
   fun x hx => D.localMap_mem_boundary_of_mem_core hctr hx,
   fun x hx t => D.localMap_eq_self_of_not_mem_region hctr hx t⟩

/-- **The piece datum at a point** `x`: the chart at `x`, centre the image of `x`, and a core radius
half of an outer radius that keeps the closed ambient ball inside the chart target (via
`PushDatum.exists_closedBall_subset_target`). -/
def ofPoint (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanHalfSpace 9) M] (x : M) :
    ColDatum M :=
  let e := chartAt H9 x
  let w := PushDatum.exists_closedBall_subset_target (e := e) (mem_chart_target H9 x)
  { chart := e
    chart_mem_atlas := ChartedSpace.chart_mem_atlas x
    center := (e x).1
    r := Classical.choose w / 2
    R := Classical.choose w
    hr_pos := by linarith [(Classical.choose_spec w).1]
    hrR := by linarith [(Classical.choose_spec w).1]
    closedBall_subset := fun y hy => (Classical.choose_spec w).2 y hy }

theorem ofPoint_chart (x : M) : (ofPoint M x).chart = chartAt H9 x := rfl

theorem ofPoint_center (x : M) : (ofPoint M x).center = ((chartAt H9 x) x).1 := rfl

/-- The centre of the datum at a **boundary** point lies on the boundary hyperplane of its chart —
so the datum satisfies `hctr`, which is what `localMap_spec` needs. -/
theorem ofPoint_center_zero (x : M)
    (hxb : x ∈ (modelWithCornersEuclideanHalfSpace 9).boundary M) :
    (ofPoint M x).center 0 = 0 := by
  rw [ofPoint_center]
  have hnot : ¬ (0 < ((chartAt H9 x) x).1 0) := fun h =>
    ((isInteriorPoint_iff_not_mem_boundary x).mp
      ((isInteriorPoint_iff_chart_coord (M := M) (ChartedSpace.chart_mem_atlas x)
        (mem_chart_source H9 x)).mpr h)) hxb
  linarith [not_lt.mp hnot, ((chartAt H9 x) x).2]

/-- **Every boundary point lies in the core of its own piece datum** — the ingredient of the finite
cover of `∂M` by cores. -/
theorem ofPoint_mem_core (x : M)
    (hxb : x ∈ (modelWithCornersEuclideanHalfSpace 9).boundary M) :
    x ∈ (ofPoint M x).core := by
  refine mem_core.mpr ⟨?_, ?_⟩
  · rw [ofPoint_chart]
    exact mem_chart_source H9 x
  · rw [ofPoint_chart, ofPoint_center, dist_self]
    show (0 : ℝ) ≤ (Classical.choose (PushDatum.exists_closedBall_subset_target
      (e := chartAt H9 x) (mem_chart_target H9 x))) / 2
    have h := (Classical.choose_spec (PushDatum.exists_closedBall_subset_target
      (e := chartAt H9 x) (mem_chart_target H9 x))).1
    linarith

/-- **Every boundary point lies in the *interior* of the core of its own datum** — the form needed by
`IsCompact.elim_finite_subcover`, which requires the covering family to be open.  The open set is the
shrunken region `{dist (chart y) center < r/2} ∩ chart.source`, which sits inside the core. -/
theorem ofPoint_mem_interior_core (x : M)
    (hxb : x ∈ (modelWithCornersEuclideanHalfSpace 9).boundary M) :
    x ∈ interior (ofPoint M x).core := by
  have hAopen : IsOpen ((ofPoint M x).chart.source ∩
      {y : M | dist ((ofPoint M x).chart y).1 (ofPoint M x).center < (ofPoint M x).r / 2}) := by
    have h : IsOpen {y : H9 | dist y.1 (ofPoint M x).center < (ofPoint M x).r / 2} :=
      Metric.isOpen_ball.preimage continuous_subtype_val
    have h2 := (ofPoint M x).chart.isOpen_inter_preimage h
    simpa only [Set.preimage_setOf_eq, Set.mem_setOf_eq] using h2
  have hA : x ∈ (ofPoint M x).chart.source ∩
      {y : M | dist ((ofPoint M x).chart y).1 (ofPoint M x).center < (ofPoint M x).r / 2} := by
    refine ⟨?_, ?_⟩
    · rw [ofPoint_chart]
      exact mem_chart_source H9 x
    · rw [ofPoint_chart, ofPoint_center]
      have hd : dist ((chartAt H9 x) x).1 ((chartAt H9 x) x).1 < (ofPoint M x).r / 2 := by
        rw [dist_self]
        linarith [(ofPoint M x).hr_pos]
      exact hd
  have hsub : (ofPoint M x).chart.source ∩
      {y : M | dist ((ofPoint M x).chart y).1 (ofPoint M x).center < (ofPoint M x).r / 2}
      ⊆ (ofPoint M x).core := by
    rintro y ⟨hys, hyd⟩
    exact mem_core.mpr ⟨hys, le_of_lt (lt_of_lt_of_le hyd (by linarith [(ofPoint M x).hr_pos]))⟩
  exact interior_maximal hsub hAopen hA

/-- **Finitely many piece cores cover `∂M`** (taken as *interiors*, so that
`IsCompact.elim_finite_subcover` — which requires an open family — applies). -/
theorem exists_finset_core_cover :
    ∃ S : Finset M, ∀ x : M,
      x ∈ (modelWithCornersEuclideanHalfSpace 9).boundary M →
        x ∈ ⋃ y ∈ S, interior (ofPoint M y).core := by
  classical
  have hbdry_closed : IsClosed ((modelWithCornersEuclideanHalfSpace 9).boundary M) :=
    (modelWithCornersEuclideanHalfSpace 9).isClosed_boundary (n := (1 : WithTop ℕ∞))
      (by norm_num)
  have hbdry_compact : IsCompact ((modelWithCornersEuclideanHalfSpace 9).boundary M) :=
    hbdry_closed.isCompact
  obtain ⟨S, hS⟩ := hbdry_compact.elim_finite_subcover
    (fun x : M => interior (ofPoint M x).core)
    (fun _ => isOpen_interior)
    (fun x hx => Set.mem_iUnion.mpr ⟨x, ofPoint_mem_interior_core x hx⟩)
  exact ⟨S, fun x hx => hS hx⟩

/-- **The complement `K` of the finitely many *interiors* of the cores**: it is closed (the union of
closed sets' interiors is open) hence compact, and it lies in `int M` — because `∂M` is covered by
those interiors, so `K ∩ ∂M = ∅`. -/
theorem isCompact_compl_iUnion_interior_core (S : Finset M)
    (hS : ∀ x : M, x ∈ (modelWithCornersEuclideanHalfSpace 9).boundary M →
      x ∈ ⋃ y ∈ S, interior (ofPoint M y).core) :
    IsCompact ((⋃ y ∈ S, interior (ofPoint M y).core)ᶜ) ∧
      ((⋃ y ∈ S, interior (ofPoint M y).core)ᶜ) ⊆
        {x : M | x ∉ (modelWithCornersEuclideanHalfSpace 9).boundary M} := by
  refine ⟨?_, ?_⟩
  · exact (isClosed_compl_iff.mpr (isOpen_biUnion fun _ _ => isOpen_interior)).isCompact
  · intro x hx hxb
    exact hx (hS x hxb)

end ColDatum

end

end Work.ThomBordism.RelDuality

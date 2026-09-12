import Submission.Work.Main0U
import Submission.Work.BendArcFacts
import Submission.Work.UMatchDirection
import Submission.Work.CentrelineUBends
import Submission.Work.FlatHeightFacts
import Submission.Work.LeafContinuity

open OptimalMoebius Topology Filter
open scoped BigOperators Matrix Topology Metric
set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# Degenerate flat centre-heights: the crossing-height machinery (brick (A))

GREEN (brick (A) of the F1 route, session_status104 — next brick (B) is
the U-height accumulation at UNCOVERED degenerate flat heights, designed in
session_status105).  Content: for a U-point `x` of the strip interior, the canonical
full U-leaf through `x` (endpoints `uBendA`, `uBendB` on the boundary lines
`x0=0`, `x0=1`) crosses the centreline `{x0 = 1/2}` at a single point whose
HEIGHT `y(x)` is a `UHeight` value and satisfies the displacement bound

    |y(x) − x₁| ≤ |Δ| · |1/2 − x₀| ≤ C · |1/2 − x₀|,   C := (a²−1)/(2a),

where `Δ = B₁ − A₁ = uBendSlope` is the (signed) horizontal displacement of
the leaf.  Combined with the coordinate bounds `|x₀−1/2|, |x₁−y| ≤ ‖x−q‖`
(this file's `crossHeight_close`), this gives: a U-point within distance
`r` of the centreline point `(1/2, y)` has its leaf crossing the centreline
at a U-height within `(C+1)·r` of `y` — the input to the accumulation
argument (brick (B), next) at degenerate flat heights.
-/

noncomputable section
namespace Submission

open Submission.PaperBand

/- **Lemma list (brick (A), all GREEN, zero sorry):**
* `uBendSlope_eq_disp` — the leaf slope equals the endpoint displacement:
  `uBendSlope = B₁ − A₁`;
* `uBendCrossPt` — the crossing point of the leaf's line with the
  centreline `{x0 = 1/2}`; `uBendCrossPt_coord0` (it is a centreline
  point); `uBendCrossPt_param_mem` (interior of the leaf);
  `uBendCrossPt_mem_uBendSet`; `uBendCrossPt_dN_ne_zero` (it is a
  U-point); `uBendCrossPt_eq_centrePoint`;
* `uBendCrossPt_height_mem_UHeight` — its HEIGHT is a `UHeight`;
* `uBendCrossPt_coord1_formula` — `y(x) = x₁ + Δ·(1/2 − x₀)`;
* `uBendCrossPt_height_dist_bound` — `|y(x) − x₁| ≤ C·|1/2 − x₀|`,
  `C = (a²−1)/(2a)`;
* `coord_dist_le_norm_centrePoint`, `crossHeight_close` — the brick (A)
  corollary: `x` within `r` of `(1/2,y)` ⟹ `|y(x) − y| ≤ (C+1)·r`. -/

/-- The signed displacement of the canonical U-leaf through `x`:
`Δ = (uBendB)₁ − (uBendA)₁`, equal to the leaf slope `uBendSlope`. -/
lemma uBendSlope_eq_disp {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x : ℝ²} (hx : x ∈ stripInterior) (hdN : dN f x ≠ 0) :
    uBendSlope hf ha hx hdN =
      (uBendB hf ha hx hdN) 1 - (uBendA hf ha hx hdN) 1 := by
  unfold uBendSlope uBendA uBendB leftParam rightParam
  have hw0 : (uBendDirPos hf ha hx hdN) 0 ≠ 0 := uBendDirPos_coord_ne_zero hf ha hx hdN
  have hA1 : (x + (-x 0 / (uBendDirPos hf ha hx hdN) 0) • uBendDirPos hf ha hx hdN) 1 =
      x 1 - x 0 * ((uBendDirPos hf ha hx hdN) 1 / (uBendDirPos hf ha hx hdN) 0) := by
    simp [ray_coord0]
    field_simp [hw0]
    ring
  have hB1 : (x + ((1 - x 0) / (uBendDirPos hf ha hx hdN) 0) • uBendDirPos hf ha hx hdN) 1 =
      x 1 + (1 - x 0) * ((uBendDirPos hf ha hx hdN) 1 / (uBendDirPos hf ha hx hdN) 0) := by
    simp [ray_coord0]
    field_simp [hw0]
  rw [hA1, hB1]
  ring

/-- **The crossing point of the canonical U-leaf through `x` with the
centreline**: the point of the leaf's line with `x0 = 1/2`. -/
noncomputable def uBendCrossPt {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x : ℝ²} (hx : x ∈ stripInterior) (hdN : dN f x ≠ 0) : ℝ² :=
  x + (((1 / 2 : ℝ) - x 0) / (uBendDirPos hf ha hx hdN) 0) • uBendDirPos hf ha hx hdN

/-- The crossing point has `0`-coordinate `1/2` (it is a centreline point). -/
lemma uBendCrossPt_coord0 {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x : ℝ²} (hx : x ∈ stripInterior) (hdN : dN f x ≠ 0) :
    (uBendCrossPt hf ha hx hdN) 0 = 1 / 2 := by
  unfold uBendCrossPt
  rw [ray_coord0]
  have hw0 : (uBendDirPos hf ha hx hdN) 0 ≠ 0 := uBendDirPos_coord_ne_zero hf ha hx hdN
  field_simp [hw0]
  ring

/-- The crossing parameter lies strictly between the two boundary parameters
(the crossing point is in the interior of the leaf). -/
lemma uBendCrossPt_param_mem {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x : ℝ²} (hx : x ∈ stripInterior) (hdN : dN f x ≠ 0) :
    (((1 / 2 : ℝ) - x 0) / (uBendDirPos hf ha hx hdN) 0) ∈
      Set.Ioo (leftParam x (uBendDirPos hf ha hx hdN))
        (rightParam x (uBendDirPos hf ha hx hdN)) := by
  have hwpos : 0 < (uBendDirPos hf ha hx hdN) 0 := uBendDirPos_coord_pos hf ha hx hdN
  have hw0 : (uBendDirPos hf ha hx hdN) 0 ≠ 0 := ne_of_gt hwpos
  rw [Set.mem_Ioo]
  constructor
  · -- leftParam < s
    unfold leftParam
    field_simp [hw0]
    linarith
  · -- s < rightParam
    unfold rightParam
    field_simp [hw0]
    linarith

/-- The crossing point lies in the open canonical U-leaf through `x`. -/
lemma uBendCrossPt_mem_uBendSet {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x : ℝ²} (hx : x ∈ stripInterior) (hdN : dN f x ≠ 0) :
    uBendCrossPt hf ha hx hdN ∈ uBendSet hf ha hx hdN := by
  rw [uBendSet_eq_param hf ha hx hdN]
  refine ⟨(((1 / 2 : ℝ) - x 0) / (uBendDirPos hf ha hx hdN) 0), ?_, ?_⟩
  · exact uBendCrossPt_param_mem hf ha hx hdN
  · rfl

/-- The crossing point is a U-point: `dN ≠ 0` there (the whole open leaf
consists of U-points). -/
lemma uBendCrossPt_dN_ne_zero {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x : ℝ²} (hx : x ∈ stripInterior) (hdN : dN f x ≠ 0) :
    dN f (uBendCrossPt hf ha hx hdN) ≠ 0 := by
  have hmem := uBendCrossPt_mem_uBendSet hf ha hx hdN
  exact (uBendSet_subset_U_and_kernel hf ha hx hdN).1 _ hmem

/-- The crossing point is the centreline point at its own height. -/
lemma uBendCrossPt_eq_centrePoint {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x : ℝ²} (hx : x ∈ stripInterior) (hdN : dN f x ≠ 0) :
    uBendCrossPt hf ha hx hdN = centrePoint ((uBendCrossPt hf ha hx hdN) 1) := by
  ext i <;> fin_cases i
  · simp [centrePoint, uBendCrossPt_coord0 hf ha hx hdN]
  · simp [centrePoint]

/-- The height of the crossing point is a U-height: the centreline point
`(1/2, y(x))` (which IS the crossing point) is a U-point. -/
lemma uBendCrossPt_height_mem_UHeight {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x : ℝ²} (hx : x ∈ stripInterior) (hdN : dN f x ≠ 0) :
    (uBendCrossPt hf ha hx hdN) 1 ∈ UHeight a f := by
  rw [mem_UHeight]
  have heq := uBendCrossPt_eq_centrePoint hf ha hx hdN
  rw [← heq]
  exact uBendCrossPt_dN_ne_zero hf ha hx hdN

/-- **Crossing-height formula**: the height `y(x)` at which the canonical
U-leaf through `x` crosses the centreline is
`y(x) = x₁ + Δ · (1/2 − x₀)` with `Δ = uBendSlope` the leaf displacement. -/
lemma uBendCrossPt_coord1_formula {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x : ℝ²} (hx : x ∈ stripInterior) (hdN : dN f x ≠ 0) :
    (uBendCrossPt hf ha hx hdN) 1 =
      x 1 + uBendSlope hf ha hx hdN * (1 / 2 - x 0) := by
  unfold uBendCrossPt uBendSlope
  have hw0 : (uBendDirPos hf ha hx hdN) 0 ≠ 0 := uBendDirPos_coord_ne_zero hf ha hx hdN
  simp
  field_simp [hw0]

/-- **The crossing-height displacement bound**: the height `y(x)` at which
the canonical U-leaf crosses the centreline differs from `x₁` by at most
`C · |1/2 − x₀|`, where `C = (a²−1)/(2a)` is the universal displacement
bound of any canonical U-leaf. -/
lemma uBendCrossPt_height_dist_bound {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x : ℝ²} (hx : x ∈ stripInterior) (hdN : dN f x ≠ 0) :
    |(uBendCrossPt hf ha hx hdN) 1 - x 1| ≤
      ((a ^ 2 - 1) / (2 * a)) * |1 / 2 - x 0| := by
  rw [uBendCrossPt_coord1_formula hf ha hx hdN]
  have hΔ : |uBendSlope hf ha hx hdN| ≤ (a ^ 2 - 1) / (2 * a) := by
    rw [uBendSlope_eq_disp hf ha hx hdN]
    exact uBend_abs_disp_bound hf ha hx hdN
  calc
    |x 1 + uBendSlope hf ha hx hdN * (1 / 2 - x 0) - x 1| =
        |uBendSlope hf ha hx hdN * (1 / 2 - x 0)| := by
      congr 1
      ring
    _ = |uBendSlope hf ha hx hdN| * |1 / 2 - x 0| := abs_mul _ _
    _ ≤ ((a ^ 2 - 1) / (2 * a)) * |1 / 2 - x 0| := by
      exact mul_le_mul_of_nonneg_right hΔ (abs_nonneg _)

/-- A centreline point `q = (1/2, y)`: `x₀` is within `‖x − q‖` of `1/2`,
and `x₁` within `‖x − q‖` of `y` (coordinate distances are bounded by the
norm distance). -/
lemma coord_dist_le_norm_centrePoint (x : ℝ²) (y : ℝ) :
    |x 0 - 1 / 2| ≤ ‖x - centrePoint y‖ ∧ |x 1 - y| ≤ ‖x - centrePoint y‖ := by
  constructor
  · have h := abs_coord0_le_norm (x - centrePoint y)
    have h0 : (x - centrePoint y) 0 = x 0 - 1 / 2 := by
      simp [centrePoint]
    simpa [h0] using h
  · have h := abs_coord1_le_norm (x - centrePoint y)
    have h1 : (x - centrePoint y) 1 = x 1 - y := by
      simp [centrePoint]
    simpa [h1] using h

/-- **The displacement coefficient is non-negative**: the existence of a
U-point in the strip interior forces `0 ≤ (a²−1)/(2a)` (the displacement
bound `|Δ| ≤ (a²−1)/(2a)` with `|Δ| ≥ 0`). -/
lemma uBendDispCoeff_nonneg {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x : ℝ²} (hx : x ∈ stripInterior) (hdN : dN f x ≠ 0) :
    0 ≤ (a ^ 2 - 1) / (2 * a) := by
  have hb := uBend_abs_disp_bound hf ha hx hdN
  have hs : 0 ≤ |(uBendB hf ha hx hdN) 1 - (uBendA hf ha hx hdN) 1| := abs_nonneg _
  linarith

/-- **Brick (A), main corollary**: if `x` is a U-point of the strip interior
within distance `r` of the centreline point `(1/2, y)`, then the canonical
U-leaf through `x` crosses the centreline at a U-height within
`(C + 1) · r` of `y`, where `C = (a²−1)/(2a)`. -/
theorem crossHeight_close {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x : ℝ²} (hx : x ∈ stripInterior) (hdN : dN f x ≠ 0)
    {y r : ℝ} (hr : 0 ≤ r) (hxr : ‖x - centrePoint y‖ ≤ r) :
    |(uBendCrossPt hf ha hx hdN) 1 - y| ≤
      (((a ^ 2 - 1) / (2 * a)) + 1) * r := by
  let C : ℝ := (a ^ 2 - 1) / (2 * a)
  have hC0 : 0 ≤ C := by
    have hb := uBend_abs_disp_bound hf ha hx hdN
    have hs : 0 ≤ |(uBendB hf ha hx hdN) 1 - (uBendA hf ha hx hdN) 1| := abs_nonneg _
    dsimp [C]
    linarith
  have hxy := uBendCrossPt_height_dist_bound hf ha hx hdN
  rcases coord_dist_le_norm_centrePoint x y with ⟨hc0, hc1⟩
  have hL : |1 / 2 - x 0| ≤ r := by
    rw [abs_sub_comm]
    linarith [hc0, hxr]
  have hb1 : |(uBendCrossPt hf ha hx hdN) 1 - x 1| ≤ C * r := by
    have hmul : C * |1 / 2 - x 0| ≤ C * r := mul_le_mul_of_nonneg_left hL hC0
    dsimp [C] at hmul hxy
    linarith
  have hb2 : |x 1 - y| ≤ r := by linarith [hc1, hxr]
  calc
    |(uBendCrossPt hf ha hx hdN) 1 - y| ≤
        |(uBendCrossPt hf ha hx hdN) 1 - x 1| + |x 1 - y| := by
      rw [show (uBendCrossPt hf ha hx hdN) 1 - y =
          ((uBendCrossPt hf ha hx hdN) 1 - x 1) + (x 1 - y) by ring]
      exact abs_add_le _ _
    _ ≤ (C + 1) * r := by nlinarith
    _ = (((a ^ 2 - 1) / (2 * a)) + 1) * r := by dsimp [C]

end Submission

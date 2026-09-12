import Submission.Work.UFoliation
import Submission.Work.NoVerticalKernel

open OptimalMoebius Topology ContDiff
open scoped BigOperators Matrix Topology Metric
open InnerProductGeometry

set_option autoImplicit false
set_option maxHeartbeats 600000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# Prop main0 (U-part): closed leaves with endpoints on the strip boundary

Lemma `mc` (U-part) is complete in `Submission.Work.UFoliation`: through each
interior point `x` of `U = {dN ≠ 0}` there is a unique maximal full kernel
segment (`uBendSet x`), the interior part of the affine line through `x` in
the canonical crossing direction `uBendDir x`; distinct such segments are
disjoint or equal.

This file adds the **closed-leaf / boundary geometry** of those segments, the
form in which Prop main0 and Lemma T consume them:
* the canonical direction is oriented so that it crosses the strip left to
  right (`uBendDirPos`, `0 < w 0`);
* the two boundary-line parameters (`leftParam`, `rightParam`) and the two
  endpoints `uBendA ∈ leftEdge`, `uBendB ∈ rightEdge` of the leaf;
* the open leaf as a parametrized interval (`uBendSet_eq_param`);
* the closed leaf `uBendClosed` (the whole chord of the strip cut out by the
  leaf's line), with membership of its endpoints and of `x`;
* `uBendSet_of_mem`: the open leaf through any point `y` of the open leaf of
  `x` is the same leaf — the leaves partition `U` (unique leaf through each
  point, leaf independent of the chosen point on it).
-/

noncomputable section
namespace Submission.PaperBand

/-- The parameter at which the ray through `x` in direction `w` (with
`0 < w 0`) meets the line `x0 = 0`. -/
def leftParam (x w : ℝ²) : ℝ := -x 0 / w 0

/-- The parameter at which the ray through `x` in direction `w` (with
`0 < w 0`) meets the line `x0 = 1`. -/
def rightParam (x w : ℝ²) : ℝ := (1 - x 0) / w 0

/-- The left-boundary parameter point has `0`-coordinate `0`. -/
lemma leftParam_coord {x w : ℝ²} (hw0 : w 0 ≠ 0) :
    (x + leftParam x w • w) 0 = 0 := by
  unfold leftParam
  rw [ray_coord0]
  field_simp [hw0]
  ring

/-- The right-boundary parameter point has `0`-coordinate `1`. -/
lemma rightParam_coord {x w : ℝ²} (hw0 : w 0 ≠ 0) :
    (x + rightParam x w • w) 0 = 1 := by
  unfold rightParam
  rw [ray_coord0]
  field_simp [hw0]
  ring

/-- For `0 < w 0` the left parameter is negative (the starting point `x` has
`0 < x 0`). -/
lemma leftParam_neg {x w : ℝ²} (hwpos : 0 < w 0) (hx0 : 0 < x 0) :
    leftParam x w < 0 := by
  unfold leftParam
  rw [div_lt_iff₀ hwpos]
  nlinarith

/-- For `0 < w 0` the right parameter is positive (the starting point `x` has
`x 0 < 1`). -/
lemma rightParam_pos {x w : ℝ²} (hwpos : 0 < w 0) (hx1 : x 0 < 1) :
    0 < rightParam x w := by
  unfold rightParam
  rw [lt_div_iff₀ hwpos]
  nlinarith

/-- The boundary parameters are ordered: `left < right`. -/
lemma leftParam_lt_rightParam {x w : ℝ²} (hwpos : 0 < w 0) (hx0 : 0 < x 0) (hx1 : x 0 < 1) :
    leftParam x w < rightParam x w := by
  exact lt_trans (leftParam_neg hwpos hx0) (rightParam_pos hwpos hx1)

/-- A point of the ray lies in the strip interior exactly between the two
boundary parameters (valid when the direction crosses with `0 < w 0`). -/
lemma param_stripInterior_iff {x w : ℝ²} (hwpos : 0 < w 0) (s : ℝ) :
    s ∈ Set.Ioo (leftParam x w) (rightParam x w) ↔ x + s • w ∈ stripInterior := by
  constructor
  · intro hs
    rw [Set.mem_Ioo] at hs
    have h0 : 0 < x 0 + s * w 0 := by
      have hlt := (div_lt_iff₀ hwpos).1 (by simpa [leftParam] using hs.1)
      nlinarith
    have h1 : x 0 + s * w 0 < 1 := by
      have hlt := (lt_div_iff₀ hwpos).1 (by simpa [rightParam] using hs.2)
      nlinarith
    rw [mem_stripInterior_ray_iff]
    exact ⟨h0, h1⟩
  · intro hs
    rw [Set.mem_Ioo]
    rw [mem_stripInterior_ray_iff] at hs
    rcases hs with ⟨h0, h1⟩
    constructor
    · unfold leftParam
      rw [div_lt_iff₀ hwpos]
      nlinarith
    · unfold rightParam
      rw [lt_div_iff₀ hwpos]
      nlinarith

/-- Orient a nonzero vector so that its `0`-coordinate is positive. -/
def orientPos (w : ℝ²) : ℝ² := if 0 < w 0 then w else -w

/-- `orientPos` makes the `0`-coordinate positive (for nonzero input). -/
lemma orientPos_coord_pos {w : ℝ²} (hw0 : w 0 ≠ 0) : 0 < (orientPos w) 0 := by
  unfold orientPos
  by_cases h : 0 < w 0
  · simp [h]
  · have hneg : w 0 < 0 := lt_of_le_of_ne (le_of_not_gt h) (by
      intro hz
      exact hw0 hz)
    simp [h]
    linarith

/-- `orientPos w` is either `w` or `-w`. -/
lemma orientPos_eq_self_or_neg (w : ℝ²) :
    orientPos w = w ∨ orientPos w = -w := by
  unfold orientPos
  by_cases h : 0 < w 0 <;> simp [h]

/-- A kernel direction is also a kernel direction after negation. -/
lemma dN_kernel_neg {f : ℝ² → ℝ³} {x w : ℝ²} (hker : dN f x w = 0) :
    dN f x (-w) = 0 := by
  exact (map_neg_eq_zero_iff (dN f x : ℝ² →ₗ[ℝ] ℝ³) w).2 hker

/-- The canonical crossing kernel direction at a `U`-point, oriented so that
it crosses the strip from the line `x0 = 0` to the line `x0 = 1`. -/
noncomputable def uBendDirPos {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x : ℝ²} (hx : x ∈ stripInterior) (hdN : dN f x ≠ 0) : ℝ² :=
  orientPos (uBendDir hf ha hx hdN)

/-- The oriented canonical direction is a kernel direction, nonzero, and
crosses the strip (`0 < w 0`). -/
lemma uBendDirPos_spec {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x : ℝ²} (hx : x ∈ stripInterior) (hdN : dN f x ≠ 0) :
    dN f x (uBendDirPos hf ha hx hdN) = 0 ∧
      uBendDirPos hf ha hx hdN ≠ 0 ∧
      0 < (uBendDirPos hf ha hx hdN) 0 := by
  rcases uBendDir_spec hf ha hx hdN with ⟨hker, hwne, hw0⟩
  unfold uBendDirPos orientPos
  by_cases hpos : 0 < uBendDir hf ha hx hdN 0
  · -- orientPos keeps the direction
    have hred : (if 0 < uBendDir hf ha hx hdN 0 then uBendDir hf ha hx hdN
        else -uBendDir hf ha hx hdN) = uBendDir hf ha hx hdN := if_pos hpos
    rw [hred]
    exact ⟨hker, hwne, hpos⟩
  · -- orientPos negates the direction
    have hneg : uBendDir hf ha hx hdN 0 < 0 := lt_of_le_of_ne (le_of_not_gt hpos) (by
      intro hz
      exact hw0 hz)
    have hred : (if 0 < uBendDir hf ha hx hdN 0 then uBendDir hf ha hx hdN
        else -uBendDir hf ha hx hdN) = -uBendDir hf ha hx hdN := if_neg hpos
    rw [hred]
    constructor
    · exact dN_kernel_neg hker
    constructor
    · intro hz
      have hnegzero : -(uBendDir hf ha hx hdN) = 0 := hz
      have : uBendDir hf ha hx hdN = 0 := by
        calc
          uBendDir hf ha hx hdN = -(-(uBendDir hf ha hx hdN)) := by simp
          _ = 0 := by simp [hnegzero]
      exact hwne this
    · simp
      linarith

/-- The open canonical bend set equals the set of points of the oriented ray
at parameters strictly between the two boundary parameters (equivalently: the
interior part of the line inside the strip). -/
lemma uBendSet_eq_param {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x : ℝ²} (hx : x ∈ stripInterior) (hdN : dN f x ≠ 0) :
    uBendSet hf ha hx hdN =
      {y | ∃ s : ℝ, s ∈ Set.Ioo (leftParam x (uBendDirPos hf ha hx hdN))
            (rightParam x (uBendDirPos hf ha hx hdN)) ∧
          y = x + s • (uBendDirPos hf ha hx hdN)} := by
  rcases uBendDirPos_spec hf ha hx hdN with ⟨hkerp, hwnep, hwposp⟩
  rcases uBendDir_spec hf ha hx hdN with ⟨hker, hwne, hw0⟩
  have hlin : uBendSet hf ha hx hdN = lineInteriorSet x (uBendDirPos hf ha hx hdN) := by
    unfold uBendSet
    exact ubend_unique_through_point hf hx hdN hker hwne hw0 hkerp hwnep (ne_of_gt hwposp)
  rw [hlin]
  rw [← kernelSegmentSet_eq_lineInterior (x := x) (w := uBendDirPos hf ha hx hdN)
    (α := leftParam x (uBendDirPos hf ha hx hdN))
    (β := rightParam x (uBendDirPos hf ha hx hdN))]
  rfl
  · intro s
    exact param_stripInterior_iff hwposp s

/-- The left endpoint of the canonical bend: the point of the leaf's line on
the boundary line `x0 = 0`. -/
noncomputable def uBendA {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x : ℝ²} (hx : x ∈ stripInterior) (hdN : dN f x ≠ 0) : ℝ² :=
  x + leftParam x (uBendDirPos hf ha hx hdN) • uBendDirPos hf ha hx hdN

/-- The right endpoint of the canonical bend: the point of the leaf's line on
the boundary line `x0 = 1`. -/
noncomputable def uBendB {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x : ℝ²} (hx : x ∈ stripInterior) (hdN : dN f x ≠ 0) : ℝ² :=
  x + rightParam x (uBendDirPos hf ha hx hdN) • uBendDirPos hf ha hx hdN

/-- `uBendA` lies on the left boundary line `x0 = 0`. -/
lemma uBendA_leftEdge {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x : ℝ²} (hx : x ∈ stripInterior) (hdN : dN f x ≠ 0) :
    uBendA hf ha hx hdN ∈ leftEdge := by
  unfold leftEdge
  rcases uBendDirPos_spec hf ha hx hdN with ⟨hkerp, hwnep, hwposp⟩
  exact leftParam_coord (x := x) (w := uBendDirPos hf ha hx hdN) (ne_of_gt hwposp)

/-- `uBendB` lies on the right boundary line `x0 = 1`. -/
lemma uBendB_rightEdge {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x : ℝ²} (hx : x ∈ stripInterior) (hdN : dN f x ≠ 0) :
    uBendB hf ha hx hdN ∈ rightEdge := by
  unfold rightEdge
  rcases uBendDirPos_spec hf ha hx hdN with ⟨hkerp, hwnep, hwposp⟩
  exact rightParam_coord (x := x) (w := uBendDirPos hf ha hx hdN) (ne_of_gt hwposp)

/-- `x` lies strictly between the two boundary parameters (left < 0 < right),
so the parameter `0` is interior to the chord. -/
lemma zero_between_params {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x : ℝ²} (hx : x ∈ stripInterior) (hdN : dN f x ≠ 0) :
    leftParam x (uBendDirPos hf ha hx hdN) < 0 ∧
      0 < rightParam x (uBendDirPos hf ha hx hdN) := by
  rcases uBendDirPos_spec hf ha hx hdN with ⟨hkerp, hwnep, hwposp⟩
  have hx0 : 0 < x 0 := by
    rw [stripInterior] at hx
    exact hx.1
  have hx1 : x 0 < 1 := by
    rw [stripInterior] at hx
    exact hx.2
  exact ⟨leftParam_neg hwposp hx0, rightParam_pos hwposp hx1⟩

/-- The closed canonical bend: the full chord of the strip cut out by the
leaf's line (parameters from the left to the right boundary line). -/
noncomputable def uBendClosed {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x : ℝ²} (hx : x ∈ stripInterior) (hdN : dN f x ≠ 0) : Set ℝ² :=
  {y | ∃ s ∈ Set.Icc (leftParam x (uBendDirPos hf ha hx hdN))
        (rightParam x (uBendDirPos hf ha hx hdN)),
      y = x + s • (uBendDirPos hf ha hx hdN)}

/-- The left endpoint lies in the closed bend. -/
lemma uBendA_mem_closed {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x : ℝ²} (hx : x ∈ stripInterior) (hdN : dN f x ≠ 0) :
    uBendA hf ha hx hdN ∈ uBendClosed hf ha hx hdN := by
  unfold uBendClosed uBendA
  refine ⟨leftParam x (uBendDirPos hf ha hx hdN), ?_, rfl⟩
  rw [Set.mem_Icc]
  exact ⟨le_rfl, le_of_lt ((zero_between_params hf ha hx hdN).1.trans (zero_between_params hf ha hx hdN).2)⟩

/-- The right endpoint lies in the closed bend. -/
lemma uBendB_mem_closed {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x : ℝ²} (hx : x ∈ stripInterior) (hdN : dN f x ≠ 0) :
    uBendB hf ha hx hdN ∈ uBendClosed hf ha hx hdN := by
  unfold uBendClosed uBendB
  refine ⟨rightParam x (uBendDirPos hf ha hx hdN), ?_, rfl⟩
  rw [Set.mem_Icc]
  exact ⟨le_of_lt ((zero_between_params hf ha hx hdN).1.trans (zero_between_params hf ha hx hdN).2), le_rfl⟩

/-- The bend point `x` itself lies in the closed bend. -/
lemma uBendClosed_mem_self {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x : ℝ²} (hx : x ∈ stripInterior) (hdN : dN f x ≠ 0) :
    x ∈ uBendClosed hf ha hx hdN := by
  unfold uBendClosed
  refine ⟨0, ?_, by simp⟩
  rw [Set.mem_Icc]
  exact ⟨le_of_lt (zero_between_params hf ha hx hdN).1, le_of_lt (zero_between_params hf ha hx hdN).2⟩

/-- The open leaf is contained in the closed bend. -/
lemma uBendSet_subset_closed {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x : ℝ²} (hx : x ∈ stripInterior) (hdN : dN f x ≠ 0) :
    uBendSet hf ha hx hdN ⊆ uBendClosed hf ha hx hdN := by
  intro y hy
  rw [uBendSet_eq_param hf ha hx hdN] at hy
  rcases hy with ⟨s, hsIoo, hyEq⟩
  rw [Set.mem_Ioo] at hsIoo
  unfold uBendClosed
  refine ⟨s, ?_, hyEq⟩
  rw [Set.mem_Icc]
  exact ⟨le_of_lt hsIoo.1, le_of_lt hsIoo.2⟩

/-- **The leaves partition `U`**: if `y` lies in the open leaf of `x`, then
the open leaf of `y` is the same set — the leaf is independent of the point
chosen on it, and the leaf through each point is unique. -/
theorem uBendSet_of_mem {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x : ℝ²} (hx : x ∈ stripInterior) (hdN : dN f x ≠ 0)
    {y : ℝ²} (hy : y ∈ uBendSet hf ha hx hdN) :
    uBendSet hf ha (show y ∈ stripInterior from hy.1)
        ((uBendSet_subset_U_and_kernel hf ha hx hdN).1 y hy) = uBendSet hf ha hx hdN := by
  let hyI : y ∈ stripInterior := hy.1
  let hyU : dN f y ≠ 0 := (uBendSet_subset_U_and_kernel hf ha hx hdN).1 y hy
  rcases uBendDir_spec hf ha hx hdN with ⟨hkerx, hwnex, hw0x⟩
  rcases uBendDir_spec hf ha hyI hyU with ⟨hkery, hwney, hw0y⟩
  unfold uBendSet
  exact ubend_disjoint_or_equal hf (x₁ := y) (w₁ := uBendDir hf ha hyI hyU)
    hyI hyU hkery hwney hw0y (x₂ := x) (w₂ := uBendDir hf ha hx hdN)
    hx hdN hkerx hwnex hw0x
    ⟨y, mem_lineInterior_self hyI, by simpa [uBendSet] using hy⟩



/-- A parameter in the closed interval is either interior to the open
interval or one of the two endpoints (for `left < right`). -/
lemma mem_Icc_eq_Ioo_or_endpoints {a b : ℝ} (hab : a < b) {s : ℝ} :
    s ∈ Set.Icc a b ↔ s ∈ Set.Ioo a b ∨ s = a ∨ s = b := by
  constructor
  · intro hs
    rw [Set.mem_Icc] at hs
    by_cases hsa : s = a
    · exact Or.inr (Or.inl hsa)
    · by_cases hsb : s = b
      · exact Or.inr (Or.inr hsb)
      · exact Or.inl (by rw [Set.mem_Ioo]; exact ⟨lt_of_le_of_ne hs.1 (Ne.symm hsa), lt_of_le_of_ne hs.2 hsb⟩)
  · intro h
    rw [Set.mem_Icc]
    rcases h with hsIoo | h | h
    · rw [Set.mem_Ioo] at hsIoo
      exact ⟨le_of_lt hsIoo.1, le_of_lt hsIoo.2⟩
    · subst s
      exact ⟨le_rfl, le_of_lt hab⟩
    · subst s
      exact ⟨le_of_lt hab, le_rfl⟩

/-- The interior part of the closed leaf (points of the closed bend inside
the strip interior) is exactly the open leaf. -/
lemma uBendClosed_interior_eq_open {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x : ℝ²} (hx : x ∈ stripInterior) (hdN : dN f x ≠ 0) :
    uBendClosed hf ha hx hdN ∩ stripInterior = uBendSet hf ha hx hdN := by
  ext y
  constructor
  · intro hy
    rcases hy with ⟨hyC, hyI⟩
    unfold uBendClosed at hyC
    rcases hyC with ⟨s, hsIcc, hyEq⟩
    have hab0 : leftParam x (uBendDirPos hf ha hx hdN) < rightParam x (uBendDirPos hf ha hx hdN) :=
      (zero_between_params hf ha hx hdN).1.trans (zero_between_params hf ha hx hdN).2
    rw [mem_Icc_eq_Ioo_or_endpoints (a := leftParam x (uBendDirPos hf ha hx hdN))
      (b := rightParam x (uBendDirPos hf ha hx hdN)) hab0 (s := s)] at hsIcc
    rcases hsIcc with hsIoo | h | h
    · rw [uBendSet_eq_param hf ha hx hdN]
      exact ⟨s, hsIoo, hyEq⟩
    · subst s
      -- the left endpoint is on x0 = 0, not in the strip interior
      exfalso
      have hyA : y = uBendA hf ha hx hdN := hyEq
      rw [hyA] at hyI
      have hA0 : (uBendA hf ha hx hdN) 0 = 0 := by
        unfold uBendA
        rcases uBendDirPos_spec hf ha hx hdN with ⟨hkerp, hwnep, hwposp⟩
        exact leftParam_coord (x := x) (w := uBendDirPos hf ha hx hdN) (ne_of_gt hwposp)
      have hlt : 0 < (uBendA hf ha hx hdN) 0 := by
        rw [stripInterior] at hyI
        exact hyI.1
      rw [hA0] at hlt
      linarith
    · subst s
      exfalso
      have hyB : y = uBendB hf ha hx hdN := hyEq
      rw [hyB] at hyI
      have hB1 : (uBendB hf ha hx hdN) 0 = 1 := by
        unfold uBendB
        rcases uBendDirPos_spec hf ha hx hdN with ⟨hkerp, hwnep, hwposp⟩
        exact rightParam_coord (x := x) (w := uBendDirPos hf ha hx hdN) (ne_of_gt hwposp)
      have hlt : (uBendB hf ha hx hdN) 0 < 1 := by
        rw [stripInterior] at hyI
        exact hyI.2
      rw [hB1] at hlt
      linarith
  · intro hy
    constructor
    · exact uBendSet_subset_closed hf ha hx hdN hy
    · rw [uBendSet_eq_param hf ha hx hdN] at hy
      rcases hy with ⟨s, hsIoo, hEq⟩
      rw [hEq]
      exact (param_stripInterior_iff (uBendDirPos_spec hf ha hx hdN).2.2 s).1 hsIoo

/-- The closed bend is the open leaf together with its two boundary
endpoints. -/
theorem uBendClosed_eq_open_union_endpoints {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {x : ℝ²} (hx : x ∈ stripInterior)
    (hdN : dN f x ≠ 0) :
    uBendClosed hf ha hx hdN =
      uBendSet hf ha hx hdN ∪
        ({uBendA hf ha hx hdN, uBendB hf ha hx hdN} : Set ℝ²) := by
  ext y
  constructor
  · intro hyC
    unfold uBendClosed at hyC
    rcases hyC with ⟨s, hsIcc, hyEq⟩
    have hab0 : leftParam x (uBendDirPos hf ha hx hdN) < rightParam x (uBendDirPos hf ha hx hdN) :=
      (zero_between_params hf ha hx hdN).1.trans (zero_between_params hf ha hx hdN).2
    rw [mem_Icc_eq_Ioo_or_endpoints (a := leftParam x (uBendDirPos hf ha hx hdN))
      (b := rightParam x (uBendDirPos hf ha hx hdN)) hab0 (s := s)] at hsIcc
    rcases hsIcc with hsIoo | hsa | hsb
    · exact Or.inl (by rw [uBendSet_eq_param hf ha hx hdN]; exact ⟨s, hsIoo, hyEq⟩)
    · subst s
      exact Or.inr (Or.inl (by simpa [uBendA] using hyEq))
    · subst s
      exact Or.inr (Or.inr (by simpa [uBendB] using hyEq))
  · intro hyU
    rcases hyU with hyO | hyE
    · exact uBendSet_subset_closed hf ha hx hdN hyO
    · rcases (by simpa using hyE : y = uBendA hf ha hx hdN ∨ y = uBendB hf ha hx hdN) with hyA | hyB
      · rw [hyA]
        exact uBendA_mem_closed hf ha hx hdN
      · rw [hyB]
        exact uBendB_mem_closed hf ha hx hdN

/-- Every point of the closed bend lies in the closed unit strip. -/
lemma uBendClosed_subset_unitStrip {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x : ℝ²} (hx : x ∈ stripInterior) (hdN : dN f x ≠ 0) :
    uBendClosed hf ha hx hdN ⊆ unitStrip := by
  rw [uBendClosed_eq_open_union_endpoints hf ha hx hdN]
  intro y hy
  rcases hy with hyO | hyE
  · have hI : y ∈ stripInterior := by
      rw [uBendSet_eq_param hf ha hx hdN] at hyO
      rcases hyO with ⟨s, hsIoo, hEq⟩
      rw [hEq]
      exact (param_stripInterior_iff (uBendDirPos_spec hf ha hx hdN).2.2 s).1 hsIoo
    rw [unitStrip]
    have hc : y 0 ∈ Set.Ioo (0 : ℝ) 1 := by
      rw [stripInterior] at hI
      exact hI
    rcases hc with ⟨h0, h1⟩
    exact ⟨le_of_lt h0, le_of_lt h1⟩
  · rcases (by simpa using hyE : y = uBendA hf ha hx hdN ∨ y = uBendB hf ha hx hdN) with hyA | hyB
    · rw [hyA]
      exact stripBoundary_subset_unitStrip (Or.inl (uBendA_leftEdge hf ha hx hdN))
    · rw [hyB]
      exact stripBoundary_subset_unitStrip (Or.inr (uBendB_rightEdge hf ha hx hdN))

end Submission.PaperBand

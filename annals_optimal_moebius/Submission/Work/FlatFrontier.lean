import Submission.Work.LeafContinuity

open OptimalMoebius Topology ContDiff
open scoped BigOperators Matrix Topology Metric
open InnerProductGeometry

set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# Prop main0 (block C): first structural lemmas — U-bends avoid the flat set

Since the U-part of Lemma `mc` is complete, every interior point of the open
leaf `uBendSet x` of a `U`-point `x` is itself a `U`-point (kernel and
`U`-membership propagate along the whole maximal segment,
`UFoliation.uBendSet_subset_U_and_kernel`), and the maximal segment is the
FULL interior part of its line inside the strip
(`uBendSet_eq_param`, `Main0U.uBendClosed_eq_open_union_endpoints`).

The first flat-structure consequences (recorded here):
* **U-bend chords never meet the flat set**: `uBendSet x ∩ FlatSet = ∅` and
  `uBendClosed x ∩ FlatSet ⊆ {uBendA, uBendB}` — the only flat points on a
  closed bend are its two boundary endpoints (which lie on the boundary
  lines `x0 = 0`/`x0 = 1`, where `dN` is not even defined by our interior
  data);
* consequently the interior of a flat region contains no point of any
  U-bend: a maximal bend line can neither cross nor be tangent through a
  flat piece — it must run along the boundary of the piece.  This is the
  mechanism that makes the flat components of `stripInterior ∖ U` have
  straight bend edges parallel to the surrounding rulings (the trapezoid
  picture of Prop main0).

These are the first lemmas of block (C) (`session_status32` next steps);
they are pointwise/algebraic and build directly on the completed U-part.
-/

noncomputable section
namespace Submission.PaperBand

/-- **The open leaf of a `U`-point contains no flat point**: every point of
`uBendSet x` is a `U`-point (`dN ≠ 0`), hence is not in `FlatSet`. -/
theorem uBendSet_disjoint_FlatSet {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x : ℝ²} (hx : x ∈ stripInterior) (hdN : dN f x ≠ 0) :
    uBendSet hf ha hx hdN ∩ FlatSet f = ∅ := by
  ext y
  constructor
  · rintro ⟨hyL, hyF⟩
    exact (uBendSet_subset_U_and_kernel hf ha hx hdN).1 y hyL (mem_FlatSet.mp hyF).2
  · rintro hy
    exact False.elim ((Set.mem_empty_iff_false y).mp hy)

/-- **The closed leaf of a `U`-point meets the flat set only possibly in its
two boundary endpoints**: flat points of the closed chord lie in
`{uBendA, uBendB}` (which sit on the strip boundary lines). -/
theorem uBendClosed_FlatSet_subset_endpoints {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {x : ℝ²} (hx : x ∈ stripInterior)
    (hdN : dN f x ≠ 0) :
    uBendClosed hf ha hx hdN ∩ FlatSet f ⊆
      ({uBendA hf ha hx hdN, uBendB hf ha hx hdN} : Set ℝ²) := by
  intro y hy
  rw [uBendClosed_eq_open_union_endpoints hf ha hx hdN] at hy
  rcases hy with ⟨hyC, hyF⟩
  rcases hyC with hyO | hyE
  · -- y in the open leaf: cannot be flat
    exfalso
    exact (uBendSet_subset_U_and_kernel hf ha hx hdN).1 y hyO (mem_FlatSet.mp hyF).2
  · exact hyE

/-- **No point of the flat set lies on the open leaf of a `U`-point**
(symmetric form of `uBendSet_disjoint_FlatSet`). -/
theorem FlatSet_disjoint_uBendSet {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x : ℝ²} (hx : x ∈ stripInterior) (hdN : dN f x ≠ 0) :
    FlatSet f ∩ uBendSet hf ha hx hdN = ∅ := by
  rw [Set.inter_comm]
  exact uBendSet_disjoint_FlatSet hf ha hx hdN

/-- **Flat points do not lie on U-bend lines**: a flat point `p` is not on
the open leaf of any `U`-point. -/
theorem IsFlatInterior_not_mem_uBendSet {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x p : ℝ²} (hx : x ∈ stripInterior) (hdN : dN f x ≠ 0)
    (hpF : p ∈ FlatSet f) :
    p ∉ uBendSet hf ha hx hdN := by
  intro hp
  exact (uBendSet_subset_U_and_kernel hf ha hx hdN).1 p hp (mem_FlatSet.mp hpF).2

/-- **Characterization of the open leaf**: `z` lies in the canonical open
leaf through the `U`-point `x` iff `z` is an interior point of the strip on
the canonical line `x + ℝ·(uBendDirPos x)`. -/
theorem mem_uBendSet_iff_on_line_interior {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x z : ℝ²} (hx : x ∈ stripInterior) (hdN : dN f x ≠ 0) :
    z ∈ uBendSet hf ha hx hdN ↔
      z ∈ stripInterior ∧ ∃ s : ℝ, z = x + s • (uBendDirPos hf ha hx hdN) := by
  -- uBendSet = lineInteriorSet x wpos
  have hlin : uBendSet hf ha hx hdN = lineInteriorSet x (uBendDirPos hf ha hx hdN) := by
    rcases uBendDirPos_spec hf ha hx hdN with ⟨hkerp, hwnep, hwposp⟩
    rcases uBendDir_spec hf ha hx hdN with ⟨hker, hwne, hw0⟩
    unfold uBendSet
    exact ubend_unique_through_point hf hx hdN hker hwne hw0 hkerp hwnep (ne_of_gt hwposp)
  rw [hlin]
  unfold lineInteriorSet
  rfl

/-- **Interior points on the canonical line are `U`-points**: since the
maximal kernel segment is the full interior part of its line, any interior
strip point collinear with a `U`-point along its kernel direction lies on
the open leaf, hence in `U`. -/
theorem interior_on_line_is_U {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x z : ℝ²} (hx : x ∈ stripInterior) (hdN : dN f x ≠ 0)
    (hz : z ∈ stripInterior) (hline : ∃ s : ℝ, z = x + s • (uBendDirPos hf ha hx hdN)) :
    dN f z ≠ 0 := by
  have hzL : z ∈ uBendSet hf ha hx hdN :=
    (mem_uBendSet_iff_on_line_interior hf ha hx hdN).2 ⟨hz, hline⟩
  exact (uBendSet_subset_U_and_kernel hf ha hx hdN).1 z hzL

end Submission.PaperBand

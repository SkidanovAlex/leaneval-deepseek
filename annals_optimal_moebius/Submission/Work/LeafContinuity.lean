import Submission.Work.BendImage
import Submission.Work.NoVerticalKernel
import Submission.PaperBand.KernelUnit

open OptimalMoebius Topology ContDiff
open scoped BigOperators Matrix Topology Metric
open InnerProductGeometry
open Filter

set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# Leaf continuity along the centreline (Prop main0, U-part; Lemma T input)

Goal (block B of session_status29/30): the canonical U-leaf varies
continuously with its base point.  Concretely, for the centreline point
`c(y) = !₂[1/2, y]` we show that the endpoints of the leaf through `c(y)`
(determined by the mirror kernel field `V2f`) depend continuously on `y`
whenever `c(y) ∈ U`.

Key facts used:
* the mirror kernel field `V2f f x = (c, −b)` (`McStraight`) is smooth on
  `stripInterior` (`continuousAt_V2f`), is a section of the kernel
  (`V2f_mem_ker`), and is NONZERO at every `U`-point with a crossing kernel
  direction (`KernelUnit.V2f_ne_zero_of_kernel_crossing` + the existence of
  crossing directions, `NoVerticalKernel.exists_crossing_kernel_direction`);
* at a `U`-point the kernel line is NOT vertical
  (`NoVerticalKernel.vertical_kernel_impossible`), so every nonzero kernel
  vector — in particular `V2f f x` — has nonzero `0`-coordinate; hence the
  intersection of the kernel line with the boundary lines is given by the
  smooth formulas `leftPointOfDir`/`rightPointOfDir` below;
* these formulas give the canonical leaf endpoints `uBendA`/`uBendB`
  (`Main0U`), because at `U`-points all nonzero kernel vectors are parallel
  (`kernel_direction_parallel`), and the endpoint formulas are invariant
  under nonzero scaling of the direction.
-/

noncomputable section
namespace Submission.PaperBand

/-- **A nonzero kernel vector at a `U`-point is never vertical**: if `v` is a
nonzero vector in the kernel of the shape operator at the interior point `x`
with `dN f x ≠ 0`, then `v 0 ≠ 0` (the kernel line is not the vertical
direction). -/
lemma kernel_vector_coord0_ne_zero {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x : ℝ²} (hx : x ∈ stripInterior) (hdN : dN f x ≠ 0)
    {v : ℝ²} (hker : dN f x v = 0) (hvne : v ≠ 0) : v 0 ≠ 0 := by
  intro hv0
  -- v is vertical: v = v1 • e₁, and since dN f x v = 0 with v1 ≠ 0, e₁ is a
  -- kernel direction — contradicting `vertical_kernel_impossible`
  have hv1 : v 1 ≠ 0 := by
    intro hv1
    apply hvne
    ext i
    fin_cases i
    · exact hv0
    · exact hv1
  have hlin : dN f x v = (v 1) • (dN f x !₂[0, 1]) := by
    calc
      dN f x v = dN f x ((v 0) • !₂[1, 0] + (v 1) • !₂[0, 1]) := by
        congr 1
        ext i <;> fin_cases i <;> simp [hv0]
      _ = (v 0) • (dN f x !₂[1, 0]) + (v 1) • (dN f x !₂[0, 1]) := by
        rw [map_add, map_smul, map_smul]
      _ = (v 1) • (dN f x !₂[0, 1]) := by rw [hv0]; simp
  have hk1 : dN f x !₂[0, 1] = 0 := by
    have hsmul : (v 1) • (dN f x !₂[0, 1]) = 0 := by
      rwa [hlin] at hker
    exact smul_eq_zero.mp hsmul |>.resolve_left hv1
  exact (vertical_kernel_impossible hf ha hx hdN) hk1

/-- **`V2f` is nonzero at every `U`-point**: at an interior point with
nonzero shape operator there is a crossing kernel direction
(`exists_crossing_kernel_direction`), and `KernelUnit` gives
`V2f f x ≠ 0`. -/
lemma V2f_ne_zero_at_U {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x : ℝ²} (hx : x ∈ stripInterior) (hdN : dN f x ≠ 0) :
    V2f f x ≠ 0 := by
  rcases exists_crossing_kernel_direction hf ha hx hdN with ⟨w, hker, hwne, hw0⟩
  exact V2f_ne_zero_of_kernel_crossing hf hx hdN hw0 hker

/-- **`V2f` has nonzero `0`-coordinate at every `U`-point** (it is a nonzero
kernel vector there, hence non-vertical). -/
lemma V2f_coord0_ne_zero_at_U {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x : ℝ²} (hx : x ∈ stripInterior) (hdN : dN f x ≠ 0) :
    (V2f f x) 0 ≠ 0 := by
  exact kernel_vector_coord0_ne_zero hf ha hx hdN (V2f_mem_ker hf x hx)
    (V2f_ne_zero_at_U hf ha hx hdN)

/-- The intersection of the affine line through `x` in direction `d` (with
`d 0 ≠ 0`) with the boundary line `x0 = 0`. -/
def leftPointOfDir (x d : ℝ²) : ℝ² := x + leftParam x d • d

/-- The intersection of the affine line through `x` in direction `d` (with
`d 0 ≠ 0`) with the boundary line `x0 = 1`. -/
def rightPointOfDir (x d : ℝ²) : ℝ² := x + rightParam x d • d

/-- The left-boundary intersection point has `0`-coordinate `0`. -/
lemma leftPointOfDir_coord0 {x d : ℝ²} (hd0 : d 0 ≠ 0) :
    (leftPointOfDir x d) 0 = 0 := by
  unfold leftPointOfDir leftParam
  rw [ray_coord0]
  field_simp [hd0]
  ring

/-- The right-boundary intersection point has `0`-coordinate `1`. -/
lemma rightPointOfDir_coord0 {x d : ℝ²} (hd0 : d 0 ≠ 0) :
    (rightPointOfDir x d) 0 = 1 := by
  unfold rightPointOfDir rightParam
  rw [ray_coord0]
  field_simp [hd0]
  ring

/-- The left-intersection formula is invariant under nonzero scaling of the
direction. -/
lemma leftPointOfDir_smul {x d : ℝ²} {c : ℝ} (hc : c ≠ 0) (hd0 : d 0 ≠ 0) :
    leftPointOfDir x (c • d) = leftPointOfDir x d := by
  unfold leftPointOfDir leftParam
  congr 1
  rw [smul_smul]
  congr 1
  have hcoord : (c • d) 0 = c * d 0 := by simp
  rw [hcoord]
  field_simp [hc, hd0]

/-- The right-intersection formula is invariant under nonzero scaling of the
direction. -/
lemma rightPointOfDir_smul {x d : ℝ²} {c : ℝ} (hc : c ≠ 0) (hd0 : d 0 ≠ 0) :
    rightPointOfDir x (c • d) = rightPointOfDir x d := by
  unfold rightPointOfDir rightParam
  congr 1
  rw [smul_smul]
  congr 1
  have hcoord : (c • d) 0 = c * d 0 := by simp
  rw [hcoord]
  field_simp [hc, hd0]

/-- The left endpoint of the canonical leaf equals the smooth
left-intersection formula with the direction `uBendDirPos`. -/
lemma uBendA_eq_leftPointOfDir {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x : ℝ²} (hx : x ∈ stripInterior) (hdN : dN f x ≠ 0) :
    uBendA hf ha hx hdN = leftPointOfDir x (uBendDirPos hf ha hx hdN) := by
  rfl

/-- The right endpoint of the canonical leaf equals the smooth
right-intersection formula with the direction `uBendDirPos`. -/
lemma uBendB_eq_rightPointOfDir {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x : ℝ²} (hx : x ∈ stripInterior) (hdN : dN f x ≠ 0) :
    uBendB hf ha hx hdN = rightPointOfDir x (uBendDirPos hf ha hx hdN) := by
  rfl

/-- **`V2f` is parallel to the canonical leaf direction at every `U`-point**
(same kernel line). -/
lemma V2f_parallel_uBendDirPos {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x : ℝ²} (hx : x ∈ stripInterior) (hdN : dN f x ≠ 0) :
    ∃ c : ℝ, V2f f x = c • uBendDirPos hf ha hx hdN := by
  rcases uBendDirPos_spec hf ha hx hdN with ⟨hker, hwne, hwpos⟩
  exact kernel_direction_parallel hf hx hdN hker (V2f_mem_ker hf x hx) hwne

/-- The parallel factor between `V2f` and the canonical direction is
nonzero. -/
lemma V2f_parallel_uBendDirPos_c {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x : ℝ²} (hx : x ∈ stripInterior) (hdN : dN f x ≠ 0) :
    ∃ c : ℝ, c ≠ 0 ∧ V2f f x = c • uBendDirPos hf ha hx hdN := by
  rcases V2f_parallel_uBendDirPos hf ha hx hdN with ⟨c, hc⟩
  refine ⟨c, ?_, hc⟩
  intro hc0
  have : V2f f x = 0 := by
    rw [hc, hc0]
    simp
  exact V2f_ne_zero_at_U hf ha hx hdN this

/-- **The left endpoint of the canonical leaf equals the smooth
left-intersection formula with the mirror kernel field `V2f`**. -/
lemma uBendA_eq_leafLeftEnd {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x : ℝ²} (hx : x ∈ stripInterior) (hdN : dN f x ≠ 0) :
    uBendA hf ha hx hdN = leftPointOfDir x (V2f f x) := by
  rcases V2f_parallel_uBendDirPos_c hf ha hx hdN with ⟨c, hcne, hc⟩
  rcases uBendDirPos_spec hf ha hx hdN with ⟨hker, hwne, hwpos⟩
  calc
    uBendA hf ha hx hdN = leftPointOfDir x (uBendDirPos hf ha hx hdN) :=
      uBendA_eq_leftPointOfDir hf ha hx hdN
    _ = leftPointOfDir x (c • uBendDirPos hf ha hx hdN) := by
      rw [← leftPointOfDir_smul hcne (ne_of_gt hwpos)]
    _ = leftPointOfDir x (V2f f x) := by rw [hc]

/-- **The right endpoint of the canonical leaf equals the smooth
right-intersection formula with the mirror kernel field `V2f`**. -/
lemma uBendB_eq_leafRightEnd {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x : ℝ²} (hx : x ∈ stripInterior) (hdN : dN f x ≠ 0) :
    uBendB hf ha hx hdN = rightPointOfDir x (V2f f x) := by
  rcases V2f_parallel_uBendDirPos_c hf ha hx hdN with ⟨c, hcne, hc⟩
  rcases uBendDirPos_spec hf ha hx hdN with ⟨hker, hwne, hwpos⟩
  calc
    uBendB hf ha hx hdN = rightPointOfDir x (uBendDirPos hf ha hx hdN) :=
      uBendB_eq_rightPointOfDir hf ha hx hdN
    _ = rightPointOfDir x (c • uBendDirPos hf ha hx hdN) := by
      rw [← rightPointOfDir_smul hcne (ne_of_gt hwpos)]
    _ = rightPointOfDir x (V2f f x) := by rw [hc]

/-- **The leaf left endpoint is continuous at every `U`-point** (ambient,
2-dimensional): `x ↦ leftPointOfDir x (V2f f x)` is continuous at interior
`x` with `dN f x ≠ 0` (the mirror kernel field is smooth and never vertical
there). -/
lemma continuousAt_leafLeftEnd {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x₀ : ℝ²} (hx₀ : x₀ ∈ stripInterior) (hU0 : dN f x₀ ≠ 0) :
    ContinuousAt (fun x : ℝ² => leftPointOfDir x (V2f f x)) x₀ := by
  unfold leftPointOfDir leftParam
  have hd0 : (V2f f x₀) 0 ≠ 0 := V2f_coord0_ne_zero_at_U hf ha hx₀ hU0
  have hcV2 : ContinuousAt (V2f f) x₀ := continuousAt_V2f hf x₀ hx₀
  have hcnum : ContinuousAt (fun x : ℝ² => -(x 0)) x₀ := by fun_prop
  have hcden : ContinuousAt (fun x : ℝ² => (V2f f x) 0) x₀ := by
    have hc0 : ContinuousAt (fun z : ℝ² => z 0) (V2f f x₀) := by fun_prop
    exact ContinuousAt.comp (x := x₀) (f := V2f f) (g := fun z : ℝ² => z 0) hc0 hcV2
  have hcdiv : ContinuousAt (fun x : ℝ² => -(x 0) / (V2f f x) 0) x₀ :=
    ContinuousAt.div hcnum hcden hd0
  have hcsmul : ContinuousAt (fun x : ℝ² => (-(x 0) / (V2f f x) 0) • V2f f x) x₀ :=
    ContinuousAt.smul hcdiv hcV2
  have hid : ContinuousAt (fun x : ℝ² => x) x₀ := continuousAt_id
  exact ContinuousAt.add hid hcsmul

/-- **The leaf right endpoint is continuous at every `U`-point** (ambient,
2-dimensional). -/
lemma continuousAt_leafRightEnd {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x₀ : ℝ²} (hx₀ : x₀ ∈ stripInterior) (hU0 : dN f x₀ ≠ 0) :
    ContinuousAt (fun x : ℝ² => rightPointOfDir x (V2f f x)) x₀ := by
  unfold rightPointOfDir rightParam
  have hd0 : (V2f f x₀) 0 ≠ 0 := V2f_coord0_ne_zero_at_U hf ha hx₀ hU0
  have hcV2 : ContinuousAt (V2f f) x₀ := continuousAt_V2f hf x₀ hx₀
  have hcnum : ContinuousAt (fun x : ℝ² => 1 - x 0) x₀ := by fun_prop
  have hcden : ContinuousAt (fun x : ℝ² => (V2f f x) 0) x₀ := by
    have hc0 : ContinuousAt (fun z : ℝ² => z 0) (V2f f x₀) := by fun_prop
    exact ContinuousAt.comp (x := x₀) (f := V2f f) (g := fun z : ℝ² => z 0) hc0 hcV2
  have hcdiv : ContinuousAt (fun x : ℝ² => (1 - x 0) / (V2f f x) 0) x₀ :=
    ContinuousAt.div hcnum hcden hd0
  have hcsmul : ContinuousAt (fun x : ℝ² => ((1 - x 0) / (V2f f x) 0) • V2f f x) x₀ :=
    ContinuousAt.smul hcdiv hcV2
  have hid : ContinuousAt (fun x : ℝ² => x) x₀ := continuousAt_id
  exact ContinuousAt.add hid hcsmul

/-- The centreline lift: `c(y) = (1/2, y)`. -/
def centrePoint (y : ℝ) : ℝ² := !₂[(1 / 2 : ℝ), y]

/-- `(1/2, y)` always lies in the strip interior. -/
lemma centrePoint_mem_stripInterior (y : ℝ) : centrePoint y ∈ stripInterior := by
  rw [stripInterior, centrePoint]
  change (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1
  norm_num

/-- The centreline map is continuous. -/
lemma continuousAt_centrePoint (y₀ : ℝ) : ContinuousAt centrePoint y₀ := by
  unfold centrePoint
  fun_prop

/-- The left endpoint of the leaf through the centreline point `(1/2, y)`,
as a smooth function of `y`. -/
noncomputable def centreLeafLeftEnd (f : ℝ² → ℝ³) (y : ℝ) : ℝ² :=
  leftPointOfDir (centrePoint y) (V2f f (centrePoint y))

/-- The right endpoint of the leaf through the centreline point `(1/2, y)`,
as a smooth function of `y`. -/
noncomputable def centreLeafRightEnd (f : ℝ² → ℝ³) (y : ℝ) : ℝ² :=
  rightPointOfDir (centrePoint y) (V2f f (centrePoint y))

/-- **Continuity of the left leaf endpoint along the centreline**: at a
height `y₀` whose centreline point is in `U`, the map
`y ↦ leftPointOfDir (1/2, y) (V2f f (1/2, y))` is continuous at `y₀`. -/
theorem continuousAt_centreLeafLeftEnd {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y₀ : ℝ} (hU0 : dN f (centrePoint y₀) ≠ 0) :
    ContinuousAt (centreLeafLeftEnd f) y₀ := by
  have hx₀ : centrePoint y₀ ∈ stripInterior := centrePoint_mem_stripInterior y₀
  have hcont2 : ContinuousAt (fun x : ℝ² => leftPointOfDir x (V2f f x)) (centrePoint y₀) :=
    continuousAt_leafLeftEnd hf ha hx₀ hU0
  have hcomp : ContinuousAt (fun y : ℝ => leftPointOfDir (centrePoint y) (V2f f (centrePoint y))) y₀ :=
    ContinuousAt.comp (x := y₀) (f := centrePoint) (g := fun x : ℝ² => leftPointOfDir x (V2f f x))
      hcont2 (continuousAt_centrePoint y₀)
  exact hcomp

/-- **Continuity of the right leaf endpoint along the centreline**. -/
theorem continuousAt_centreLeafRightEnd {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y₀ : ℝ} (hU0 : dN f (centrePoint y₀) ≠ 0) :
    ContinuousAt (centreLeafRightEnd f) y₀ := by
  have hx₀ : centrePoint y₀ ∈ stripInterior := centrePoint_mem_stripInterior y₀
  have hcont2 : ContinuousAt (fun x : ℝ² => rightPointOfDir x (V2f f x)) (centrePoint y₀) :=
    continuousAt_leafRightEnd hf ha hx₀ hU0
  have hcomp : ContinuousAt (fun y : ℝ => rightPointOfDir (centrePoint y) (V2f f (centrePoint y))) y₀ :=
    ContinuousAt.comp (x := y₀) (f := centrePoint) (g := fun x : ℝ² => rightPointOfDir x (V2f f x))
      hcont2 (continuousAt_centrePoint y₀)
  exact hcomp

/-- **The canonical left leaf endpoint through the centreline point equals
the smooth centreline function at `U`-heights**:
`uBendA … (centrePoint y) = centreLeafLeftEnd f y`. -/
lemma centreU_leafLeftEnd_eq_uBendA {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y : ℝ} (hU0 : dN f (centrePoint y) ≠ 0) :
    centreLeafLeftEnd f y = uBendA hf ha (centrePoint_mem_stripInterior y) hU0 := by
  unfold centreLeafLeftEnd
  rw [← uBendA_eq_leafLeftEnd hf ha (centrePoint_mem_stripInterior y) hU0]

/-- **The canonical right leaf endpoint through the centreline point equals
the smooth centreline function at `U`-heights**. -/
lemma centreU_leafRightEnd_eq_uBendB {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y : ℝ} (hU0 : dN f (centrePoint y) ≠ 0) :
    centreLeafRightEnd f y = uBendB hf ha (centrePoint_mem_stripInterior y) hU0 := by
  unfold centreLeafRightEnd
  rw [← uBendB_eq_leafRightEnd hf ha (centrePoint_mem_stripInterior y) hU0]

/-- The **chord direction** of the leaf through the centreline point
`(1/2, y)`: the vector from its left to its right boundary endpoint.  Its
`0`-coordinate is `1` (right endpoint on `x0 = 1`, left on `x0 = 0`), so it
is nonzero, `‖·‖ ≥ 1`, and it points from the `x0 = 0` side to the
`x0 = 1` side — the positive orientation of the leaf. -/
noncomputable def centreLeafDirVec (f : ℝ² → ℝ³) (y : ℝ) : ℝ² :=
  centreLeafRightEnd f y - centreLeafLeftEnd f y

/-- The **unit chord direction** of the leaf through `(1/2, y)`: the
normalization of `centreLeafDirVec`, wherever the chord is nondegenerate
(i.e. wherever `centreLeafDirVec ≠ 0`, in particular at `U`-heights). -/
noncomputable def centreLeafUnitDir (f : ℝ² → ℝ³) (y : ℝ) : ℝ² :=
  (‖centreLeafDirVec f y‖⁻¹) • centreLeafDirVec f y

/-- At a `U`-height the chord-direction's `0`-coordinate is `1` (the right
endpoint lies on `x0 = 1`, the left on `x0 = 0`). -/
lemma centreLeafDirVec_coord0 {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y : ℝ} (hU0 : dN f (centrePoint y) ≠ 0) :
    (centreLeafDirVec f y) 0 = 1 := by
  unfold centreLeafDirVec
  have hR : (centreLeafRightEnd f y) 0 = 1 := by
    unfold centreLeafRightEnd
    exact rightPointOfDir_coord0 (V2f_coord0_ne_zero_at_U hf ha (centrePoint_mem_stripInterior y) hU0)
  have hL : (centreLeafLeftEnd f y) 0 = 0 := by
    unfold centreLeafLeftEnd
    exact leftPointOfDir_coord0 (V2f_coord0_ne_zero_at_U hf ha (centrePoint_mem_stripInterior y) hU0)
  simp [hR, hL]

/-- The chord direction is nonzero at a `U`-height. -/
lemma centreLeafDirVec_ne_zero {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y : ℝ} (hU0 : dN f (centrePoint y) ≠ 0) :
    centreLeafDirVec f y ≠ 0 := by
  intro hz
  have hc : (centreLeafDirVec f y) 0 = 0 := congrArg (fun z : ℝ² => z 0) hz
  rw [centreLeafDirVec_coord0 hf ha hU0] at hc
  norm_num at hc

/-- The norm of the chord direction is at least `1` at a `U`-height. -/
lemma one_le_norm_centreLeafDirVec {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y : ℝ} (hU0 : dN f (centrePoint y) ≠ 0) :
    (1 : ℝ) ≤ ‖centreLeafDirVec f y‖ := by
  have hc : (centreLeafDirVec f y) 0 = 1 := centreLeafDirVec_coord0 hf ha hU0
  have hsq : (1 : ℝ) ≤ ‖centreLeafDirVec f y‖ ^ 2 := by
    rw [norm_sq_coord_sum]
    rw [hc]
    nlinarith [sq_nonneg ((centreLeafDirVec f y) 1)]
  have hnn : 0 ≤ ‖centreLeafDirVec f y‖ := norm_nonneg _
  nlinarith

/-- The unit chord direction has norm `1` at a `U`-height. -/
lemma norm_centreLeafUnitDir {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y : ℝ} (hU0 : dN f (centrePoint y) ≠ 0) :
    ‖centreLeafUnitDir f y‖ = 1 := by
  unfold centreLeafUnitDir
  have hnorm : ‖centreLeafDirVec f y‖ ≠ 0 := by
    exact ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
      (one_le_norm_centreLeafDirVec hf ha hU0))
  calc
    ‖(‖centreLeafDirVec f y‖⁻¹) • centreLeafDirVec f y‖
        = ‖(‖centreLeafDirVec f y‖⁻¹ : ℝ)‖ * ‖centreLeafDirVec f y‖ := by rw [norm_smul]
    _ = ‖centreLeafDirVec f y‖⁻¹ * ‖centreLeafDirVec f y‖ := by
      congr 1
      rw [Real.norm_eq_abs]
      exact abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))
    _ = 1 := by field_simp [hnorm]

/-- The chord direction is continuous in the height at every `U`-height. -/
theorem continuousAt_centreLeafDirVec {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y₀ : ℝ} (hU0 : dN f (centrePoint y₀) ≠ 0) :
    ContinuousAt (centreLeafDirVec f) y₀ := by
  unfold centreLeafDirVec
  exact (continuousAt_centreLeafRightEnd hf ha hU0).sub (continuousAt_centreLeafLeftEnd hf ha hU0)

/-- The **unit chord direction is continuous in the height** at every
`U`-height (denominator bounded away from zero). -/
theorem continuousAt_centreLeafUnitDir {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y₀ : ℝ} (hU0 : dN f (centrePoint y₀) ≠ 0) :
    ContinuousAt (centreLeafUnitDir f) y₀ := by
  unfold centreLeafUnitDir
  have hnorm_ne : ‖centreLeafDirVec f y₀‖ ≠ 0 := by
    exact ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
      (one_le_norm_centreLeafDirVec hf ha hU0))
  have hcont_norm : ContinuousAt (fun y : ℝ => ‖centreLeafDirVec f y‖) y₀ :=
    (continuousAt_centreLeafDirVec hf ha hU0).norm
  have hcont_inv : ContinuousAt (fun y : ℝ => (‖centreLeafDirVec f y‖⁻¹ : ℝ)) y₀ :=
    hcont_norm.inv₀ hnorm_ne
  exact hcont_inv.smul (continuousAt_centreLeafDirVec hf ha hU0)

/-- The chord direction lies in the kernel of the shape operator along the
centreline at `U`-heights (it is a scalar multiple of the kernel vector
`V2f`). -/
lemma centreLeafDirVec_mem_ker {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y : ℝ} (hU0 : dN f (centrePoint y) ≠ 0) :
    dN f (centrePoint y) (centreLeafDirVec f y) = 0 := by
  unfold centreLeafDirVec centreLeafRightEnd centreLeafLeftEnd
  unfold rightPointOfDir leftPointOfDir
  have hd : ((centrePoint y) + rightParam (centrePoint y) (V2f f (centrePoint y))
      • V2f f (centrePoint y)) - ((centrePoint y) + leftParam (centrePoint y)
        (V2f f (centrePoint y)) • V2f f (centrePoint y))
      = (rightParam (centrePoint y) (V2f f (centrePoint y)) -
          leftParam (centrePoint y) (V2f f (centrePoint y))) • V2f f (centrePoint y) := by
    calc
      (centrePoint y) + rightParam (centrePoint y) (V2f f (centrePoint y))
          • V2f f (centrePoint y) - ((centrePoint y) + leftParam (centrePoint y)
            (V2f f (centrePoint y)) • V2f f (centrePoint y))
          = rightParam (centrePoint y) (V2f f (centrePoint y)) • V2f f (centrePoint y)
            - leftParam (centrePoint y) (V2f f (centrePoint y)) • V2f f (centrePoint y) := by
            abel
      _ = (rightParam (centrePoint y) (V2f f (centrePoint y)) -
            leftParam (centrePoint y) (V2f f (centrePoint y))) • V2f f (centrePoint y) := by
            rw [← sub_smul]
  rw [hd]
  rw [map_smul]
  simp [V2f_mem_ker hf (centrePoint y) (centrePoint_mem_stripInterior y)]

/-- The chord direction through a centreline `U`-point is parallel to the
canonical leaf direction there (a nonzero scalar multiple). -/
lemma centreLeafDirVec_parallel_wpos {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y : ℝ} (hU0 : dN f (centrePoint y) ≠ 0) :
    ∃ c : ℝ, centreLeafDirVec f y = c • uBendDirPos hf ha (centrePoint_mem_stripInterior y) hU0 := by
  rcases uBendDirPos_spec hf ha (centrePoint_mem_stripInterior y) hU0 with ⟨hker, hwne, hwpos⟩
  exact kernel_direction_parallel hf (centrePoint_mem_stripInterior y) hU0 hker
    (centreLeafDirVec_mem_ker hf ha hU0) hwne

/-- The parallel factor between the chord direction and the canonical
direction is nonzero. -/
lemma centreLeafDirVec_parallel_wpos_c {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y : ℝ} (hU0 : dN f (centrePoint y) ≠ 0) :
    ∃ c : ℝ, c ≠ 0 ∧ centreLeafDirVec f y = c • uBendDirPos hf ha (centrePoint_mem_stripInterior y) hU0 := by
  rcases centreLeafDirVec_parallel_wpos hf ha hU0 with ⟨c, hc⟩
  refine ⟨c, ?_, hc⟩
  intro hc0
  have : centreLeafDirVec f y = 0 := by
    rw [hc, hc0]
    simp
  exact centreLeafDirVec_ne_zero hf ha hU0 this

/-- The chord direction has positive `0`-coordinate (`1`), so the parallel
factor to the positive canonical direction is positive, and the **unit
chord direction equals the normalized canonical direction**. -/
lemma centreLeafUnitDir_eq_wposUnit {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y : ℝ} (hU0 : dN f (centrePoint y) ≠ 0) :
    centreLeafUnitDir f y =
      (‖uBendDirPos hf ha (centrePoint_mem_stripInterior y) hU0‖⁻¹) •
        uBendDirPos hf ha (centrePoint_mem_stripInterior y) hU0 := by
  rcases centreLeafDirVec_parallel_wpos_c hf ha hU0 with ⟨c, hcne, hc⟩
  rcases uBendDirPos_spec hf ha (centrePoint_mem_stripInterior y) hU0 with ⟨hker, hwne, hwpos⟩
  let w : ℝ² := uBendDirPos hf ha (centrePoint_mem_stripInterior y) hU0
  change centreLeafUnitDir f y = (‖w‖⁻¹) • w
  have hc0 : (centreLeafDirVec f y) 0 = c * w 0 := by
    rw [hc]
    simp [w]
  have hc1 : (centreLeafDirVec f y) 0 = 1 := centreLeafDirVec_coord0 hf ha hU0
  have hcpos : 0 < c := by
    have hmul : c * w 0 = 1 := by
      rw [← hc0]
      exact hc1
    exact pos_of_mul_pos_left (by rw [hmul]; norm_num) (le_of_lt (by simpa [w] using hwpos))
  have hw0 : w ≠ 0 := by simpa [w] using hwne
  have hwnorm : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw0
  unfold centreLeafUnitDir
  rw [hc]
  have hnormc : ‖c • w‖ = c * ‖w‖ := by
    rw [norm_smul]
    rw [Real.norm_eq_abs]
    rw [abs_of_nonneg (le_of_lt hcpos)]
  rw [hnormc]
  rw [smul_smul]
  congr 1
  field_simp [hcne, hwnorm]

/-- The **image unit direction of the bend through the centreline point**
`(1/2, y)`: the normalization of the image displacement between the images
of its two boundary endpoints. -/
noncomputable def centreBendImageDir (f : ℝ² → ℝ³) (y : ℝ) : ℝ³ :=
  (‖f (centreLeafRightEnd f y) - f (centreLeafLeftEnd f y)‖⁻¹) •
    (f (centreLeafRightEnd f y) - f (centreLeafLeftEnd f y))

/-- The **unit tangent of the preimage leaf direction pushed to the image**:
`fderiv f (1/2, y)` applied to the unit chord direction.  By the isometry
this is the image unit direction of the bend. -/
noncomputable def centreTangentDir (f : ℝ² → ℝ³) (y : ℝ) : ℝ³ :=
  fderiv ℝ f (centrePoint y) (centreLeafUnitDir f y)

/-- **The unit tangent is the fderiv-image of the unit preimage direction**:
at a `U`-height the bend image unit direction equals `centreTangentDir`. -/
lemma centreBendImageDir_eq_tangent {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y : ℝ} (hU0 : dN f (centrePoint y) ≠ 0) :
    centreBendImageDir f y = centreTangentDir f y := by
  unfold centreBendImageDir centreTangentDir
  rw [centreU_leafRightEnd_eq_uBendB hf ha hU0, centreU_leafLeftEnd_eq_uBendA hf ha hU0]
  rw [canonicalImageUnitDir_eq_tangent hf ha (centrePoint_mem_stripInterior y) hU0]
  rw [← centreLeafUnitDir_eq_wposUnit hf ha hU0]

/-- The map `y ↦ fderiv f (centrePoint y) v` is continuous at a `U`-height
for a FIXED direction `v` (the centreline point is interior). -/
lemma continuousAt_centrePoint_fderiv_apply {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) {y₀ : ℝ} (v : ℝ²) :
    ContinuousAt (fun y : ℝ => fderiv ℝ f (centrePoint y) v) y₀ := by
  have hdf : ContinuousAt (fun q : ℝ² => fderiv ℝ f q v) (centrePoint y₀) :=
    (differentiableAt_fderiv_apply hf (centrePoint y₀) (centrePoint_mem_stripInterior y₀) v).continuousAt
  exact ContinuousAt.comp (x := y₀) (f := centrePoint) (g := fun q : ℝ² => fderiv ℝ f q v)
    hdf (continuousAt_centrePoint y₀)

/-- **The unit tangent direction is continuous in the height** at every
`U`-height: `y ↦ fderiv f (1/2, y) (centreLeafUnitDir f y)` is continuous
(fderiv is smooth on the interior; the unit chord direction is continuous
and bounded). -/
theorem continuousAt_centreTangentDir {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y₀ : ℝ} (hU0 : dN f (centrePoint y₀) ≠ 0) :
    ContinuousAt (centreTangentDir f) y₀ := by
  unfold centreTangentDir
  have hcontU : ContinuousAt (centreLeafUnitDir f) y₀ := continuousAt_centreLeafUnitDir hf ha hU0
  have hcU0 : ContinuousAt (fun y : ℝ => (centreLeafUnitDir f y) 0) y₀ := by
    have hc0 : ContinuousAt (fun z : ℝ² => z 0) (centreLeafUnitDir f y₀) := by fun_prop
    exact ContinuousAt.comp (x := y₀) (f := centreLeafUnitDir f) (g := fun z : ℝ² => z 0) hc0 hcontU
  have hcU1 : ContinuousAt (fun y : ℝ => (centreLeafUnitDir f y) 1) y₀ := by
    have hc1 : ContinuousAt (fun z : ℝ² => z 1) (centreLeafUnitDir f y₀) := by fun_prop
    exact ContinuousAt.comp (x := y₀) (f := centreLeafUnitDir f) (g := fun z : ℝ² => z 1) hc1 hcontU
  have hd0 : ContinuousAt (fun y : ℝ => fderiv ℝ f (centrePoint y) !₂[1, 0]) y₀ :=
    continuousAt_centrePoint_fderiv_apply hf !₂[1, 0]
  have hd1 : ContinuousAt (fun y : ℝ => fderiv ℝ f (centrePoint y) !₂[0, 1]) y₀ :=
    continuousAt_centrePoint_fderiv_apply hf !₂[0, 1]
  have hterm0 : ContinuousAt
      (fun y : ℝ => (centreLeafUnitDir f y) 0 • fderiv ℝ f (centrePoint y) !₂[1, 0]) y₀ :=
    ContinuousAt.smul hcU0 hd0
  have hterm1 : ContinuousAt
      (fun y : ℝ => (centreLeafUnitDir f y) 1 • fderiv ℝ f (centrePoint y) !₂[0, 1]) y₀ :=
    ContinuousAt.smul hcU1 hd1
  have hmain : ContinuousAt
      (fun y : ℝ => (centreLeafUnitDir f y) 0 • fderiv ℝ f (centrePoint y) !₂[1, 0]
        + (centreLeafUnitDir f y) 1 • fderiv ℝ f (centrePoint y) !₂[0, 1]) y₀ :=
    ContinuousAt.add hterm0 hterm1
  exact ContinuousAt.congr_of_eventuallyEq hmain (by
    filter_upwards with y
    exact fderiv_apply_vec_decomp (f := f) (centrePoint y) (centreLeafUnitDir f y))

/-- **The bend image unit direction is continuous in the height** at every
`U`-height: at such heights it equals `centreTangentDir`
(`centreBendImageDir_eq_tangent`), which is continuous, and nearby heights
are `U`-heights (continuity of `dN`). -/
theorem continuousAt_centreBendImageDir {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y₀ : ℝ} (hU0 : dN f (centrePoint y₀) ≠ 0) :
    ContinuousAt (centreBendImageDir f) y₀ := by
  have htg : ContinuousAt (centreTangentDir f) y₀ := continuousAt_centreTangentDir hf ha hU0
  -- dN is continuous along the centreline (contDiffOn_dN on the interior),
  -- so nearby heights are U-heights
  have hcontDN : ContinuousAt (fun z : ℝ² => dN f z) (centrePoint y₀) :=
    ContinuousOn.continuousAt (ContDiffOn.continuousOn (contDiffOn_dN hf))
      (IsOpen.mem_nhds stripInterior_isOpen (centrePoint_mem_stripInterior y₀))
  have hcDN : ContinuousAt (fun y : ℝ => dN f (centrePoint y)) y₀ :=
    ContinuousAt.comp (x := y₀) (f := centrePoint) (g := fun z : ℝ² => dN f z)
      hcontDN (continuousAt_centrePoint y₀)
  have hNev : (fun y : ℝ => dN f (centrePoint y) ≠ 0) ∈ 𝓝 y₀ := by
    exact hcDN.preimage_mem_nhds (isOpen_ne.mem_nhds hU0)
  -- equality of the two functions on that U-neighbourhood
  have heq : centreBendImageDir f =ᶠ[𝓝 y₀] centreTangentDir f := by
    rw [Filter.EventuallyEq]
    exact eventually_of_mem hNev (fun y hy => centreBendImageDir_eq_tangent hf ha hy)
  exact ContinuousAt.congr_of_eventuallyEq htg heq

end Submission.PaperBand
import Submission.Work.LeafContinuity
import Submission.Work.Main0Interface
import Submission.Work.DeckFrame
import Submission.Work.BendArcFacts

open OptimalMoebius Topology ContDiff
open scoped BigOperators Matrix Topology Metric
set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# Centreline-U leaf family: the U-part of the bend foliation (GREEN)

For every centreline height whose point `(1/2, y)` is a `U`-point
(`dN ≠ 0`) the canonical U-bend machinery
(`Main0U.uBendA/uBendB`, `BendImage`, `LeafContinuity`) provides the leaf:
a pre-bend chord from the left to the right boundary line through
`(1/2, y)`.  This file bundles that data as continuous functions of the
height over the OPEN set `UHeight a f = {y | dN f (centrePoint y) ≠ 0}`,
with the `BendData` interface properties that `BandFoliation` requires on
its U-portion: endpoint boundary coordinates, the centreline-crossing
condition (`centreHeight = y`), the pre-bend image-isometry property, and
continuity of the endpoints.  The remaining `BandFoliation` ingredients
(deck flip under `y ↦ y+a`, and the leaves through FLAT centreline points)
are separate, documented as open items (deck transfer + flat-component
chord foliation).

The continuity lemmas rest on `LeafContinuity`: the canonical endpoints
equal the smooth centreline functions `centreLeafLeftEnd/RightEnd`
(`centreU_leafLeftEnd_eq_uBendA/B`), which are continuous at every
`U`-height (`continuousAt_centreLeafLeftEnd/RightEnd`).
-/

noncomputable section
namespace Submission

open Submission.PaperBand

/-- The set of centreline heights whose centreline point is a `U`-point
(`dN ≠ 0`): the centreline portion of `U`. -/
def UHeight (a : ℝ) (f : ℝ² → ℝ³) : Set ℝ := {y : ℝ | dN f (centrePoint y) ≠ 0}

/-- Membership in `UHeight`. -/
lemma mem_UHeight {a : ℝ} {f : ℝ² → ℝ³} {y : ℝ} :
    y ∈ UHeight a f ↔ dN f (centrePoint y) ≠ 0 := by
  rfl

/-- The map `y ↦ dN f (1/2, y)` is continuous (composition of the smooth
shape operator on the strip interior with the centreline map). -/
lemma continuousAt_dN_centreline {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (y₀ : ℝ) : ContinuousAt (fun y : ℝ => dN f (centrePoint y)) y₀ := by
  have hdN : ContinuousOn (fun x : ℝ² => dN f x) stripInterior :=
    (contDiffOn_dN hf).continuousOn
  have hcc : ContinuousAt centrePoint y₀ := continuousAt_centrePoint y₀
  -- centrePoint y₀ ∈ stripInterior, so continuous-on-strip + continuous-into-strip composes
  have hval : centrePoint y₀ ∈ stripInterior := centrePoint_mem_stripInterior y₀
  have hdNat : ContinuousAt (fun x : ℝ² => dN f x) (centrePoint y₀) :=
    (ContinuousOn.continuousAt hdN (IsOpen.mem_nhds stripInterior_isOpen hval))
  exact hdNat.comp hcc

/-- `UHeight` is open (preimage of `{0}ᶜ` under a continuous map). -/
lemma isOpen_UHeight {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    IsOpen (UHeight a f) := by
  unfold UHeight
  have hc : Continuous (fun y : ℝ => dN f (centrePoint y)) := by
    exact continuous_iff_continuousAt.mpr (continuousAt_dN_centreline hf)
  -- {L | L ≠ 0} is open in the space of continuous linear maps
  have hone : IsOpen ({L : ℝ² →L[ℝ] ℝ³ | L ≠ 0}) := isOpen_ne
  exact isOpen_ne.preimage hc

/-- Left endpoint of the canonical U-leaf through the centreline point
`(1/2, y)` at a `U`-height `y`. -/
noncomputable def uHeightA {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (y : UHeight a f) : ℝ² :=
  uBendA hf ha (centrePoint_mem_stripInterior y.1) y.2

/-- Right endpoint of the canonical U-leaf through `(1/2, y)` at a
`U`-height `y`. -/
noncomputable def uHeightB {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (y : UHeight a f) : ℝ² :=
  uBendB hf ha (centrePoint_mem_stripInterior y.1) y.2

/-- The left endpoint lies on the left boundary line `x0 = 0`. -/
lemma uHeightA_left_coord {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (y : UHeight a f) : (uHeightA hf ha y) 0 = 0 := by
  unfold uHeightA
  have h := uBendA_leftEdge hf ha (centrePoint_mem_stripInterior y.1) y.2
  -- h : uBendA … ∈ leftEdge = {x | x 0 = 0}
  rw [leftEdge] at h
  simpa using h

/-- The right endpoint lies on the right boundary line `x0 = 1`. -/
lemma uHeightB_right_coord {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (y : UHeight a f) : (uHeightB hf ha y) 0 = 1 := by
  unfold uHeightB
  have h := uBendB_rightEdge hf ha (centrePoint_mem_stripInterior y.1) y.2
  rw [rightEdge] at h
  simpa using h

/-- The canonical U-leaf through the centreline point `(1/2, y)` as a
`BendData` chord (left endpoint on `x0 = 0`, right on `x0 = 1`). -/
noncomputable def uHeightBend {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (y : UHeight a f) : BendData where
  A := uHeightA hf ha y
  B := uHeightB hf ha y
  left_coord := uHeightA_left_coord hf ha y
  right_coord := uHeightB_right_coord hf ha y

/-- For `x` on the centreline the two boundary parameters of the leaf line
cancel: `leftParam + rightParam = 0`. -/
lemma leftParam_add_rightParam_centre {x w : ℝ²} (hx0 : x 0 = 1 / 2) (hw0 : w 0 ≠ 0) :
    leftParam x w + rightParam x w = 0 := by
  unfold leftParam rightParam
  rw [hx0]
  field_simp [hw0]
  ring

/-- The canonical U-leaf through `(1/2, y)` crosses the centreline exactly
at its midpoint, whose height is `y`: `(A1 + B1) / 2 = y`. -/
lemma uHeightBend_centre {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (y : UHeight a f) : (uHeightBend hf ha y).centreHeight = y.1 := by
  unfold BendData.centreHeight
  unfold uHeightBend
  let x : ℝ² := centrePoint y.1
  let w : ℝ² := uBendDirPos hf ha (centrePoint_mem_stripInterior y.1) y.2
  have hx1 : x 1 = y.1 := by simp [x, centrePoint]
  have hw0 : w 0 ≠ 0 := (uBendDirPos_spec hf ha (centrePoint_mem_stripInterior y.1) y.2).2.2.ne'
  have hsum0 : leftParam x w + rightParam x w = 0 :=
    leftParam_add_rightParam_centre (by simp [x, centrePoint]) hw0
  have hA : uBendA hf ha (centrePoint_mem_stripInterior y.1) y.2 = x + leftParam x w • w := by
    rfl
  have hB : uBendB hf ha (centrePoint_mem_stripInterior y.1) y.2 = x + rightParam x w • w := by
    rfl
  -- A + B = 2x, hence (A1+B1)/2 = x1 = y
  have hsum : (uHeightA hf ha y) 1 + (uHeightB hf ha y) 1 = 2 * y.1 := by
    unfold uHeightA uHeightB
    rw [hA, hB]
    have hc0 : (x + leftParam x w • w) 1 = x 1 + leftParam x w * w 1 := by simp
    have hc1 : (x + rightParam x w • w) 1 = x 1 + rightParam x w * w 1 := by simp
    rw [hc0, hc1, hx1]
    have hlin : 2 * y.1 + (leftParam x w + rightParam x w) * w 1 = 2 * y.1 := by
      rw [hsum0]
      ring
    nlinarith
  field_simp [show (2 : ℝ) ≠ 0 by norm_num]
  linarith

/-- The image of the canonical U-leaf is an isometric straight segment:
`‖f B − f A‖ = ‖B − A‖` (the pre-bend property). -/
lemma uHeightBend_preBend {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (y : UHeight a f) :
    ‖f ((uHeightBend hf ha y).B) - f ((uHeightBend hf ha y).A)‖ =
    ‖(uHeightBend hf ha y).B - (uHeightBend hf ha y).A‖ := by
  unfold uHeightBend uHeightA uHeightB
  exact bend_length_eq hf ha (centrePoint_mem_stripInterior y.1) y.2

/-- `uHeightA` is continuous as a function of the height over `UHeight`. -/
lemma continuous_uHeightA {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) : Continuous (fun y : UHeight a f => uHeightA hf ha y) := by
  -- uHeightA = centreLeafLeftEnd f ∘ val
  have h : (fun y : UHeight a f => uHeightA hf ha y) =
      fun y : UHeight a f => centreLeafLeftEnd f y.1 := by
    funext y
    exact (centreU_leafLeftEnd_eq_uBendA hf ha y.2).symm
  rw [h]
  rw [continuous_iff_continuousAt]
  intro y₀
  have hc : ContinuousAt (centreLeafLeftEnd f) y₀.1 :=
    continuousAt_centreLeafLeftEnd hf ha y₀.2
  have hval : ContinuousAt (fun y : UHeight a f => (y : ℝ)) y₀ :=
    continuousAt_subtype_val
  exact hc.comp hval

/-- `uHeightB` is continuous as a function of the height over `UHeight`. -/
lemma continuous_uHeightB {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) : Continuous (fun y : UHeight a f => uHeightB hf ha y) := by
  have h : (fun y : UHeight a f => uHeightB hf ha y) =
      fun y : UHeight a f => centreLeafRightEnd f y.1 := by
    funext y
    exact (centreU_leafRightEnd_eq_uBendB hf ha y.2).symm
  rw [h]
  rw [continuous_iff_continuousAt]
  intro y₀
  have hc : ContinuousAt (centreLeafRightEnd f) y₀.1 :=
    continuousAt_centreLeafRightEnd hf ha y₀.2
  have hval : ContinuousAt (fun y : UHeight a f => (y : ℝ)) y₀ :=
    continuousAt_subtype_val
  exact hc.comp hval


/-! ## The deck flip of the canonical centreline U-leaf -/

/-- The deck map shifts the centreline point: `(1/2, y+a) = period a (1/2, y)`. -/
lemma centrePoint_period (a : ℝ) (y : ℝ) : centrePoint (y + a) = period a (centrePoint y) := by
  ext i <;> fin_cases i <;> simp [centrePoint, period] <;> norm_num

/-- `UHeight` is invariant under the deck: `y+a` is a `U`-height iff `y` is
(the shape operator vanishes at `period x` iff it vanishes at `x`). -/
lemma mem_UHeight_add_period {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (y : ℝ) : y + a ∈ UHeight a f ↔ y ∈ UHeight a f := by
  rw [mem_UHeight, mem_UHeight]
  rw [centrePoint_period a y]
  exact dN_ne_zero_period_iff hf (centrePoint_mem_stripInterior y)

/-- The height `y+a` (itself a `U`-height) as a `UHeight` element. -/
noncomputable def uHeightShift {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (y : UHeight a f) : UHeight a f := ⟨y.1 + a, (mem_UHeight_add_period hf y.1).2 y.2⟩

/-- **Deck flip of the left endpoint**: the canonical U-leaf through
`(1/2, y+a)` starts at the period image of the right endpoint of the leaf
through `(1/2, y)`: `A (y+a) = period a (B y)`. -/
lemma uHeightA_period {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (y : UHeight a f) :
    uHeightA hf ha (uHeightShift hf y) = period a (uHeightB hf ha y) := by
  let x : ℝ² := centrePoint y.1
  have hx : x ∈ stripInterior := centrePoint_mem_stripInterior y.1
  have hxp : period a x ∈ stripInterior := period_mem_stripInterior a hx
  have hd0 : (V2f f x) 0 ≠ 0 := V2f_coord0_ne_zero_at_U hf ha hx y.2
  change uBendA hf ha (centrePoint_mem_stripInterior (y.1 + a))
      ((mem_UHeight_add_period hf y.1).2 y.2) = period a (uBendB hf ha (centrePoint_mem_stripInterior y.1) y.2)
  calc
    uBendA hf ha (centrePoint_mem_stripInterior (y.1 + a))
        ((mem_UHeight_add_period hf y.1).2 y.2)
        = leftPointOfDir (centrePoint (y.1 + a)) (V2f f (centrePoint (y.1 + a))) := by
          exact uBendA_eq_leafLeftEnd hf ha (centrePoint_mem_stripInterior (y.1 + a))
            ((mem_UHeight_add_period hf y.1).2 y.2)
    _ = leftPointOfDir (period a (centrePoint y.1)) (V2f f (period a (centrePoint y.1))) := by
          rw [centrePoint_period a y.1]
    _ = leftPointOfDir (period a x) (V2f f (period a x)) := by rfl
    _ = leftPointOfDir (period a x) (deckFlip (V2f f x)) := by
          rw [V2f_deck_flip hf hx]
    _ = period a (rightPointOfDir x (V2f f x)) := leftPointOfDir_period_deckFlip a hd0
    _ = period a (uBendB hf ha (centrePoint_mem_stripInterior y.1) y.2) := by
          rw [← uBendB_eq_leafRightEnd hf ha (centrePoint_mem_stripInterior y.1) y.2]

/-- **Deck flip of the right endpoint**: `B (y+a) = period a (A y)`. -/
lemma uHeightB_period {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (y : UHeight a f) :
    uHeightB hf ha (uHeightShift hf y) = period a (uHeightA hf ha y) := by
  let x : ℝ² := centrePoint y.1
  have hx : x ∈ stripInterior := centrePoint_mem_stripInterior y.1
  have hxp : period a x ∈ stripInterior := period_mem_stripInterior a hx
  have hd0 : (V2f f x) 0 ≠ 0 := V2f_coord0_ne_zero_at_U hf ha hx y.2
  change uBendB hf ha (centrePoint_mem_stripInterior (y.1 + a))
      ((mem_UHeight_add_period hf y.1).2 y.2) = period a (uBendA hf ha (centrePoint_mem_stripInterior y.1) y.2)
  calc
    uBendB hf ha (centrePoint_mem_stripInterior (y.1 + a))
        ((mem_UHeight_add_period hf y.1).2 y.2)
        = rightPointOfDir (centrePoint (y.1 + a)) (V2f f (centrePoint (y.1 + a))) := by
          exact uBendB_eq_leafRightEnd hf ha (centrePoint_mem_stripInterior (y.1 + a))
            ((mem_UHeight_add_period hf y.1).2 y.2)
    _ = rightPointOfDir (period a (centrePoint y.1)) (V2f f (period a (centrePoint y.1))) := by
          rw [centrePoint_period a y.1]
    _ = rightPointOfDir (period a x) (V2f f (period a x)) := by rfl
    _ = rightPointOfDir (period a x) (deckFlip (V2f f x)) := by
          rw [V2f_deck_flip hf hx]
    _ = period a (leftPointOfDir x (V2f f x)) := rightPointOfDir_period_deckFlip a hd0
    _ = period a (uBendA hf ha (centrePoint_mem_stripInterior y.1) y.2) := by
          rw [← uBendA_eq_leafLeftEnd hf ha (centrePoint_mem_stripInterior y.1) y.2]

/-- **The canonical U-leaf satisfies the `BandFoliation` deck field on the
U-heights**: `chord (y+a)` is the period-flip of `chord y` (endpoints
swapped, `uHeightBend (y+a) = period a (uHeightBend y)` with the A/B swap). -/
lemma uHeightBend_deck {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (y : UHeight a f) :
    (uHeightBend hf ha (uHeightShift hf y)).A = period a (uHeightBend hf ha y).B ∧
    (uHeightBend hf ha (uHeightShift hf y)).B = period a (uHeightBend hf ha y).A := by
  change uHeightA hf ha (uHeightShift hf y) = period a (uHeightB hf ha y) ∧
    uHeightB hf ha (uHeightShift hf y) = period a (uHeightA hf ha y)
  exact ⟨uHeightA_period hf ha y, uHeightB_period hf ha y⟩

end Submission

import Submission.Work.Main0Interface
import Submission.Commons.Topology.BorsukUlam.exists_perp_coplanar_pair
import Submission.PaperBand.EmbeddingFacts
import Submission.Work.BendArcFacts

open OptimalMoebius Topology ContDiff
open scoped BigOperators Matrix Topology Metric
set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# The f-relative band-foliation interface for Lemma T (WORK IN PROGRESS)

`Main0Interface.FoliationData a` is a PREIMAGE-only continuous family of
straight chords through the centreline points with the deck symmetry.  As
`Main0Interface.lemmaT_target_false_for_horizontal` shows, that interface
is too weak for Lemma T: it carries no image geometry, so e.g. the
horizontal foliation at `a = 2` (all image directions parallel) cannot be
excluded even though it can never come from an embedded band.

This file adds the f-relative layer that fixes the design:

* `BandFoliation a f hf` — a continuous family of pre-bend chords through
  every centreline point of the ACTUAL embedded band `f`, with the deck
  symmetry AND the pre-bend property (each chord's image is an isometric
  straight segment: `‖f B − f A‖ = ‖B − A‖`).  Prop main0 will instantiate
  this from the U-bend / flat-chord machinery.
* Derived IMAGE data (the only data Lemma T's F-map needs):
  `imageDir F y` — the unit image direction of the leaf through
  `(1/2, y)`;  `imageMid F y` — its image midpoint `f(1/2,y)`.
  The deck symmetry forces the crucial ODDNESS `imageDir (y+a) = −imageDir y`
  (exactly what the horizontal counterexample violates) and the
  PERIODICITY `imageMid (y+a) = imageMid y`, both derived here (zero
  `sorry`).
* `lemmaT_tpattern` — PROVED (zero `sorry`): from the f-relative
  foliation, two leaves (at centreline heights `y` and `y+δ`, `0<δ<a`,
  hence distinct) with perpendicular directions and coplanar midpoints —
  the T-pattern.  Proof: direct application of the fleet-proved topological
  core `Commons.Topology.BorsukUlam.exists_perp_coplanar_pair` (continuous
  odd unit `u`, continuous periodic `m` ⟹ such a pair) to
  `u := imageDir F`, `m := imageMid F`.

Open design points (documented for the next sessions):
* leaf pairwise DISJOINTNESS (the "embedded" part of the T-pattern, and
  needed later by Lemma G's cut-open argument) is a further property of a
  genuine foliation; it is NOT in this interface yet — it will be supplied
  by Prop main0 (disjoint or equal canonical segments) and consumed at the
  Lemma-G assembly, not by Lemma T itself.
* the leaf family must be "complete" (through every centreline point) and
  continuous — exactly Prop main0's content.
-/

noncomputable section
namespace Submission

/-- Cross product on `ℝ³ = EuclideanSpace ℝ (Fin 3)` (Mathlib's `⨯₃` lives
on `Fin 3 → ℝ`). -/
def cross3 (u v : ℝ³) : ℝ³ := WithLp.toLp 2 (WithLp.ofLp u ⨯₃ WithLp.ofLp v)

/-- An **f-relative continuous band foliation by pre-bends**: a continuous
family `y ↦ [A y, B y]` of straight chords of the strip, each meeting the
centreline point `(1/2, y)` exactly once (`centreHeight y = y`), with the
deck symmetry `chord (y+a)` = period-flip of `chord y`, continuous
endpoints, and each chord a genuine pre-bend of the embedded band `f`
(its image is an isometric straight segment). -/
structure BandFoliation (a : ℝ) (f : ℝ² → ℝ³) (hf : IsMoebiusEmbedding a f) where
  chord : ℝ → BendData
  centre : ∀ y : ℝ, (chord y).centreHeight = y
  deck : ∀ y : ℝ,
    (chord (y + a)).A = period a (chord y).B ∧
    (chord (y + a)).B = period a (chord y).A
  cont_left : Continuous (fun y : ℝ => ((chord y).A 1 : ℝ))
  cont_right : Continuous (fun y : ℝ => ((chord y).B 1 : ℝ))
  preBend : ∀ y : ℝ, ‖f ((chord y).B) - f ((chord y).A)‖ = ‖(chord y).B - (chord y).A‖

namespace BandFoliation

variable {a : ℝ} {f : ℝ² → ℝ³} {hf : IsMoebiusEmbedding a f}

/-- Left endpoint of the leaf through centreline height `y`. -/
def A (F : BandFoliation a f hf) (y : ℝ) : ℝ² := (F.chord y).A

/-- Right endpoint of the leaf through centreline height `y`. -/
def B (F : BandFoliation a f hf) (y : ℝ) : ℝ² := (F.chord y).B

/-- The horizontal displacement `Δ = B1 − A1` of the leaf. -/
def Δ (F : BandFoliation a f hf) (y : ℝ) : ℝ := (F.chord y).slope

/-- `A y` lies on the left boundary line. -/
lemma A_left_coord (F : BandFoliation a f hf) (y : ℝ) : (A F y) 0 = 0 := by
  simpa [A] using (F.chord y).left_coord

/-- `B y` lies on the right boundary line. -/
lemma B_right_coord (F : BandFoliation a f hf) (y : ℝ) : (B F y) 0 = 1 := by
  simpa [B] using (F.chord y).right_coord

/-- `A y` is a unit-strip point. -/
lemma A_mem_unitStrip (F : BandFoliation a f hf) (y : ℝ) : A F y ∈ unitStrip := by
  rw [unitStrip]
  simp [A_left_coord F y]

/-- `B y` is a unit-strip point. -/
lemma B_mem_unitStrip (F : BandFoliation a f hf) (y : ℝ) : B F y ∈ unitStrip := by
  rw [unitStrip]
  simp [B_right_coord F y]

/-- The midpoint of the preimage chord is the centreline point `(1/2, y)`. -/
lemma A_add_B_eq_centre (F : BandFoliation a f hf) (y : ℝ) :
    A F y + B F y = !₂[1, 2 * y] := by
  ext i <;> fin_cases i
  · have hA0 : (A F y) 0 = 0 := A_left_coord F y
    have hB0 : (B F y) 0 = 1 := B_right_coord F y
    have h : (A F y + B F y) 0 = 1 := by simp [hA0, hB0]
    simpa using h
  · have hc : ((F.chord y).A 1 + (F.chord y).B 1) / 2 = y := F.centre y
    have hc1 : (F.chord y).A 1 + (F.chord y).B 1 = 2 * y := by
      have hh := hc
      field_simp [show (2 : ℝ) ≠ 0 by norm_num] at hh
      linarith
    have hsum : (A F y) 1 + (B F y) 1 = 2 * y := by simpa [A, B] using hc1
    have h : (A F y + B F y) 1 = 2 * y := by simpa using hsum
    simpa using h

/-- The preimage chord length squared: `‖B − A‖² = 1 + Δ²`. -/
lemma chordLength_sq (F : BandFoliation a f hf) (y : ℝ) :
    ‖B F y - A F y‖ ^ 2 = 1 + (Δ F y) ^ 2 := by
  rw [Submission.PaperBand.norm_sq_coord_sum]
  have hA0 : (A F y) 0 = 0 := A_left_coord F y
  have hB0 : (B F y) 0 = 1 := B_right_coord F y
  have h0 : (B F y - A F y) 0 = 1 := by simp [hA0, hB0]
  have h1 : (B F y - A F y) 1 = (B F y) 1 - (A F y) 1 := by simp
  have hΔ : (Δ F y) = (B F y) 1 - (A F y) 1 := by
    unfold Δ BendData.slope
    simpa [A, B]
  rw [h0, h1, ← hΔ]
  ring

/-- The preimage chord length is positive (`≥ 1`). -/
lemma chordLength_pos (F : BandFoliation a f hf) (y : ℝ) : 0 < ‖B F y - A F y‖ := by
  have hsq := chordLength_sq F y
  by_contra h
  have hle0 : ‖B F y - A F y‖ ≤ 0 := le_of_not_gt h
  have hz : ‖B F y - A F y‖ = 0 := le_antisymm hle0 (norm_nonneg _)
  nlinarith [sq_nonneg (Δ F y)]

/-- `‖f B − f A‖` is nonzero along every leaf (genuine pre-bend). -/
lemma imageChord_ne_zero (F : BandFoliation a f hf) (y : ℝ) :
    f (B F y) - f (A F y) ≠ 0 := by
  intro h
  have hlen : ‖f (B F y) - f (A F y)‖ = ‖B F y - A F y‖ := F.preBend y
  have hz : ‖B F y - A F y‖ = 0 := by
    rw [← hlen, h]
    simp
  have hpos := chordLength_pos F y
  linarith

/-- The image displacement of the leaf (direction times length). -/
def leafVec (F : BandFoliation a f hf) (y : ℝ) : ℝ³ := f (B F y) - f (A F y)

/-- The unit image direction of the leaf (the orientation from `A` to `B`). -/
def imageDir (F : BandFoliation a f hf) (y : ℝ) : ℝ³ :=
  (‖leafVec F y‖ ⁻¹) • leafVec F y

/-- The image midpoint of the leaf. -/
def imageMid (F : BandFoliation a f hf) (y : ℝ) : ℝ³ :=
  (1 / 2 : ℝ) • (f (A F y) + f (B F y))

/-- The deck map sends the right endpoint to the left endpoint of the next
leaf: `A (y+a) = period a (B y)`. -/
lemma A_period (F : BandFoliation a f hf) (y : ℝ) :
    A F (y + a) = period a (B F y) := by
  simpa [A, B] using (F.deck y).1

/-- The deck map sends the left endpoint to the right endpoint of the next
leaf: `B (y+a) = period a (A y)`. -/
lemma B_period (F : BandFoliation a f hf) (y : ℝ) :
    B F (y + a) = period a (A F y) := by
  simpa [A, B] using (F.deck y).2

/-- **Images of deck-paired endpoints coincide**: `f (A (y+a)) = f (B y)`. -/
lemma f_A_period (F : BandFoliation a f hf) (y : ℝ) :
    f (A F (y + a)) = f (B F y) := by
  have h := hf.periodic (B F y) (B_mem_unitStrip F y)
  have hA : A F (y + a) = period a (B F y) := A_period F y
  simpa [hA] using h

/-- **Images of deck-paired endpoints coincide**: `f (B (y+a)) = f (A y)`. -/
lemma f_B_period (F : BandFoliation a f hf) (y : ℝ) :
    f (B F (y + a)) = f (A F y) := by
  have h := hf.periodic (A F y) (A_mem_unitStrip F y)
  have hB : B F (y + a) = period a (A F y) := B_period F y
  simpa [hB] using h

/-- **The image displacement is odd under the deck**: going once around the
band reverses the leaf's direction — `leafVec (y+a) = −leafVec y`. -/
lemma leafVec_odd (F : BandFoliation a f hf) (y : ℝ) :
    leafVec F (y + a) = -leafVec F y := by
  unfold leafVec
  rw [f_A_period F y, f_B_period F y]
  abel

/-- **The unit image direction is odd under the deck**:
`imageDir (y+a) = −imageDir y` — the Möbius orientation flip that Lemma T's
odd-map argument needs. -/
lemma imageDir_odd (F : BandFoliation a f hf) (y : ℝ) :
    imageDir F (y + a) = -imageDir F y := by
  unfold imageDir
  have hl : leafVec F (y + a) = -leafVec F y := leafVec_odd F y
  rw [hl]
  have hn : ‖-leafVec F y‖ = ‖leafVec F y‖ := norm_neg _
  rw [hn, smul_neg]

/-- The image direction is a unit vector. -/
lemma imageDir_unit (F : BandFoliation a f hf) (y : ℝ) : ‖imageDir F y‖ = 1 := by
  unfold imageDir
  have hne : ‖leafVec F y‖ ≠ 0 := by
    have hlen : ‖f (B F y) - f (A F y)‖ = ‖B F y - A F y‖ := F.preBend y
    have hpos : 0 < ‖leafVec F y‖ := by
      unfold leafVec
      rw [hlen]
      exact chordLength_pos F y
    exact ne_of_gt hpos
  rw [norm_smul]
  rw [Real.norm_eq_abs]
  have habs : |(‖leafVec F y‖ : ℝ)⁻¹| = (‖leafVec F y‖ : ℝ)⁻¹ :=
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))
  rw [habs]
  exact inv_mul_cancel₀ hne

/-- **The image midpoint is periodic under the deck**: `m (y+a) = m y`. -/
lemma imageMid_period (F : BandFoliation a f hf) (y : ℝ) :
    imageMid F (y + a) = imageMid F y := by
  unfold imageMid
  rw [f_A_period F y, f_B_period F y]
  rw [add_comm]

/-- `A` is continuous in the centreline height. -/
lemma continuous_A (F : BandFoliation a f hf) : Continuous (fun y : ℝ => A F y) := by
  have h : (fun y : ℝ => A F y) = fun y : ℝ => (F.chord y).A 1 • (!₂[0, (1 : ℝ)] : ℝ²) := by
    funext y
    have hv : A F y = !₂[0, (A F y) 1] := Submission.PaperBand.leftEdge_eq_vec (A_left_coord F y)
    calc
      A F y = !₂[0, (A F y) 1] := hv
      _ = (A F y) 1 • (!₂[0, (1 : ℝ)] : ℝ²) := by
        ext i <;> fin_cases i <;> simp
  rw [h]
  exact Continuous.smul F.cont_left continuous_const

/-- `B` is continuous in the centreline height. -/
lemma continuous_B (F : BandFoliation a f hf) : Continuous (fun y : ℝ => B F y) := by
  have h : (fun y : ℝ => B F y) = fun y : ℝ =>
      (!₂[1, (0 : ℝ)] : ℝ²) + (F.chord y).B 1 • (!₂[0, (1 : ℝ)] : ℝ²) := by
    funext y
    have hv : B F y = !₂[1, (B F y) 1] := Submission.PaperBand.rightEdge_eq_vec (B_right_coord F y)
    calc
      B F y = !₂[1, (B F y) 1] := hv
      _ = (!₂[1, (0 : ℝ)] : ℝ²) + (B F y) 1 • (!₂[0, (1 : ℝ)] : ℝ²) := by
        ext i <;> fin_cases i <;> simp
  rw [h]
  exact (continuous_const.add (Continuous.smul F.cont_right continuous_const))

/-- `f` is continuous on the unit strip (from smoothness). -/
lemma f_continuousOn_strip {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ContinuousOn f unitStrip :=
  hf.smooth.continuousOn

/-- `f ∘ A` is continuous (the values stay in the strip). -/
lemma continuous_fA (F : BandFoliation a f hf) : Continuous (fun y : ℝ => f (A F y)) := by
  exact ContinuousOn.comp_continuous (f_continuousOn_strip hf) (continuous_A F)
    (fun y => A_mem_unitStrip F y)

/-- `f ∘ B` is continuous. -/
lemma continuous_fB (F : BandFoliation a f hf) : Continuous (fun y : ℝ => f (B F y)) := by
  exact ContinuousOn.comp_continuous (f_continuousOn_strip hf) (continuous_B F)
    (fun y => B_mem_unitStrip F y)

/-- `leafVec` is continuous. -/
lemma continuous_leafVec (F : BandFoliation a f hf) :
    Continuous (fun y : ℝ => leafVec F y) := by
  unfold leafVec
  exact (continuous_fB F).sub (continuous_fA F)

/-- `imageDir` is continuous (the leaf direction varies continuously). -/
lemma continuous_imageDir (F : BandFoliation a f hf) :
    Continuous (fun y : ℝ => imageDir F y) := by
  unfold imageDir
  have hnorm : Continuous (fun y : ℝ => ‖leafVec F y‖) := (continuous_leafVec F).norm
  have hne : ∀ y : ℝ, ‖leafVec F y‖ ≠ 0 := by
    intro y
    have hlen : ‖f (B F y) - f (A F y)‖ = ‖B F y - A F y‖ := F.preBend y
    have hpos : 0 < ‖leafVec F y‖ := by
      unfold leafVec
      rw [hlen]
      exact chordLength_pos F y
    exact ne_of_gt hpos
  have hscalar : Continuous (fun y : ℝ => (‖leafVec F y‖ : ℝ)⁻¹) := hnorm.inv₀ hne
  exact hscalar.smul (continuous_leafVec F)

/-- `imageMid` is continuous (the image midpoint varies continuously). -/
lemma continuous_imageMid (F : BandFoliation a f hf) :
    Continuous (fun y : ℝ => imageMid F y) := by
  unfold imageMid
  have hsum : Continuous (fun y : ℝ => f (A F y) + f (B F y)) :=
    (continuous_fA F).add (continuous_fB F)
  have hhalf : Continuous (fun y : ℝ => (1 / 2 : ℝ)) := continuous_const
  exact hhalf.smul hsum

/-- `imageDir` has unit norm at every height. -/
lemma imageDir_unit_all (F : BandFoliation a f hf) : ∀ y : ℝ, ‖imageDir F y‖ = 1 := by
  intro y
  exact imageDir_unit F y

/-- `imageDir` is odd. -/
lemma imageDir_odd_all (F : BandFoliation a f hf) : ∀ y : ℝ, imageDir F (y + a) = -imageDir F y := by
  intro y
  exact imageDir_odd F y

/-- `imageMid` is periodic. -/
lemma imageMid_periodic_all (F : BandFoliation a f hf) : ∀ y : ℝ, imageMid F (y + a) = imageMid F y := by
  intro y
  exact imageMid_period F y

end BandFoliation

/-!
## Lemma T (f-relative statement, PROVED)

`lemmaT_tpattern` is proved by applying the fleet-proved abstract
topological core
`Commons.Topology.BorsukUlam.exists_perp_coplanar_pair` to
`u := imageDir F`, `m := imageMid F` — the five hypotheses are exactly the
derived interface facts (`continuous_imageDir`, `imageDir_unit_all`,
`imageDir_odd_all`, `continuous_imageMid`, `imageMid_periodic_all`).

The conclusion: two leaves at centreline heights `y` and `y + δ`
(`0 < δ < a`, distinct quotient points) whose image directions are
perpendicular (`⬝ᵥ`-dot on `Fin 3 → ℝ` via `WithLp.ofLp`) and whose
midpoint displacement is coplanar with them (the `⨯₃`-cross term) — the
T-pattern (perpendicular intersecting lines through the two leaf
directions/midpoints; disjointness of the leaves is a foliation property,
supplied later by Prop main0 for the "embedded" part).  Dot and cross are
expressed with `WithLp.ofLp` in the ambient `Fin 3 → ℝ` exactly as in the
commons theorem, so the proof is a direct `exact`.
-/
theorem lemmaT_tpattern {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (F : BandFoliation a f hf) :
    ∃ y : ℝ, ∃ δ : ℝ, 0 < δ ∧ δ < a ∧
      (WithLp.ofLp (BandFoliation.imageDir F y) ⬝ᵥ
         WithLp.ofLp (BandFoliation.imageDir F (y + δ)) = 0) ∧
      (WithLp.ofLp (BandFoliation.imageMid F y - BandFoliation.imageMid F (y + δ)) ⬝ᵥ
         (WithLp.ofLp (BandFoliation.imageDir F y) ⨯₃
           WithLp.ofLp (BandFoliation.imageDir F (y + δ))) = 0) := by
  exact Commons.Topology.BorsukUlam.exists_perp_coplanar_pair (a := a) ha
    (u := fun y => BandFoliation.imageDir F y) (m := fun y => BandFoliation.imageMid F y)
    (BandFoliation.continuous_imageDir F) (BandFoliation.imageDir_unit_all F)
    (BandFoliation.imageDir_odd_all F) (BandFoliation.continuous_imageMid F)
    (BandFoliation.imageMid_periodic_all F)

end Submission

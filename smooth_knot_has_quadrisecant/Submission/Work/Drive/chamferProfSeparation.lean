import Mathlib
import Submission.Work.Drive.chamferLoopGenDefs
import Submission.Work.Drive.chamferProfDefs
import Submission.Work.Drive.radialGapOfTools
import Submission.Work.Drive.thinLoopSeparation

/-!
# The point-set separation of the generalised chamfer profile (Lemma A of the uniform-`ρ₀` design)

`Work.Drive.chamferProfGen r D lay a b σ` is the generalised chamfer loop written in terms of its
profile: the retained arc (cut at fraction `a` of the slice) for `u ∈ [0,1/2]`, the head connector
from the arc point at fraction `1-a` to the chord point at fraction `1-b`, the chord back from
fraction `1-b` to fraction `b`, and the tail connector from the chord point at fraction `b` to the
arc point at fraction `a`.

This module proves the eight point-set separations that the combinatorial lemma
`Work.Drive.chamferProfGen_injOn_of_separation` consumes, from the geometric hypotheses of the
lead's Lemma A (`NOTES_LEAD_endgameUniform.md` §4):

* `hgapA`/`hgapB` : the *radial gaps* at the two cut points: the distance from the cut arc point to
  the endpoint of the slice is smaller than the distance from any point of the retained arc to that
  endpoint (the output of `Work.Drive.radialGapOfTools`);
* `hballA`/`hballB` : the two *ball bounds*: the connector target lies within the ball around the
  slice endpoint of radius the distance to the cut arc point;
* `hsum` : the two connectors are separated by the chord (`‖P_a - A‖ + ‖P_b - B‖ < ‖B - A‖`);
* `hmid` : the retained arc carries no middle of the chord.

Nothing here is specific to the chord sweep: the statements are about the four points
`A = r (taR)`, `B = r (tbR)` and the arc.
-/

noncomputable section
namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-! ## Elementary complements -/

/-- **The chord coordinate of an affine point of the chord line.** -/
lemma clg_chordCoord_affine {A B : Space} (hAB : A ≠ B) (μ : ℝ) :
    chordCoord A B ((1 - μ) • A + μ • B) = μ * ‖B - A‖ := by
  rw [chordCoord_convex_combo, chordCoord_self, chordCoord_other _ _ hAB]
  ring

/-- **An affine point of the chord line has zero perpendicular part.** -/
lemma clg_chordPerp_affine {A B : Space} (hAB : A ≠ B) (μ : ℝ) :
    chordPerp A B ((1 - μ) • A + μ • B) = 0 := by
  have h1 : (1 - μ) • A + μ • B - A = μ • (B - A) := by module
  rw [chordPerp_eq_zero_iff, clg_chordCoord_affine hAB, ← smul_smul, chordDir_smul A B hAB, h1]

/-- The chord coordinate of the chord point at fraction `ξ`. -/
lemma clg_chordCoord_sweepChord {r : ℝ → Space} {d : BandArcData} (D : SweepData d) {σ ξ : ℝ}
    (hAB : r (taR D σ) ≠ r (tbR D σ)) :
    chordCoord (r (taR D σ)) (r (tbR D σ)) (sweepChord' r D σ ξ)
      = ξ * ‖r (tbR D σ) - r (taR D σ)‖ :=
  clg_chordCoord_affine hAB ξ

/-- The chord point at fraction `ξ` has zero perpendicular part. -/
lemma clg_chordPerp_sweepChord {r : ℝ → Space} {d : BandArcData} (D : SweepData d) {σ ξ : ℝ}
    (hAB : r (taR D σ) ≠ r (tbR D σ)) :
    chordPerp (r (taR D σ)) (r (tbR D σ)) (sweepChord' r D σ ξ) = 0 :=
  clg_chordPerp_affine hAB ξ

/-- `sweepW'` is positive and smaller than a period at an interior parameter. -/
lemma clg_sweepW_pos_lt {d : BandArcData} (D : SweepData d) {σ : ℝ}
    (hσ : σ ∈ Set.Ioo (0 : ℝ) 1) : 0 < sweepW' D σ ∧ sweepW' D σ < period := by
  have hclamp : clampI σ = ⟨σ, ⟨hσ.1.le, hσ.2.le⟩⟩ := by
    apply Subtype.ext
    show min 1 (max 0 σ) = σ
    rw [max_eq_right hσ.1.le, min_eq_right hσ.2.le]
  have hta : taR D σ = D.ta ⟨σ, ⟨hσ.1.le, hσ.2.le⟩⟩ := by rw [taR, hclamp]
  have htb : tbR D σ = D.tb ⟨σ, ⟨hσ.1.le, hσ.2.le⟩⟩ := by rw [tbR, hclamp]
  have h := sweepW_pos_lt D ⟨σ, ⟨hσ.1.le, hσ.2.le⟩⟩ ⟨hσ.1, hσ.2⟩
  simpa [sweepW', sweepW, hta, htb] using h

/-- The chord endpoints of an interior slice are distinct. -/
lemma clg_AB_ne {r : ℝ → Space} {d : BandArcData} (D : SweepData d) {σ a : ℝ}
    (hsum : ‖sweepArc' r D σ a - r (taR D σ)‖ + ‖sweepArc' r D σ (1 - a) - r (tbR D σ)‖
      < ‖r (tbR D σ) - r (taR D σ)‖) :
    r (taR D σ) ≠ r (tbR D σ) := by
  have hL : 0 < ‖r (tbR D σ) - r (taR D σ)‖ := by
    have h1 : (0 : ℝ) ≤ ‖sweepArc' r D σ a - r (taR D σ)‖ := norm_nonneg _
    have h2 : (0 : ℝ) ≤ ‖sweepArc' r D σ (1 - a) - r (tbR D σ)‖ := norm_nonneg _
    linarith
  intro h
  rw [← h, sub_self, norm_zero] at hL
  exact lt_irrefl 0 hL

/-- **The arc parameter window.**  The retained arc's parameter range `[taR + a·w, tbR - a·w]`
contains the arc point of every fraction `ξ ∈ [a, 1-a]`. -/
lemma clg_arc_param_mem {d : BandArcData} (D : SweepData d) {σ a ξ : ℝ}
    (hσ : σ ∈ Set.Ioo (0 : ℝ) 1) (hξ : ξ ∈ Set.Icc a (1 - a)) :
    taR D σ + a * sweepW' D σ ≤ taR D σ + ξ * sweepW' D σ ∧
      taR D σ + ξ * sweepW' D σ ≤ tbR D σ - a * sweepW' D σ := by
  have hw := (clg_sweepW_pos_lt D hσ).1
  have hwdef : sweepW' D σ = tbR D σ - taR D σ := rfl
  constructor
  · have h : a * sweepW' D σ ≤ ξ * sweepW' D σ := mul_le_mul_of_nonneg_right hξ.1 hw.le
    linarith
  · have h1 : ξ * sweepW' D σ ≤ (1 - a) * sweepW' D σ := mul_le_mul_of_nonneg_right hξ.2 hw.le
    have h2 : (1 - a) * sweepW' D σ = tbR D σ - a * sweepW' D σ - taR D σ := by
      rw [hwdef]; ring
    linarith

/-- **The arc parameter window is shorter than a period.** -/
lemma clg_arc_window_lt {d : BandArcData} (D : SweepData d) {σ a : ℝ}
    (hσ : σ ∈ Set.Ioo (0 : ℝ) 1) (ha0 : 0 < a) (ha2 : 2 * a < 1) :
    tbR D σ - a * sweepW' D σ - (taR D σ + a * sweepW' D σ) < period := by
  have hw := clg_sweepW_pos_lt D hσ
  have hwdef : sweepW' D σ = tbR D σ - taR D σ := rfl
  have hgoal : tbR D σ - a * sweepW' D σ - (taR D σ + a * sweepW' D σ)
      = (1 - 2 * a) * sweepW' D σ := by rw [hwdef]; ring
  rw [hgoal]
  calc (1 - 2 * a) * sweepW' D σ ≤ 1 * sweepW' D σ :=
        mul_le_mul_of_nonneg_right (by linarith) hw.1.le
    _ = sweepW' D σ := one_mul _
    _ < period := hw.2

/-! ## The eight separations -/

/-- **The retained arc is injective on its fraction range**, by injectivity of the knot on one
period. -/
lemma clg_arc_injOn {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData} (D : SweepData d)
    {σ a : ℝ} (hσ : σ ∈ Set.Ioo (0 : ℝ) 1) (ha0 : 0 < a) (ha2 : 2 * a < 1) :
    Set.InjOn (fun ξ : ℝ => sweepArc' r D σ ξ) (Set.Icc a (1 - a)) := by
  have hw := clg_sweepW_pos_lt D hσ
  intro ξ₁ h₁ ξ₂ h₂ heq
  obtain ⟨hlo₁, hhi₁⟩ := clg_arc_param_mem D hσ h₁
  obtain ⟨hlo₂, hhi₂⟩ := clg_arc_param_mem D hσ h₂
  have hwin := clg_arc_window_lt D hσ ha0 ha2
  have hθ : taR D σ + ξ₁ * sweepW' D σ = taR D σ + ξ₂ * sweepW' D σ := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact absurd heq (knot_ne_of_sub_mem_Ioo hr (by linarith) (by linarith))
    · exact absurd heq.symm (knot_ne_of_sub_mem_Ioo hr (by linarith) (by linarith))
  exact mul_right_cancel₀ (ne_of_gt hw.1) (by linarith)

/-- **The chord is injective on its fraction range.** -/
lemma clg_chord_injOn {r : ℝ → Space} {d : BandArcData} (D : SweepData d) {σ b : ℝ}
    (hAB : r (taR D σ) ≠ r (tbR D σ)) :
    Set.InjOn (fun ξ : ℝ => sweepChord' r D σ ξ) (Set.Icc b (1 - b)) :=
  fun _ _ _ _ heq => convex_combo_inj hAB heq

/-- **The retained arc misses the open chord.** -/
lemma clg_arc_ne_chord {r : ℝ → Space} {d : BandArcData} (D : SweepData d) {σ a : ℝ}
    (hσ : σ ∈ Set.Ioo (0 : ℝ) 1) (ha0 : 0 < a) (ha2 : 2 * a < 1)
    (hmid : ∀ u : ℝ, taR D σ + a * sweepW' D σ ≤ u → u ≤ tbR D σ - a * sweepW' D σ →
      r u ∉ openSegment ℝ (r (taR D σ)) (r (tbR D σ))) :
    ∀ ξ ∈ Set.Icc a (1 - a), ∀ ξ' ∈ Set.Ioo (0 : ℝ) 1,
      sweepArc' r D σ ξ ≠ sweepChord' r D σ ξ' := by
  intro ξ hξ ξ' hξ' heq
  obtain ⟨hlo, hhi⟩ := clg_arc_param_mem D hσ hξ
  have hmem : sweepChord' r D σ ξ' ∈ openSegment ℝ (r (taR D σ)) (r (tbR D σ)) := by
    rw [openSegment_eq_image]
    exact ⟨ξ', ⟨hξ'.1, hξ'.2⟩, rfl⟩
  have hmem2 : sweepArc' r D σ ξ ∈ openSegment ℝ (r (taR D σ)) (r (tbR D σ)) := by
    rw [heq]; exact hmem
  exact hmid (taR D σ + ξ * sweepW' D σ) hlo hhi hmem2

/-! ## The ball bounds for the two connectors -/

/-- **The head connector lies in the ball about `B`** of radius the distance from the cut arc point
`P_b` to `B`. -/
lemma clg_head_ball {r : ℝ → Space} {d : BandArcData} (D : SweepData d) {σ a b c : ℝ}
    (hb0 : 0 < b) (hc : c ∈ Set.Icc (0 : ℝ) 1)
    (hballB : b * ‖r (tbR D σ) - r (taR D σ)‖
      ≤ ‖sweepArc' r D σ (1 - a) - r (tbR D σ)‖) :
    ‖(1 - c) • sweepArc' r D σ (1 - a) + c • sweepChord' r D σ (1 - b) - r (tbR D σ)‖
      ≤ ‖sweepArc' r D σ (1 - a) - r (tbR D σ)‖ := by
  have hQ : sweepChord' r D σ (1 - b) - r (tbR D σ)
      = b • (r (taR D σ) - r (tbR D σ)) := by
    rw [sweepChord']; module
  have hQn : ‖sweepChord' r D σ (1 - b) - r (tbR D σ)‖
      = b * ‖r (tbR D σ) - r (taR D σ)‖ := by
    rw [hQ, norm_smul, Real.norm_eq_abs, abs_of_pos hb0, norm_sub_rev]
  have hX : (1 - c) • sweepArc' r D σ (1 - a) + c • sweepChord' r D σ (1 - b) - r (tbR D σ)
      = (1 - c) • (sweepArc' r D σ (1 - a) - r (tbR D σ))
        + c • (sweepChord' r D σ (1 - b) - r (tbR D σ)) := by module
  rw [hX]
  calc ‖(1 - c) • (sweepArc' r D σ (1 - a) - r (tbR D σ))
        + c • (sweepChord' r D σ (1 - b) - r (tbR D σ))‖
      ≤ ‖(1 - c) • (sweepArc' r D σ (1 - a) - r (tbR D σ))‖
        + ‖c • (sweepChord' r D σ (1 - b) - r (tbR D σ))‖ := norm_add_le _ _
    _ = (1 - c) * ‖sweepArc' r D σ (1 - a) - r (tbR D σ)‖
        + c * ‖sweepChord' r D σ (1 - b) - r (tbR D σ)‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (by linarith [hc.2] : (0:ℝ) ≤ 1 - c), abs_of_nonneg hc.1]
    _ ≤ (1 - c) * ‖sweepArc' r D σ (1 - a) - r (tbR D σ)‖
        + c * ‖sweepArc' r D σ (1 - a) - r (tbR D σ)‖ := by
        have h1 : c * ‖sweepChord' r D σ (1 - b) - r (tbR D σ)‖
            ≤ c * ‖sweepArc' r D σ (1 - a) - r (tbR D σ)‖ :=
          mul_le_mul_of_nonneg_left (by rw [hQn]; exact hballB) hc.1
        linarith
    _ = ‖sweepArc' r D σ (1 - a) - r (tbR D σ)‖ := by ring

/-- **The tail connector lies in the ball about `A`** of radius the distance from the cut arc point
`P_a` to `A`. -/
lemma clg_tail_ball {r : ℝ → Space} {d : BandArcData} (D : SweepData d) {σ a b c : ℝ}
    (hb0 : 0 < b) (hc : c ∈ Set.Icc (0 : ℝ) 1)
    (hballA : b * ‖r (tbR D σ) - r (taR D σ)‖
      ≤ ‖sweepArc' r D σ a - r (taR D σ)‖) :
    ‖(1 - c) • sweepChord' r D σ b + c • sweepArc' r D σ a - r (taR D σ)‖
      ≤ ‖sweepArc' r D σ a - r (taR D σ)‖ := by
  have hQ : sweepChord' r D σ b - r (taR D σ) = b • (r (tbR D σ) - r (taR D σ)) := by
    rw [sweepChord']; module
  have hQn : ‖sweepChord' r D σ b - r (taR D σ)‖ = b * ‖r (tbR D σ) - r (taR D σ)‖ := by
    rw [hQ, norm_smul, Real.norm_eq_abs, abs_of_pos hb0]
  have hX : (1 - c) • sweepChord' r D σ b + c • sweepArc' r D σ a - r (taR D σ)
      = (1 - c) • (sweepChord' r D σ b - r (taR D σ))
        + c • (sweepArc' r D σ a - r (taR D σ)) := by module
  rw [hX]
  calc ‖(1 - c) • (sweepChord' r D σ b - r (taR D σ))
        + c • (sweepArc' r D σ a - r (taR D σ))‖
      ≤ ‖(1 - c) • (sweepChord' r D σ b - r (taR D σ))‖
        + ‖c • (sweepArc' r D σ a - r (taR D σ))‖ := norm_add_le _ _
    _ = (1 - c) * ‖sweepChord' r D σ b - r (taR D σ)‖
        + c * ‖sweepArc' r D σ a - r (taR D σ)‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (by linarith [hc.2] : (0:ℝ) ≤ 1 - c), abs_of_nonneg hc.1]
    _ ≤ (1 - c) * ‖sweepArc' r D σ a - r (taR D σ)‖
        + c * ‖sweepArc' r D σ a - r (taR D σ)‖ := by
        have h1 : (1 - c) * ‖sweepChord' r D σ b - r (taR D σ)‖
            ≤ (1 - c) * ‖sweepArc' r D σ a - r (taR D σ)‖ :=
          mul_le_mul_of_nonneg_left (by rw [hQn]; exact hballA)
            (by linarith [hc.2] : (0:ℝ) ≤ 1 - c)
        linarith
    _ = ‖sweepArc' r D σ a - r (taR D σ)‖ := by ring

/-! ## The arc against the two connectors -/

/-- **The head connector meets the retained arc only at its arc endpoint** (fraction `1-a`). -/
lemma clg_arc_head {r : ℝ → Space} {d : BandArcData} (D : SweepData d) {σ a b : ℝ}
    (hσ : σ ∈ Set.Ioo (0 : ℝ) 1) (hb0 : 0 < b)
    (hgapB : ∀ θ : ℝ, taR D σ + a * sweepW' D σ ≤ θ → θ < tbR D σ - a * sweepW' D σ →
      ‖sweepArc' r D σ (1 - a) - r (tbR D σ)‖ < ‖r θ - r (tbR D σ)‖)
    (hballB : b * ‖r (tbR D σ) - r (taR D σ)‖
      ≤ ‖sweepArc' r D σ (1 - a) - r (tbR D σ)‖) :
    ∀ c ∈ Set.Icc (0 : ℝ) 1, ∀ ξ ∈ Set.Icc a (1 - a),
      (1 - c) • sweepArc' r D σ (1 - a) + c • sweepChord' r D σ (1 - b)
        = sweepArc' r D σ ξ → ξ = 1 - a := by
  intro c hc ξ hξ heq
  have hw := (clg_sweepW_pos_lt D hσ).1
  have hwdef : sweepW' D σ = tbR D σ - taR D σ := rfl
  have hball := clg_head_ball D hb0 hc hballB
  have hle : 1 - a ≤ ξ := by
    by_contra hcon
    have hlt : ξ < 1 - a := not_le.mp hcon
    have h1 : taR D σ + a * sweepW' D σ ≤ taR D σ + ξ * sweepW' D σ := by
      have := mul_le_mul_of_nonneg_right hξ.1 hw.le
      linarith
    have h2 : taR D σ + ξ * sweepW' D σ < tbR D σ - a * sweepW' D σ := by
      have hmul := mul_lt_mul_of_pos_right hlt hw
      have h3 : taR D σ + (1 - a) * sweepW' D σ = tbR D σ - a * sweepW' D σ := by
        rw [hwdef]; ring
      linarith
    have hgap := hgapB (taR D σ + ξ * sweepW' D σ) h1 h2
    have hEq : (1 - c) • sweepArc' r D σ (1 - a) + c • sweepChord' r D σ (1 - b)
        = r (taR D σ + ξ * sweepW' D σ) := heq
    rw [hEq] at hball
    linarith
  exact le_antisymm hξ.2 hle

/-- **The tail connector meets the retained arc only at its arc endpoint** (fraction `a`). -/
lemma clg_arc_tail {r : ℝ → Space} {d : BandArcData} (D : SweepData d) {σ a b : ℝ}
    (hσ : σ ∈ Set.Ioo (0 : ℝ) 1) (hb0 : 0 < b)
    (hgapA : ∀ θ : ℝ, taR D σ + a * sweepW' D σ < θ → θ ≤ tbR D σ - a * sweepW' D σ →
      ‖sweepArc' r D σ a - r (taR D σ)‖ < ‖r θ - r (taR D σ)‖)
    (hballA : b * ‖r (tbR D σ) - r (taR D σ)‖ ≤ ‖sweepArc' r D σ a - r (taR D σ)‖) :
    ∀ c ∈ Set.Icc (0 : ℝ) 1, ∀ ξ ∈ Set.Icc a (1 - a),
      (1 - c) • sweepChord' r D σ b + c • sweepArc' r D σ a = sweepArc' r D σ ξ → ξ = a := by
  intro c hc ξ hξ heq
  have hw := (clg_sweepW_pos_lt D hσ).1
  have hwdef : sweepW' D σ = tbR D σ - taR D σ := rfl
  have hball := clg_tail_ball D hb0 hc hballA
  have hle : ξ ≤ a := by
    by_contra hcon
    have hlt : a < ξ := not_le.mp hcon
    have h1 : taR D σ + a * sweepW' D σ < taR D σ + ξ * sweepW' D σ := by
      have hmul := mul_lt_mul_of_pos_right hlt hw
      linarith
    have h2 : taR D σ + ξ * sweepW' D σ ≤ tbR D σ - a * sweepW' D σ := by
      have hmul := mul_le_mul_of_nonneg_right hξ.2 hw.le
      have h3 : taR D σ + (1 - a) * sweepW' D σ = tbR D σ - a * sweepW' D σ := by
        rw [hwdef]; ring
      linarith
    have hgap := hgapA (taR D σ + ξ * sweepW' D σ) h1 h2
    have hEq : (1 - c) • sweepChord' r D σ b + c • sweepArc' r D σ a
        = r (taR D σ + ξ * sweepW' D σ) := heq
    rw [hEq] at hball
    linarith
  exact le_antisymm hle hξ.1

/-- **The chord coordinate separates points by their distance.** -/
lemma clg_abs_chordCoord_sub_le {A B P Q : Space} :
    |chordCoord A B P - chordCoord A B Q| ≤ ‖P - Q‖ := by
  have h : chordCoord A B P - chordCoord A B Q = inner ℝ (P - Q) (chordDir A B) := by
    rw [chordCoord, chordCoord, ← inner_sub_left]
    congr 1
    abel
  rw [h]
  calc |inner ℝ (P - Q) (chordDir A B)| ≤ ‖P - Q‖ * ‖chordDir A B‖ :=
        abs_real_inner_le_norm _ _
    _ ≤ ‖P - Q‖ * 1 := mul_le_mul_of_nonneg_left (chordDir_norm_le A B) (norm_nonneg _)
    _ = ‖P - Q‖ := mul_one _

/-! ## The chord against the two connectors -/

/-- **The head connector meets the chord only at its own chord endpoint** (`c = 1`). -/
lemma clg_chord_head {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData} (D : SweepData d)
    {σ a b : ℝ} (hσ : σ ∈ Set.Ioo (0 : ℝ) 1) (ha0 : 0 < a) (ha2 : 2 * a < 1) (hb0 : 0 < b)
    (hsum : ‖sweepArc' r D σ a - r (taR D σ)‖ + ‖sweepArc' r D σ (1 - a) - r (tbR D σ)‖
      < ‖r (tbR D σ) - r (taR D σ)‖)
    (hmid : ∀ u : ℝ, taR D σ + a * sweepW' D σ ≤ u → u ≤ tbR D σ - a * sweepW' D σ →
      r u ∉ openSegment ℝ (r (taR D σ)) (r (tbR D σ))) :
    ∀ c ∈ Set.Icc (0 : ℝ) 1, ∀ ξ ∈ Set.Icc b (1 - b),
      (1 - c) • sweepArc' r D σ (1 - a) + c • sweepChord' r D σ (1 - b)
        = sweepChord' r D σ ξ → c = 1 := by
  intro c hc ξ hξ heq
  have hAB := clg_AB_ne D hsum
  have hw := clg_sweepW_pos_lt D hσ
  have hLpos : 0 < ‖r (tbR D σ) - r (taR D σ)‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hAB))
  -- the cut arc point at the head, written with the chord's endpoint parameter
  have hP : sweepArc' r D σ (1 - a) = r (tbR D σ - a * sweepW' D σ) := by
    show r (taR D σ + (1 - a) * sweepW' D σ) = r (tbR D σ - a * sweepW' D σ)
    congr 1
    rw [show sweepW' D σ = tbR D σ - taR D σ from rfl]
    ring
  have hmidlo : taR D σ + a * sweepW' D σ ≤ tbR D σ - a * sweepW' D σ := by
    have hwdef : sweepW' D σ = tbR D σ - taR D σ := rfl
    have h2 : (2 * a) * sweepW' D σ ≤ sweepW' D σ := by
      have h3 := mul_le_mul_of_nonneg_right ha2.le hw.1.le
      simpa using h3
    linarith
  have hmidP : sweepArc' r D σ (1 - a) ∉ openSegment ℝ (r (taR D σ)) (r (tbR D σ)) := by
    rw [hP]
    exact hmid (tbR D σ - a * sweepW' D σ) hmidlo le_rfl
  have hpb_ne_B : sweepArc' r D σ (1 - a) ≠ r (tbR D σ) := by
    rw [hP]
    refine knot_ne_of_sub_mem_Ioo hr ?_ ?_
    · have : (0 : ℝ) < a * sweepW' D σ := mul_pos ha0 hw.1
      linarith
    · have h2 : a * sweepW' D σ < period := by nlinarith [hw.2]
      linarith
  -- the perpendicular part of the head connector point
  have hzero : (1 - c) • chordPerp (r (taR D σ)) (r (tbR D σ)) (sweepArc' r D σ (1 - a)) = 0 := by
    have h := chordPerp_convex_combo (A := r (taR D σ)) (B := r (tbR D σ))
      (X := sweepArc' r D σ (1 - a)) (Y := sweepChord' r D σ (1 - b)) c
    rw [heq, clg_chordPerp_sweepChord D hAB, clg_chordPerp_sweepChord D hAB, smul_zero,
      add_zero] at h
    exact h.symm
  rcases eq_or_ne (chordPerp (r (taR D σ)) (r (tbR D σ)) (sweepArc' r D σ (1 - a))) 0 with
    hperp | hperp
  · -- the cut arc point lies on the chord *line*
    have hclose : |chordCoord (r (taR D σ)) (r (tbR D σ)) (sweepArc' r D σ (1 - a))
        - ‖r (tbR D σ) - r (taR D σ)‖| < ‖r (tbR D σ) - r (taR D σ)‖ := by
      have h1 : |chordCoord (r (taR D σ)) (r (tbR D σ)) (sweepArc' r D σ (1 - a))
          - chordCoord (r (taR D σ)) (r (tbR D σ)) (r (tbR D σ))| ≤
            ‖sweepArc' r D σ (1 - a) - r (tbR D σ)‖ :=
        clg_abs_chordCoord_sub_le
      rw [chordCoord_other _ _ hAB] at h1
      have h2 : ‖sweepArc' r D σ (1 - a) - r (tbR D σ)‖ < ‖r (tbR D σ) - r (taR D σ)‖ := by
        have h3 : (0 : ℝ) ≤ ‖sweepArc' r D σ a - r (taR D σ)‖ := norm_nonneg _
        linarith
      linarith
    obtain ⟨hlo0, hhi0⟩ := abs_lt.mp hclose
    have hcc_pos : 0 < chordCoord (r (taR D σ)) (r (tbR D σ)) (sweepArc' r D σ (1 - a)) := by
      linarith
    have hge : ‖r (tbR D σ) - r (taR D σ)‖
        ≤ chordCoord (r (taR D σ)) (r (tbR D σ)) (sweepArc' r D σ (1 - a)) := by
      by_contra hcon
      exact hmidP (mem_openSegment_of_chordPerp_eq_zero hAB hcc_pos (not_le.mp hcon) hperp)
    have hgt : ‖r (tbR D σ) - r (taR D σ)‖
        < chordCoord (r (taR D σ)) (r (tbR D σ)) (sweepArc' r D σ (1 - a)) := by
      rcases lt_or_eq_of_le hge with h | h
      · exact h
      · exfalso
        have hdec : sweepArc' r D σ (1 - a) - r (taR D σ)
            = chordCoord (r (taR D σ)) (r (tbR D σ)) (sweepArc' r D σ (1 - a))
              • chordDir (r (taR D σ)) (r (tbR D σ)) :=
          (chordPerp_eq_zero_iff _ _ _).mp hperp
        have hdec' : sweepArc' r D σ (1 - a) - r (taR D σ) = r (tbR D σ) - r (taR D σ) := by
          rw [hdec, ← h, chordDir_smul _ _ hAB]
        refine hpb_ne_B ?_
        have h2 := congrArg (fun z : Space => z + r (taR D σ)) hdec'
        simpa using h2
    have hccEq : chordCoord (r (taR D σ)) (r (tbR D σ))
          ((1 - c) • sweepArc' r D σ (1 - a) + c • sweepChord' r D σ (1 - b))
        = chordCoord (r (taR D σ)) (r (tbR D σ)) (sweepChord' r D σ ξ) := by rw [heq]
    rw [chordCoord_convex_combo, clg_chordCoord_sweepChord D hAB,
      clg_chordCoord_sweepChord D hAB] at hccEq
    have hcb : c * b ≤ b := by
      have := mul_le_mul_of_nonneg_right hc.2 hb0.le
      simpa using this
    rcases lt_or_eq_of_le hc.2 with hclt | hceq
    · have hc1 : 0 < 1 - c := by linarith
      have h1 : (1 - c) * ‖r (tbR D σ) - r (taR D σ)‖
          < (1 - c) * chordCoord (r (taR D σ)) (r (tbR D σ)) (sweepArc' r D σ (1 - a)) :=
        mul_lt_mul_of_pos_left hgt hc1
      have h2 : (1 - c) * ‖r (tbR D σ) - r (taR D σ)‖
          + c * ((1 - b) * ‖r (tbR D σ) - r (taR D σ)‖)
          = ‖r (tbR D σ) - r (taR D σ)‖ * (1 - c * b) := by ring
      have h3 : ‖r (tbR D σ) - r (taR D σ)‖ * (1 - b)
          ≤ ‖r (tbR D σ) - r (taR D σ)‖ * (1 - c * b) :=
        mul_le_mul_of_nonneg_left (by linarith) hLpos.le
      have h4 : ξ * ‖r (tbR D σ) - r (taR D σ)‖
          ≤ (1 - b) * ‖r (tbR D σ) - r (taR D σ)‖ :=
        mul_le_mul_of_nonneg_right hξ.2 hLpos.le
      nlinarith [h1, h2, h3, h4, hccEq]
    · exact hceq
  · rcases smul_eq_zero.mp hzero with h1 | h2
    · linarith
    · exact absurd h2 hperp

/-- **The tail connector meets the chord only at its own chord endpoint** (`c = 0`). -/
lemma clg_chord_tail {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData} (D : SweepData d)
    {σ a b : ℝ} (hσ : σ ∈ Set.Ioo (0 : ℝ) 1) (ha0 : 0 < a) (ha2 : 2 * a < 1) (hb0 : 0 < b)
    (hsum : ‖sweepArc' r D σ a - r (taR D σ)‖ + ‖sweepArc' r D σ (1 - a) - r (tbR D σ)‖
      < ‖r (tbR D σ) - r (taR D σ)‖)
    (hmid : ∀ u : ℝ, taR D σ + a * sweepW' D σ ≤ u → u ≤ tbR D σ - a * sweepW' D σ →
      r u ∉ openSegment ℝ (r (taR D σ)) (r (tbR D σ))) :
    ∀ c ∈ Set.Icc (0 : ℝ) 1, ∀ ξ ∈ Set.Icc b (1 - b),
      (1 - c) • sweepChord' r D σ b + c • sweepArc' r D σ a = sweepChord' r D σ ξ → c = 0 := by
  intro c hc ξ hξ heq
  have hAB := clg_AB_ne D hsum
  have hw := clg_sweepW_pos_lt D hσ
  have hLpos : 0 < ‖r (tbR D σ) - r (taR D σ)‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hAB))
  have hmidlo : taR D σ + a * sweepW' D σ ≤ tbR D σ - a * sweepW' D σ := by
    have hwdef : sweepW' D σ = tbR D σ - taR D σ := rfl
    have h2 : (2 * a) * sweepW' D σ ≤ sweepW' D σ := by
      have h3 := mul_le_mul_of_nonneg_right ha2.le hw.1.le
      simpa using h3
    linarith
  have hmidP : sweepArc' r D σ a ∉ openSegment ℝ (r (taR D σ)) (r (tbR D σ)) :=
    hmid (taR D σ + a * sweepW' D σ) le_rfl hmidlo
  have hzero : c • chordPerp (r (taR D σ)) (r (tbR D σ)) (sweepArc' r D σ a) = 0 := by
    have h := chordPerp_convex_combo (A := r (taR D σ)) (B := r (tbR D σ))
      (X := sweepChord' r D σ b) (Y := sweepArc' r D σ a) c
    rw [heq, clg_chordPerp_sweepChord D hAB, clg_chordPerp_sweepChord D hAB, smul_zero,
      zero_add] at h
    exact h.symm
  rcases eq_or_ne (chordPerp (r (taR D σ)) (r (tbR D σ)) (sweepArc' r D σ a)) 0 with hperp | hperp
  · -- the cut arc point lies on the chord *line*
    have hclose : |chordCoord (r (taR D σ)) (r (tbR D σ)) (sweepArc' r D σ a)|
        < ‖r (tbR D σ) - r (taR D σ)‖ := by
      have h1 := clg_abs_chordCoord_sub_le (A := r (taR D σ)) (B := r (tbR D σ))
        (P := sweepArc' r D σ a) (Q := r (taR D σ))
      rw [chordCoord_self, sub_zero] at h1
      have h2 : ‖sweepArc' r D σ a - r (taR D σ)‖ < ‖r (tbR D σ) - r (taR D σ)‖ := by
        have h3 : (0 : ℝ) ≤ ‖sweepArc' r D σ (1 - a) - r (tbR D σ)‖ := norm_nonneg _
        linarith
      linarith
    have hcc_nonpos : chordCoord (r (taR D σ)) (r (tbR D σ)) (sweepArc' r D σ a) ≤ 0 := by
      by_contra hcon
      have hpos : 0 < chordCoord (r (taR D σ)) (r (tbR D σ)) (sweepArc' r D σ a) := not_le.mp hcon
      have hlt : chordCoord (r (taR D σ)) (r (tbR D σ)) (sweepArc' r D σ a)
          < ‖r (tbR D σ) - r (taR D σ)‖ := (abs_lt.mp hclose).2
      exact hmidP (mem_openSegment_of_chordPerp_eq_zero hAB hpos hlt hperp)
    rcases lt_or_eq_of_le hc.1 with hcpos | hc0
    · exfalso
      have hccEq : chordCoord (r (taR D σ)) (r (tbR D σ))
            ((1 - c) • sweepChord' r D σ b + c • sweepArc' r D σ a)
          = chordCoord (r (taR D σ)) (r (tbR D σ)) (sweepChord' r D σ ξ) := by rw [heq]
      rw [chordCoord_convex_combo, clg_chordCoord_sweepChord D hAB,
        clg_chordCoord_sweepChord D hAB] at hccEq
      have h4 : b * ‖r (tbR D σ) - r (taR D σ)‖
          ≤ ξ * ‖r (tbR D σ) - r (taR D σ)‖ :=
        mul_le_mul_of_nonneg_right hξ.1 hLpos.le
      have hbl_pos : 0 < b * ‖r (tbR D σ) - r (taR D σ)‖ := mul_pos hb0 hLpos
      have hlt : (1 - c) * (b * ‖r (tbR D σ) - r (taR D σ)‖)
          + c * (chordCoord (r (taR D σ)) (r (tbR D σ)) (sweepArc' r D σ a))
          < b * ‖r (tbR D σ) - r (taR D σ)‖ := by
        nlinarith [hbl_pos, hcpos, hcc_nonpos, hc.2]
      nlinarith [hccEq, h4, hlt]
    · exact hc0.symm
  · rcases smul_eq_zero.mp hzero with h1 | h2
    · exact h1
    · exact absurd h2 hperp

/-- **The two connectors are disjoint.** -/
lemma clg_chamfers {r : ℝ → Space} {d : BandArcData} (D : SweepData d) {σ a b : ℝ}
    (hb0 : 0 < b)
    (hballA : b * ‖r (tbR D σ) - r (taR D σ)‖ ≤ ‖sweepArc' r D σ a - r (taR D σ)‖)
    (hballB : b * ‖r (tbR D σ) - r (taR D σ)‖ ≤ ‖sweepArc' r D σ (1 - a) - r (tbR D σ)‖)
    (hsum : ‖sweepArc' r D σ a - r (taR D σ)‖ + ‖sweepArc' r D σ (1 - a) - r (tbR D σ)‖
      < ‖r (tbR D σ) - r (taR D σ)‖) :
    ∀ c ∈ Set.Icc (0 : ℝ) 1, ∀ c' ∈ Set.Icc (0 : ℝ) 1,
      (1 - c) • sweepChord' r D σ b + c • sweepArc' r D σ a
        ≠ (1 - c') • sweepArc' r D σ (1 - a) + c' • sweepChord' r D σ (1 - b) := by
  intro c hc c' hc' heq
  have hA := clg_tail_ball D hb0 hc hballA
  have hB := clg_head_ball D hb0 hc' hballB
  have htri : ‖r (tbR D σ) - r (taR D σ)‖
      ≤ ‖(1 - c') • sweepArc' r D σ (1 - a) + c' • sweepChord' r D σ (1 - b)
          - r (tbR D σ)‖
        + ‖(1 - c) • sweepChord' r D σ b + c • sweepArc' r D σ a - r (taR D σ)‖ := by
    have h2 := dist_triangle (r (tbR D σ))
      ((1 - c') • sweepArc' r D σ (1 - a) + c' • sweepChord' r D σ (1 - b)) (r (taR D σ))
    simp only [dist_eq_norm] at h2
    have h3 : ‖(1 - c') • sweepArc' r D σ (1 - a) + c' • sweepChord' r D σ (1 - b)
          - r (taR D σ)‖
        = ‖(1 - c) • sweepChord' r D σ b + c • sweepArc' r D σ a - r (taR D σ)‖ := by
      rw [← heq]
    rw [h3, norm_sub_rev (r (tbR D σ))
      ((1 - c') • sweepArc' r D σ (1 - a) + c' • sweepChord' r D σ (1 - b))] at h2
    exact h2
  linarith

/-- **The chord target fraction is below one half.**  The two ball bounds and the separation of the
connectors by the chord force `2 b < 1`. -/
lemma clg_beta_lt_half {r : ℝ → Space} {d : BandArcData} (D : SweepData d) {σ a b : ℝ}
    (hb0 : 0 < b)
    (hballA : b * ‖r (tbR D σ) - r (taR D σ)‖ ≤ ‖sweepArc' r D σ a - r (taR D σ)‖)
    (hballB : b * ‖r (tbR D σ) - r (taR D σ)‖ ≤ ‖sweepArc' r D σ (1 - a) - r (tbR D σ)‖)
    (hsum : ‖sweepArc' r D σ a - r (taR D σ)‖ + ‖sweepArc' r D σ (1 - a) - r (tbR D σ)‖
      < ‖r (tbR D σ) - r (taR D σ)‖) :
    2 * b < 1 := by
  have hL : 0 < ‖r (tbR D σ) - r (taR D σ)‖ := by
    have h1 : (0 : ℝ) ≤ ‖sweepArc' r D σ a - r (taR D σ)‖ := norm_nonneg _
    have h2 : (0 : ℝ) ≤ ‖sweepArc' r D σ (1 - a) - r (tbR D σ)‖ := norm_nonneg _
    linarith
  nlinarith [hballA, hballB, hsum, hL, hb0]

end Work.Drive

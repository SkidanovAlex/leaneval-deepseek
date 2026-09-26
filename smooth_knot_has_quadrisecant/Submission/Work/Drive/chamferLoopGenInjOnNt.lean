import Mathlib
import Submission.Work.Drive.chamferLoopGenDefs
import Submission.Work.Drive.chamferLoopInjOnNT
import Submission.Work.Drive.chamferProfGen_injOn_of_separation
import Submission.Work.Drive.chamferProfSeparation
import Submission.Work.Drive.separation_of_far_parameters

namespace Work.Drive

set_option maxHeartbeats 1000000

open LeanEval.KnotTheory.Quadrisecant

/-! ## 0. Basic vocabulary -/

lemma cli_sweepW_eq_sub {d : BandArcData} (D : SweepData d) (σ : ℝ) :
    sweepW' D σ = tbR D σ - taR D σ := rfl

lemma cli_continuous_clampI : Continuous clampI := by
  unfold clampI
  fun_prop

lemma cli_continuous_taR {d : BandArcData} (D : SweepData d) : Continuous (taR D) :=
  D.cont_ta.comp cli_continuous_clampI

lemma cli_continuous_tbR {d : BandArcData} (D : SweepData d) : Continuous (tbR D) :=
  D.cont_tb.comp cli_continuous_clampI

/-! ## 1. The slack functional at an endpoint -/

/-- **The slack functional at a point.**  Let `n` be the orthogonal projection of the velocity at
`t` onto the plane orthogonal to a chord (so `⟪n, velocity r t⟫ = ‖n‖ ^ 2`), with `μ ≤ ‖n‖`.  On the
scale `θ ≤ μ / (2C)` (`C` a Lipschitz constant of the velocity) the functional
`θ ↦ ⟪n, r (t + θ) - r t⟫` is monotone with slope `≥ μ ^ 2 / 2`, and likewise on the negative
side. -/
lemma cli_slack_at_point {r : ℝ → Space} (hr : IsSmoothKnot r) {n : Space} {t C μ : ℝ}
    (hC : 0 < C) (hμ : 0 < μ) (hnn : inner ℝ n (velocity r t) = ‖n‖ ^ 2) (hnμ : μ ≤ ‖n‖)
    (hvlip : ∀ s t' : ℝ, ‖velocity r s - velocity r t'‖ ≤ C * |t' - s|) :
    (∀ θ : ℝ, 0 ≤ θ → θ ≤ μ / (2 * C) → (μ ^ 2 / 2) * θ ≤ inner ℝ n (r t - r (t - θ))) ∧
    (∀ θ : ℝ, 0 ≤ θ → θ ≤ μ / (2 * C) → (μ ^ 2 / 2) * θ ≤ inner ℝ n (r (t + θ) - r t)) ∧
    (∀ θ₁ θ₂ : ℝ, 0 ≤ θ₁ → θ₁ ≤ θ₂ → θ₂ ≤ μ / (2 * C) →
      inner ℝ n (r (t - θ₂) - r (t - θ₁)) ≤ 0) ∧
    (∀ θ₁ θ₂ : ℝ, 0 ≤ θ₁ → θ₁ ≤ θ₂ → θ₂ ≤ μ / (2 * C) →
      0 ≤ inner ℝ n (r (t + θ₂) - r (t + θ₁))) := by
  have hC0 : 0 ≤ C := hC.le
  have hξ : C * (μ / (2 * C)) ≤ ‖n‖ / 2 := by
    have h1 : C * (μ / (2 * C)) = μ / 2 := by field_simp
    rw [h1]
    linarith
  have hslack : ∀ y ∈ Set.Icc (t - μ / (2 * C)) (t + μ / (2 * C)),
      ‖n‖ ^ 2 / 2 ≤ inner ℝ n (velocity r y) :=
    inner_slack_of_reach hC0 hvlip hnn hξ
  have hν : μ ^ 2 / 2 ≤ ‖n‖ ^ 2 / 2 := by nlinarith [hμ, hnμ]
  have hν0 : (0 : ℝ) ≤ ‖n‖ ^ 2 / 2 := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro θ hθ0 hθ
    have hmem : ∀ y ∈ Set.Icc (t - θ) t,
        ‖n‖ ^ 2 / 2 ≤ inner ℝ n (velocity r y) := by
      intro y hy
      exact hslack y ⟨by linarith [hy.1, hθ0], by linarith [hy.2, hθ0, hθ]⟩
    have h := inner_knot_slack_mono hr hmem (t - θ) ⟨by linarith, by linarith⟩ t
      ⟨by linarith, by linarith⟩ (by linarith)
    have h2 : (μ ^ 2 / 2) * θ ≤ (‖n‖ ^ 2 / 2) * θ := mul_le_mul_of_nonneg_right hν hθ0
    linarith [h, h2]
  · intro θ hθ0 hθ
    have hmem : ∀ y ∈ Set.Icc t (t + θ),
        ‖n‖ ^ 2 / 2 ≤ inner ℝ n (velocity r y) := by
      intro y hy
      exact hslack y ⟨by linarith [hy.1, hθ0], by linarith [hy.2, hθ0, hθ]⟩
    have h := inner_knot_slack_mono hr hmem t ⟨by linarith, by linarith⟩ (t + θ)
      ⟨by linarith, by linarith⟩ (by linarith)
    have h2 : (μ ^ 2 / 2) * θ ≤ (‖n‖ ^ 2 / 2) * θ := mul_le_mul_of_nonneg_right hν hθ0
    linarith [h, h2]
  · intro θ₁ θ₂ hθ₁ hθ hθ₂
    have hmem : ∀ y ∈ Set.Icc (t - θ₂) (t - θ₁),
        ‖n‖ ^ 2 / 2 ≤ inner ℝ n (velocity r y) := by
      intro y hy
      exact hslack y ⟨by linarith [hy.1, hθ₂], by linarith [hy.2, hθ₁, hθ₂]⟩
    have h := inner_knot_slack_mono hr hmem (t - θ₂) ⟨by linarith, by linarith [hθ]⟩
      (t - θ₁) ⟨by linarith [hθ, hθ₂], by linarith⟩ (by linarith)
    have h1 : 0 ≤ (‖n‖ ^ 2 / 2) * (θ₂ - θ₁) := mul_nonneg hν0 (by linarith)
    have h3 : inner ℝ n (r (t - θ₂) - r (t - θ₁))
        = - inner ℝ n (r (t - θ₁) - r (t - θ₂)) := by
      have h4 : r (t - θ₂) - r (t - θ₁) = -(r (t - θ₁) - r (t - θ₂)) := by abel
      rw [h4, inner_neg_right]
    rw [h3]
    linarith [h, h1]
  · intro θ₁ θ₂ hθ₁ hθ hθ₂
    have hmem : ∀ y ∈ Set.Icc (t + θ₁) (t + θ₂),
        ‖n‖ ^ 2 / 2 ≤ inner ℝ n (velocity r y) := by
      intro y hy
      exact hslack y ⟨by linarith [hy.1, hθ₁, hθ₂], by linarith [hy.2, hθ₂]⟩
    have h := inner_knot_slack_mono hr hmem (t + θ₁) ⟨by linarith, by linarith [hθ, hθ₂]⟩
      (t + θ₂) ⟨by linarith, by linarith [hθ₂]⟩ (by linarith)
    have h1 : 0 ≤ (‖n‖ ^ 2 / 2) * (θ₂ - θ₁) := mul_nonneg hν0 (by linarith)
    linarith [h, h1]

/-! ## 2. The two connector balls -/

/-- The tail connector (from the chord point at fraction `b` to the cut arc point at fraction `a`)
lies within `M (a w)` of the arc's start point plus the chord length `b L`. -/
lemma cli_tailConn_ball {r : ℝ → Space} {d : BandArcData} (D : SweepData d) {σ a b c M : ℝ}
    (hM : 0 ≤ M) (ha0 : 0 < a) (hb0 : 0 < b) (hWp : 0 < sweepW' D σ)
    (hc : c ∈ Set.Icc (0 : ℝ) 1)
    (hlip : ∀ s t' : ℝ, ‖r s - r t'‖ ≤ M * |s - t'|) :
    ‖(1 - c) • sweepChord' r D σ b + c • sweepArc' r D σ a - r (taR D σ)‖
      ≤ M * (a * sweepW' D σ) + b * ‖r (tbR D σ) - r (taR D σ)‖ := by
  have hX : sweepChord' r D σ b - r (taR D σ) = b • (r (tbR D σ) - r (taR D σ)) := by
    rw [sweepChord']; module
  have hY : ‖sweepArc' r D σ a - r (taR D σ)‖ ≤ M * (a * sweepW' D σ) := by
    have h6 := hlip (taR D σ + a * sweepW' D σ) (taR D σ)
    have h7 : taR D σ + a * sweepW' D σ - taR D σ = a * sweepW' D σ := by ring
    rw [h7, abs_of_pos (mul_pos ha0 hWp)] at h6
    simpa [sweepArc'] using h6
  have h1 : (1 - c) • sweepChord' r D σ b + c • sweepArc' r D σ a - r (taR D σ)
      = (1 - c) • (sweepChord' r D σ b - r (taR D σ))
        + c • (sweepArc' r D σ a - r (taR D σ)) := by module
  rw [h1]
  have h2 : ‖sweepChord' r D σ b - r (taR D σ)‖ = b * ‖r (tbR D σ) - r (taR D σ)‖ := by
    rw [hX, norm_smul, Real.norm_eq_abs, abs_of_pos hb0]
  calc ‖(1 - c) • (sweepChord' r D σ b - r (taR D σ))
        + c • (sweepArc' r D σ a - r (taR D σ))‖
      ≤ ‖(1 - c) • (sweepChord' r D σ b - r (taR D σ))‖
        + ‖c • (sweepArc' r D σ a - r (taR D σ))‖ := norm_add_le _ _
    _ = (1 - c) * ‖sweepChord' r D σ b - r (taR D σ)‖
        + c * ‖sweepArc' r D σ a - r (taR D σ)‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (by linarith [hc.2]), abs_of_nonneg hc.1]
    _ ≤ (1 - c) * (b * ‖r (tbR D σ) - r (taR D σ)‖) + c * (M * (a * sweepW' D σ)) := by
        refine add_le_add ?_ ?_
        · rw [h2]
        · exact mul_le_mul_of_nonneg_left hY hc.1
    _ ≤ M * (a * sweepW' D σ) + b * ‖r (tbR D σ) - r (taR D σ)‖ := by
        have h8 : (0 : ℝ) ≤ b * ‖r (tbR D σ) - r (taR D σ)‖ := by positivity
        have h9 : (0 : ℝ) ≤ M * (a * sweepW' D σ) := mul_nonneg hM (by positivity)
        nlinarith [hc.1, hc.2, h8, h9]

/-- The head connector (from the cut arc point at fraction `1 - a` to the chord point at fraction
`1 - b`) lies within `M (a w)` of the arc's end point plus the chord length `b L`. -/
lemma cli_headConn_ball {r : ℝ → Space} {d : BandArcData} (D : SweepData d) {σ a b c M : ℝ}
    (hM : 0 ≤ M) (ha0 : 0 < a) (hb0 : 0 < b) (hWp : 0 < sweepW' D σ)
    (hc : c ∈ Set.Icc (0 : ℝ) 1)
    (hlip : ∀ s t' : ℝ, ‖r s - r t'‖ ≤ M * |s - t'|) :
    ‖(1 - c) • sweepArc' r D σ (1 - a) + c • sweepChord' r D σ (1 - b) - r (tbR D σ)‖
      ≤ M * (a * sweepW' D σ) + b * ‖r (tbR D σ) - r (taR D σ)‖ := by
  have hWdef : sweepW' D σ = tbR D σ - taR D σ := rfl
  have hX : sweepArc' r D σ (1 - a) - r (tbR D σ)
      = r (tbR D σ - a * sweepW' D σ) - r (tbR D σ) := by
    have harg : taR D σ + (1 - a) * sweepW' D σ = tbR D σ - a * sweepW' D σ := by
      rw [hWdef]; ring
    rw [sweepArc', harg]
  have hY : sweepChord' r D σ (1 - b) - r (tbR D σ)
      = (-b) • (r (tbR D σ) - r (taR D σ)) := by
    rw [sweepChord']; module
  have hXb : ‖sweepArc' r D σ (1 - a) - r (tbR D σ)‖ ≤ M * (a * sweepW' D σ) := by
    rw [hX]
    have h6 := hlip (tbR D σ - a * sweepW' D σ) (tbR D σ)
    have h7 : tbR D σ - a * sweepW' D σ - tbR D σ = -(a * sweepW' D σ) := by ring
    rw [h7, abs_neg, abs_of_pos (mul_pos ha0 hWp)] at h6
    exact h6
  have h1 : (1 - c) • sweepArc' r D σ (1 - a) + c • sweepChord' r D σ (1 - b) - r (tbR D σ)
      = (1 - c) • (sweepArc' r D σ (1 - a) - r (tbR D σ))
        + c • (sweepChord' r D σ (1 - b) - r (tbR D σ)) := by module
  rw [h1]
  have h2 : ‖sweepChord' r D σ (1 - b) - r (tbR D σ)‖
      = b * ‖r (tbR D σ) - r (taR D σ)‖ := by
    rw [hY, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hb0]
  calc ‖(1 - c) • (sweepArc' r D σ (1 - a) - r (tbR D σ))
        + c • (sweepChord' r D σ (1 - b) - r (tbR D σ))‖
      ≤ ‖(1 - c) • (sweepArc' r D σ (1 - a) - r (tbR D σ))‖
        + ‖c • (sweepChord' r D σ (1 - b) - r (tbR D σ))‖ := norm_add_le _ _
    _ = (1 - c) * ‖sweepArc' r D σ (1 - a) - r (tbR D σ)‖
        + c * ‖sweepChord' r D σ (1 - b) - r (tbR D σ)‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (by linarith [hc.2]), abs_of_nonneg hc.1]
    _ ≤ (1 - c) * (M * (a * sweepW' D σ)) + c * (b * ‖r (tbR D σ) - r (taR D σ)‖) := by
        refine add_le_add ?_ ?_
        · exact mul_le_mul_of_nonneg_left hXb (by linarith [hc.2])
        · rw [h2]
    _ ≤ M * (a * sweepW' D σ) + b * ‖r (tbR D σ) - r (taR D σ)‖ := by
        have h8 : (0 : ℝ) ≤ b * ‖r (tbR D σ) - r (taR D σ)‖ := by positivity
        have h9 : (0 : ℝ) ≤ M * (a * sweepW' D σ) := mul_nonneg hM (by positivity)
        nlinarith [hc.1, hc.2, h8, h9]

/-- **The two connectors are disjoint** (they are separated by the chord). -/
lemma cli_chamfers_disjoint {r : ℝ → Space} {d : BandArcData} (D : SweepData d)
    {σ a b M : ℝ} (hM : 0 ≤ M) (ha0 : 0 < a) (hb0 : 0 < b) (hWp : 0 < sweepW' D σ)
    (hlip : ∀ s t' : ℝ, ‖r s - r t'‖ ≤ M * |s - t'|)
    (hgap : 2 * (M * (a * sweepW' D σ) + b * ‖r (tbR D σ) - r (taR D σ)‖)
      < ‖r (tbR D σ) - r (taR D σ)‖) :
    ∀ c ∈ Set.Icc (0 : ℝ) 1, ∀ c' ∈ Set.Icc (0 : ℝ) 1,
      (1 - c) • sweepChord' r D σ b + c • sweepArc' r D σ a
        ≠ (1 - c') • sweepArc' r D σ (1 - a) + c' • sweepChord' r D σ (1 - b) := by
  intro c hc c' hc' hEq
  set F : Space := (1 - c) • sweepChord' r D σ b + c • sweepArc' r D σ a with hF
  set G : Space := (1 - c') • sweepArc' r D σ (1 - a) + c' • sweepChord' r D σ (1 - b) with hG
  have htail : ‖F - r (taR D σ)‖
      ≤ M * (a * sweepW' D σ) + b * ‖r (tbR D σ) - r (taR D σ)‖ := by
    rw [hF]
    exact cli_tailConn_ball D hM ha0 hb0 hWp hc hlip
  have hhead : ‖G - r (tbR D σ)‖
      ≤ M * (a * sweepW' D σ) + b * ‖r (tbR D σ) - r (taR D σ)‖ := by
    rw [hG]
    exact cli_headConn_ball D hM ha0 hb0 hWp hc' hlip
  have hsub : r (tbR D σ) - r (taR D σ)
      = (r (tbR D σ) - G) + (G - F) + (F - r (taR D σ)) := by
    rw [hEq]; abel
  have hfinal : ‖r (tbR D σ) - r (taR D σ)‖
      ≤ 2 * (M * (a * sweepW' D σ) + b * ‖r (tbR D σ) - r (taR D σ)‖) := by
    conv_lhs => rw [hsub]
    have h1 := norm_add_le ((r (tbR D σ) - G) + (G - F)) (F - r (taR D σ))
    have h2 : ‖(r (tbR D σ) - G) + (G - F)‖ ≤ ‖G - r (tbR D σ)‖ := by
      calc ‖(r (tbR D σ) - G) + (G - F)‖ ≤ ‖r (tbR D σ) - G‖ + ‖G - F‖ := norm_add_le _ _
        _ = ‖G - r (tbR D σ)‖ := by
            rw [sub_eq_zero.mpr hEq.symm, norm_zero, add_zero, norm_sub_rev]
    linarith [h1, h2, hhead, htail]
  linarith [hfinal, hgap]

/-! ## 4. The two connector–chord separations -/

/-- **The head connector meets the chord only at its chord endpoint.** -/
lemma cli_chord_head {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData} (D : SweepData d)
    {σ a b C μ : ℝ} (hC : 0 < C) (hμ : 0 < μ)
    (hvlip : ∀ s t' : ℝ, ‖velocity r s - velocity r t'‖ ≤ C * |t' - s|)
    (hσ : σ ∈ Set.Ioo (0 : ℝ) 1)
    (ha0 : 0 < a) (ha2 : 2 * a < 1) (hb0 : 0 < b) (hb2 : 2 * b < 1)
    (hT : μ ≤ ‖chordTilt (r (taR D σ)) (r (tbR D σ)) (velocity r (tbR D σ))‖)
    (hξ1 : a * sweepW' D σ ≤ μ / (2 * C)) :
    ∀ c ∈ Set.Icc (0 : ℝ) 1, ∀ ξ ∈ Set.Icc b (1 - b),
      (1 - c) • sweepArc' r D σ (1 - a) + c • sweepChord' r D σ (1 - b)
        = sweepChord' r D σ ξ → c = 1 := by
  intro c hc ξ hξ heq
  have hW := clg_sweepW_pos_lt D hσ
  have hWp : 0 < sweepW' D σ := hW.1
  have hWdef : sweepW' D σ = tbR D σ - taR D σ := rfl
  have hAB : r (taR D σ) ≠ r (tbR D σ) := by
    refine knot_ne_of_sub_mem_Ioo hr ?_ ?_
    · rw [← hWdef]; exact hWp
    · rw [← hWdef]; exact hW.2
  set n : Space := chordTilt (r (taR D σ)) (r (tbR D σ)) (velocity r (tbR D σ)) with hn
  have hnn : inner ℝ n (velocity r (tbR D σ)) = ‖n‖ ^ 2 := inner_chordTilt_self hAB _
  have hnμ : μ ≤ ‖n‖ := hT
  have hVn : inner ℝ n (r (tbR D σ) - r (taR D σ)) = 0 := by
    have hsm : r (tbR D σ) - r (taR D σ)
        = ‖r (tbR D σ) - r (taR D σ)‖ • chordDir (r (taR D σ)) (r (tbR D σ)) :=
      (chordDir_smul _ _ hAB).symm
    rw [hsm, inner_smul_right, hn, inner_chordTilt_chordDir hAB]
    ring
  have hsl := cli_slack_at_point hr hC hμ hnn hnμ hvlip
  have hlev : inner ℝ n (r (tbR D σ - a * sweepW' D σ) - r (tbR D σ)) < 0 := by
    have h1 := hsl.1 (a * sweepW' D σ) (by positivity) hξ1
    have h2 : (0 : ℝ) < μ ^ 2 / 2 * (a * sweepW' D σ) := by
      have h3 : 0 < a * sweepW' D σ := mul_pos ha0 hWp
      positivity
    have h4 : inner ℝ n (r (tbR D σ - a * sweepW' D σ) - r (tbR D σ))
        = - inner ℝ n (r (tbR D σ) - r (tbR D σ - a * sweepW' D σ)) := by
      have h5 : r (tbR D σ - a * sweepW' D σ) - r (tbR D σ)
          = -(r (tbR D σ) - r (tbR D σ - a * sweepW' D σ)) := by abel
      rw [h5, inner_neg_right]
    rw [h4]
    linarith
  have hA : sweepArc' r D σ (1 - a) - r (tbR D σ)
      = r (tbR D σ - a * sweepW' D σ) - r (tbR D σ) := by
    have harg : taR D σ + (1 - a) * sweepW' D σ = tbR D σ - a * sweepW' D σ := by
      rw [hWdef]; ring
    simp only [sweepArc', harg]
  have hQ : sweepChord' r D σ (1 - b) - r (tbR D σ)
      = (-b) • (r (tbR D σ) - r (taR D σ)) := by
    rw [sweepChord']; module
  have hzero : (1 - c) * inner ℝ n (r (tbR D σ - a * sweepW' D σ) - r (tbR D σ)) = 0 := by
    have hsplit : (1 - c) • sweepArc' r D σ (1 - a) + c • sweepChord' r D σ (1 - b) - r (tbR D σ)
        = (1 - c) • (sweepArc' r D σ (1 - a) - r (tbR D σ))
          + c • (sweepChord' r D σ (1 - b) - r (tbR D σ)) := by module
    have h1 : inner ℝ n (sweepChord' r D σ ξ - r (tbR D σ))
        = (1 - c) * inner ℝ n (sweepArc' r D σ (1 - a) - r (tbR D σ))
          + c * inner ℝ n (sweepChord' r D σ (1 - b) - r (tbR D σ)) := by
      rw [← heq, hsplit, inner_add_right, inner_smul_right, inner_smul_right]
    have h2 : inner ℝ n (sweepChord' r D σ ξ - r (tbR D σ)) = 0 := by
      have h3 : sweepChord' r D σ ξ - r (tbR D σ)
          = (-(1 - ξ)) • (r (tbR D σ) - r (taR D σ)) := by
        rw [sweepChord']; module
      rw [h3, inner_smul_right, hVn, mul_zero]
    rw [h2, hA, hQ, inner_smul_right, hVn, mul_zero] at h1
    simpa using h1.symm
  rcases mul_eq_zero.mp hzero with h1 | h1
  · linarith
  · exact absurd h1 (ne_of_lt hlev)

/-- **The tail connector meets the chord only at its chord endpoint.** -/
lemma cli_chord_tail {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData} (D : SweepData d)
    {σ a b C μ : ℝ} (hC : 0 < C) (hμ : 0 < μ)
    (hvlip : ∀ s t' : ℝ, ‖velocity r s - velocity r t'‖ ≤ C * |t' - s|)
    (hσ : σ ∈ Set.Ioo (0 : ℝ) 1)
    (ha0 : 0 < a) (ha2 : 2 * a < 1) (hb0 : 0 < b) (hb2 : 2 * b < 1)
    (hT : μ ≤ ‖chordTilt (r (taR D σ)) (r (tbR D σ)) (velocity r (taR D σ))‖)
    (hξ1 : a * sweepW' D σ ≤ μ / (2 * C)) :
    ∀ c ∈ Set.Icc (0 : ℝ) 1, ∀ ξ ∈ Set.Icc b (1 - b),
      (1 - c) • sweepChord' r D σ b + c • sweepArc' r D σ a
        = sweepChord' r D σ ξ → c = 0 := by
  intro c hc ξ hξ heq
  have hW := clg_sweepW_pos_lt D hσ
  have hWp : 0 < sweepW' D σ := hW.1
  have hWdef : sweepW' D σ = tbR D σ - taR D σ := rfl
  have hAB : r (taR D σ) ≠ r (tbR D σ) := by
    refine knot_ne_of_sub_mem_Ioo hr ?_ ?_
    · rw [← hWdef]; exact hWp
    · rw [← hWdef]; exact hW.2
  set n : Space := chordTilt (r (taR D σ)) (r (tbR D σ)) (velocity r (taR D σ)) with hn
  have hnn : inner ℝ n (velocity r (taR D σ)) = ‖n‖ ^ 2 := inner_chordTilt_self hAB _
  have hnμ : μ ≤ ‖n‖ := hT
  have hVn : inner ℝ n (r (tbR D σ) - r (taR D σ)) = 0 := by
    have hsm : r (tbR D σ) - r (taR D σ)
        = ‖r (tbR D σ) - r (taR D σ)‖ • chordDir (r (taR D σ)) (r (tbR D σ)) :=
      (chordDir_smul _ _ hAB).symm
    rw [hsm, inner_smul_right, hn, inner_chordTilt_chordDir hAB]
    ring
  have hsl := cli_slack_at_point hr hC hμ hnn hnμ hvlip
  have hlev : 0 < inner ℝ n (r (taR D σ + a * sweepW' D σ) - r (taR D σ)) := by
    have h1 := hsl.2.1 (a * sweepW' D σ) (by positivity) hξ1
    have h2 : (0 : ℝ) < μ ^ 2 / 2 * (a * sweepW' D σ) := by
      have h3 : 0 < a * sweepW' D σ := mul_pos ha0 hWp
      positivity
    linarith
  have hA : sweepArc' r D σ a - r (taR D σ)
      = r (taR D σ + a * sweepW' D σ) - r (taR D σ) := rfl
  have hQ : sweepChord' r D σ b - r (taR D σ)
      = b • (r (tbR D σ) - r (taR D σ)) := by
    rw [sweepChord']; module
  have hzero : c * inner ℝ n (r (taR D σ + a * sweepW' D σ) - r (taR D σ)) = 0 := by
    have hsplit : (1 - c) • sweepChord' r D σ b + c • sweepArc' r D σ a - r (taR D σ)
        = (1 - c) • (sweepChord' r D σ b - r (taR D σ))
          + c • (sweepArc' r D σ a - r (taR D σ)) := by module
    have h1 : inner ℝ n (sweepChord' r D σ ξ - r (taR D σ))
        = (1 - c) * inner ℝ n (sweepChord' r D σ b - r (taR D σ))
          + c * inner ℝ n (sweepArc' r D σ a - r (taR D σ)) := by
      rw [← heq, hsplit, inner_add_right, inner_smul_right, inner_smul_right]
    have h2 : inner ℝ n (sweepChord' r D σ ξ - r (taR D σ)) = 0 := by
      have h3 : sweepChord' r D σ ξ - r (taR D σ) = ξ • (r (tbR D σ) - r (taR D σ)) := by
        rw [sweepChord']; module
      rw [h3, inner_smul_right, hVn, mul_zero]
    rw [h2, hA, hQ, inner_smul_right, hVn, mul_zero] at h1
    simpa using h1.symm
  rcases mul_eq_zero.mp hzero with h1 | h1
  · exact h1
  · exact absurd h1 (ne_of_gt hlev)

/-! ## 5. The arc–chamfer separations -/

/-- **The head connector meets the retained arc only at its own arc endpoint.**  The chord carries a
uniform tilt margin `μ` at its `tb` end; the depth `ε` of the crossing displacement is small on both
the tilt scale `μ / (2C)` and the far-separation scale `σsep`. -/
lemma cli_arc_head {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData} (D : SweepData d)
    {σ a b M C μ m δ σsep : ℝ}
    (hM : 0 ≤ M) (hC : 0 < C) (hμ : 0 < μ) (hm : 0 < m) (hδ : 0 < δ)
    (hlip : ∀ s t' : ℝ, ‖r s - r t'‖ ≤ M * |s - t'|)
    (hvlip : ∀ s t' : ℝ, ‖velocity r s - velocity r t'‖ ≤ C * |t' - s|)
    (hnear : ∀ s t' : ℝ, |s - t'| ≤ δ → (m / 2) * |s - t'| ≤ ‖r s - r t'‖)
    (hfar : ∀ s t' : ℝ, δ ≤ |s - t'| → |s - t'| ≤ period - δ → σsep ≤ ‖r s - r t'‖)
    (hσ : σ ∈ Set.Ioo (0 : ℝ) 1)
    (ha0 : 0 < a) (ha2 : 2 * a < 1) (hb0 : 0 < b) (hb2 : 2 * b < 1)
    (hT : μ ≤ ‖chordTilt (r (taR D σ)) (r (tbR D σ)) (velocity r (tbR D σ))‖)
    (hξ1 : a * sweepW' D σ ≤ μ / (2 * C))
    (hξ2 : 4 * C * (b * ‖r (tbR D σ) - r (taR D σ)‖ + M * (a * sweepW' D σ)) ≤ m * μ)
    (hsep : b * ‖r (tbR D σ) - r (taR D σ)‖ + M * (a * sweepW' D σ) < σsep)
    (harc : Set.InjOn (fun ξ : ℝ => sweepArc' r D σ ξ) (Set.Icc a (1 - a)))
    (hmid : ∀ ξ ∈ Set.Icc a (1 - a), ∀ ξ' ∈ Set.Ioo (0 : ℝ) 1,
      sweepArc' r D σ ξ ≠ sweepChord' r D σ ξ') :
    ∀ c ∈ Set.Icc (0 : ℝ) 1, ∀ ξ ∈ Set.Icc a (1 - a),
      (1 - c) • sweepArc' r D σ (1 - a) + c • sweepChord' r D σ (1 - b)
        = sweepArc' r D σ ξ → ξ = 1 - a := by
  intro c hc ξ hξ heq
  set eps : ℝ := b * ‖r (tbR D σ) - r (taR D σ)‖ + M * (a * sweepW' D σ) with heps
  have hW := clg_sweepW_pos_lt D hσ
  have hWp : 0 < sweepW' D σ := hW.1
  have hWdef : sweepW' D σ = tbR D σ - taR D σ := rfl
  have hAB : r (taR D σ) ≠ r (tbR D σ) := by
    refine knot_ne_of_sub_mem_Ioo hr ?_ ?_
    · rw [← hWdef]; exact hWp
    · rw [← hWdef]; exact hW.2
  rcases eq_or_lt_of_le hc.1 with hc0 | hc0
  · subst hc0
    simp only [sub_zero, one_smul, zero_smul, add_zero] at heq
    exact (harc ⟨by linarith, le_rfl⟩ hξ heq).symm
  rcases lt_or_eq_of_le hc.2 with hclt | hc1
  · set n : Space := chordTilt (r (taR D σ)) (r (tbR D σ)) (velocity r (tbR D σ)) with hn
    have hnn : inner ℝ n (velocity r (tbR D σ)) = ‖n‖ ^ 2 := inner_chordTilt_self hAB _
    have hnμ : μ ≤ ‖n‖ := hT
    have hVn : inner ℝ n (r (tbR D σ) - r (taR D σ)) = 0 := by
      have hsm : r (tbR D σ) - r (taR D σ)
          = ‖r (tbR D σ) - r (taR D σ)‖ • chordDir (r (taR D σ)) (r (tbR D σ)) :=
        (chordDir_smul _ _ hAB).symm
      rw [hsm, inner_smul_right, hn, inner_chordTilt_chordDir hAB]
      ring
    have hsl := cli_slack_at_point hr hC hμ hnn hnμ hvlip
    have hlev : inner ℝ n (r (tbR D σ - a * sweepW' D σ) - r (tbR D σ)) < 0 := by
      have h1 := hsl.1 (a * sweepW' D σ) (by positivity) hξ1
      have h2 : (0 : ℝ) < μ ^ 2 / 2 * (a * sweepW' D σ) := by
        have h3 : 0 < a * sweepW' D σ := mul_pos ha0 hWp
        positivity
      have h4 : inner ℝ n (r (tbR D σ - a * sweepW' D σ) - r (tbR D σ))
          = - inner ℝ n (r (tbR D σ) - r (tbR D σ - a * sweepW' D σ)) := by
        have h5 : r (tbR D σ - a * sweepW' D σ) - r (tbR D σ)
            = -(r (tbR D σ) - r (tbR D σ - a * sweepW' D σ)) := by abel
        rw [h5, inner_neg_right]
      rw [h4]
      linarith
    -- the crossing parameter
    set x : ℝ := taR D σ + ξ * sweepW' D σ with hxdef
    have hxξ : sweepArc' r D σ ξ = r x := by
      simp only [sweepArc', hxdef]
    have hs : tbR D σ - x = (1 - ξ) * sweepW' D σ := by
      rw [hxdef, hWdef]; ring
    have hs_ge : a * sweepW' D σ ≤ tbR D σ - x := by
      rw [hs]
      exact mul_le_mul_of_nonneg_right (by linarith [hξ.2]) hWp.le
    have hs_pos : 0 < tbR D σ - x := lt_of_lt_of_le (mul_pos ha0 hWp) hs_ge
    have hs_le : tbR D σ - x ≤ sweepW' D σ := by
      rw [hs]
      calc (1 - ξ) * sweepW' D σ ≤ 1 * sweepW' D σ :=
            mul_le_mul_of_nonneg_right (by linarith [hξ.1]) hWp.le
        _ = sweepW' D σ := one_mul _
    -- the displacement of the crossing
    have hdisp : ‖r x - r (tbR D σ)‖ ≤ eps := by
      have hX : r x = (1 - c) • sweepArc' r D σ (1 - a) + c • sweepChord' r D σ (1 - b) := by
        rw [← hxξ]; exact heq.symm
      have hsplit : r x - r (tbR D σ)
          = (1 - c) • (sweepArc' r D σ (1 - a) - r (tbR D σ))
            + c • (sweepChord' r D σ (1 - b) - r (tbR D σ)) := by rw [hX]; module
      have hA : sweepArc' r D σ (1 - a) - r (tbR D σ)
          = r (tbR D σ - a * sweepW' D σ) - r (tbR D σ) := by
        have harg : taR D σ + (1 - a) * sweepW' D σ = tbR D σ - a * sweepW' D σ := by
          rw [hWdef]; ring
        simp only [sweepArc', harg]
      have hQ : sweepChord' r D σ (1 - b) - r (tbR D σ)
          = (-b) • (r (tbR D σ) - r (taR D σ)) := by
        rw [sweepChord']; module
      have h2 : ‖sweepArc' r D σ (1 - a) - r (tbR D σ)‖ ≤ M * (a * sweepW' D σ) := by
        rw [hA]
        have h4 := hlip (tbR D σ - a * sweepW' D σ) (tbR D σ)
        have h5 : tbR D σ - a * sweepW' D σ - tbR D σ = -(a * sweepW' D σ) := by ring
        rw [h5, abs_neg, abs_of_pos (mul_pos ha0 hWp)] at h4
        exact h4
      have h6 : ‖sweepChord' r D σ (1 - b) - r (tbR D σ)‖
          = b * ‖r (tbR D σ) - r (taR D σ)‖ := by
        rw [hQ, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hb0]
      rw [hsplit, heps]
      calc ‖(1 - c) • (sweepArc' r D σ (1 - a) - r (tbR D σ))
            + c • (sweepChord' r D σ (1 - b) - r (tbR D σ))‖
          ≤ ‖(1 - c) • (sweepArc' r D σ (1 - a) - r (tbR D σ))‖
            + ‖c • (sweepChord' r D σ (1 - b) - r (tbR D σ))‖ := norm_add_le _ _
        _ = (1 - c) * ‖sweepArc' r D σ (1 - a) - r (tbR D σ)‖
            + c * ‖sweepChord' r D σ (1 - b) - r (tbR D σ)‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_nonneg (by linarith [hc.2]), abs_of_nonneg hc0.le]
        _ ≤ (1 - c) * (M * (a * sweepW' D σ)) + c * (b * ‖r (tbR D σ) - r (taR D σ)‖) := by
            exact add_le_add (mul_le_mul_of_nonneg_left h2 (by linarith [hc.2]))
              (mul_le_mul_of_nonneg_left (le_of_eq h6) hc0.le)
        _ ≤ b * ‖r (tbR D σ) - r (taR D σ)‖ + M * (a * sweepW' D σ) := by
            have h8 : (0 : ℝ) ≤ b * ‖r (tbR D σ) - r (taR D σ)‖ := by positivity
            have h9 : (0 : ℝ) ≤ M * (a * sweepW' D σ) := mul_nonneg hM (by positivity)
            nlinarith [hc.2, hc0.le, h8, h9]
    -- the exact pairing
    have hkey : inner ℝ n (r x - r (tbR D σ))
        = (1 - c) * inner ℝ n (r (tbR D σ - a * sweepW' D σ) - r (tbR D σ)) := by
      have hX : r x = (1 - c) • sweepArc' r D σ (1 - a) + c • sweepChord' r D σ (1 - b) := by
        rw [← hxξ]; exact heq.symm
      have hsplit : r x - r (tbR D σ)
          = (1 - c) • (sweepArc' r D σ (1 - a) - r (tbR D σ))
            + c • (sweepChord' r D σ (1 - b) - r (tbR D σ)) := by rw [hX]; module
      have hA : sweepArc' r D σ (1 - a) - r (tbR D σ)
          = r (tbR D σ - a * sweepW' D σ) - r (tbR D σ) := by
        have harg : taR D σ + (1 - a) * sweepW' D σ = tbR D σ - a * sweepW' D σ := by
          rw [hWdef]; ring
        simp only [sweepArc', harg]
      have hQ : sweepChord' r D σ (1 - b) - r (tbR D σ)
          = (-b) • (r (tbR D σ) - r (taR D σ)) := by
        rw [sweepChord']; module
      rw [hsplit, inner_add_right, inner_smul_right, inner_smul_right, hA, hQ]
      simp only [inner_smul_right, hVn, mul_zero, add_zero]
    -- the three cases for the crossing parameter
    have hsmall : 2 * eps ≤ (μ / (2 * C)) * m := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      nlinarith [hξ2]
    by_cases hcaseA : tbR D σ - x ≤ δ
    · -- near the head
      have habs : |x - tbR D σ| = tbR D σ - x := by
        rw [abs_of_neg (by linarith [hs_pos])]; ring
      have h1 := hnear x (tbR D σ) (by rw [habs]; exact hcaseA)
      rw [habs] at h1
      have hs_small : tbR D σ - x ≤ μ / (2 * C) := by
        have h2 : (m / 2) * (tbR D σ - x) ≤ eps := by
          linarith [h1, hdisp]
        have h3 : tbR D σ - x ≤ 2 * eps / m := by
          rw [le_div_iff₀ hm]
          nlinarith [h2]
        have h4 : 2 * eps / m ≤ μ / (2 * C) := by
          rw [div_le_iff₀ hm]
          nlinarith [hsmall]
        linarith [h3, h4]
      have hmono := hsl.2.2.1 (a * sweepW' D σ) (tbR D σ - x)
        (by positivity) hs_ge hs_small
      rw [show tbR D σ - (tbR D σ - x) = x by ring] at hmono
      have hle : (1 - c) * inner ℝ n (r (tbR D σ - a * sweepW' D σ) - r (tbR D σ))
          ≤ inner ℝ n (r (tbR D σ - a * sweepW' D σ) - r (tbR D σ)) := by
        rw [← hkey]
        have hsplit : inner ℝ n (r x - r (tbR D σ))
            = inner ℝ n (r x - r (tbR D σ - a * sweepW' D σ))
              + inner ℝ n (r (tbR D σ - a * sweepW' D σ) - r (tbR D σ)) := by
          rw [← inner_add_right]
          congr 1
          abel
        rw [hsplit]
        linarith [hmono]
      nlinarith [hle, hlev, hc0]
    · by_cases hcaseC : period - δ < tbR D σ - x
      · -- wrapped: the crossing parameter is `period`-close to the head
        have he_pos : 0 < period - (tbR D σ - x) := by
          linarith [hs_le, hW.2]
        have he_lt : period - (tbR D σ - x) < δ := by linarith [hcaseC]
        have he_small : period - (tbR D σ - x) ≤ μ / (2 * C) := by
          have habs : |x + period - tbR D σ| = period - (tbR D σ - x) := by
            rw [abs_of_pos (by linarith [he_pos])]; ring
          have h1 := hnear (x + period) (tbR D σ) (by rw [habs]; exact he_lt.le)
          rw [habs, hr.periodic x] at h1
          have h2 : (m / 2) * (period - (tbR D σ - x)) ≤ eps := by linarith [h1, hdisp]
          have h3 : period - (tbR D σ - x) ≤ 2 * eps / m := by
            rw [le_div_iff₀ hm]
            nlinarith [h2]
          have h4 : 2 * eps / m ≤ μ / (2 * C) := by
            rw [div_le_iff₀ hm]
            nlinarith [hsmall]
          linarith [h3, h4]
        have hpos : 0 < inner ℝ n (r x - r (tbR D σ)) := by
          have h1 := hsl.2.1 (period - (tbR D σ - x)) he_pos.le he_small
          have h2 : (0 : ℝ) < μ ^ 2 / 2 * (period - (tbR D σ - x)) := by positivity
          have harg : tbR D σ + (period - (tbR D σ - x)) = x + period := by ring
          rw [harg, hr.periodic x] at h1
          linarith [h1, h2]
        rw [hkey] at hpos
        nlinarith [hpos, hlev, hclt]
      · -- far from the head
        have hbig : δ ≤ tbR D σ - x := le_of_not_ge hcaseA
        have hle : tbR D σ - x ≤ period - δ := le_of_not_gt hcaseC
        have habs : |x - tbR D σ| = tbR D σ - x := by
          rw [abs_of_neg (by linarith [hs_pos])]; ring
        have h1 := hfar x (tbR D σ) (by rw [habs]; exact hbig) (by rw [habs]; exact hle)
        linarith [h1, hdisp, hsep]
  · subst hc1
    simp only [sub_self, zero_smul, zero_add, one_smul] at heq
    exact absurd heq.symm (hmid ξ hξ (1 - b) ⟨by linarith [hb0], by linarith [hb2]⟩)

/-- **The tail connector meets the retained arc only at its own arc endpoint** (the mirror of
`cli_arc_head`, with the tilt margin taken at the `ta` end). -/
lemma cli_arc_tail {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData} (D : SweepData d)
    {σ a b M C μ m δ σsep : ℝ}
    (hM : 0 ≤ M) (hC : 0 < C) (hμ : 0 < μ) (hm : 0 < m) (hδ : 0 < δ)
    (hlip : ∀ s t' : ℝ, ‖r s - r t'‖ ≤ M * |s - t'|)
    (hvlip : ∀ s t' : ℝ, ‖velocity r s - velocity r t'‖ ≤ C * |t' - s|)
    (hnear : ∀ s t' : ℝ, |s - t'| ≤ δ → (m / 2) * |s - t'| ≤ ‖r s - r t'‖)
    (hfar : ∀ s t' : ℝ, δ ≤ |s - t'| → |s - t'| ≤ period - δ → σsep ≤ ‖r s - r t'‖)
    (hσ : σ ∈ Set.Ioo (0 : ℝ) 1)
    (ha0 : 0 < a) (ha2 : 2 * a < 1) (hb0 : 0 < b) (hb2 : 2 * b < 1)
    (hT : μ ≤ ‖chordTilt (r (taR D σ)) (r (tbR D σ)) (velocity r (taR D σ))‖)
    (hξ1 : a * sweepW' D σ ≤ μ / (2 * C))
    (hξ2 : 4 * C * (b * ‖r (tbR D σ) - r (taR D σ)‖ + M * (a * sweepW' D σ)) ≤ m * μ)
    (hsep : b * ‖r (tbR D σ) - r (taR D σ)‖ + M * (a * sweepW' D σ) < σsep)
    (harc : Set.InjOn (fun ξ : ℝ => sweepArc' r D σ ξ) (Set.Icc a (1 - a)))
    (hmid : ∀ ξ ∈ Set.Icc a (1 - a), ∀ ξ' ∈ Set.Ioo (0 : ℝ) 1,
      sweepArc' r D σ ξ ≠ sweepChord' r D σ ξ') :
    ∀ c ∈ Set.Icc (0 : ℝ) 1, ∀ ξ ∈ Set.Icc a (1 - a),
      (1 - c) • sweepChord' r D σ b + c • sweepArc' r D σ a
        = sweepArc' r D σ ξ → ξ = a := by
  intro c hc ξ hξ heq
  set eps : ℝ := b * ‖r (tbR D σ) - r (taR D σ)‖ + M * (a * sweepW' D σ) with heps
  have hW := clg_sweepW_pos_lt D hσ
  have hWp : 0 < sweepW' D σ := hW.1
  have hWdef : sweepW' D σ = tbR D σ - taR D σ := rfl
  have hAB : r (taR D σ) ≠ r (tbR D σ) := by
    refine knot_ne_of_sub_mem_Ioo hr ?_ ?_
    · rw [← hWdef]; exact hWp
    · rw [← hWdef]; exact hW.2
  rcases eq_or_lt_of_le hc.1 with hc0 | hc0
  · subst hc0
    simp only [sub_zero, one_smul, zero_smul, add_zero] at heq
    exact absurd heq.symm (hmid ξ hξ b ⟨by linarith [hb0], by linarith [hb2]⟩)
  rcases lt_or_eq_of_le hc.2 with hclt | hc1
  · set n : Space := chordTilt (r (taR D σ)) (r (tbR D σ)) (velocity r (taR D σ)) with hn
    have hnn : inner ℝ n (velocity r (taR D σ)) = ‖n‖ ^ 2 := inner_chordTilt_self hAB _
    have hnμ : μ ≤ ‖n‖ := hT
    have hVn : inner ℝ n (r (tbR D σ) - r (taR D σ)) = 0 := by
      have hsm : r (tbR D σ) - r (taR D σ)
          = ‖r (tbR D σ) - r (taR D σ)‖ • chordDir (r (taR D σ)) (r (tbR D σ)) :=
        (chordDir_smul _ _ hAB).symm
      rw [hsm, inner_smul_right, hn, inner_chordTilt_chordDir hAB]
      ring
    have hsl := cli_slack_at_point hr hC hμ hnn hnμ hvlip
    have hlev : 0 < inner ℝ n (r (taR D σ + a * sweepW' D σ) - r (taR D σ)) := by
      have h1 := hsl.2.1 (a * sweepW' D σ) (by positivity) hξ1
      have h2 : (0 : ℝ) < μ ^ 2 / 2 * (a * sweepW' D σ) := by
        have h3 : 0 < a * sweepW' D σ := mul_pos ha0 hWp
        positivity
      linarith
    -- the crossing parameter
    set x : ℝ := taR D σ + ξ * sweepW' D σ with hxdef
    have hxξ : sweepArc' r D σ ξ = r x := by
      simp only [sweepArc', hxdef]
    have hs : x - taR D σ = ξ * sweepW' D σ := by
      rw [hxdef]; ring
    have hs_ge : a * sweepW' D σ ≤ x - taR D σ := by
      rw [hs]
      exact mul_le_mul_of_nonneg_right hξ.1 hWp.le
    have hs_pos : 0 < x - taR D σ := lt_of_lt_of_le (mul_pos ha0 hWp) hs_ge
    have hs_le : x - taR D σ < period := by
      rw [hs]
      calc ξ * sweepW' D σ ≤ 1 * sweepW' D σ :=
            mul_le_mul_of_nonneg_right (by linarith [hξ.2]) hWp.le
        _ = sweepW' D σ := one_mul _
        _ < period := hW.2
    -- the displacement of the crossing
    have hdisp : ‖r x - r (taR D σ)‖ ≤ eps := by
      have hX : r x = (1 - c) • sweepChord' r D σ b + c • sweepArc' r D σ a := by
        rw [← hxξ]; exact heq.symm
      have hsplit : r x - r (taR D σ)
          = (1 - c) • (sweepChord' r D σ b - r (taR D σ))
            + c • (sweepArc' r D σ a - r (taR D σ)) := by rw [hX]; module
      have hQ : sweepChord' r D σ b - r (taR D σ)
          = b • (r (tbR D σ) - r (taR D σ)) := by
        rw [sweepChord']; module
      have hA : sweepArc' r D σ a - r (taR D σ)
          = r (taR D σ + a * sweepW' D σ) - r (taR D σ) := rfl
      have h2 : ‖sweepChord' r D σ b - r (taR D σ)‖ = b * ‖r (tbR D σ) - r (taR D σ)‖ := by
        rw [hQ, norm_smul, Real.norm_eq_abs, abs_of_pos hb0]
      have h6 : ‖sweepArc' r D σ a - r (taR D σ)‖ ≤ M * (a * sweepW' D σ) := by
        rw [hA]
        have h4 := hlip (taR D σ + a * sweepW' D σ) (taR D σ)
        have h5 : taR D σ + a * sweepW' D σ - taR D σ = a * sweepW' D σ := by ring
        rw [h5, abs_of_pos (mul_pos ha0 hWp)] at h4
        exact h4
      rw [hsplit, heps]
      calc ‖(1 - c) • (sweepChord' r D σ b - r (taR D σ))
            + c • (sweepArc' r D σ a - r (taR D σ))‖
          ≤ ‖(1 - c) • (sweepChord' r D σ b - r (taR D σ))‖
            + ‖c • (sweepArc' r D σ a - r (taR D σ))‖ := norm_add_le _ _
        _ = (1 - c) * ‖sweepChord' r D σ b - r (taR D σ)‖
            + c * ‖sweepArc' r D σ a - r (taR D σ)‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_nonneg (by linarith [hc.2]), abs_of_nonneg hc0.le]
        _ ≤ (1 - c) * (b * ‖r (tbR D σ) - r (taR D σ)‖) + c * (M * (a * sweepW' D σ)) := by
            exact add_le_add (mul_le_mul_of_nonneg_left (le_of_eq h2) (by linarith [hc.2]))
              (mul_le_mul_of_nonneg_left h6 hc0.le)
        _ ≤ b * ‖r (tbR D σ) - r (taR D σ)‖ + M * (a * sweepW' D σ) := by
            have h8 : (0 : ℝ) ≤ b * ‖r (tbR D σ) - r (taR D σ)‖ := by positivity
            have h9 : (0 : ℝ) ≤ M * (a * sweepW' D σ) := mul_nonneg hM (by positivity)
            nlinarith [hc.2, hc0.le, h8, h9]
    -- the exact pairing
    have hkey : inner ℝ n (r x - r (taR D σ))
        = c * inner ℝ n (r (taR D σ + a * sweepW' D σ) - r (taR D σ)) := by
      have hX : r x = (1 - c) • sweepChord' r D σ b + c • sweepArc' r D σ a := by
        rw [← hxξ]; exact heq.symm
      have hsplit : r x - r (taR D σ)
          = (1 - c) • (sweepChord' r D σ b - r (taR D σ))
            + c • (sweepArc' r D σ a - r (taR D σ)) := by rw [hX]; module
      have hQ : sweepChord' r D σ b - r (taR D σ)
          = b • (r (tbR D σ) - r (taR D σ)) := by
        rw [sweepChord']; module
      have hA : sweepArc' r D σ a - r (taR D σ)
          = r (taR D σ + a * sweepW' D σ) - r (taR D σ) := rfl
      rw [hsplit, inner_add_right, inner_smul_right, inner_smul_right, hQ, hA]
      simp only [inner_smul_right, hVn, mul_zero, zero_add]
    have hsmall : 2 * eps ≤ (μ / (2 * C)) * m := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      nlinarith [hξ2]
    by_cases hcaseA : x - taR D σ ≤ δ
    · -- near the tail
      have habs : |x - taR D σ| = x - taR D σ := abs_of_pos hs_pos
      have h1 := hnear x (taR D σ) (by rw [habs]; exact hcaseA)
      rw [habs] at h1
      have hs_small : x - taR D σ ≤ μ / (2 * C) := by
        have h2 : (m / 2) * (x - taR D σ) ≤ eps := by linarith [h1, hdisp]
        have h3 : x - taR D σ ≤ 2 * eps / m := by
          rw [le_div_iff₀ hm]
          nlinarith [h2]
        have h4 : 2 * eps / m ≤ μ / (2 * C) := by
          rw [div_le_iff₀ hm]
          nlinarith [hsmall]
        linarith [h3, h4]
      have hmono := hsl.2.2.2 (a * sweepW' D σ) (x - taR D σ) (by positivity) hs_ge hs_small
      have hmono' : 0 ≤ inner ℝ n (r x - r (taR D σ + a * sweepW' D σ)) := by
        have harg : taR D σ + (x - taR D σ) = x := by ring
        rwa [harg] at hmono
      have hsplit : inner ℝ n (r x - r (taR D σ))
          = inner ℝ n (r x - r (taR D σ + a * sweepW' D σ))
            + inner ℝ n (r (taR D σ + a * sweepW' D σ) - r (taR D σ)) := by
        rw [← inner_add_right]
        congr 1
        abel
      have hge : inner ℝ n (r (taR D σ + a * sweepW' D σ) - r (taR D σ))
          ≤ c * inner ℝ n (r (taR D σ + a * sweepW' D σ) - r (taR D σ)) := by
        rw [← hkey, hsplit]
        linarith [hmono']
      nlinarith [hge, hlev, hclt]
    · by_cases hcaseC : period - δ < x - taR D σ
      · -- wrapped
        have he_pos : 0 < period - (x - taR D σ) := by linarith [hs_le]
        have he_lt : period - (x - taR D σ) < δ := by linarith [hcaseC]
        have he_small : period - (x - taR D σ) ≤ μ / (2 * C) := by
          have habs : |x - period - taR D σ| = period - (x - taR D σ) := by
            rw [abs_of_neg (by linarith [he_pos])]; ring
          have h1 := hnear (x - period) (taR D σ) (by rw [habs]; exact he_lt.le)
          rw [habs] at h1
          have hper : r (x - period) = r x := by
            have h2 := hr.periodic (x - period)
            rw [show x - period + period = x by ring] at h2
            exact h2.symm
          rw [hper] at h1
          have h2 : (m / 2) * (period - (x - taR D σ)) ≤ eps := by linarith [h1, hdisp]
          have h3 : period - (x - taR D σ) ≤ 2 * eps / m := by
            rw [le_div_iff₀ hm]
            nlinarith [h2]
          have h4 : 2 * eps / m ≤ μ / (2 * C) := by
            rw [div_le_iff₀ hm]
            nlinarith [hsmall]
          linarith [h3, h4]
        have hneg : inner ℝ n (r (taR D σ - (period - (x - taR D σ))) - r (taR D σ)) < 0 := by
          have h1 := hsl.1 (period - (x - taR D σ)) he_pos.le he_small
          have h2 : (0 : ℝ) < μ ^ 2 / 2 * (period - (x - taR D σ)) := by positivity
          have h3 : inner ℝ n (r (taR D σ - (period - (x - taR D σ))) - r (taR D σ))
              = - inner ℝ n (r (taR D σ) - r (taR D σ - (period - (x - taR D σ)))) := by
            have h5 : r (taR D σ - (period - (x - taR D σ))) - r (taR D σ)
                = -(r (taR D σ) - r (taR D σ - (period - (x - taR D σ)))) := by abel
            rw [h5, inner_neg_right]
          rw [h3]
          linarith
        have harg : taR D σ - (period - (x - taR D σ)) = x - period := by ring
        rw [harg] at hneg
        have hper : r (x - period) = r x := by
          have h2 := hr.periodic (x - period)
          rw [show x - period + period = x by ring] at h2
          exact h2.symm
        rw [hper] at hneg
        rw [hkey] at hneg
        nlinarith [hneg, hlev, hc0]
      · -- far from the tail
        have hbig : δ ≤ x - taR D σ := le_of_not_ge hcaseA
        have hle : x - taR D σ ≤ period - δ := le_of_not_gt hcaseC
        have habs : |x - taR D σ| = x - taR D σ := abs_of_pos hs_pos
        have h1 := hfar x (taR D σ) (by rw [habs]; exact hbig) (by rw [habs]; exact hle)
        linarith [h1, hdisp, hsep]
  · subst hc1
    simp only [sub_self, zero_smul, zero_add, one_smul] at heq
    exact (harc ⟨le_rfl, by linarith⟩ hξ heq).symm

/-! ## 6. The uniform tilt margin at the head endpoint -/

/-- **Uniform tilt margin at the head endpoint.** -/
lemma cli_exists_tilt_margin_head {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : SweepData d) {a b : ℝ} (hab : a ≤ b)
    (hpos : ∀ s ∈ Set.Icc a b, 0 < sweepW' D s ∧ sweepW' D s < period)
    (hnt : ∀ s ∈ Set.Icc a b, ∀ m : ℝ, r (tbR D s) - r (taR D s) ≠ m • velocity r (tbR D s)) :
    ∃ μ : ℝ, 0 < μ ∧ ∀ s ∈ Set.Icc a b,
      μ ≤ ‖chordTilt (r (taR D s)) (r (tbR D s)) (velocity r (tbR D s))‖ := by
  have hrc : Continuous r := hr.continuous
  have hvc : Continuous (velocity r) := hr.smooth.continuous_deriv (by simp)
  have hAB : ∀ s ∈ Set.Icc a b, r (taR D s) ≠ r (tbR D s) := fun s hs =>
    knot_ne_of_sub_mem_Ioo hr (by rw [← cli_sweepW_eq_sub]; exact (hpos s hs).1)
      (by rw [← cli_sweepW_eq_sub]; exact (hpos s hs).2)
  have hdel : ContinuousOn (fun s => r (tbR D s) - r (taR D s)) (Set.Icc a b) :=
    ((hrc.comp (cli_continuous_tbR D)).sub (hrc.comp (cli_continuous_taR D))).continuousOn
  have hnorm : ContinuousOn (fun s => ‖r (tbR D s) - r (taR D s)‖) (Set.Icc a b) := hdel.norm
  have hinv : ContinuousOn (fun s => (‖r (tbR D s) - r (taR D s)‖)⁻¹) (Set.Icc a b) :=
    hnorm.inv₀ (fun s hs => norm_ne_zero_iff.mpr (sub_ne_zero.mpr (Ne.symm (hAB s hs))))
  have hcd : ContinuousOn (fun s => chordDir (r (taR D s)) (r (tbR D s))) (Set.Icc a b) := by
    show ContinuousOn
      (fun s => (‖r (tbR D s) - r (taR D s)‖)⁻¹ • (r (tbR D s) - r (taR D s))) (Set.Icc a b)
    exact hinv.smul hdel
  have hv : ContinuousOn (fun s => velocity r (tbR D s)) (Set.Icc a b) :=
    (hvc.comp (cli_continuous_tbR D)).continuousOn
  have hinner : ContinuousOn
      (fun s => inner ℝ (velocity r (tbR D s)) (chordDir (r (taR D s)) (r (tbR D s))))
      (Set.Icc a b) := hv.inner hcd
  have htilt : ContinuousOn
      (fun s => chordTilt (r (taR D s)) (r (tbR D s)) (velocity r (tbR D s))) (Set.Icc a b) := by
    show ContinuousOn (fun s => velocity r (tbR D s)
      - inner ℝ (velocity r (tbR D s)) (chordDir (r (taR D s)) (r (tbR D s)))
        • chordDir (r (taR D s)) (r (tbR D s))) (Set.Icc a b)
    exact hv.sub (hinner.smul hcd)
  have hF : ContinuousOn
      (fun s => ‖chordTilt (r (taR D s)) (r (tbR D s)) (velocity r (tbR D s))‖) (Set.Icc a b) :=
    htilt.norm
  obtain ⟨s₀, hs₀, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨a, le_rfl, hab⟩ hF
  refine ⟨‖chordTilt (r (taR D s₀)) (r (tbR D s₀)) (velocity r (tbR D s₀))‖, ?_,
    fun s hs => hmin hs⟩
  exact norm_pos_iff.mpr
    (chordTilt_ne_zero_of_not_smul (hAB s₀ hs₀) (hr.regular (tbR D s₀)) (hnt s₀ hs₀))

/-! ## 7. A uniform lower bound for the chord length on the window -/

/-- **The chord length is bounded below on the window.** -/
lemma cli_exists_chordLen_pos {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : SweepData d) {a b : ℝ} (hab : a ≤ b)
    (hV : ∀ s ∈ Set.Icc a b, r (taR D s) ≠ r (tbR D s)) :
    ∃ Lmin : ℝ, 0 < Lmin ∧ ∀ s ∈ Set.Icc a b, Lmin ≤ ‖r (tbR D s) - r (taR D s)‖ := by
  have hcont : ContinuousOn (fun s => ‖r (tbR D s) - r (taR D s)‖) (Set.Icc a b) :=
    (((hr.continuous.comp (cli_continuous_tbR D)).sub
      (hr.continuous.comp (cli_continuous_taR D))).norm).continuousOn
  obtain ⟨s₀, hs₀, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨a, le_rfl, hab⟩ hcont
  exact ⟨‖r (tbR D s₀) - r (taR D s₀)‖, norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm (hV s₀ hs₀))),
    fun s hs => hmin hs⟩

/-! ## 8. The profile-to-loop passage -/

/-- Injectivity of the loop on one period follows from injectivity of its profile. -/
lemma cli_injOn_chamferLoopGen_of_profile {r : ℝ → Space} {d : BandArcData} (D : SweepData d)
    {lay : ℝ} {α β : ℝ → ℝ} {σ : ℝ}
    (hprof : Set.InjOn (chamferProfGen r D lay (α σ) (β σ) σ) (Set.Ico (0 : ℝ) 1)) :
    Set.InjOn (chamferLoopGen r D lay α β σ) (Set.Ico 0 period) := by
  intro t₁ ht₁ t₂ ht₂ h
  simp only [chamferLoopGen_eq_prof] at h
  have hpar : sweepParam t₁ = sweepParam t₂ :=
    hprof (sweepParam_mem t₁) (sweepParam_mem t₂) h
  rw [sweepParam_eq_div ht₁, sweepParam_eq_div ht₂] at hpar
  have h3 : t₁ / period * period = t₂ / period * period := by rw [hpar]
  rwa [div_mul_cancel₀ t₁ period_ne_zero, div_mul_cancel₀ t₂ period_ne_zero] at h3

/-! ## 9. The main theorem -/

theorem chamferLoopGenInjOnNt {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r)
    {d : LeanEval.KnotTheory.Quadrisecant.BandArcData} (D : Work.Drive.SweepData d)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (hV : ∀ σ ∈ Set.Icc a b, r (Work.Drive.taR D σ) ≠ r (Work.Drive.tbR D σ))
    (hntA : ∀ σ ∈ Set.Icc a b, ∀ m : ℝ,
      r (Work.Drive.tbR D σ) - r (Work.Drive.taR D σ) ≠
        m • LeanEval.KnotTheory.Quadrisecant.velocity r (Work.Drive.taR D σ))
    (hntB : ∀ σ ∈ Set.Icc a b, ∀ m : ℝ,
      r (Work.Drive.tbR D σ) - r (Work.Drive.taR D σ) ≠
        m • LeanEval.KnotTheory.Quadrisecant.velocity r (Work.Drive.tbR D σ))
    {κ₁ κ₂ : ℝ} (hκ₁ : 0 < κ₁) (hκ₁₂ : κ₁ ≤ κ₂) :
    ∃ L : ℝ, 0 < L ∧ L ≤ 1 / 4 ∧ ∀ lay : ℝ, 0 < lay → lay ≤ L → κ₂ * lay < 1 / 2 →
      ∀ α β : ℝ → ℝ, ∀ σ ∈ Set.Icc a b,
        α σ = lay → κ₁ * lay ≤ β σ → β σ ≤ κ₂ * lay →
        (∀ u : ℝ, Work.Drive.taR D σ + lay * Work.Drive.sweepW' D σ ≤ u →
          u ≤ Work.Drive.tbR D σ - lay * Work.Drive.sweepW' D σ →
          r u ∉ openSegment ℝ (r (Work.Drive.taR D σ)) (r (Work.Drive.tbR D σ))) →
        Set.InjOn (Work.Drive.chamferLoopGen r D lay α β σ)
          (Set.Ico 0 LeanEval.KnotTheory.Quadrisecant.period) := by
  classical
  have hp : 0 < period := period_pos
  have hκ₂ : 0 < κ₂ := lt_of_lt_of_le hκ₁ hκ₁₂
  have h1κ₂ : 0 < 1 + κ₂ := by linarith
  -- the window
  have hσIoo : ∀ σ ∈ Set.Icc a b, σ ∈ Set.Ioo (0 : ℝ) 1 := fun σ hσ =>
    ⟨lt_of_lt_of_le ha hσ.1, lt_of_le_of_lt hσ.2 hb⟩
  have hposab : ∀ σ ∈ Set.Icc a b, 0 < sweepW' D σ ∧ sweepW' D σ < period := fun σ hσ =>
    clg_sweepW_pos_lt D (hσIoo σ hσ)
  have hposab' : ∀ σ ∈ Set.Icc a b, 0 < tbR D σ - taR D σ ∧ tbR D σ - taR D σ < period := by
    intro σ hσ
    have h := hposab σ hσ
    rwa [cli_sweepW_eq_sub] at h
  -- the uniform separation bounds for the knot
  obtain ⟨m, δ, σsep, hm, hδ, hδhalf, hσpo, hbounds⟩ :=
    uniformBoundsC1 (F := fun t (_s : ℝ) => r t)
      ((hr.smooth.comp contDiff_fst).of_le le_top)
      (fun s _ => isCInfKnot_of_isSmoothKnot hr)
  have hvel : ∀ t : ℝ, m ≤ ‖velocity r t‖ :=
    fun t => (hbounds 0 ⟨le_rfl, zero_le_one⟩).1 t
  have hnear : ∀ s t' : ℝ, |s - t'| ≤ δ → (m / 2) * |s - t'| ≤ ‖r s - r t'‖ := by
    intro s t' h
    have h1 := (hbounds 0 ⟨le_rfl, zero_le_one⟩).2.1 s t' (by rwa [abs_sub_comm])
    rwa [abs_sub_comm] at h1
  have hfar : ∀ s t' : ℝ, δ ≤ |s - t'| → |s - t'| ≤ period - δ → σsep ≤ ‖r s - r t'‖ := by
    intro s t' h1 h2
    exact (hbounds 0 ⟨le_rfl, zero_le_one⟩).2.2 s t' (by rwa [abs_sub_comm])
      (by rwa [abs_sub_comm])
  -- a Lipschitz constant for the knot and one for the velocity
  obtain ⟨m₂, M₂, C, hm₂, hM₂, hC, hvelub1, hvelub2, hvlip⟩ := exists_knot_c2_bounds hr
  have hlip : ∀ s t' : ℝ, ‖r s - r t'‖ ≤ M₂ * |s - t'| := by
    intro s t'
    have h := norm_sub_le_of_velocity_bound hr.smooth hvelub2 s t'
    rwa [norm_sub_rev, abs_sub_comm] at h
  -- the tilt margins
  obtain ⟨μa, hμa, hμa'⟩ := exists_tilt_margin hr (taR D) (tbR D) (cli_continuous_taR D)
    (cli_continuous_tbR D) hab.le hposab' hntA
  obtain ⟨μb, hμb, hμb'⟩ := cli_exists_tilt_margin_head hr D hab.le hposab hntB
  obtain ⟨Lmin, hLminpos, hLmin⟩ := cli_exists_chordLen_pos hr D hab.le hV
  set μ : ℝ := min μa μb with hμdef
  have hμpos : 0 < μ := lt_min hμa hμb
  have hμa_le : μ ≤ μa := min_le_left _ _
  have hμb_le : μ ≤ μb := min_le_right _ _
  -- the constants
  have hden1 : 0 < 4 * C * M₂ * period * (1 + κ₂) := by positivity
  have hden2 : 0 < 2 * M₂ * period * (1 + κ₂) := by positivity
  have hden3 : 0 < 2 * C * period := by positivity
  have hden4 : 0 < 4 * M₂ * period * (1 + κ₂) := by positivity
  set L : ℝ := min (1 / 4)
    (min (m * μ / (4 * C * M₂ * period * (1 + κ₂)))
      (min (σsep / (2 * M₂ * period * (1 + κ₂)))
        (min (μ / (2 * C * period)) (Lmin / (4 * M₂ * period * (1 + κ₂)))))) with hLdef
  have hLpos : 0 < L := by
    rw [hLdef]
    exact lt_min (by norm_num)
      (lt_min (by positivity) (lt_min (by positivity) (lt_min (by positivity) (by positivity))))
  have hL1 : L ≤ 1 / 4 := by rw [hLdef]; exact min_le_left _ _
  have hL2 : L ≤ m * μ / (4 * C * M₂ * period * (1 + κ₂)) := by
    rw [hLdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hL3 : L ≤ σsep / (2 * M₂ * period * (1 + κ₂)) := by
    rw [hLdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hL4 : L ≤ μ / (2 * C * period) := by
    rw [hLdef]
    exact le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hL5 : L ≤ Lmin / (4 * M₂ * period * (1 + κ₂)) := by
    rw [hLdef]
    exact le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  refine ⟨L, hLpos, hL1, ?_⟩
  intro lay hlay hleL hκ₂lay α β σ hσ hα_eq hβlo hβhi hmid
  have hσI := hσIoo σ hσ
  have hW := clg_sweepW_pos_lt D hσI
  have ha0 : 0 < lay := hlay
  have ha2 : 2 * lay < 1 := by linarith [hleL, hL1]
  have hlay2 : lay < 1 / 2 := by linarith
  have hb0 : 0 < β σ := lt_of_lt_of_le (mul_pos hκ₁ hlay) hβlo
  have hb2 : 2 * β σ < 1 := by linarith [hβhi, hκ₂lay]
  have hbκ : β σ ≤ κ₂ * lay := hβhi
  -- the chord length bound
  have hLle : ‖r (tbR D σ) - r (taR D σ)‖ ≤ M₂ * period := by
    have h1 := hlip (tbR D σ) (taR D σ)
    have h2 : |tbR D σ - taR D σ| = sweepW' D σ := by
      rw [← cli_sweepW_eq_sub]; exact abs_of_pos hW.1
    rw [h2] at h1
    nlinarith [h1, hW.2, hM₂]
  have hLge : Lmin ≤ ‖r (tbR D σ) - r (taR D σ)‖ := hLmin σ hσ
  -- the depth bound
  have heps_le : β σ * ‖r (tbR D σ) - r (taR D σ)‖ + M₂ * (lay * sweepW' D σ)
      ≤ lay * M₂ * period * (1 + κ₂) := by
    have h1 : β σ * ‖r (tbR D σ) - r (taR D σ)‖ ≤ (κ₂ * lay) * (M₂ * period) :=
      mul_le_mul hbκ hLle (norm_nonneg _) (by positivity)
    have h2 : M₂ * (lay * sweepW' D σ) ≤ M₂ * (lay * period) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hW.2.le hlay.le) hM₂.le
    have h3 : (κ₂ * lay) * (M₂ * period) + M₂ * (lay * period) = lay * M₂ * period * (1 + κ₂) := by
      ring
    linarith [h1, h2, h3.le, h3.ge]
  have hξ1 : lay * sweepW' D σ ≤ μ / (2 * C) := by
    have h2 : lay ≤ μ / (2 * C * period) := le_trans hleL hL4
    rw [le_div_iff₀ hden3] at h2
    have h4 : lay * period ≤ μ / (2 * C) := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * C)]
      nlinarith [h2]
    have h3 : lay * sweepW' D σ ≤ lay * period := mul_le_mul_of_nonneg_left hW.2.le hlay.le
    linarith
  have hε4 : 4 * C * (β σ * ‖r (tbR D σ) - r (taR D σ)‖ + M₂ * (lay * sweepW' D σ)) ≤ m * μ := by
    have h1 : 4 * C * (β σ * ‖r (tbR D σ) - r (taR D σ)‖ + M₂ * (lay * sweepW' D σ))
        ≤ 4 * C * (lay * M₂ * period * (1 + κ₂)) := by
      have h2 := mul_le_mul_of_nonneg_left heps_le (by positivity : (0 : ℝ) ≤ 4 * C)
      linarith [h2]
    have h2 : lay ≤ m * μ / (4 * C * M₂ * period * (1 + κ₂)) := le_trans hleL hL2
    rw [le_div_iff₀ hden1] at h2
    nlinarith [h1, h2]
  have hεsep : β σ * ‖r (tbR D σ) - r (taR D σ)‖ + M₂ * (lay * sweepW' D σ) < σsep := by
    have h2 : lay ≤ σsep / (2 * M₂ * period * (1 + κ₂)) := le_trans hleL hL3
    rw [le_div_iff₀ hden2] at h2
    have h1 : lay * M₂ * period * (1 + κ₂) ≤ σsep / 2 := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      nlinarith [h2]
    linarith [heps_le, h1]
  have hεgap : 2 * (M₂ * (lay * sweepW' D σ) + β σ * ‖r (tbR D σ) - r (taR D σ)‖)
      < ‖r (tbR D σ) - r (taR D σ)‖ := by
    have h3 : lay ≤ Lmin / (4 * M₂ * period * (1 + κ₂)) := le_trans hleL hL5
    rw [le_div_iff₀ hden4] at h3
    have h2 : 2 * (lay * M₂ * period * (1 + κ₂)) ≤ Lmin / 2 := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      nlinarith [h3]
    have h4 : 2 * (M₂ * (lay * sweepW' D σ) + β σ * ‖r (tbR D σ) - r (taR D σ)‖)
        ≤ 2 * (lay * M₂ * period * (1 + κ₂)) := by
      have h5 : M₂ * (lay * sweepW' D σ) ≤ M₂ * (lay * period) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hW.2.le hlay.le) hM₂.le
      have h6 : β σ * ‖r (tbR D σ) - r (taR D σ)‖ ≤ (κ₂ * lay) * (M₂ * period) :=
        mul_le_mul hbκ hLle (norm_nonneg _) (by positivity)
      have h7 : (κ₂ * lay) * (M₂ * period) + M₂ * (lay * period)
          = lay * M₂ * period * (1 + κ₂) := by ring
      nlinarith [h5, h6, h7.le, h7.ge]
    linarith [h4, h2, hLge, hLminpos]
  -- the separations
  have hTh : μ ≤ ‖chordTilt (r (taR D σ)) (r (tbR D σ)) (velocity r (tbR D σ))‖ :=
    le_trans hμb_le (hμb' σ hσ)
  have hTt : μ ≤ ‖chordTilt (r (taR D σ)) (r (tbR D σ)) (velocity r (taR D σ))‖ :=
    le_trans hμa_le (hμa' σ hσ)
  have harc := clg_arc_injOn hr D hσI ha0 ha2
  have hAB : r (taR D σ) ≠ r (tbR D σ) := hV σ hσ
  have hchord : Set.InjOn (fun ξ : ℝ => sweepChord' r D σ ξ) (Set.Icc (β σ) (1 - β σ)) :=
    clg_chord_injOn D hAB
  have hac : ∀ ξ ∈ Set.Icc lay (1 - lay), ∀ ξ' ∈ Set.Ioo (0 : ℝ) 1,
      sweepArc' r D σ ξ ≠ sweepChord' r D σ ξ' :=
    clg_arc_ne_chord D hσI ha0 ha2 hmid
  have hhd := cli_arc_head hr D hM₂.le hC hμpos hm hδ hlip hvlip hnear hfar hσI ha0 ha2 hb0 hb2
    hTh hξ1 hε4 hεsep harc hac
  have htl := cli_arc_tail hr D hM₂.le hC hμpos hm hδ hlip hvlip hnear hfar hσI ha0 ha2 hb0 hb2
    hTt hξ1 hε4 hεsep harc hac
  have hct := cli_chord_tail hr D hC hμpos hvlip hσI ha0 ha2 hb0 hb2 hTt hξ1
  have hch := cli_chord_head hr D hC hμpos hvlip hσI ha0 ha2 hb0 hb2 hTh hξ1
  have hdj := cli_chamfers_disjoint D hM₂.le ha0 hb0 hW.1 hlip hεgap
  have hprof : Set.InjOn (chamferProfGen r D lay lay (β σ) σ) (Set.Ico (0 : ℝ) 1) :=
    chamferProfGen_injOn_of_separation D hlay hlay2 ha0 ha2 hb0 hb2 harc hchord hac hhd htl hct hch hdj
  have hprof' : Set.InjOn (chamferProfGen r D lay (α σ) (β σ) σ) (Set.Ico (0 : ℝ) 1) := by
    simpa [hα_eq] using hprof
  exact cli_injOn_chamferLoopGen_of_profile D hprof'

end Work.Drive

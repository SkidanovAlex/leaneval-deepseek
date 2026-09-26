import Mathlib
import Submission.Work.Drive.shiftedNeedleChart
import Submission.Work.Drive.arcPointDeviationBound
import Submission.Work.Drive.chordEndNormLower

/-!
# `Work.Drive.exists_needleChartFrame` — the chart frame of the shifted needle

The needle `N = needleFam r D lam δ₁ δ₂ ε` is a thin lens whose chord is the segment between
`chordEndA r D δ₂ ε` and `chordEndB r D δ₂ ε`.  This module supplies the frame in which the needle is
charted: the unit chord direction `v`, a unit normal `e ⊥ v`, and the positivity of the `e`-height
`Work.Drive.nHeight r D lam δ₁ δ₂ ε e 0` of the shifted needle's base point above the chord's *line*.

The mathematical content is small but it is the only place where the non-degeneracy of the needle's
chord and the off-line-ness of its base point are used:

* the blurred chord is non-degenerate (`Work.Drive.chordEndNormLower`: the weighted width
  `∫ v, sweepBump v * sweepW' D (ε - δ₂ v)` of the retained arcs is positive — `sweepW'` is positive
  on `(0,1)`, which the window `[ε - δ₂, ε + δ₂] ⊆ (ε/2, 3ε/2) ⊂ (0,1)` guarantees for small `ε` —
  and it is dominated by the chord length);
* the needle's base point `needleFam … (period/4)` does not lie on the chord's affine line, which is
  exactly the hypothesis of the statement;

and then the frame is obtained by elementary Hilbert-space algebra
(`Work.Drive.exists_unitFrame_of_offLine`): take `v` to be the unit vector along `B - A` and `e` the
normalisation of the component of `P - A` orthogonal to `v`.
-/

noncomputable section
namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology

/-- **The frame extracted from a point off the line of a nondegenerate chord.**  If `B ≠ A` and `P`
does not lie on the affine line through `A` and `B`, there is an orthonormal frame `(e, v)` whose
second vector is the unit chord direction, whose first vector is orthogonal to the chord, and which
pairs positively with `P - A`.  This is the algebraic content of
`Work.Drive.exists_needleChartFrame`. -/
lemma exists_unitFrame_of_offLine {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {A B P : E} (hAB : B - A ≠ 0)
    (h : ∀ s : ℝ, P ≠ (1 - s) • A + s • B) :
    ∃ e v : E, ‖e‖ = 1 ∧ ‖v‖ = 1 ∧ inner ℝ e v = 0 ∧
      0 < ‖B - A‖ ∧ B - A = ‖B - A‖ • v ∧ 0 < inner ℝ (P - A) e := by
  have hℓpos : 0 < ‖B - A‖ := norm_pos_iff.mpr hAB
  have hℓne : ‖B - A‖ ≠ 0 := ne_of_gt hℓpos
  set v : E := (‖B - A‖)⁻¹ • (B - A) with hv
  have hvnorm : ‖v‖ = 1 := by
    rw [hv, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      inv_mul_cancel₀ hℓne]
  have hvchord : B - A = ‖B - A‖ • v := (smul_inv_smul₀ hℓne (B - A)).symm
  have hvv : inner ℝ v v = 1 := by rw [real_inner_self_eq_norm_sq, hvnorm]; norm_num
  set c : ℝ := inner ℝ (P - A) v with hc
  set w : E := (P - A) - c • v with hw
  have hwv : inner ℝ w v = 0 := by
    rw [hw, hc, inner_sub_left, real_inner_smul_left, hvv, mul_one, sub_self]
  have hvw : inner ℝ v w = 0 := by rw [real_inner_comm, hwv]
  have hwne : w ≠ 0 := by
    intro hwz
    have hPA : P - A = c • v := by
      rw [hw] at hwz
      exact sub_eq_zero.mp hwz
    have hPA' : P - A = (c / ‖B - A‖) • (B - A) := by
      rw [hPA, hv, smul_smul, div_eq_mul_inv]
    have hP2 : P = (c / ‖B - A‖) • (B - A) + A := by
      rw [sub_eq_iff_eq_add] at hPA'
      exact hPA'
    have h2 : (c / ‖B - A‖) • (B - A) + A
        = (1 - c / ‖B - A‖) • A + (c / ‖B - A‖) • B := by
      rw [smul_sub, sub_smul, one_smul]
      abel
    exact h _ (hP2.trans h2)
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hwne
  have hwnorm : ‖w‖ ≠ 0 := ne_of_gt hwpos
  have hPw : inner ℝ (P - A) w = ‖w‖ ^ 2 := by
    have hdec : P - A = w + c • v := by rw [hw]; abel
    rw [hdec, inner_add_left, real_inner_smul_left, hvw, mul_zero, add_zero,
      real_inner_self_eq_norm_sq]
  refine ⟨(‖w‖)⁻¹ • w, v, ?_, hvnorm, ?_, hℓpos, hvchord, ?_⟩
  · rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ hwnorm]
  · rw [real_inner_smul_left, hwv, mul_zero]
  · rw [real_inner_smul_right, hPw]
    have : (‖w‖)⁻¹ * ‖w‖ ^ 2 = ‖w‖ := by
      rw [sq, ← mul_assoc, inv_mul_cancel₀ hwnorm, one_mul]
    rw [this]
    exact hwpos

/-- **The weighted width of the retained arcs over the sweep window is positive.**  For `0 < ε` with
`3ε/2 < 1` and `0 ≤ δ₂ ≤ ε/2`, every point of the window `[ε - δ₂, ε + δ₂]` lies in `(0,1)`, where
both the bump `sweepBump` and the width `sweepW'` are positive; hence the integral is positive. -/
lemma sweepBump_mul_sweepW'_integral_pos {d : BandArcData} (D : SweepData d) {δ₂ ε : ℝ}
    (hε0 : 0 < ε) (hδ₂0 : 0 ≤ δ₂) (hδ₂ : δ₂ ≤ ε / 2) (hε1 : 3 * ε / 2 < 1) :
    0 < ∫ v in (-1 : ℝ)..1, sweepBump v * sweepW' D (ε - δ₂ * v) := by
  have hcont : Continuous fun v : ℝ => sweepBump v * sweepW' D (ε - δ₂ * v) :=
    sweepBump_continuous.mul ((continuous_sweepW' D).comp
      (continuous_const.sub (continuous_const.mul continuous_id)))
  refine intervalIntegral.intervalIntegral_pos_of_pos_on (hcont.intervalIntegrable _ _) ?_
    (by norm_num)
  intro v hv
  obtain ⟨hv1, hv2⟩ := hv
  have hσ1 : 0 < ε - δ₂ * v := by
    have h1 : δ₂ * v ≤ δ₂ * 1 := mul_le_mul_of_nonneg_left hv2.le hδ₂0
    linarith
  have hσ2 : ε - δ₂ * v < 1 := by
    have h1 : δ₂ * (-1) ≤ δ₂ * v := mul_le_mul_of_nonneg_left hv1.le hδ₂0
    linarith
  refine mul_pos (sweepBump_pos hv1 hv2) ?_
  have hsw : sweepW' D (ε - δ₂ * v) = sweepW D ⟨ε - δ₂ * v, ⟨hσ1.le, hσ2.le⟩⟩ :=
    sweepW'_coeU D ⟨ε - δ₂ * v, ⟨hσ1.le, hσ2.le⟩⟩
  rw [hsw]
  exact (sweepW_pos_lt D _ ⟨hσ1, hσ2⟩).1

theorem exists_needleChartFrame {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r)
    {d : LeanEval.KnotTheory.Quadrisecant.BandArcData} (D : Work.Drive.SweepData d) :
    ∃ ε₀ L : ℝ, 0 < ε₀ ∧ 0 < L ∧
      ∀ (lam δ₁ δ₂ ε : ℝ), 0 < lam → lam ≤ L → lam < 1 / 2 → 0 < δ₁ → δ₁ ≤ L →
        0 < δ₂ → δ₂ ≤ L → 0 < ε → ε ≤ ε₀ → δ₂ ≤ ε / 2 →
        (∀ s : ℝ, Work.Drive.needleFam r D lam δ₁ δ₂ ε
              (LeanEval.KnotTheory.Quadrisecant.period / 4)
            ≠ (1 - s) • Work.Drive.chordEndA r D δ₂ ε
              + s • Work.Drive.chordEndB r D δ₂ ε) →
        ∃ e v : LeanEval.KnotTheory.Quadrisecant.Space, ‖e‖ = 1 ∧ ‖v‖ = 1 ∧
          inner ℝ e v = 0 ∧
          0 < ‖Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε‖ ∧
          Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε
            = ‖Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε‖ • v ∧
          0 < Work.Drive.nHeight r D lam δ₁ δ₂ ε e 0 := by
  -- the blurred chord is non-degenerate: the weighted width dominates the chord length
  obtain ⟨ε₁, c, hε₁pos, hcpos, hNorm⟩ := chordEndNormLower hr D
  refine ⟨min ε₁ (1 / 2), 1, lt_min hε₁pos (by norm_num), one_pos, ?_⟩
  intro lam δ₁ δ₂ ε hlam0 hlamL hlamh hδ₁0 hδ₁L hδ₂0 hδ₂L hε0 hεε hδ₂ε hoff
  have hε₁ : ε ≤ ε₁ := le_trans hεε (min_le_left _ _)
  have hεhalf : ε ≤ 1 / 2 := le_trans hεε (min_le_right _ _)
  have hIpos : 0 < ∫ v in (-1 : ℝ)..1, sweepBump v * sweepW' D (ε - δ₂ * v) :=
    sweepBump_mul_sweepW'_integral_pos D hε0 hδ₂0.le hδ₂ε (by linarith)
  have hℓ : 0 < ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖ :=
    lt_of_lt_of_le (mul_pos hcpos hIpos) (hNorm δ₂ ε hδ₂0 hδ₂ε hε0 hε₁)
  -- the frame, from the off-line hypothesis
  obtain ⟨e, v, he, hv, hev, hℓ', hchord, hpos⟩ :=
    exists_unitFrame_of_offLine (A := chordEndA r D δ₂ ε) (B := chordEndB r D δ₂ ε)
      (P := needleFam r D lam δ₁ δ₂ ε (period / 4)) (norm_pos_iff.mp hℓ) hoff
  exact ⟨e, v, he, hv, hev, hℓ', hchord,
    by simpa only [nHeight, shiftedNeedle, zero_add] using hpos⟩

end Work.Drive

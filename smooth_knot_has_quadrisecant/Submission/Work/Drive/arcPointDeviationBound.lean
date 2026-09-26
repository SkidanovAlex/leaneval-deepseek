import Mathlib
import Submission.Work.Drive.needleProfileDefs
import Submission.Work.Drive.loopDevNormBound
import Submission.Work.Drive.chordEndNormLower

/-!
# `Work.Drive.arcPointDeviationBound` — the arc average deviates from the chord by at most one
eighth of the chord

The needle's *arc side* is the average, over the `σ`-window of the sweep parameter, of the retained
arcs of the loops; the needle's *chord* is the segment between the two blurred endpoints
`chordEndA`, `chordEndB` (`needleProfileDefs.lean`).  This module proves that, for small `ε`, the
average arc point at any fraction `ξ` is within `1/8` of the corresponding point of the needle's
chord:

    ‖ ∫ v, bump v • sweepArc' r D (ε - δ₂ v) ξ - chordEndA - ξ • (chordEndB - chordEndA) ‖
      ≤ (1/8) * ‖chordEndB - chordEndA‖ .

The point is that the average of the loops' deviations is a *second order* quantity in the width
`sweepW'` (`Work.Drive.loopDevNormBound`), while the blurred chord is a *first order* quantity
(`Work.Drive.chordEndNormLower`); the quadratic term is absorbed as soon as the width of the window
is small, i.e. for `ε ≤ ε₀`.

The single identity that drives the estimate is `sweepArc_integral_sub_chordEnds` below: the average
of the arc points minus the (affine) chord term is exactly the average of the loops' deviations
`loopDev`, because `loopDev` is the deviation of the arc from the affine interpolation of the
endpoints and the bump has total mass `1`.
-/

noncomputable section
namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant MeasureTheory
open scoped Real Topology

/-- **The deviation identity.**  The average over the `σ`-window of the retained arc points, minus
the affine interpolation of the blurred endpoints, is the average of the loops' deviations
`loopDev` from their own chords. -/
lemma sweepArc_integral_sub_chordEnds {r : ℝ → Space} (hr : Continuous r) {d : BandArcData}
    (D : SweepData d) (ε δ₂ ξ : ℝ) :
    (∫ v in (-1 : ℝ)..1, sweepBump v • sweepArc' r D (ε - δ₂ * v) ξ)
      - chordEndA r D δ₂ ε - ξ • (chordEndB r D δ₂ ε - chordEndA r D δ₂ ε)
    = ∫ v in (-1 : ℝ)..1, sweepBump v • loopDev r D (ε - δ₂ * v) ξ := by
  have hta : Continuous (taR D) := continuous_taR D
  have htb : Continuous (tbR D) := continuous_tbR D
  have hW : Continuous (sweepW' D) := continuous_sweepW' D
  have hσ : Continuous (fun v : ℝ => ε - δ₂ * v) := by fun_prop
  have hcont_A : Continuous (fun v : ℝ => sweepBump v • r (taR D (ε - δ₂ * v))) :=
    sweepBump_continuous.smul (hr.comp (hta.comp hσ))
  have hcont_B : Continuous (fun v : ℝ => sweepBump v • r (tbR D (ε - δ₂ * v))) :=
    sweepBump_continuous.smul (hr.comp (htb.comp hσ))
  have hcont_L : Continuous (fun v : ℝ => loopDev r D (ε - δ₂ * v) ξ) := by
    show Continuous (fun v : ℝ =>
      r (taR D (ε - δ₂ * v) + ξ * sweepW' D (ε - δ₂ * v))
        - ((1 - ξ) • r (taR D (ε - δ₂ * v)) + ξ • r (tbR D (ε - δ₂ * v))))
    exact (hr.comp ((hta.comp hσ).add (continuous_const.mul (hW.comp hσ)))).sub
      (((hr.comp (hta.comp hσ)).const_smul (1 - ξ)).add
        ((hr.comp (htb.comp hσ)).const_smul ξ))
  have hcont_D : Continuous (fun v : ℝ => sweepBump v • loopDev r D (ε - δ₂ * v) ξ) :=
    sweepBump_continuous.smul hcont_L
  have hA : IntervalIntegrable
      (fun v : ℝ => (1 - ξ) • (sweepBump v • r (taR D (ε - δ₂ * v)))) volume (-1) 1 :=
    (hcont_A.const_smul (1 - ξ)).intervalIntegrable (μ := volume) (-1) 1
  have hB : IntervalIntegrable
      (fun v : ℝ => ξ • (sweepBump v • r (tbR D (ε - δ₂ * v)))) volume (-1) 1 :=
    (hcont_B.const_smul ξ).intervalIntegrable (μ := volume) (-1) 1
  have hGD : IntervalIntegrable
      (fun v : ℝ => sweepBump v • loopDev r D (ε - δ₂ * v) ξ) volume (-1) 1 :=
    hcont_D.intervalIntegrable (μ := volume) (-1) 1
  have hABint : IntervalIntegrable
      (fun v : ℝ => ((1 - ξ) • (sweepBump v • r (taR D (ε - δ₂ * v)))
        + ξ • (sweepBump v • r (tbR D (ε - δ₂ * v))))) volume (-1) 1 := hA.add hB
  have hABeq : (∫ v in (-1 : ℝ)..1,
        ((1 - ξ) • (sweepBump v • r (taR D (ε - δ₂ * v)))
          + ξ • (sweepBump v • r (tbR D (ε - δ₂ * v)))))
      = (1 - ξ) • chordEndA r D δ₂ ε + ξ • chordEndB r D δ₂ ε := by
    have hsplit : (∫ v in (-1 : ℝ)..1,
          ((1 - ξ) • (sweepBump v • r (taR D (ε - δ₂ * v)))
            + ξ • (sweepBump v • r (tbR D (ε - δ₂ * v)))))
        = (∫ v in (-1 : ℝ)..1, (1 - ξ) • (sweepBump v • r (taR D (ε - δ₂ * v))))
          + (∫ v in (-1 : ℝ)..1, ξ • (sweepBump v • r (tbR D (ε - δ₂ * v)))) :=
      intervalIntegral.integral_add hA hB
    have hsm1 : (∫ v in (-1 : ℝ)..1, (1 - ξ) • (sweepBump v • r (taR D (ε - δ₂ * v))))
        = (1 - ξ) • chordEndA r D δ₂ ε :=
      intervalIntegral.integral_smul (1 - ξ)
        (fun v : ℝ => sweepBump v • r (taR D (ε - δ₂ * v)))
    have hsm2 : (∫ v in (-1 : ℝ)..1, ξ • (sweepBump v • r (tbR D (ε - δ₂ * v))))
        = ξ • chordEndB r D δ₂ ε :=
      intervalIntegral.integral_smul ξ
        (fun v : ℝ => sweepBump v • r (tbR D (ε - δ₂ * v)))
    rw [hsplit, hsm1, hsm2]
  have hcongr : (∫ v in (-1 : ℝ)..1, sweepBump v • sweepArc' r D (ε - δ₂ * v) ξ)
      = (∫ v in (-1 : ℝ)..1, (sweepBump v • loopDev r D (ε - δ₂ * v) ξ
          + ((1 - ξ) • (sweepBump v • r (taR D (ε - δ₂ * v)))
            + ξ • (sweepBump v • r (tbR D (ε - δ₂ * v)))))) :=
    intervalIntegral.integral_congr
      (fun v _ => by simp only [sweepArc', loopDev]; module)
  have hsplit2 : (∫ v in (-1 : ℝ)..1, (sweepBump v • loopDev r D (ε - δ₂ * v) ξ
          + ((1 - ξ) • (sweepBump v • r (taR D (ε - δ₂ * v)))
            + ξ • (sweepBump v • r (tbR D (ε - δ₂ * v))))))
      = (∫ v in (-1 : ℝ)..1, sweepBump v • loopDev r D (ε - δ₂ * v) ξ)
        + (∫ v in (-1 : ℝ)..1,
            ((1 - ξ) • (sweepBump v • r (taR D (ε - δ₂ * v)))
              + ξ • (sweepBump v • r (tbR D (ε - δ₂ * v))))) :=
    intervalIntegral.integral_add hGD hABint
  have harc : (∫ v in (-1 : ℝ)..1, sweepBump v • sweepArc' r D (ε - δ₂ * v) ξ)
      = (∫ v in (-1 : ℝ)..1, sweepBump v • loopDev r D (ε - δ₂ * v) ξ)
        + ((1 - ξ) • chordEndA r D δ₂ ε + ξ • chordEndB r D δ₂ ε) := by
    rw [hcongr, hsplit2, hABeq]
  rw [harc]
  module

theorem arcPointDeviationBound {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r)
    {d : LeanEval.KnotTheory.Quadrisecant.BandArcData} (D : Work.Drive.SweepData d) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ (δ₂ ε : ℝ), 0 < δ₂ → δ₂ ≤ ε / 2 → 0 < ε → ε ≤ ε₀ →
        ∀ ξ : ℝ, 0 ≤ ξ → ξ ≤ 1 →
          ‖(∫ v in (-1 : ℝ)..1, Work.Drive.sweepBump v •
                Work.Drive.sweepArc' r D (ε - δ₂ * v) ξ)
              - Work.Drive.chordEndA r D δ₂ ε
              - ξ • (Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε)‖
            ≤ (1 / 8) * ‖Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε‖ := by
  obtain ⟨C, hCpos, hDev⟩ := loopDevNormBound hr D
  obtain ⟨ε₁, c, hε₁pos, hcpos, hNorm⟩ := chordEndNormLower hr D
  set M : ℝ := c / (8 * C) with hMdef
  have hMpos : 0 < M := by rw [hMdef]; positivity
  have hCM : C * M = c / 8 := by rw [hMdef]; field_simp
  have hW0 : sweepW' D 0 = 0 := by
    simp only [sweepW']
    rw [tbR_zero_eq_taR_zero D, sub_self]
  obtain ⟨η, hηpos, hη⟩ := exists_abs_sub_le_of_continuousAt
      (f := sweepW' D) (x := 0) (continuous_sweepW' D).continuousAt hMpos
  have hη' : ∀ y : ℝ, |y| ≤ η → sweepW' D y ≤ M := by
    intro y hy
    have h := hη y (by simpa using hy)
    rw [hW0, sub_zero] at h
    rwa [abs_of_nonneg (loopDevNormBound_sweepW'_nonneg D y)] at h
  refine ⟨min (η / 2) ε₁, lt_min (by linarith) hε₁pos, ?_⟩
  intro δ₂ ε hδ₂pos hδ₂le hεpos hεle ξ hξ0 hξ1
  have hεη : ε ≤ η / 2 := le_trans hεle (min_le_left _ _)
  have hεε₁ : ε ≤ ε₁ := le_trans hεle (min_le_right _ _)
  -- the width of the retained arc is uniformly small on the window
  have hWbound : ∀ v : ℝ, |v| ≤ 1 → sweepW' D (ε - δ₂ * v) ≤ M := by
    intro v hv
    apply hη'
    have h1 : |ε - δ₂ * v| ≤ ε + δ₂ * |v| := by
      have h := abs_sub_le ε 0 (δ₂ * v)
      rw [sub_zero, zero_sub, abs_neg, abs_of_pos hεpos, abs_mul, abs_of_pos hδ₂pos] at h
      exact h
    have h2 : δ₂ * |v| ≤ δ₂ := by
      calc δ₂ * |v| ≤ δ₂ * 1 := mul_le_mul_of_nonneg_left hv hδ₂pos.le
        _ = δ₂ := mul_one _
    have h3 : ε + δ₂ ≤ 3 * ε / 2 := by linarith
    have h4 : 3 * ε / 2 ≤ η := by linarith [hεη, hηpos]
    linarith
  -- the blurred chord is bounded below by the average width
  have hInt : (∫ v in (-1 : ℝ)..1, sweepBump v * sweepW' D (ε - δ₂ * v))
      ≤ (1 / c) * ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖ := by
    have h := hNorm δ₂ ε hδ₂pos hδ₂le hεpos hεε₁
    rw [one_div, inv_mul_eq_div]
    exact (le_div_iff₀ hcpos).mpr (by rw [mul_comm]; exact h)
  have hta : Continuous (taR D) := continuous_taR D
  have htb : Continuous (tbR D) := continuous_tbR D
  have hWc : Continuous (sweepW' D) := continuous_sweepW' D
  have hσ : Continuous (fun v : ℝ => ε - δ₂ * v) := by fun_prop
  have hcont_L : Continuous (fun v : ℝ => loopDev r D (ε - δ₂ * v) ξ) := by
    show Continuous (fun v : ℝ =>
      r (taR D (ε - δ₂ * v) + ξ * sweepW' D (ε - δ₂ * v))
        - ((1 - ξ) • r (taR D (ε - δ₂ * v)) + ξ • r (tbR D (ε - δ₂ * v))))
    exact (hr.smooth.continuous.comp
        ((hta.comp hσ).add (continuous_const.mul (hWc.comp hσ)))).sub
      (((hr.smooth.continuous.comp (hta.comp hσ)).const_smul (1 - ξ)).add
        ((hr.smooth.continuous.comp (htb.comp hσ)).const_smul ξ))
  have hf2 : IntervalIntegrable
      (fun v : ℝ => sweepBump v * ‖loopDev r D (ε - δ₂ * v) ξ‖) volume (-1) 1 :=
    (sweepBump_continuous.mul hcont_L.norm).intervalIntegrable (μ := volume) (-1) 1
  have hf3 : IntervalIntegrable
      (fun v : ℝ => sweepBump v * (C * (sweepW' D (ε - δ₂ * v)) ^ 2)) volume (-1) 1 :=
    (sweepBump_continuous.mul (continuous_const.mul ((hWc.comp hσ).pow 2))).intervalIntegrable
      (μ := volume) (-1) 1
  have hf4 : IntervalIntegrable
      (fun v : ℝ => sweepBump v * (C * M * sweepW' D (ε - δ₂ * v))) volume (-1) 1 :=
    (sweepBump_continuous.mul (continuous_const.mul (hWc.comp hσ))).intervalIntegrable
      (μ := volume) (-1) 1
  have hnorm : ‖∫ v in (-1 : ℝ)..1, sweepBump v • loopDev r D (ε - δ₂ * v) ξ‖
      ≤ (1 / 8) * ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖ := by
    calc ‖∫ v in (-1 : ℝ)..1, sweepBump v • loopDev r D (ε - δ₂ * v) ξ‖
        ≤ ∫ v in (-1 : ℝ)..1, ‖sweepBump v • loopDev r D (ε - δ₂ * v) ξ‖ :=
          intervalIntegral.norm_integral_le_integral_norm (by norm_num)
      _ = ∫ v in (-1 : ℝ)..1, sweepBump v * ‖loopDev r D (ε - δ₂ * v) ξ‖ := by
          refine intervalIntegral.integral_congr (fun v _ => ?_)
          rw [norm_smul, Real.norm_of_nonneg (sweepBump_nonneg v)]
      _ ≤ ∫ v in (-1 : ℝ)..1, sweepBump v * (C * (sweepW' D (ε - δ₂ * v)) ^ 2) := by
          refine intervalIntegral.integral_mono_on (by norm_num) hf2 hf3 (fun v _ => ?_)
          refine mul_le_mul_of_nonneg_left ?_ (sweepBump_nonneg v)
          exact hDev (ε - δ₂ * v) ξ hξ0 hξ1
      _ ≤ ∫ v in (-1 : ℝ)..1, sweepBump v * (C * M * sweepW' D (ε - δ₂ * v)) := by
          refine intervalIntegral.integral_mono_on (by norm_num) hf3 hf4 (fun v hv => ?_)
          refine mul_le_mul_of_nonneg_left ?_ (sweepBump_nonneg v)
          have hv1 : |v| ≤ 1 := abs_le.mpr ⟨hv.1, hv.2⟩
          have hWnn : 0 ≤ sweepW' D (ε - δ₂ * v) := loopDevNormBound_sweepW'_nonneg D _
          have hWM : sweepW' D (ε - δ₂ * v) ≤ M := hWbound v hv1
          calc C * (sweepW' D (ε - δ₂ * v)) ^ 2
              = C * sweepW' D (ε - δ₂ * v) * sweepW' D (ε - δ₂ * v) := by ring
            _ ≤ C * sweepW' D (ε - δ₂ * v) * M :=
                mul_le_mul_of_nonneg_left hWM (mul_nonneg hCpos.le hWnn)
            _ = C * M * sweepW' D (ε - δ₂ * v) := by ring
      _ = C * M * (∫ v in (-1 : ℝ)..1, sweepBump v * sweepW' D (ε - δ₂ * v)) := by
          rw [show (∫ v in (-1 : ℝ)..1,
                sweepBump v * (C * M * sweepW' D (ε - δ₂ * v)))
              = ∫ v in (-1 : ℝ)..1,
                  (C * M) * (sweepBump v * sweepW' D (ε - δ₂ * v)) from
              intervalIntegral.integral_congr (fun v _ => by ring)]
          rw [intervalIntegral.integral_const_mul]
      _ ≤ (1 / 8) * ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖ := by
          rw [hCM]
          calc (c / 8) * (∫ v in (-1 : ℝ)..1, sweepBump v * sweepW' D (ε - δ₂ * v))
              ≤ (c / 8) * ((1 / c) * ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖) :=
                mul_le_mul_of_nonneg_left hInt (by positivity)
            _ = (1 / 8) * ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖ := by
                field_simp
  rw [sweepArc_integral_sub_chordEnds hr.smooth.continuous D ε δ₂ ξ]
  exact hnorm

end Work.Drive

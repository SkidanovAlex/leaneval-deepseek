import Mathlib
import Submission.Work.Drive.needleProfileDefs
import Submission.Work.Drive.chamfer2_avgAux

/-!
# `Work.Drive.chordEndNormLower` — a lower bound for the blurred chord length

The needle's chord is the straight segment between its two blurred endpoints
`chordEndA r D δ₂ ε`, `chordEndB r D δ₂ ε` (`needleProfileDefs.lean`).  This module proves that,
for small `ε` and `δ₂ ≤ ε/2`, the *length* of that chord dominates a positive multiple of the
average width `sweepW' D (ε - δ₂ * v)` of the retained arcs in the `σ`-window: the two blurred
endpoints are both within a small neighbourhood of the common base point `taR D 0 = tbR D 0`, so
each chord `r (tbR D σ) - r (taR D σ)` has a positive component along a *fixed* direction (the
unit tangent at the base point) and the blurred difference inherits a positive such component:

    (m₀/2) * ∫ v, bump v * sweepW' D (ε - δ₂ * v) ≤ ⟪chordEndB - chordEndA, u₀⟫
                                                 ≤ ‖chordEndB - chordEndA‖ ,

where `m₀ = ‖velocity r (taR D 0)‖ > 0` and `u₀ = m₀⁻¹ • velocity r (taR D 0)` is the unit
tangent there.  The pointwise ingredient is the mean value theorem (here: the fundamental theorem
of calculus for `s ↦ ⟪r s, u₀⟫`) applied on the short parameter interval between the two lift
values: `⟪r b - r a, u₀⟫ = ∫_a^b ⟪velocity r s, u₀⟫ ds ≥ (m₀/2) * (b - a)`.
-/

noncomputable section
namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant MeasureTheory
open scoped Real Topology

section Helpers

/-- Clamping an element of the unit interval is the identity. -/
lemma clampI_coeU (s : Set.Icc (0:ℝ) 1) : clampI (s : ℝ) = s := by
  apply Subtype.ext
  show min 1 (max 0 (s : ℝ)) = (s : ℝ)
  rw [max_eq_right s.2.1, min_eq_right s.2.2]

/-- The width at a unit-interval parameter, read at the real parameter. -/
lemma sweepW'_coeU {d : BandArcData} (D : SweepData d) (s : Set.Icc (0:ℝ) 1) :
    sweepW' D (s : ℝ) = sweepW D s := by
  simp [sweepW', sweepW, taR, tbR, clampI_coeU]

/-- The two lift values at the real parameter `0` coincide (the band arc starts at a point). -/
lemma tbR_zero_eq_taR_zero {d : BandArcData} (D : SweepData d) : tbR D 0 = taR D 0 := by
  have h : clampI (0 : ℝ) = (0 : Set.Icc (0:ℝ) 1) := Subtype.ext (by simp [clampI])
  simp only [taR, tbR]
  rw [h]
  exact D.left_eq.symm

/-- The inner product commutes with the interval integral of a bumped vector. -/
lemma inner_intervalIntegral_smul_bump (u : Space) {g : ℝ → Space} (hg : Continuous g) :
    inner ℝ u (∫ v in (-1 : ℝ)..1, sweepBump v • g v)
      = ∫ v in (-1 : ℝ)..1, sweepBump v * inner ℝ u (g v) := by
  have hc : Continuous fun v : ℝ => sweepBump v • g v := sweepBump_continuous.smul hg
  change (innerSL ℝ u) (∫ v in (-1 : ℝ)..1, sweepBump v • g v)
      = ∫ v in (-1 : ℝ)..1, sweepBump v * inner ℝ u (g v)
  rw [← ContinuousLinearMap.intervalIntegral_comp_comm (innerSL ℝ u)
      (hc.intervalIntegrable (-1) 1)]
  refine intervalIntegral.integral_congr (fun v _ => ?_)
  show inner ℝ u (sweepBump v • g v) = sweepBump v * inner ℝ u (g v)
  rw [inner_smul_right]

/-- **Pointwise chord bound.**  If a parameter `σ` is between `0` and `1` and both lift values
`taR D σ`, `tbR D σ` lie within `ρ` of the base point `q`, and `u` is a direction in which the
velocity is bounded below by `m0/2` on that `ρ`-neighbourhood of `q`, then the chord
`r (tbR D σ) - r (taR D σ)` has `u`-component at least `(m0/2) * sweepW' D σ`. -/
lemma inner_chord_end_ge {r : ℝ → Space} (hr : IsSmoothKnot r)
    {q m0 ρ : ℝ} {u : Space}
    (hρ : ∀ s : ℝ, |s - q| ≤ ρ → m0 / 2 ≤ inner ℝ (velocity r s) u)
    {d : BandArcData} {D : SweepData d} {σ : ℝ}
    (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (ha : |taR D σ - q| ≤ ρ) (hb : |tbR D σ - q| ≤ ρ) :
    (m0 / 2) * sweepW' D σ ≤ inner ℝ u (r (tbR D σ) - r (taR D σ)) := by
  have hσI : sweepW' D σ = sweepW D ⟨σ, ⟨hσ0.le, hσ1.le⟩⟩ :=
    sweepW'_coeU D ⟨σ, ⟨hσ0.le, hσ1.le⟩⟩
  have hWpos : 0 < sweepW' D σ := by
    rw [hσI]
    exact (sweepW_pos_lt D _ ⟨hσ0, hσ1⟩).1
  have hab : taR D σ < tbR D σ := by
    have h : sweepW' D σ = tbR D σ - taR D σ := rfl
    linarith [hWpos, h.symm]
  have hderiv : ∀ x ∈ Set.uIcc (taR D σ) (tbR D σ),
      HasDerivAt (fun s : ℝ => inner ℝ (r s) u) (inner ℝ (velocity r x) u) x := by
    intro x hx
    have h1 : HasDerivAt (fun s : ℝ => r s) (velocity r x) x :=
      ((hr.smooth.differentiable (by simp)) x).hasDerivAt
    have h2 : HasDerivAt (fun _ : ℝ => u) 0 x := hasDerivAt_const x u
    have h3 := h1.inner ℝ h2
    simpa using h3
  have hcont1 : IntervalIntegrable (fun s : ℝ => inner ℝ (velocity r s) u) volume
      (taR D σ) (tbR D σ) :=
    ((hr.smooth.continuous_deriv (by simp)).inner continuous_const).intervalIntegrable _ _
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont1
  have hle : ∀ x ∈ Set.Icc (taR D σ) (tbR D σ), m0 / 2 ≤ inner ℝ (velocity r x) u := by
    intro x hx
    apply hρ
    have ha' : q - ρ ≤ taR D σ := by
      have := (abs_le.mp ha).1; linarith
    have hb' : tbR D σ ≤ q + ρ := by
      have := (abs_le.mp hb).2; linarith
    exact abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hmono := intervalIntegral.integral_mono_on hab.le
    (continuous_const.intervalIntegrable (taR D σ) (tbR D σ)) hcont1 hle
  have hconst : ∫ x in (taR D σ)..(tbR D σ), (m0 / 2) = (m0 / 2) * sweepW' D σ := by
    rw [intervalIntegral.integral_const]
    simp [sweepW', smul_eq_mul, mul_comm]
  calc (m0 / 2) * sweepW' D σ
      = ∫ x in (taR D σ)..(tbR D σ), (m0 / 2) := hconst.symm
    _ ≤ ∫ x in (taR D σ)..(tbR D σ), inner ℝ (velocity r x) u := hmono
    _ = inner ℝ (r (tbR D σ)) u - inner ℝ (r (taR D σ)) u := hFTC
    _ = inner ℝ u (r (tbR D σ) - r (taR D σ)) := by
          simp only [inner_sub_right, real_inner_comm]

/-- Continuity at a point gives a closed neighbourhood on which the values are within `c`. -/
lemma exists_abs_sub_le_of_continuousAt {f : ℝ → ℝ} {x c : ℝ} (hf : ContinuousAt f x)
    (hc : 0 < c) : ∃ δ : ℝ, 0 < δ ∧ ∀ y : ℝ, |y - x| ≤ δ → |f y - f x| ≤ c := by
  rw [Metric.continuousAt_iff] at hf
  obtain ⟨δ, hδpos, hδ⟩ := hf c hc
  refine ⟨δ / 2, by linarith, fun y hy => ?_⟩
  have h1 : dist y x < δ := by rw [Real.dist_eq]; linarith
  have h2 := hδ h1
  rw [Real.dist_eq] at h2
  exact le_of_lt h2

/-- Continuity at a point gives a closed neighbourhood on which the values stay above a level. -/
lemma exists_le_of_continuousAt {f : ℝ → ℝ} {x c : ℝ} (hf : ContinuousAt f x) (h : c < f x) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y : ℝ, |y - x| ≤ δ → c ≤ f y := by
  obtain ⟨δ, hδpos, hδ⟩ := exists_abs_sub_le_of_continuousAt hf (by linarith : 0 < f x - c)
  refine ⟨δ, hδpos, fun y hy => ?_⟩
  have h1 := (abs_le.mp (hδ y hy)).1
  linarith

end Helpers

theorem chordEndNormLower {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r)
    {d : LeanEval.KnotTheory.Quadrisecant.BandArcData} (D : Work.Drive.SweepData d) :
    ∃ ε₀ c : ℝ, 0 < ε₀ ∧ 0 < c ∧
      ∀ (δ₂ ε : ℝ), 0 < δ₂ → δ₂ ≤ ε / 2 → 0 < ε → ε ≤ ε₀ →
        c * (∫ v in (-1 : ℝ)..1, Work.Drive.sweepBump v * Work.Drive.sweepW' D (ε - δ₂ * v)) ≤
          ‖Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε‖ := by
  have hvcont : Continuous (velocity r) := hr.smooth.continuous_deriv (by simp)
  have hm0pos : 0 < ‖velocity r (taR D 0)‖ := norm_pos_iff.mpr (hr.regular _)
  have hne : ‖velocity r (taR D 0)‖ ≠ 0 := ne_of_gt hm0pos
  have hu : inner ℝ (velocity r (taR D 0))
      ((‖velocity r (taR D 0)‖)⁻¹ • velocity r (taR D 0)) = ‖velocity r (taR D 0)‖ := by
    rw [inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  have hu_norm : ‖(‖velocity r (taR D 0)‖)⁻¹ • velocity r (taR D 0)‖ = 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ hne]
  -- a closed neighbourhood of the base point on which the velocity is bounded below in `u`
  obtain ⟨ρ₀, hρ₀pos, hρ₀⟩ : ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ s : ℝ, |s - taR D 0| ≤ ρ₀ →
      ‖velocity r (taR D 0)‖ / 2 ≤
        inner ℝ (velocity r s) ((‖velocity r (taR D 0)‖)⁻¹ • velocity r (taR D 0)) := by
    have hct : ContinuousAt (fun s : ℝ => inner ℝ (velocity r s)
        ((‖velocity r (taR D 0)‖)⁻¹ • velocity r (taR D 0))) (taR D 0) :=
      (hvcont.inner continuous_const).continuousAt
    have hlt : ‖velocity r (taR D 0)‖ / 2 < inner ℝ (velocity r (taR D 0))
        ((‖velocity r (taR D 0)‖)⁻¹ • velocity r (taR D 0)) := by rw [hu]; linarith
    exact exists_le_of_continuousAt hct hlt
  -- a neighbourhood of `0` on which both lift values stay close to their common value at `0`
  obtain ⟨ε₂, hε₂pos, hε₂⟩ : ∃ ε₂ : ℝ, 0 < ε₂ ∧ ∀ σ : ℝ, |σ| ≤ ε₂ →
      |taR D σ - taR D 0| ≤ ρ₀ ∧ |tbR D σ - taR D 0| ≤ ρ₀ := by
    obtain ⟨δa, hδapos, hδa⟩ : ∃ δa : ℝ, 0 < δa ∧
        ∀ σ : ℝ, |σ - 0| ≤ δa → |taR D σ - taR D 0| ≤ ρ₀ :=
      exists_abs_sub_le_of_continuousAt (x := 0) (continuous_taR D).continuousAt hρ₀pos
    obtain ⟨δb, hδbpos, hδb⟩ : ∃ δb : ℝ, 0 < δb ∧
        ∀ σ : ℝ, |σ - 0| ≤ δb → |tbR D σ - tbR D 0| ≤ ρ₀ :=
      exists_abs_sub_le_of_continuousAt (x := 0) (continuous_tbR D).continuousAt hρ₀pos
    refine ⟨min δa δb, lt_min hδapos hδbpos, fun σ hσ => ⟨?_, ?_⟩⟩
    · apply hδa
      simpa using le_trans hσ (min_le_left _ _)
    · have h := hδb σ (by simpa using le_trans hσ (min_le_right _ _))
      rwa [tbR_zero_eq_taR_zero D] at h
  refine ⟨min (2 * ε₂ / 3) (1 / 2), ‖velocity r (taR D 0)‖ / 2, ?_, by positivity, ?_⟩
  · exact lt_min (by linarith) (by norm_num)
  · intro δ₂ ε hδ₂pos hδ₂le hεpos hεle
    set u0 : Space := (‖velocity r (taR D 0)‖)⁻¹ • velocity r (taR D 0) with hu0
    set c0 : ℝ := ‖velocity r (taR D 0)‖ / 2 with hc0
    have hρ : ∀ s : ℝ, |s - taR D 0| ≤ ρ₀ → c0 ≤ inner ℝ (velocity r s) u0 := hρ₀
    have hu_norm' : ‖u0‖ = 1 := hu_norm
    have hca : Continuous fun v : ℝ => taR D (ε - δ₂ * v) :=
      (continuous_taR D).comp (continuous_const.sub (continuous_const.mul continuous_id))
    have hcb : Continuous fun v : ℝ => tbR D (ε - δ₂ * v) :=
      (continuous_tbR D).comp (continuous_const.sub (continuous_const.mul continuous_id))
    have hcr : Continuous r := hr.smooth.continuous
    have hGA : Continuous fun v : ℝ => sweepBump v • r (taR D (ε - δ₂ * v)) :=
      sweepBump_continuous.smul (hcr.comp hca)
    have hGB : Continuous fun v : ℝ => sweepBump v • r (tbR D (ε - δ₂ * v)) :=
      sweepBump_continuous.smul (hcr.comp hcb)
    have hG : Continuous fun v : ℝ =>
        r (tbR D (ε - δ₂ * v)) - r (taR D (ε - δ₂ * v)) :=
      (hcr.comp hcb).sub (hcr.comp hca)
    have hWc : Continuous fun v : ℝ => sweepW' D (ε - δ₂ * v) :=
      (continuous_sweepW' D).comp (continuous_const.sub (continuous_const.mul continuous_id))
    -- the chord endpoints as an integral of the pointwise chords
    have hvec : chordEndB r D δ₂ ε - chordEndA r D δ₂ ε
        = ∫ v in (-1 : ℝ)..1, sweepBump v •
            (r (tbR D (ε - δ₂ * v)) - r (taR D (ε - δ₂ * v))) := by
      rw [chordEndB, chordEndA, ← intervalIntegral.integral_sub
        (hGB.intervalIntegrable _ _) (hGA.intervalIntegrable _ _)]
      refine intervalIntegral.integral_congr (fun v _ => ?_)
      rw [smul_sub]
    have hinner : inner ℝ u0 (chordEndB r D δ₂ ε - chordEndA r D δ₂ ε)
        = ∫ v in (-1 : ℝ)..1, sweepBump v *
            inner ℝ u0 (r (tbR D (ε - δ₂ * v)) - r (taR D (ε - δ₂ * v))) := by
      rw [hvec]
      exact inner_intervalIntegral_smul_bump u0 hG
    -- the pointwise bound
    have hpt : ∀ v ∈ Set.Icc (-1 : ℝ) 1, sweepBump v * (c0 * sweepW' D (ε - δ₂ * v)) ≤
        sweepBump v * inner ℝ u0 (r (tbR D (ε - δ₂ * v)) - r (taR D (ε - δ₂ * v))) := by
      intro v hv
      refine mul_le_mul_of_nonneg_left ?_ (sweepBump_nonneg v)
      obtain ⟨hv1, hv2⟩ := hv
      have hδ₂nn : 0 ≤ δ₂ := hδ₂pos.le
      have hσge : ε / 2 ≤ ε - δ₂ * v := by
        have h1 : δ₂ * v ≤ δ₂ * 1 := mul_le_mul_of_nonneg_left hv2 hδ₂nn
        have h2 : δ₂ * 1 ≤ ε / 2 := by simpa using hδ₂le
        linarith
      have hσle : ε - δ₂ * v ≤ 3 * ε / 2 := by
        have h1 : δ₂ * (-1) ≤ δ₂ * v := mul_le_mul_of_nonneg_left hv1 hδ₂nn
        linarith
      have hσpos : 0 < ε - δ₂ * v := by linarith [hεpos, hσge]
      have hσlt1 : ε - δ₂ * v < 1 := by
        have hε1 : ε ≤ 1 / 2 := le_trans hεle (min_le_right _ _)
        linarith
      have hσabs : |ε - δ₂ * v| ≤ ε₂ := by
        rw [abs_of_pos hσpos]
        have hε2 : ε ≤ 2 * ε₂ / 3 := le_trans hεle (min_le_left _ _)
        linarith
      obtain ⟨ha, hb⟩ := hε₂ (ε - δ₂ * v) hσabs
      exact inner_chord_end_ge hr hρ hσpos hσlt1 ha hb
    have hmono_int : ∫ v in (-1 : ℝ)..1, sweepBump v * (c0 * sweepW' D (ε - δ₂ * v)) ≤
        ∫ v in (-1 : ℝ)..1, sweepBump v *
          inner ℝ u0 (r (tbR D (ε - δ₂ * v)) - r (taR D (ε - δ₂ * v))) := by
      refine intervalIntegral.integral_mono_on (by norm_num) ?_ ?_ hpt
      · exact (sweepBump_continuous.mul (continuous_const.mul hWc)).intervalIntegrable _ _
      · have hgi : Continuous fun v : ℝ =>
            inner ℝ u0 (r (tbR D (ε - δ₂ * v)) - r (taR D (ε - δ₂ * v))) :=
          Continuous.inner (𝕜 := ℝ) continuous_const hG
        exact (sweepBump_continuous.mul hgi).intervalIntegrable _ _
    have hci : c0 * (∫ v in (-1 : ℝ)..1, sweepBump v * sweepW' D (ε - δ₂ * v))
        = ∫ v in (-1 : ℝ)..1, sweepBump v * (c0 * sweepW' D (ε - δ₂ * v)) := by
      have hA : ∫ v in (-1 : ℝ)..1, sweepBump v * (c0 * sweepW' D (ε - δ₂ * v))
          = ∫ v in (-1 : ℝ)..1, c0 * (sweepBump v * sweepW' D (ε - δ₂ * v)) :=
        intervalIntegral.integral_congr (fun v _ => by ring)
      rw [hA, intervalIntegral.integral_const_mul]
    have hnorm : inner ℝ (chordEndB r D δ₂ ε - chordEndA r D δ₂ ε) u0
        ≤ ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖ := by
      calc inner ℝ (chordEndB r D δ₂ ε - chordEndA r D δ₂ ε) u0
          ≤ ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖ * ‖u0‖ := real_inner_le_norm _ _
        _ = ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖ := by rw [hu_norm', mul_one]
    calc c0 * (∫ v in (-1 : ℝ)..1, sweepBump v * sweepW' D (ε - δ₂ * v))
        = ∫ v in (-1 : ℝ)..1, sweepBump v * (c0 * sweepW' D (ε - δ₂ * v)) := hci
      _ ≤ ∫ v in (-1 : ℝ)..1, sweepBump v *
            inner ℝ u0 (r (tbR D (ε - δ₂ * v)) - r (taR D (ε - δ₂ * v))) := hmono_int
      _ = inner ℝ u0 (chordEndB r D δ₂ ε - chordEndA r D δ₂ ε) := hinner.symm
      _ = inner ℝ (chordEndB r D δ₂ ε - chordEndA r D δ₂ ε) u0 := real_inner_comm _ _
      _ ≤ ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖ := hnorm


end Work.Drive

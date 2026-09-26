import Mathlib
import Submission.Work.Drive.shiftedNeedleDefs
import Submission.Work.Drive.arcPointDeviationBound

/-!
# `Work.Drive.loopBlur_chart` — the blurred loop point in the chord chart

The `σ`-blurred loop point `loopBlur r D lam δ₂ ε τ` is the average of the chamfered loop points
over the sweep window.  Every loop point at loop parameter `τ` is a convex combination of the
retained arc's point and the chord's point at the *same* fraction `needleFrac lam τ` (with a weight
`needleW lam τ` that depends only on `lam` and `τ`).  Averaging, and applying the deviation bound
`arcPointDeviationBound` to the arc part, gives the chart estimate

    |⟪loopBlur τ - chordEndA, v⟫ - ‖chordEndB - chordEndA‖ * needleFrac lam τ|
      ≤ (1/8) * ‖chordEndB - chordEndA‖

for any unit `v` along the chord.  The chord part of the loop contributes *exactly* its fraction of
the chord (the blur of an affine interpolation of the same two blurred endpoints is that affine
interpolation), and only the arc part enters the estimate — through the width estimate of
`arcPointDeviationBound`.  The weight `needleW` keeps the arc part's coefficient in `[0,1]`.

## Main definitions

* `Work.Drive.needleW lam τ` — the chamfer weight of the loop parameter: the fraction of the chord
  point in the convex combination which is the loop point at `τ`.
-/
noncomputable section
namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant MeasureTheory
open scoped Real Topology intervalIntegral

/-- The chamfer weight of the loop parameter: writing the loop point at loop parameter `τ` as the
convex combination `(1 - needleW lam τ) • (arc point at fraction needleFrac lam τ)
+ needleW lam τ • (chord point at fraction needleFrac lam τ)`. -/
def needleW (lam τ : ℝ) : ℝ :=
  if sweepParam τ ≤ 1 / 2 then 0
  else if sweepParam τ ≤ 1 / 2 + lam / 2 then (2 * sweepParam τ - 1) / lam
  else if sweepParam τ ≤ 1 - lam / 2 then 1
  else 1 - (sweepParam τ - (1 - lam / 2)) / (lam / 2)

lemma needleW_mem {lam τ : ℝ} (h0 : 0 < lam) (h1 : lam < 1 / 2) :
    0 ≤ needleW lam τ ∧ needleW lam τ ≤ 1 := by
  have hu := sweepParam_mem τ
  rw [needleW]
  by_cases h : sweepParam τ ≤ 1 / 2
  · rw [if_pos h]; norm_num
  · rw [if_neg h]
    by_cases h2 : sweepParam τ ≤ 1 / 2 + lam / 2
    · rw [if_pos h2]
      have hnum0 : 0 ≤ 2 * sweepParam τ - 1 := by linarith [lt_of_not_ge h]
      have hnum1 : 2 * sweepParam τ - 1 ≤ lam := by linarith
      exact ⟨div_nonneg hnum0 h0.le, (div_le_one h0).mpr hnum1⟩
    · rw [if_neg h2]
      by_cases h3 : sweepParam τ ≤ 1 - lam / 2
      · rw [if_pos h3]; norm_num
      · rw [if_neg h3]
        have hgt : 0 < sweepParam τ - (1 - lam / 2) := by linarith [lt_of_not_ge h3]
        have hlt : sweepParam τ - (1 - lam / 2) < lam / 2 := by linarith [hu.2]
        have hb : (0 : ℝ) < lam / 2 := by linarith
        have hs0 : 0 ≤ (sweepParam τ - (1 - lam / 2)) / (lam / 2) := div_nonneg hgt.le hb.le
        have hs1 : (sweepParam τ - (1 - lam / 2)) / (lam / 2) ≤ 1 := (div_le_one hb).mpr hlt.le
        constructor <;> linarith

lemma sweepLoopChamfer_eq_combo {r : ℝ → Space} {d : BandArcData} (D : SweepData d)
    {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1 / 2) (s τ : ℝ) :
    sweepLoopChamfer r D lam s τ
      = (1 - needleW lam τ) • sweepArc' r D s (needleFrac lam τ)
        + needleW lam τ • sweepChord' r D s (needleFrac lam τ) := by
  rw [sweepLoopChamfer_eq_profile r D h0 (by linarith)]
  rw [sweepLoopProfile, needleFrac, needleW, sweepChordParam]
  by_cases h : sweepParam τ ≤ 1 / 2
  · rw [if_pos h, if_pos h, if_pos h]; module
  · rw [if_neg h, if_neg h, if_neg h]
    by_cases h2 : sweepParam τ ≤ 1 / 2 + lam / 2
    · rw [if_pos h2, if_pos h2, if_pos h2]
    · rw [if_neg h2, if_neg h2, if_neg h2]
      by_cases h3 : sweepParam τ ≤ 1 - lam / 2
      · rw [if_pos h3, if_pos h3, if_pos h3]; module
      · rw [if_neg h3, if_neg h3, if_neg h3]; module

lemma continuous_sweepArc'_sigma {r : ℝ → Space} (hr : Continuous r) {d : BandArcData}
    (D : SweepData d) (δ₂ ε ξ : ℝ) :
    Continuous (fun v : ℝ => sweepArc' r D (ε - δ₂ * v) ξ) := by
  have h1 : Continuous (fun v : ℝ => taR D (ε - δ₂ * v)) :=
    (continuous_taR D).comp (by fun_prop)
  have h2 : Continuous (fun v : ℝ => ξ * sweepW' D (ε - δ₂ * v)) :=
    continuous_const.mul ((continuous_sweepW' D).comp (by fun_prop))
  show Continuous (fun v : ℝ => r (taR D (ε - δ₂ * v) + ξ * sweepW' D (ε - δ₂ * v)))
  exact hr.comp (h1.add h2)

lemma continuous_sweepChord'_sigma {r : ℝ → Space} (hr : Continuous r) {d : BandArcData}
    (D : SweepData d) (δ₂ ε ξ : ℝ) :
    Continuous (fun v : ℝ => sweepChord' r D (ε - δ₂ * v) ξ) := by
  have h1 : Continuous (fun v : ℝ => r (taR D (ε - δ₂ * v))) :=
    hr.comp ((continuous_taR D).comp (by fun_prop))
  have h2 : Continuous (fun v : ℝ => r (tbR D (ε - δ₂ * v))) :=
    hr.comp ((continuous_tbR D).comp (by fun_prop))
  show Continuous (fun v : ℝ => (1 - ξ) • r (taR D (ε - δ₂ * v)) + ξ • r (tbR D (ε - δ₂ * v)))
  exact (h1.const_smul (1 - ξ)).add (h2.const_smul ξ)

lemma integral_bump_sweepChord {r : ℝ → Space} (hr : Continuous r) {d : BandArcData}
    (D : SweepData d) (δ₂ ε ξ : ℝ) :
    (∫ v in (-1 : ℝ)..1, sweepBump v • sweepChord' r D (ε - δ₂ * v) ξ)
      = (1 - ξ) • chordEndA r D δ₂ ε + ξ • chordEndB r D δ₂ ε := by
  have hcontA : Continuous (fun v : ℝ => sweepBump v • r (taR D (ε - δ₂ * v))) :=
    sweepBump_continuous.smul (hr.comp ((continuous_taR D).comp (by fun_prop)))
  have hcontB : Continuous (fun v : ℝ => sweepBump v • r (tbR D (ε - δ₂ * v))) :=
    sweepBump_continuous.smul (hr.comp ((continuous_tbR D).comp (by fun_prop)))
  have hIA : IntervalIntegrable (fun v : ℝ => (1 - ξ) • (sweepBump v • r (taR D (ε - δ₂ * v))))
      volume (-1 : ℝ) 1 := (hcontA.const_smul (1 - ξ)).intervalIntegrable _ _
  have hIB : IntervalIntegrable (fun v : ℝ => ξ • (sweepBump v • r (tbR D (ε - δ₂ * v))))
      volume (-1 : ℝ) 1 := (hcontB.const_smul ξ).intervalIntegrable _ _
  calc (∫ v in (-1 : ℝ)..1, sweepBump v • sweepChord' r D (ε - δ₂ * v) ξ)
      = ∫ v in (-1 : ℝ)..1, ((1 - ξ) • (sweepBump v • r (taR D (ε - δ₂ * v)))
          + ξ • (sweepBump v • r (tbR D (ε - δ₂ * v)))) := by
        refine intervalIntegral.integral_congr (fun v _ => ?_)
        show sweepBump v • ((1 - ξ) • r (taR D (ε - δ₂ * v)) + ξ • r (tbR D (ε - δ₂ * v))) = _
        simp only [smul_add, smul_smul]
        rw [mul_comm (sweepBump v) (1 - ξ), mul_comm (sweepBump v) ξ]
    _ = (∫ v in (-1 : ℝ)..1, (1 - ξ) • (sweepBump v • r (taR D (ε - δ₂ * v))))
          + (∫ v in (-1 : ℝ)..1, ξ • (sweepBump v • r (tbR D (ε - δ₂ * v)))) := by
        rw [intervalIntegral.integral_add hIA hIB]
    _ = (1 - ξ) • (∫ v in (-1 : ℝ)..1, sweepBump v • r (taR D (ε - δ₂ * v)))
          + ξ • (∫ v in (-1 : ℝ)..1, sweepBump v • r (tbR D (ε - δ₂ * v))) := by
        rw [intervalIntegral.integral_smul, intervalIntegral.integral_smul]
    _ = (1 - ξ) • chordEndA r D δ₂ ε + ξ • chordEndB r D δ₂ ε := rfl

lemma inner_chordB_sub_chordA {r : ℝ → Space} {d : BandArcData} (D : SweepData d)
    (δ₂ ε : ℝ) {v : Space} (hv : ‖v‖ = 1)
    (hV : chordEndB r D δ₂ ε - chordEndA r D δ₂ ε
      = ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖ • v) :
    inner ℝ (chordEndB r D δ₂ ε - chordEndA r D δ₂ ε) v
      = ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖ := by
  calc inner ℝ (chordEndB r D δ₂ ε - chordEndA r D δ₂ ε) v
      = inner ℝ (‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖ • v) v :=
        congrArg (fun z => inner ℝ z v) hV
    _ = ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖ * inner ℝ v v := by
        rw [real_inner_smul_left]
    _ = ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖ := by
        rw [real_inner_self_eq_norm_sq, hv]; ring

lemma loopBlur_eq_combo {r : ℝ → Space} (hr : Continuous r) {d : BandArcData} (D : SweepData d)
    {lam δ₂ ε : ℝ} (h0 : 0 < lam) (h1 : lam < 1 / 2) (τ : ℝ) :
    loopBlur r D lam δ₂ ε τ
      = (1 - needleW lam τ) •
          (∫ v in (-1 : ℝ)..1, sweepBump v • sweepArc' r D (ε - δ₂ * v) (needleFrac lam τ))
        + needleW lam τ •
          ((1 - needleFrac lam τ) • chordEndA r D δ₂ ε
            + needleFrac lam τ • chordEndB r D δ₂ ε) := by
  have hpt : ∀ v : ℝ, sweepLoopChamfer r D lam (ε - δ₂ * v) τ
      = (1 - needleW lam τ) • sweepArc' r D (ε - δ₂ * v) (needleFrac lam τ)
        + needleW lam τ • sweepChord' r D (ε - δ₂ * v) (needleFrac lam τ) :=
    fun v => sweepLoopChamfer_eq_combo D h0 h1 (ε - δ₂ * v) τ
  have hcontX : Continuous (fun v : ℝ =>
      sweepBump v • sweepArc' r D (ε - δ₂ * v) (needleFrac lam τ)) :=
    sweepBump_continuous.smul (continuous_sweepArc'_sigma hr D δ₂ ε (needleFrac lam τ))
  have hcontY : Continuous (fun v : ℝ =>
      sweepBump v • sweepChord' r D (ε - δ₂ * v) (needleFrac lam τ)) :=
    sweepBump_continuous.smul (continuous_sweepChord'_sigma hr D δ₂ ε (needleFrac lam τ))
  calc loopBlur r D lam δ₂ ε τ
      = ∫ v in (-1 : ℝ)..1, sweepBump v • ((1 - needleW lam τ) •
            sweepArc' r D (ε - δ₂ * v) (needleFrac lam τ)
          + needleW lam τ • sweepChord' r D (ε - δ₂ * v) (needleFrac lam τ)) := by
        simp only [loopBlur]
        exact intervalIntegral.integral_congr (fun v _ => by rw [hpt v])
    _ = ∫ v in (-1 : ℝ)..1, ((1 - needleW lam τ) •
            (sweepBump v • sweepArc' r D (ε - δ₂ * v) (needleFrac lam τ))
          + needleW lam τ •
            (sweepBump v • sweepChord' r D (ε - δ₂ * v) (needleFrac lam τ))) := by
        refine intervalIntegral.integral_congr (fun v _ => ?_)
        simp only [smul_add, smul_smul]
        rw [mul_comm (sweepBump v) (1 - needleW lam τ), mul_comm (sweepBump v) (needleW lam τ)]
    _ = (∫ v in (-1 : ℝ)..1, (1 - needleW lam τ) •
            (sweepBump v • sweepArc' r D (ε - δ₂ * v) (needleFrac lam τ)))
          + (∫ v in (-1 : ℝ)..1, needleW lam τ •
            (sweepBump v • sweepChord' r D (ε - δ₂ * v) (needleFrac lam τ))) := by
        rw [intervalIntegral.integral_add
              (f := fun v : ℝ => (1 - needleW lam τ) •
                (sweepBump v • sweepArc' r D (ε - δ₂ * v) (needleFrac lam τ)))
              (g := fun v : ℝ => needleW lam τ •
                (sweepBump v • sweepChord' r D (ε - δ₂ * v) (needleFrac lam τ)))
              ((hcontX.const_smul (1 - needleW lam τ)).intervalIntegrable _ _)
              ((hcontY.const_smul (needleW lam τ)).intervalIntegrable _ _)]
    _ = (1 - needleW lam τ) •
          (∫ v in (-1 : ℝ)..1, sweepBump v • sweepArc' r D (ε - δ₂ * v) (needleFrac lam τ))
        + needleW lam τ •
          ((1 - needleFrac lam τ) • chordEndA r D δ₂ ε
            + needleFrac lam τ • chordEndB r D δ₂ ε) := by
        rw [intervalIntegral.integral_smul, intervalIntegral.integral_smul,
          integral_bump_sweepChord hr D δ₂ ε (needleFrac lam τ)]

theorem loopBlur_chart {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r)
    {d : LeanEval.KnotTheory.Quadrisecant.BandArcData} (D : Work.Drive.SweepData d) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ (lam δ₂ ε : ℝ), 0 < lam → lam < 1 / 2 → 0 < δ₂ → δ₂ ≤ ε / 2 → 0 < ε → ε ≤ ε₀ →
        ∀ v : LeanEval.KnotTheory.Quadrisecant.Space, ‖v‖ = 1 →
          Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε
            = ‖Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε‖ • v →
          ∀ τ : ℝ,
            |inner ℝ (Work.Drive.loopBlur r D lam δ₂ ε τ - Work.Drive.chordEndA r D δ₂ ε) v
              - ‖Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε‖
                * Work.Drive.needleFrac lam τ|
            ≤ (1 / 8) * ‖Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε‖ := by
  obtain ⟨ε₀, hε₀pos, hdev⟩ := arcPointDeviationBound hr D
  refine ⟨ε₀, hε₀pos, ?_⟩
  intro lam δ₂ ε hlam0 hlam12 hδ₂0 hδ₂le hε0 hεle v hv hV τ
  have hrc : Continuous r := hr.smooth.continuous
  obtain ⟨hw0, hw1⟩ := needleW_mem (lam := lam) (τ := τ) hlam0 hlam12
  obtain ⟨hξ0, hξ1⟩ := needleFrac_unit (lam := lam) (τ := τ) hlam0 hlam12
  have hdevb := hdev δ₂ ε hδ₂0 hδ₂le hε0 hεle (needleFrac lam τ) hξ0 hξ1
  have hLB := loopBlur_eq_combo hrc D (δ₂ := δ₂) (ε := ε) hlam0 hlam12 τ
  -- the algebraic reduction
  have hmain : loopBlur r D lam δ₂ ε τ - chordEndA r D δ₂ ε
        - needleFrac lam τ • (chordEndB r D δ₂ ε - chordEndA r D δ₂ ε)
      = (1 - needleW lam τ) •
        ((∫ v in (-1 : ℝ)..1, sweepBump v •
            sweepArc' r D (ε - δ₂ * v) (needleFrac lam τ))
          - chordEndA r D δ₂ ε
          - needleFrac lam τ • (chordEndB r D δ₂ ε - chordEndA r D δ₂ ε)) := by
    rw [hLB]; module
  have hnorm : ‖loopBlur r D lam δ₂ ε τ - chordEndA r D δ₂ ε
        - needleFrac lam τ • (chordEndB r D δ₂ ε - chordEndA r D δ₂ ε)‖
      ≤ (1 / 8) * ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖ := by
    rw [hmain, norm_smul, Real.norm_eq_abs]
    have hw : |1 - needleW lam τ| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    calc |1 - needleW lam τ| * ‖(∫ v in (-1 : ℝ)..1, sweepBump v •
              sweepArc' r D (ε - δ₂ * v) (needleFrac lam τ))
            - chordEndA r D δ₂ ε
            - needleFrac lam τ • (chordEndB r D δ₂ ε - chordEndA r D δ₂ ε)‖
        ≤ 1 * ‖(∫ v in (-1 : ℝ)..1, sweepBump v •
              sweepArc' r D (ε - δ₂ * v) (needleFrac lam τ))
            - chordEndA r D δ₂ ε
            - needleFrac lam τ • (chordEndB r D δ₂ ε - chordEndA r D δ₂ ε)‖ :=
          mul_le_mul_of_nonneg_right hw (norm_nonneg _)
      _ = ‖(∫ v in (-1 : ℝ)..1, sweepBump v •
              sweepArc' r D (ε - δ₂ * v) (needleFrac lam τ))
            - chordEndA r D δ₂ ε
            - needleFrac lam τ • (chordEndB r D δ₂ ε - chordEndA r D δ₂ ε)‖ := one_mul _
      _ ≤ (1 / 8) * ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖ := hdevb
  have hinnerV : inner ℝ (needleFrac lam τ •
        (chordEndB r D δ₂ ε - chordEndA r D δ₂ ε)) v
      = needleFrac lam τ * ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖ := by
    rw [real_inner_smul_left, inner_chordB_sub_chordA D δ₂ ε hv hV]
  have hsplit : inner ℝ (loopBlur r D lam δ₂ ε τ - chordEndA r D δ₂ ε) v
      = inner ℝ (loopBlur r D lam δ₂ ε τ - chordEndA r D δ₂ ε
          - needleFrac lam τ • (chordEndB r D δ₂ ε - chordEndA r D δ₂ ε)) v
        + needleFrac lam τ * ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖ := by
    have h1 : loopBlur r D lam δ₂ ε τ - chordEndA r D δ₂ ε
        = (loopBlur r D lam δ₂ ε τ - chordEndA r D δ₂ ε
            - needleFrac lam τ • (chordEndB r D δ₂ ε - chordEndA r D δ₂ ε))
          + needleFrac lam τ • (chordEndB r D δ₂ ε - chordEndA r D δ₂ ε) := by abel
    conv_lhs => rw [h1]
    rw [inner_add_left, hinnerV]
  have h3 : inner ℝ (loopBlur r D lam δ₂ ε τ - chordEndA r D δ₂ ε) v
        - ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖ * needleFrac lam τ
      = inner ℝ (loopBlur r D lam δ₂ ε τ - chordEndA r D δ₂ ε
          - needleFrac lam τ • (chordEndB r D δ₂ ε - chordEndA r D δ₂ ε)) v := by
    rw [hsplit]; ring
  rw [h3]
  calc |inner ℝ (loopBlur r D lam δ₂ ε τ - chordEndA r D δ₂ ε
          - needleFrac lam τ • (chordEndB r D δ₂ ε - chordEndA r D δ₂ ε)) v|
      ≤ ‖loopBlur r D lam δ₂ ε τ - chordEndA r D δ₂ ε
          - needleFrac lam τ • (chordEndB r D δ₂ ε - chordEndA r D δ₂ ε)‖ * ‖v‖ :=
        abs_real_inner_le_norm _ _
    _ = ‖loopBlur r D lam δ₂ ε τ - chordEndA r D δ₂ ε
          - needleFrac lam τ • (chordEndB r D δ₂ ε - chordEndA r D δ₂ ε)‖ := by
        rw [hv, mul_one]
    _ ≤ (1 / 8) * ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖ := hnorm

end Work.Drive

import Mathlib
import Submission.Work.Drive.sweepBlurFacts
import Submission.Work.Drive.chordSweepSmooth
import Submission.Work.Drive.chordSweepDefs

/-!
# The doubly smoothed chord sweep on its *chord zone*

`Work.Drive.sweepFam r D lam δ₁ δ₂ σ t` is the doubly smoothed chord sweep
(`Submission/Work/Drive/chordSweepSmooth.lean`): the chamfered loop `sweepLoopChamfer` at sweep
parameter `σ`, convolved in the loop parameter `t` with the bump `sweepBump` at scale `δ₁` and then
in the sweep parameter `σ` at scale `δ₂`.

This file evaluates that family **exactly** when the loop-parameter window
`{t - δ₁ u | u ∈ [-1,1]}` lies entirely inside one of the two *chord zones* of the chamfered loop,
i.e. when

`sweepParam (t - δ₁ u) ∈ [1/2 + lam/2, 1 - lam/2]` for all `u ∈ [-1,1]`.

Then the loop is on its chord side everywhere in the window, and — crucially — the chord fraction
`sweepChordParam lam (sweepParam (t - δ₁ u))` is an **affine** function of `u` (the loop parameter
never crosses an integer multiple of the period, so the `⌊·⌋` in `sweepParam` is constant and can be
cancelled).  Since the bump has total mass one and vanishing first moment, convolving an affine map
returns its value at `u = 0` (`Work.Drive.sweepBlur_affine`), so the inner convolution collapses to
the chord at the fraction `sweepChordParam lam (sweepParam t)`, and the outer convolution then only
moves the two *endpoints* of that chord:

    sweepFam r D lam δ₁ δ₂ σ t
      = (1 - ξ) • (∫ v in -1..1, sweepBump v • r (taR D (σ - δ₂ v)))
        + ξ • (∫ v in -1..1, sweepBump v • r (tbR D (σ - δ₂ v))),      ξ = sweepChordParam lam (sweepParam t).

This is the "chord" half of the two-zone decomposition of the sweep (the arc zone is the other
half); it is what shows that, away from the four corner windows, the doubly smoothed slice is a
genuine chord segment of the two blurred endpoints.

## Main statement

* `Work.Drive.sweepFam_chordZone`

## Structure

* `sweepFam_chordZone_param_sub_affine`: on a window on which the loop parameter stays positive,
  `sweepParam (t - δ u) = sweepParam t - δ u / period` — the `⌊·⌋` in `sweepParam` is constant on the
  window (an integer crossing would force `sweepParam = 0`), so the fractional part unwraps;
* `sweepFam_chordZone_chordParam_affine`: `sweepChordParam lam` is affine;
* `sweepFam_chordZone_blur_affine_lin`: the bump-blur of a linear function is its value at `0`;
* `sweepFam_chordZone_loopChamfer_chordZone`: on the chord zone the chamfered loop *is* the chord,
  including at the left corner `sweepParam t = 1/2 + lam/2`, where the chamfer branch and the chord
  branch agree.
-/

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology intervalIntegral

/-! ## Continuity of the two extended branch lifts -/

lemma sweepFam_chordZone_taR_continuous {d : BandArcData} (D : SweepData d) :
    Continuous (taR D) :=
  D.cont_ta.comp
    (Continuous.subtype_mk (continuous_const.min (continuous_const.max continuous_id)) _)

lemma sweepFam_chordZone_tbR_continuous {d : BandArcData} (D : SweepData d) :
    Continuous (tbR D) :=
  D.cont_tb.comp
    (Continuous.subtype_mk (continuous_const.min (continuous_const.max continuous_id)) _)

/-! ## The chord fraction is affine -/

/-- **`sweepChordParam lam` is affine.**  (`1/2 - lam = 0` is harmless: both sides are then the
constant `1 - lam`.) -/
lemma sweepFam_chordZone_chordParam_affine (lam a b u : ℝ) :
    sweepChordParam lam (a + u * (b - a))
      = sweepChordParam lam a + u * (sweepChordParam lam b - sweepChordParam lam a) := by
  simp only [sweepChordParam]
  by_cases h : (1 / 2 : ℝ) - lam = 0
  · rw [h]; simp
  · field_simp
    ring

/-! ## The blur of a linear function -/

/-- **The bump-blur of a linear function is its value at the centre.**  Immediate from
`Work.Drive.sweepBlur_affine` (`∫ sweepBump = 1` and `∫ u * sweepBump u = 0`). -/
lemma sweepFam_chordZone_blur_affine_lin (p w : Space) (A C : ℝ) :
    (∫ u in (-1 : ℝ)..1, sweepBump u • (p + (A + u * C) • w)) = p + A • w := by
  have h2 : (∫ u in (-1 : ℝ)..1, sweepBump u • (p + (A + u * C) • w))
      = (∫ u in (-1 : ℝ)..1, sweepBump u • (p + (A - (-C) * u) • w)) := by
    refine intervalIntegral.integral_congr (fun u _ => ?_)
    have : A + u * C = A - (-C) * u := by ring
    rw [this]
  rw [h2]
  exact sweepBlur_affine p w A (-C)

/-! ## Unwrapping the loop parameter on a positive window -/

/-- **The `⌊·⌋` in `sweepParam` is constant on a window on which the loop parameter stays
positive.**  If `⌊(t - δ u)/period⌋` differed from `⌊t/period⌋` at some `u ∈ [-1,1]`, the
intermediate value theorem (applied to the affine function `x ↦ (t - δ x)/period` on the segment
between `0` and `u`, which stays inside `[-1,1]`) would produce `w` with `(t - δ w)/period` an
integer, i.e. `sweepParam (t - δ w) = 0`, contradicting the hypothesis. -/
lemma sweepFam_chordZone_param_sub_affine {δ t : ℝ}
    (h : ∀ u : ℝ, u ∈ Set.Icc (-1 : ℝ) 1 → 0 < sweepParam (t - δ * u)) :
    ∀ u : ℝ, u ∈ Set.Icc (-1 : ℝ) 1 →
      sweepParam (t - δ * u) = sweepParam t - δ * u / period := by
  intro u hu
  have huI : Set.uIcc (0 : ℝ) u ⊆ Set.Icc (-1 : ℝ) 1 :=
    (Set.ordConnected_Icc (a := (-1 : ℝ)) (b := 1)).uIcc_subset (by norm_num) hu
  have hcont : ContinuousOn (fun x : ℝ => (t - δ * x) / period) (Set.uIcc (0 : ℝ) u) :=
    ((continuous_const.sub (continuous_const.mul continuous_id)).div_const period).continuousOn
  have hm1 : (⌊t / period⌋ : ℝ) ≤ (t - δ * u) / period := by
    by_contra hlt
    push Not at hlt
    have h0 : (⌊t / period⌋ : ℝ) ≤ (t - δ * 0) / period := by
      simpa using (Int.floor_le (t / period) : (⌊t / period⌋ : ℝ) ≤ t / period)
    have hmem : (⌊t / period⌋ : ℝ) ∈
        Set.Icc ((t - δ * u) / period) ((t - δ * 0) / period) := ⟨le_of_lt hlt, h0⟩
    obtain ⟨w, hw, hwF⟩ := (isPreconnected_uIcc (a := (0 : ℝ)) (b := u)).intermediate_value
      (a := u) (b := 0) Set.right_mem_uIcc Set.left_mem_uIcc hcont hmem
    have hwI := huI hw
    simp only [] at hwF
    have hzero : sweepParam (t - δ * w) = 0 := by
      rw [sweepParam, hwF]
      simp
    linarith [h w hwI, hzero]
  have hm2 : (t - δ * u) / period < (⌊t / period⌋ : ℝ) + 1 := by
    by_contra hle
    push Not at hle
    have h0 : (t - δ * 0) / period ≤ (⌊t / period⌋ : ℝ) + 1 := by
      simpa using (Int.lt_floor_add_one (t / period)).le
    have hmem : (⌊t / period⌋ : ℝ) + 1 ∈
        Set.Icc ((t - δ * 0) / period) ((t - δ * u) / period) := ⟨h0, hle⟩
    obtain ⟨w, hw, hwF⟩ := (isPreconnected_uIcc (a := (0 : ℝ)) (b := u)).intermediate_value
      (a := 0) (b := u) Set.left_mem_uIcc Set.right_mem_uIcc hcont hmem
    have hwI := huI hw
    simp only [] at hwF
    have hzero : sweepParam (t - δ * w) = 0 := by
      rw [sweepParam, hwF]
      simp
    linarith [h w hwI, hzero]
  have hm : ⌊(t - δ * u) / period⌋ = ⌊t / period⌋ := Int.floor_eq_iff.mpr ⟨hm1, hm2⟩
  rw [sweepParam, sweepParam, hm]
  ring

/-! ## The chamfered loop on its chord zone -/

/-- **On the chord zone the chamfered loop is the chord.**  If the loop fraction
`u = sweepParam t` lies in `[1/2 + lam/2, 1 - lam/2]`, the chamfered loop takes the value
`sweepChord' r D s (sweepChordParam lam u)`.

The subtle point is the left corner `u = 1/2 + lam/2`, which is *not* in the interior chord branch
but on the middle chamfer branch; there the chamfer weight is `(2u - 1)/lam = 1`, so the chamfer
degenerates to the chord `sweepChord' r D s (1 - lam)`, and indeed
`sweepChordParam lam (1/2 + lam/2) = 1 - lam`.  Hence `hlam1` is not needed. -/
lemma sweepFam_chordZone_loopChamfer_chordZone {r : ℝ → Space} {d : BandArcData}
    (D : SweepData d) {lam s t : ℝ} (hlam0 : 0 < lam) (_hlam1 : lam < 1 / 2)
    (h1 : 1 / 2 + lam / 2 ≤ sweepParam t) (h2 : sweepParam t ≤ 1 - lam / 2) :
    sweepLoopChamfer r D lam s t
      = sweepChord' r D s (sweepChordParam lam (sweepParam t)) := by
  simp only [sweepLoopChamfer]
  by_cases hmid : sweepParam t ≤ 1 / 2 + lam / 2
  · have heq : sweepParam t = 1 / 2 + lam / 2 := le_antisymm hmid h1
    rw [heq]
    have hA : ¬ ((1 : ℝ) / 2 + lam / 2 ≤ 1 / 2) := by linarith
    rw [if_neg hA, if_pos le_rfl]
    have h2u : 2 * (1 / 2 + lam / 2) - 1 = lam := by ring
    rw [h2u]
    have hdiv : lam / lam = 1 := div_self (ne_of_gt hlam0)
    rw [hdiv]
    simp only [sub_self, zero_smul, one_smul, zero_add]
    rw [show sweepChordParam lam (1 / 2 + lam / 2) = 1 - lam by simp [sweepChordParam]]
  · rw [not_le] at hmid
    have hA : ¬ (sweepParam t ≤ 1 / 2) := by linarith
    rw [if_neg hA, if_neg (not_le.mpr hmid), if_pos h2]
    simp only [sweepChordParam]

/-! ## The main statement -/

theorem sweepFam_chordZone {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space} (hr : Continuous r)
    {d : LeanEval.KnotTheory.Quadrisecant.BandArcData} (D : Work.Drive.SweepData d)
    {lam δ₁ δ₂ σ t : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1 / 2)
    (hclean : ∀ u : ℝ, u ∈ Set.Icc (-1 : ℝ) 1 →
      1 / 2 + lam / 2 ≤ Work.Drive.sweepParam (t - δ₁ * u) ∧
        Work.Drive.sweepParam (t - δ₁ * u) ≤ 1 - lam / 2) :
    Work.Drive.sweepFam r D lam δ₁ δ₂ σ t
      = (1 - Work.Drive.sweepChordParam lam (Work.Drive.sweepParam t)) •
          (∫ v in (-1 : ℝ)..1, Work.Drive.sweepBump v • r (Work.Drive.taR D (σ - δ₂ * v)))
        + (Work.Drive.sweepChordParam lam (Work.Drive.sweepParam t)) •
          (∫ v in (-1 : ℝ)..1, Work.Drive.sweepBump v • r (Work.Drive.tbR D (σ - δ₂ * v))) := by
  -- positivity of the loop parameter on the window
  have hpos : ∀ u : ℝ, u ∈ Set.Icc (-1 : ℝ) 1 → 0 < sweepParam (t - δ₁ * u) := by
    intro u hu
    have := (hclean u hu).1
    linarith
  -- **Step A.** The loop-parameter convolution collapses to a single chord point: for *every*
  -- sweep parameter `s`, `sweepSmoothT r D lam δ₁ s t = sweepChord' r D s ξ`.
  have hinner : ∀ s : ℝ, sweepSmoothT r D lam δ₁ s t
      = sweepChord' r D s (sweepChordParam lam (sweepParam t)) := by
    intro s
    -- the slope of `u ↦ sweepChordParam lam (sweepParam (t - δ₁ u))`
    set B : ℝ := sweepChordParam lam (sweepParam t - δ₁ / period)
        - sweepChordParam lam (sweepParam t) with hB
    have hpt : ∀ u : ℝ, u ∈ Set.Icc (-1 : ℝ) 1 →
        sweepBump u • sweepLoopChamfer r D lam s (t - δ₁ * u)
          = sweepBump u • (r (taR D s)
              + (sweepChordParam lam (sweepParam t) + u * B) • (r (tbR D s) - r (taR D s))) := by
      intro u hu
      -- the loop fraction is affine in `u`
      have harg : sweepParam (t - δ₁ * u)
          = sweepParam t + u * ((sweepParam t - δ₁ / period) - sweepParam t) := by
        rw [sweepFam_chordZone_param_sub_affine hpos u hu]
        ring
      have hcp : sweepChordParam lam (sweepParam (t - δ₁ * u))
          = sweepChordParam lam (sweepParam t) + u * B := by
        rw [harg, sweepFam_chordZone_chordParam_affine lam (sweepParam t)
          (sweepParam t - δ₁ / period) u, ← hB]
      -- on the chord zone the loop is the chord
      rw [sweepFam_chordZone_loopChamfer_chordZone D hlam0 hlam1
        (hclean u hu).1 (hclean u hu).2, hcp]
      -- the chord at affine fraction is an affine function of `u`
      have hch : sweepChord' r D s (sweepChordParam lam (sweepParam t) + u * B)
          = r (taR D s)
            + (sweepChordParam lam (sweepParam t) + u * B) • (r (tbR D s) - r (taR D s)) := by
        simp only [sweepChord']
        module
      rw [hch]
    have hcongr : (∫ u in (-1 : ℝ)..1, sweepBump u • sweepLoopChamfer r D lam s (t - δ₁ * u))
        = ∫ u in (-1 : ℝ)..1, sweepBump u • (r (taR D s)
            + (sweepChordParam lam (sweepParam t) + u * B) • (r (tbR D s) - r (taR D s))) := by
      refine intervalIntegral.integral_congr (fun u hu => ?_)
      rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hu
      exact hpt u hu
    calc sweepSmoothT r D lam δ₁ s t
        = (∫ u in (-1 : ℝ)..1, sweepBump u • sweepLoopChamfer r D lam s (t - δ₁ * u)) := rfl
      _ = (∫ u in (-1 : ℝ)..1, sweepBump u • (r (taR D s)
            + (sweepChordParam lam (sweepParam t) + u * B) • (r (tbR D s) - r (taR D s)))) :=
            hcongr
      _ = r (taR D s) + sweepChordParam lam (sweepParam t) • (r (tbR D s) - r (taR D s)) :=
            sweepFam_chordZone_blur_affine_lin (r (taR D s)) (r (tbR D s) - r (taR D s))
              (sweepChordParam lam (sweepParam t)) B
      _ = sweepChord' r D s (sweepChordParam lam (sweepParam t)) := by
            simp only [sweepChord']
            module
  -- **Step B.** The sweep-parameter convolution only moves the two endpoints of the chord.
  simp only [sweepFam]
  have h1 : (fun v : ℝ => sweepBump v • sweepSmoothT r D lam δ₁ (σ - δ₂ * v) t)
      = fun v : ℝ =>
          (1 - sweepChordParam lam (sweepParam t)) • (sweepBump v • r (taR D (σ - δ₂ * v)))
          + (sweepChordParam lam (sweepParam t)) • (sweepBump v • r (tbR D (σ - δ₂ * v))) := by
    funext v
    rw [hinner (σ - δ₂ * v)]
    simp only [sweepChord']
    rw [smul_add, smul_comm (sweepBump v) (1 - sweepChordParam lam (sweepParam t)),
      smul_comm (sweepBump v) (sweepChordParam lam (sweepParam t))]
  rw [h1]
  have hta : Continuous (fun v : ℝ => taR D (σ - δ₂ * v)) :=
    (sweepFam_chordZone_taR_continuous D).comp (by fun_prop)
  have htb : Continuous (fun v : ℝ => tbR D (σ - δ₂ * v)) :=
    (sweepFam_chordZone_tbR_continuous D).comp (by fun_prop)
  have hca : Continuous (fun v : ℝ => (1 - sweepChordParam lam (sweepParam t)) •
      (sweepBump v • r (taR D (σ - δ₂ * v)))) :=
    (sweepBump_continuous.smul (hr.comp hta)).const_smul (1 - sweepChordParam lam (sweepParam t))
  have hcb : Continuous (fun v : ℝ => (sweepChordParam lam (sweepParam t)) •
      (sweepBump v • r (tbR D (σ - δ₂ * v)))) :=
    (sweepBump_continuous.smul (hr.comp htb)).const_smul (sweepChordParam lam (sweepParam t))
  rw [intervalIntegral.integral_add (hca.intervalIntegrable (-1) 1) (hcb.intervalIntegrable (-1) 1),
    intervalIntegral.integral_smul, intervalIntegral.integral_smul]

end Work.Drive

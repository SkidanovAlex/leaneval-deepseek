import Mathlib
import Submission.Work.Drive.shiftedNeedleChart
import Submission.Work.Drive.needleArcZoneMono
import Submission.Work.Drive.needleChart
import Submission.Work.Drive.arcPointDeviationBound
import Submission.Work.Drive.shiftedNeedleDefs
import Submission.Work.Drive.shiftedNeedleWindow
import Submission.Work.Drive.shiftedNeedleBlur
import Submission.Work.Drive.loopBlur_chart
import Submission.Work.Drive.needleFrac_window

/-!
# The single-ray condition of the shifted needle

`Work.Drive.shiftedNeedle_singleRay` is the *single-ray* clause of the shifted needle's chart pin
(`Submission/Work/Drive/shiftedNeedleChart.lean`): for the box of admissible parameters, for every
frame `(e, v)` of the chord and every level `y₀` below the base point's height, a point of the
needle with the same chord coordinate as the base point and a *positive* loop parameter lies at
height `< h₀ - y₀` below the base point — i.e. it is below the ray from the centre through the base
point.

The proof is the case analysis of the loop-parameter window `{τ - δ₁ u | u ∈ [-1,1]}` of the
chamfered loop (`τ = t + period/4`), in which the needle walks through the four branches of the
loop:

* `Work.Drive.needleFrac_window` (delegated) dichotomises the window into the two arc zones, the
  chord zone, a *top* window (where the branch fraction stays near `1 - lam`) and a *bottom* window
  (where it stays near `lam`);
* `Work.Drive.loopBlur_chart` (delegated) bounds the `σ`-blurred loop point by the chord model;
* `Work.Drive.needleFam_chart` (delegated) upgrades that bound to the needle itself;
* `Work.Drive.needleArcZoneMono` and `Work.Drive.needleFam_chordZone_inner` handle the two extreme
  cases, and `Work.Drive.coord_lower_of_frac_ge` / `Work.Drive.coord_upper_of_frac_le` turn the
  pointwise top/bottom bounds into bounds for the chord coordinate of the needle.
-/

noncomputable section
namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant MeasureTheory
open scoped Real Topology intervalIntegral

set_option maxHeartbeats 1000000

/-- The `nCoord` of the shifted needle is the chord coordinate of `needleFam` at `t + period/4`. -/
lemma nCoord_eq (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (lam δ₁ δ₂ ε : ℝ)
    (v : Space) (t : ℝ) :
    nCoord r D lam δ₁ δ₂ ε v t
      = inner ℝ (needleFam r D lam δ₁ δ₂ ε (t + period / 4) - chordEndA r D δ₂ ε) v := rfl

/-- The `nHeight` of the shifted needle is the `e`-coordinate of `needleFam` at `t + period/4`. -/
lemma nHeight_eq (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (lam δ₁ δ₂ ε : ℝ)
    (e : Space) (t : ℝ) :
    nHeight r D lam δ₁ δ₂ ε e t
      = inner ℝ (needleFam r D lam δ₁ δ₂ ε (t + period / 4) - chordEndA r D δ₂ ε) e := rfl


/-- The chart bound and a lower bound for the branch fraction on the window give a lower bound for
the needle's chord coordinate. -/
lemma coord_lower_of_frac_ge {r : ℝ → Space} (hr : Continuous r) {d : BandArcData}
    (D : SweepData d) {lam δ₁ δ₂ ε c τ : ℝ} {v : Space} (hv : ‖v‖ = 1) (h0 : 0 < lam) (h1 : lam < 1 / 2)
    (hblur : ∀ τ' : ℝ, |inner ℝ (loopBlur r D lam δ₂ ε τ' - chordEndA r D δ₂ ε) v
        - ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖ * needleFrac lam τ'|
      ≤ (1 / 8) * ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖)
    (hc : ∀ u : ℝ, u ∈ Set.Icc (-1 : ℝ) 1 → c ≤ needleFrac lam (τ - δ₁ * u)) :
    ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖ * c
        - (1 / 8) * ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖
      ≤ inner ℝ (needleFam r D lam δ₁ δ₂ ε τ - chordEndA r D δ₂ ε) v := by
  have hchart : |inner ℝ (needleFam r D lam δ₁ δ₂ ε τ - chordEndA r D δ₂ ε) v
        - ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖
          * (∫ u in (-1 : ℝ)..1, sweepBump u * needleFrac lam (τ - δ₁ * u))|
      ≤ (1 / 8) * ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖ :=
    needleFam_chart_self hr D hv (norm_nonneg _) h0 h1 hblur τ
  have hΨ : c ≤ ∫ u in (-1 : ℝ)..1, sweepBump u * needleFrac lam (τ - δ₁ * u) :=
    integral_needleFrac_ge (δ := δ₁) (c := c) h0 h1 hc
  have hmul : ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖ * c
      ≤ ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖
        * (∫ u in (-1 : ℝ)..1, sweepBump u * needleFrac lam (τ - δ₁ * u)) :=
    mul_le_mul_of_nonneg_left hΨ (norm_nonneg _)
  have hlow := (abs_le.mp hchart).1
  linarith [hmul, hlow]

/-- The chart bound and an upper bound for the branch fraction on the window give an upper bound for
the needle's chord coordinate. -/
lemma coord_upper_of_frac_le {r : ℝ → Space} (hr : Continuous r) {d : BandArcData}
    (D : SweepData d) {lam δ₁ δ₂ ε c τ : ℝ} {v : Space} (hv : ‖v‖ = 1) (h0 : 0 < lam) (h1 : lam < 1 / 2)
    (hblur : ∀ τ' : ℝ, |inner ℝ (loopBlur r D lam δ₂ ε τ' - chordEndA r D δ₂ ε) v
        - ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖ * needleFrac lam τ'|
      ≤ (1 / 8) * ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖)
    (hc : ∀ u : ℝ, u ∈ Set.Icc (-1 : ℝ) 1 → needleFrac lam (τ - δ₁ * u) ≤ c) :
    inner ℝ (needleFam r D lam δ₁ δ₂ ε τ - chordEndA r D δ₂ ε) v
      ≤ ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖ * c
        + (1 / 8) * ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖ := by
  have hchart : |inner ℝ (needleFam r D lam δ₁ δ₂ ε τ - chordEndA r D δ₂ ε) v
        - ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖
          * (∫ u in (-1 : ℝ)..1, sweepBump u * needleFrac lam (τ - δ₁ * u))|
      ≤ (1 / 8) * ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖ :=
    needleFam_chart_self hr D hv (norm_nonneg _) h0 h1 hblur τ
  have hΨ : (∫ u in (-1 : ℝ)..1, sweepBump u * needleFrac lam (τ - δ₁ * u)) ≤ c :=
    integral_needleFrac_le (δ := δ₁) (c := c) h0 h1 hc
  have hmul : ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖
        * (∫ u in (-1 : ℝ)..1, sweepBump u * needleFrac lam (τ - δ₁ * u))
      ≤ ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖ * c :=
    mul_le_mul_of_nonneg_left hΨ (norm_nonneg _)
  have hup := (abs_le.mp hchart).2
  linarith [hmul, hup]

/-- A strict increase of the needle along the chord direction gives a strict increase of the chord
coordinate. -/
lemma coord_lt_of_arc {r : ℝ → Space} {d : BandArcData} (D : SweepData d) {lam δ₁ δ₂ ε : ℝ}
    {v : Space} {σ₁ σ₂ : ℝ}
    (hBA : chordEndB r D δ₂ ε - chordEndA r D δ₂ ε
      = ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖ • v)
    (hℓ : 0 < ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖)
    (h : 0 < inner ℝ (needleFam r D lam δ₁ δ₂ ε σ₂ - needleFam r D lam δ₁ δ₂ ε σ₁)
      (chordEndB r D δ₂ ε - chordEndA r D δ₂ ε)) :
    inner ℝ (needleFam r D lam δ₁ δ₂ ε σ₁ - chordEndA r D δ₂ ε) v
      < inner ℝ (needleFam r D lam δ₁ δ₂ ε σ₂ - chordEndA r D δ₂ ε) v := by
  have h1 : inner ℝ (needleFam r D lam δ₁ δ₂ ε σ₂ - needleFam r D lam δ₁ δ₂ ε σ₁)
        (chordEndB r D δ₂ ε - chordEndA r D δ₂ ε)
      = ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖
        * inner ℝ (needleFam r D lam δ₁ δ₂ ε σ₂ - needleFam r D lam δ₁ δ₂ ε σ₁) v := by
    conv_lhs => rw [hBA]
    rw [real_inner_smul_right]
  have h2 : inner ℝ (needleFam r D lam δ₁ δ₂ ε σ₂ - needleFam r D lam δ₁ δ₂ ε σ₁) v
      = inner ℝ (needleFam r D lam δ₁ δ₂ ε σ₂ - chordEndA r D δ₂ ε) v
        - inner ℝ (needleFam r D lam δ₁ δ₂ ε σ₁ - chordEndA r D δ₂ ε) v := by
    simp only [inner_sub_left, inner_sub_right]
    ring
  nlinarith [h, h1, h2]

theorem shiftedNeedle_singleRay {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r)
    {d : LeanEval.KnotTheory.Quadrisecant.BandArcData} (D : Work.Drive.SweepData d) :
    ∃ ε₀ L : ℝ, 0 < ε₀ ∧ 0 < L ∧
      ∀ (lam δ₁ δ₂ ε : ℝ), 0 < lam → lam ≤ L → lam < 1 / 2 → 0 < δ₁ → δ₁ ≤ L →
        0 < δ₂ → δ₂ ≤ L → 0 < ε → ε ≤ ε₀ → δ₂ ≤ ε / 2 →
        ∀ (e v : LeanEval.KnotTheory.Quadrisecant.Space), ‖e‖ = 1 → ‖v‖ = 1 →
          inner ℝ e v = 0 →
          0 < ‖Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε‖ →
          Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε
            = ‖Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε‖ • v →
          ∀ y₀ : ℝ, 0 < y₀ → y₀ < Work.Drive.nHeight r D lam δ₁ δ₂ ε e 0 →
            ∀ t : ℝ, 0 < t → t < LeanEval.KnotTheory.Quadrisecant.period →
              Work.Drive.nCoord r D lam δ₁ δ₂ ε v t = Work.Drive.nCoord r D lam δ₁ δ₂ ε v 0 →
              Work.Drive.nHeight r D lam δ₁ δ₂ ε e t
                < Work.Drive.nHeight r D lam δ₁ δ₂ ε e 0 - y₀ := by
  obtain ⟨ε₀a, La, hε₀a, hLa, harc⟩ := needleArcZoneMono hr D
  obtain ⟨ε₀b, hε₀b, hblurAll⟩ := loopBlur_chart hr D
  refine ⟨min ε₀a ε₀b, min (min La (1 / 16)) (period / 1024), lt_min hε₀a hε₀b,
    lt_min (lt_min hLa (by norm_num : (0 : ℝ) < 1 / 16)) (by linarith [period_pos] : (0 : ℝ) < period / 1024),
    ?_⟩
  intro lam δ₁ δ₂ ε hlam0 hlamL hlam1 hδ₁0 hδ₁L hδ₂0 hδ₂L hε0 hεε₀ hδ₂ε e v he hv hev hℓpos hBA
    y₀ hy₀ hy₀h t ht0 htP hcoord
  -- the constants
  have hp : (0 : ℝ) < period := period_pos
  have hLmem : lam ≤ min La (1 / 16) := le_trans hlamL (min_le_left _ _)
  have hLarc : lam ≤ La := le_trans hLmem (min_le_left _ _)
  have hL1 : lam ≤ 1 / 16 := le_trans hLmem (min_le_right _ _)
  have hδ₁mem : δ₁ ≤ min La (1 / 16) := le_trans hδ₁L (min_le_left _ _)
  have hδ₁La : δ₁ ≤ La := le_trans hδ₁mem (min_le_left _ _)
  have hδ₁P : δ₁ ≤ period / 1024 := le_trans hδ₁L (min_le_right _ _)
  have hδ₂mem : δ₂ ≤ min La (1 / 16) := le_trans hδ₂L (min_le_left _ _)
  have hδ₂La : δ₂ ≤ La := le_trans hδ₂mem (min_le_left _ _)
  have hεa : ε ≤ ε₀a := le_trans hεε₀ (min_le_left _ _)
  have hεb : ε ≤ ε₀b := le_trans hεε₀ (min_le_right _ _)
  have h16 : 16 * δ₁ ≤ period := by linarith
  have h34 : lam + 34 * (δ₁ / period) < 1 / 4 := by
    have h1 : δ₁ / period ≤ 1 / 1024 := by rw [div_le_iff₀ hp]; linarith
    linarith
  -- the chart bound
  have hblur : ∀ τ' : ℝ, |inner ℝ (loopBlur r D lam δ₂ ε τ' - chordEndA r D δ₂ ε) v
      - ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖ * needleFrac lam τ'|
      ≤ (1 / 8) * ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖ :=
    fun τ' => hblurAll lam δ₂ ε hlam0 hlam1 hδ₂0 hδ₂ε hε0 hεb v hv hBA τ'
  -- the shifted parameter
  set τ : ℝ := t + period / 4 with hτdef
  have hτlo : period / 4 < τ := by rw [hτdef]; linarith
  have hτhi : τ < 5 * period / 4 := by rw [hτdef]; linarith
  have hXd : inner ℝ (needleFam r D lam δ₁ δ₂ ε τ - chordEndA r D δ₂ ε) v
      = inner ℝ (needleFam r D lam δ₁ δ₂ ε (period / 4) - chordEndA r D δ₂ ε) v := by
    have h := hcoord
    rw [nCoord_eq, nCoord_eq] at h
    rw [← hτdef] at h
    simpa using h
  have heBA : inner ℝ e (chordEndB r D δ₂ ε - chordEndA r D δ₂ ε) = 0 := by
    rw [hBA, real_inner_smul_right, hev, mul_zero]
  rcases needleFrac_window hlam0 hL1 hδ₁0 h16 hτlo hτhi with
    ⟨harcwin, hτlt⟩ | ⟨harcwin, hτgt⟩ | hchord | htop | hbot
  · -- the first arc zone
    have hwin0 : ∀ u : ℝ, u ∈ Set.Icc (-1 : ℝ) 1 → sweepParam (period / 4 - δ₁ * u) ≤ 1 / 2 :=
      baseWindow_arc hδ₁0 h16
    have hgap : τ - period / 4 < period / 2 := by linarith
    have hmono := harc lam δ₁ δ₂ ε (period / 4) τ hlam0 hLarc hlam1 hδ₁0 hδ₁La hδ₂0 hδ₂La
      hε0 hεa hδ₂ε hτlo hgap hwin0 harcwin
    have hlt := coord_lt_of_arc D hBA hℓpos hmono
    linarith [hlt, hXd]
  · -- the second arc zone
    have hwin1 : ∀ u : ℝ, u ∈ Set.Icc (-1 : ℝ) 1 →
        sweepParam (5 * period / 4 - δ₁ * u) ≤ 1 / 2 := by
      refine window_arc_right hδ₁0.le ?_ ?_
      · linarith
      · linarith
    have hgap : 5 * period / 4 - τ < period / 2 := by linarith
    have hmono := harc lam δ₁ δ₂ ε τ (5 * period / 4) hlam0 hLarc hlam1 hδ₁0 hδ₁La hδ₂0 hδ₂La
      hε0 hεa hδ₂ε hτhi hgap harcwin hwin1
    have hlt := coord_lt_of_arc D hBA hℓpos hmono
    have hper : needleFam r D lam δ₁ δ₂ ε (5 * period / 4)
        = needleFam r D lam δ₁ δ₂ ε (period / 4) := by
      rw [show 5 * period / 4 = period / 4 + period by ring, needleFam_add_period]
    rw [hper] at hlt
    linarith [hlt, hXd]
  · -- the chord zone
    have hH : inner ℝ (needleFam r D lam δ₁ δ₂ ε τ - chordEndA r D δ₂ ε) e = 0 :=
      needleFam_chordZone_inner hr.smooth.continuous D hlam0 hlam1 hchord heBA
    have hnt : nHeight r D lam δ₁ δ₂ ε e t = 0 := by
      rw [nHeight_eq, ← hτdef]
      exact hH
    rw [hnt]
    linarith
  · -- above the middle of the arc (the head-chamfer side)
    have hXτ := coord_lower_of_frac_ge hr.smooth.continuous D hv hlam0 hlam1 hblur (τ := τ)
      (c := 1 - lam - 32 * (δ₁ / period)) htop
    have hbase : ∀ u : ℝ, u ∈ Set.Icc (-1 : ℝ) 1 →
        needleFrac lam (period / 4 - δ₁ * u) ≤ 1 / 2 + 2 * (δ₁ / period) :=
      fun u hu => by
        have h := (abs_le.mp (baseWindow_frac hlam0 hlam1 hδ₁0 h16 u hu)).2
        linarith
    have hX0 := coord_upper_of_frac_le hr.smooth.continuous D hv hlam0 hlam1 hblur
      (τ := period / 4) (c := 1 / 2 + 2 * (δ₁ / period)) hbase
    have hkey : ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖ * (1 / 4 - lam - 34 * (δ₁ / period))
        = (‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖ * (1 - lam - 32 * (δ₁ / period))
              - (1 / 8) * ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖)
          - (‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖ * (1 / 2 + 2 * (δ₁ / period))
              + (1 / 8) * ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖) := by ring
    have hle : ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖ * (1 / 4 - lam - 34 * (δ₁ / period))
        ≤ 0 := by linarith [hXτ, hX0, hXd, hkey]
    have hcc : 0 < 1 / 4 - lam - 34 * (δ₁ / period) := by linarith
    have hpos := mul_pos hℓpos hcc
    linarith [hle, hpos]
  · -- below the middle of the arc (the tail-chamfer side)
    have hXτ := coord_upper_of_frac_le hr.smooth.continuous D hv hlam0 hlam1 hblur (τ := τ)
      (c := lam + 32 * (δ₁ / period)) hbot
    have hbase : ∀ u : ℝ, u ∈ Set.Icc (-1 : ℝ) 1 →
        1 / 2 - 2 * (δ₁ / period) ≤ needleFrac lam (period / 4 - δ₁ * u) :=
      fun u hu => by
        have h := (abs_le.mp (baseWindow_frac hlam0 hlam1 hδ₁0 h16 u hu)).1
        linarith
    have hX0 := coord_lower_of_frac_ge hr.smooth.continuous D hv hlam0 hlam1 hblur
      (τ := period / 4) (c := 1 / 2 - 2 * (δ₁ / period)) hbase
    have hkey : ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖ * (lam + 34 * (δ₁ / period) - 1 / 4)
        = (‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖ * (lam + 32 * (δ₁ / period))
              + (1 / 8) * ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖)
          - (‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖ * (1 / 2 - 2 * (δ₁ / period))
              - (1 / 8) * ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖) := by ring
    have hle : 0 ≤ ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖ * (lam + 34 * (δ₁ / period) - 1 / 4) := by
      linarith [hXτ, hX0, hXd, hkey]
    have hcc : lam + 34 * (δ₁ / period) - 1 / 4 < 0 := by linarith
    have hneg : ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖ * (lam + 34 * (δ₁ / period) - 1 / 4) < 0 :=
      mul_neg_of_pos_of_neg hℓpos hcc
    linarith [hle, hneg]


end Work.Drive

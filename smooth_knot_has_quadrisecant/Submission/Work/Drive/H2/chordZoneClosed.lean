import Mathlib
import Submission.Work.Drive.AB.pinSetup
import Submission.Work.Drive.AB.windowDataSmall
import Submission.Work.Drive.AB.chordEndNormLower
import Submission.Work.Drive.H2.chordZone

/-!
# The chord zone of the per-loop margin, with the window data discharged

Lane H2.  `Work.Drive.H2.chordZone_margin` (`H2/chordZone.lean`) closes the chord branch of the
loop for the per-loop margin `Work.Drive.ChartLoopMargin`, with the six *window* hypotheses

* `hνh : 1024 * ν ≤ ‖chartUp‖`, `hνℓ : 1024 * ν ≤ ‖chordEndB - chordEndA‖` (the mismatch is small
  against the two geometric scales),
* `hbase : ‖shiftedNeedle … 0 - chordEndA‖ ≤ 2 ‖chordEndB - chordEndA‖` (the base point is within
  twice the chord length of the chart's `a`-end),
* `hclose`, `hA`, `hB` (the chords and endpoints of the *loop* are within `ν` of the blurred ones).

This module packages the passage from the *existing* window estimates to those hypotheses:

* `Work.Drive.H2.integral_sweepW_lower` — the bump-average of the width over the window dominates
  half the width at the centre (a *modulus* statement; no σ-derivative is used),
* `Work.Drive.H2.chordLen_lower` — the blurred chord length dominates a fixed multiple of the width
  at the centre, `c * sweepW' D ε ≤ ‖chordEndB - chordEndA‖` (from `chordEndNormLower` + the
  preceding line),
* **`Work.Drive.H2.chordZone_margin_closed`** — the chord-zone margin for every box, with a single
  `κ = c_h * c_ℓ * (sweepW' D ε)^3 / (8 * period) > 0`, from three *inputs* which are statements
  about the window data (the two proved children `H2.window_close_all`,
  `H2.basePoint_close_chordEndA` and the height bound `H2.baseHeight_lower` supply them in the
  shapes taken here).
-/

noncomputable section
namespace Work.Drive.H2

open LeanEval.KnotTheory.Quadrisecant MeasureTheory
open scoped Real Topology intervalIntegral

set_option maxHeartbeats 1000000

variable {r : ℝ → Space} {d : BandArcData} {D : SweepData d}

/-! ## The width at the centre against its bump-average -/

/-- **The bump-average of the retained width over the blur window dominates half the width at the
centre**, for a small enough window.  This is a *modulus* statement: only the continuity of
`sweepW'` is used, never a σ-derivative (the "spiky width" of the band arc is harmless here,
because the comparison is between the width at the centre and its *own* weighted average). -/
lemma integral_sweepW_lower {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ Λ : ℝ, 0 < Λ ∧ ∀ δ₂ : ℝ, 0 < δ₂ → δ₂ ≤ Λ →
      sweepW' D ε / 2 ≤ ∫ v in (-1 : ℝ)..1, sweepBump v * sweepW' D (ε - δ₂ * v) := by
  have hwε : 0 < sweepW' D ε := wds_sweepW'_pos D hε0 hε1
  have hcont : Continuous (sweepW' D) := arcWin_sweepW'_continuous D
  obtain ⟨θ, hθ, hspec⟩ := Metric.continuousAt_iff.mp (hcont.continuousAt (x := ε))
    (sweepW' D ε / 2) (by positivity)
  refine ⟨min θ (1 / 2) / 2, by positivity, ?_⟩
  intro δ₂ hδ₂ hδ₂Λ
  have hδ₂θ : δ₂ < θ := by
    have h1 : δ₂ ≤ min θ (1 / 2) / 2 := hδ₂Λ
    have h2 : min θ (1 / 2) ≤ θ := min_le_left _ _
    nlinarith [hθ, h1, h2]
  have hb : ∀ v ∈ Set.Icc (-1 : ℝ) 1, sweepW' D ε / 2 ≤ sweepW' D (ε - δ₂ * v) := by
    intro v hv
    have hv1 : |v| ≤ 1 := by rw [abs_le]; exact ⟨hv.1, hv.2⟩
    have hdist : dist (ε - δ₂ * v) ε < θ := by
      rw [Real.dist_eq, abs_sub_comm]
      calc |ε - (ε - δ₂ * v)| = |δ₂ * v| := by ring_nf
        _ = δ₂ * |v| := by rw [abs_mul, abs_of_pos hδ₂]
        _ < θ := by nlinarith [hv1, hδ₂θ]
    have := hspec hdist
    rw [Real.dist_eq] at this
    linarith [abs_lt.mp this |>.1]
  calc sweepW' D ε / 2 = ∫ v in (-1 : ℝ)..1, sweepBump v * (sweepW' D ε / 2) := by
        rw [intervalIntegral.integral_mul_const, integral_sweepBump, one_mul]
    _ ≤ ∫ v in (-1 : ℝ)..1, sweepBump v * sweepW' D (ε - δ₂ * v) := by
        refine intervalIntegral.integral_mono_on (by norm_num) ?_ ?_ ?_
        · exact (sweepBump_continuous.mul continuous_const).intervalIntegrable _ _
        · exact (sweepBump_continuous.mul
            (hcont.comp (by fun_prop))).intervalIntegrable _ _
        · intro v hv
          exact mul_le_mul_of_nonneg_left (hb v hv) (sweepBump_nonneg v)

/-! ## The blurred chord length against the width -/

/-- **The blurred chord length dominates a fixed multiple of the width at the centre.**  From
`Work.Drive.chordEndNormLower` (the blurred chord dominates its own bump-average of the width) and
`Work.Drive.H2.integral_sweepW_lower`. -/
theorem chordLen_lower (hr : IsSmoothKnot r) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < 1 ∧ ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∃ Λ : ℝ, 0 < Λ ∧ Λ ≤ ε / 2 ∧ ∀ δ₂ : ℝ, 0 < δ₂ → δ₂ ≤ Λ →
        c * sweepW' D ε ≤ ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖ := by
  obtain ⟨ε₀, c₁, hε₀0, hc₁0, hnorm⟩ := chordEndNormLower hr D
  refine ⟨min ε₀ (1 / 2), lt_min hε₀0 (by norm_num),
    lt_of_le_of_lt (min_le_right _ _) (by norm_num), c₁ / 2, by linarith, ?_⟩
  intro ε hε0 hεε₀
  have hεε₀' : ε ≤ ε₀ := le_trans hεε₀ (min_le_left _ _)
  have hε1 : ε < 1 := by linarith [le_trans hεε₀ (min_le_right _ _)]
  obtain ⟨Λw, hΛw0, hΛw⟩ := integral_sweepW_lower (D := D) hε0 hε1
  refine ⟨min Λw (ε / 2), lt_min hΛw0 (by linarith), min_le_right _ _, ?_⟩
  intro δ₂ hδ₂ hδ₂Λ
  have hδ₂w : δ₂ ≤ Λw := le_trans hδ₂Λ (min_le_left _ _)
  have hδ₂ε : δ₂ ≤ ε / 2 := le_trans hδ₂Λ (min_le_right _ _)
  have h1 := hΛw δ₂ hδ₂ hδ₂w
  have h2 := hnorm δ₂ ε hδ₂ hδ₂ε hε0 hεε₀'
  calc c₁ / 2 * sweepW' D ε = c₁ * (sweepW' D ε / 2) := by ring
    _ ≤ c₁ * ∫ v in (-1 : ℝ)..1, sweepBump v * sweepW' D (ε - δ₂ * v) :=
        mul_le_mul_of_nonneg_left h1 hc₁0.le
    _ ≤ ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖ := h2

/-! ## The chord-zone margin with the window data discharged -/

/-- **The chord zone of the per-loop margin, with the window data discharged.**  The three
`H…`-inputs are statements about the window data of the needle; the proved lemmas
`Work.Drive.H2.window_close_all` (the endpoints and the chord of the loop against the blurred ones),
`Work.Drive.H2.basePoint_close_chordEndA` (the base point against the blurred chord length) and
`Work.Drive.H2.baseHeight_lower` (the base height against the width) supply them in exactly these
shapes.  The conclusion is the chord branch of `Work.Drive.ChartLoopMargin`, with the explicit
margin `κ = c_h * c_ℓ * (sweepW' D ε)^3 / (8 * period)`, where `c_ℓ` is the constant of
`Work.Drive.H2.chordLen_lower` and `c_h` the constant of the height input. -/
theorem chordZone_margin_closed {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    {D : SweepData d} {c_h : ℝ} (hc_h : 0 < c_h)
    (Hwin : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∀ t : ℝ, 0 < t → ∃ Λ : ℝ, 0 < Λ ∧ Λ ≤ ε / 2 ∧
      ∀ δ₂ : ℝ, 0 < δ₂ → δ₂ ≤ Λ → ∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ →
        ‖r (taR D σ) - chordEndA r D δ₂ ε‖ ≤ t ∧
        ‖r (tbR D σ) - chordEndB r D δ₂ ε‖ ≤ t ∧
        ‖(r (tbR D σ) - r (taR D σ)) - (chordEndB r D δ₂ ε - chordEndA r D δ₂ ε)‖ ≤ t)
    {εb : ℝ} (hεb0 : 0 < εb)
    (Hbase : ∀ ε : ℝ, 0 < ε → ε ≤ εb → ∃ Λ : ℝ, 0 < Λ ∧ Λ ≤ ε / 2 ∧
      ∀ lam δ₁ δ₂ : ℝ, 0 < lam → lam ≤ Λ → lam < 1 / 2 → 0 < δ₁ → δ₁ ≤ Λ →
        0 < δ₂ → δ₂ ≤ Λ → δ₂ ≤ ε / 2 →
        ‖shiftedNeedle r D lam δ₁ δ₂ ε 0 - chordEndA r D δ₂ ε‖
          ≤ 2 * ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖)
    {εh : ℝ} (hεh0 : 0 < εh)
    (Hh : ∀ ε : ℝ, 0 < ε → ε ≤ εh → ∃ Λ : ℝ, 0 < Λ ∧ Λ < 1 / 2 ∧
      ∀ lam δ₁ δ₂ : ℝ, 0 < lam → lam ≤ Λ → 0 < δ₁ → δ₁ ≤ Λ → 0 < δ₂ → δ₂ ≤ Λ → δ₂ ≤ ε / 2 →
        ∀ v : Space, ‖v‖ = 1 →
          chordEndB r D δ₂ ε - chordEndA r D δ₂ ε
            = ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖ • v →
          c_h * (sweepW' D ε) ^ 2 ≤ ‖chartUp r D lam δ₁ δ₂ ε v‖) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∃ Λ : ℝ, 0 < Λ ∧ Λ ≤ ε / 2 ∧ ∃ κ : ℝ, 0 < κ ∧
        ∀ lam δ₁ δ₂ : ℝ, 0 < lam → lam ≤ Λ → lam < 1 / 2 → 0 < δ₁ → δ₁ ≤ Λ →
          0 < δ₂ → δ₂ ≤ Λ → δ₂ ≤ ε / 2 →
        ∀ v : Space, ‖v‖ = 1 →
          chordEndB r D δ₂ ε - chordEndA r D δ₂ ε
            = ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖ • v →
        ∀ σ t : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ →
          1 / 2 + lam / 2 < sweepParam t → sweepParam t ≤ 1 - lam / 2 →
          κ ≤ inner ℝ (sweepLoopChamfer r D lam σ t - chartC r D lam δ₁ δ₂ ε v)
                (chartE r D lam δ₁ δ₂ ε v)
              * inner ℝ (chamferVel r D lam σ t) v
            - inner ℝ (sweepLoopChamfer r D lam σ t - chartC r D lam δ₁ δ₂ ε v) v
              * inner ℝ (chamferVel r D lam σ t) (chartE r D lam δ₁ δ₂ ε v) := by
  obtain ⟨εL, hεL0, hεL1, cL, hcL0, hLen⟩ := chordLen_lower (r := r) hr (D := D)
  refine ⟨min (min εL εb) (min εh (1 / 2)), lt_min (lt_min hεL0 hεb0) (lt_min hεh0 (by norm_num)),
    le_trans (min_le_right _ _) (min_le_right _ _), ?_⟩
  intro ε hε0 hεε₀
  have hεL : ε ≤ εL := le_trans hεε₀ (le_trans (min_le_left _ _) (min_le_left _ _))
  have hεb : ε ≤ εb := le_trans hεε₀ (le_trans (min_le_left _ _) (min_le_right _ _))
  have hεh : ε ≤ εh := le_trans hεε₀ (le_trans (min_le_right _ _) (min_le_left _ _))
  have hε12 : ε ≤ 1 / 2 := le_trans hεε₀ (le_trans (min_le_right _ _) (min_le_right _ _))
  have hε1 : ε < 1 := by linarith
  have hwpos : 0 < sweepW' D ε := wds_sweepW'_pos D hε0 hε1
  have hP : 0 < period := period_pos
  set t₀ : ℝ := min (c_h * (sweepW' D ε) ^ 2) (cL * sweepW' D ε) * (1 / 2048) with ht₀
  have ht₀0 : 0 < t₀ := by
    rw [ht₀]
    exact mul_pos (lt_min (by positivity) (by positivity)) (by norm_num)
  obtain ⟨Λw, hΛw0, -, hΛw⟩ := Hwin ε hε0 hε12 t₀ ht₀0
  obtain ⟨Λb, hΛb0, -, hΛb⟩ := Hbase ε hε0 hεb
  obtain ⟨Λh, hΛh0, hΛh12, hΛh⟩ := Hh ε hε0 hεh
  obtain ⟨ΛL, hΛL0, -, hΛL⟩ := hLen ε hε0 hεL
  set Λ : ℝ := min (min Λw Λb) (min Λh ΛL) with hΛdef
  have hΛ0 : 0 < Λ := by
    rw [hΛdef]; exact lt_min (lt_min hΛw0 hΛb0) (lt_min hΛh0 hΛL0)
  refine ⟨min Λ (ε / 2), lt_min hΛ0 (by linarith), min_le_right _ _,
    c_h * cL * (sweepW' D ε) ^ 3 / (8 * period), div_pos (by positivity) (by positivity), ?_⟩
  intro lam δ₁ δ₂ hlam0 hlamΛ hlam12 hδ₁0 hδ₁Λ hδ₂0 hδ₂Λ hδ₂ε v hv hchord σ t hσlo hσhi hz0 hz1
  have hlamΛ' : lam ≤ Λ := le_trans hlamΛ (min_le_left _ _)
  have hδ₂Λ' : δ₂ ≤ Λ := le_trans hδ₂Λ (min_le_left _ _)
  have hΛw_le : Λ ≤ Λw := by
    rw [hΛdef]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hΛb_le : Λ ≤ Λb := by
    rw [hΛdef]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hΛh_le : Λ ≤ Λh := by
    rw [hΛdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hΛL_le : Λ ≤ ΛL := by
    rw [hΛdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hδ₂w : δ₂ ≤ Λw := le_trans hδ₂Λ' hΛw_le
  have hδ₂b : δ₂ ≤ Λb := le_trans hδ₂Λ' hΛb_le
  have hδ₂h : δ₂ ≤ Λh := le_trans hδ₂Λ' hΛh_le
  have hδ₂L : δ₂ ≤ ΛL := le_trans hδ₂Λ' hΛL_le
  have hlamΛw : lam ≤ Λw := le_trans hlamΛ' hΛw_le
  have hlamΛb : lam ≤ Λb := le_trans hlamΛ' hΛb_le
  have hlamΛh : lam ≤ Λh := le_trans hlamΛ' hΛh_le
  obtain ⟨hA, hB, hclose⟩ := hΛw δ₂ hδ₂0 hδ₂w σ hσlo hσhi
  have hbase := hΛb lam δ₁ δ₂ hlam0 hlamΛb hlam12 hδ₁0
    (le_trans hδ₁Λ (le_trans (min_le_left _ _) hΛb_le)) hδ₂0 hδ₂b hδ₂ε
  have hHh' := hΛh lam δ₁ δ₂ hlam0 hlamΛh hδ₁0 (le_trans hδ₁Λ (le_trans (min_le_left _ _) hΛh_le)) hδ₂0 hδ₂h hδ₂ε v hv hchord
  have hlen := hΛL δ₂ hδ₂0 hδ₂L
  -- the two thresholds
  have ht₀X : t₀ ≤ c_h * (sweepW' D ε) ^ 2 * (1 / 2048) := by
    rw [ht₀]
    exact mul_le_mul_of_nonneg_right (min_le_left _ _) (by norm_num)
  have ht₀Y : t₀ ≤ cL * sweepW' D ε * (1 / 2048) := by
    rw [ht₀]
    exact mul_le_mul_of_nonneg_right (min_le_right _ _) (by norm_num)
  have hνh : 1024 * t₀ ≤ ‖chartUp r D lam δ₁ δ₂ ε v‖ := by
    have h1 : 2048 * t₀ ≤ c_h * (sweepW' D ε) ^ 2 := by nlinarith [ht₀X]
    nlinarith [h1, hHh']
  have hνℓ : 1024 * t₀ ≤ ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖ := by
    have h1 : 2048 * t₀ ≤ cL * sweepW' D ε := by nlinarith [ht₀Y]
    nlinarith [h1, hlen]
  have hmain := chordZone_margin (D := D) (r := r) hv hlam0 hlam12 hchord ht₀0 hνh hνℓ hbase
    hclose hA hB hz0 hz1
  refine le_trans ?_ hmain
  have hprod : c_h * cL * (sweepW' D ε) ^ 3
      ≤ ‖chartUp r D lam δ₁ δ₂ ε v‖ * ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖ := by
    have h3 : c_h * cL * (sweepW' D ε) ^ 3
        = (c_h * (sweepW' D ε) ^ 2) * (cL * sweepW' D ε) := by ring
    rw [h3]
    exact mul_le_mul hHh' hlen (by positivity) (by positivity)
  have hfac : c_h * cL * (sweepW' D ε) ^ 3 / (8 * period)
      ≤ (‖chartUp r D lam δ₁ δ₂ ε v‖ * ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖)
        / (8 * period) := by
    exact div_le_div_of_nonneg_right hprod (by positivity)
  exact hfac


end Work.Drive.H2

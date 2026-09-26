import Mathlib
import Submission.Work.Drive.Generic.nclmData
import Submission.Work.Drive.Generic.nclm_chord_margin
import Submission.Work.Drive.Generic.nclm_chamfer_fwd_margin
import Submission.Work.Drive.Generic.nclm_chamfer_bwd_margin

set_option maxHeartbeats 4000000

/-!
# The assembly of the per-loop angular-velocity margin

This module consumes the chart-data package `Work.Drive.Generic.nclmData` and the four branch bounds
of `nclmBranch.lean` (the arc via `nclm_arc_margin`, the chord via `nclm_chord_margin`, the two
chamfers via `nclm_chamfer_fwd_margin`/`nclm_chamfer_bwd_margin`) and produces the per-loop margin of
`Work.Drive.Generic.needleChartLoop_margin` uniformly over the box.

The extra ingredient is `nclm_arc_margin_closed`: the arc bound of `nclm_arc_margin` is stated on the
*open* interval `(λ, 1-λ)`, while the loop's arc branch actually traverses the *closed* interval
(the loop parameter `s` with `sweepParam s = 0` or `1/2` gives the arc's endpoints).  The bound is
extended to the closed interval by continuity.
-/

noncomputable section
namespace Work.Drive.Generic

open LeanEval.KnotTheory.Quadrisecant MeasureTheory
open scoped Real Topology intervalIntegral

/-- The bracket of the arc piece of the margin. -/
noncomputable def nclmArcBracket (r : ℝ → Space) {d : BandArcData} (D : Work.Drive.SweepData d)
    (lam δ₁ δ₂ ε σ : ℝ) (v : Space) : ℝ → ℝ :=
  fun ξ => nclmAH r D lam δ₁ δ₂ ε σ v ξ * deriv (nclmAX r D lam δ₁ δ₂ ε σ v) ξ
    - nclmAX r D lam δ₁ δ₂ ε σ v ξ * deriv (nclmAH r D lam δ₁ δ₂ ε σ v) ξ

lemma nclmArcBracket_apply (r : ℝ → Space) {d : BandArcData} (D : Work.Drive.SweepData d)
    (lam δ₁ δ₂ ε σ : ℝ) (v : Space) (ξ : ℝ) :
    nclmArcBracket r D lam δ₁ δ₂ ε σ v ξ
      = nclmAH r D lam δ₁ δ₂ ε σ v ξ * deriv (nclmAX r D lam δ₁ δ₂ ε σ v) ξ
        - nclmAX r D lam δ₁ δ₂ ε σ v ξ * deriv (nclmAH r D lam δ₁ δ₂ ε σ v) ξ := rfl

lemma continuous_nclmArcBracket {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : Work.Drive.SweepData d) (lam δ₁ δ₂ ε σ : ℝ) (v : Space) :
    Continuous (nclmArcBracket r D lam δ₁ δ₂ ε σ v) := by
  have hvel : Continuous (velocity r) := by
    have h : Continuous (deriv r) := hr.smooth.continuous_deriv (by simp : (1 : WithTop ℕ∞) ≤ ⊤)
    rwa [show velocity r = deriv r from rfl]
  have hXc : Continuous (nclmAX r D lam δ₁ δ₂ ε σ v) := by
    show Continuous (fun ξ : ℝ => inner ℝ (Work.Drive.sweepArc' r D σ ξ
      - Work.Drive.chartC r D lam δ₁ δ₂ ε v) v)
    refine Continuous.inner ?_ continuous_const
    show Continuous (fun ξ : ℝ => r (Work.Drive.taR D σ + ξ * Work.Drive.sweepW' D σ)
      - Work.Drive.chartC r D lam δ₁ δ₂ ε v)
    exact (hr.smooth.continuous.comp
      (continuous_const.add (continuous_id.mul continuous_const))).sub continuous_const
  have hHc : Continuous (nclmAH r D lam δ₁ δ₂ ε σ v) := by
    show Continuous (fun ξ : ℝ => inner ℝ (Work.Drive.sweepArc' r D σ ξ
      - Work.Drive.chartC r D lam δ₁ δ₂ ε v) (Work.Drive.chartE r D lam δ₁ δ₂ ε v))
    refine Continuous.inner ?_ continuous_const
    show Continuous (fun ξ : ℝ => r (Work.Drive.taR D σ + ξ * Work.Drive.sweepW' D σ)
      - Work.Drive.chartC r D lam δ₁ δ₂ ε v)
    exact (hr.smooth.continuous.comp
      (continuous_const.add (continuous_id.mul continuous_const))).sub continuous_const
  have hdX : deriv (nclmAX r D lam δ₁ δ₂ ε σ v)
      = fun ξ : ℝ => Work.Drive.sweepW' D σ * inner ℝ (velocity r
          (Work.Drive.taR D σ + ξ * Work.Drive.sweepW' D σ)) v :=
    funext (nclm_deriv_nclmAX hr D lam δ₁ δ₂ ε σ v)
  have hdH : deriv (nclmAH r D lam δ₁ δ₂ ε σ v)
      = fun ξ : ℝ => Work.Drive.sweepW' D σ * inner ℝ (velocity r
          (Work.Drive.taR D σ + ξ * Work.Drive.sweepW' D σ))
            (Work.Drive.chartE r D lam δ₁ δ₂ ε v) :=
    funext (nclm_deriv_nclmAH hr D lam δ₁ δ₂ ε σ v)
  have hdXc : Continuous (deriv (nclmAX r D lam δ₁ δ₂ ε σ v)) := by
    rw [hdX]
    exact continuous_const.mul (Continuous.inner
      (hvel.comp (continuous_const.add (continuous_id.mul continuous_const))) continuous_const)
  have hdHc : Continuous (deriv (nclmAH r D lam δ₁ δ₂ ε σ v)) := by
    rw [hdH]
    exact continuous_const.mul (Continuous.inner
      (hvel.comp (continuous_const.add (continuous_id.mul continuous_const))) continuous_const)
  exact (hHc.mul hdXc).sub (hXc.mul hdHc)

/-- **The margin on the arc piece, in terms of the bracket.** -/
lemma nclm_marg_arc_eq {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : Work.Drive.SweepData d) {lam δ₁ δ₂ ε σ : ℝ} {v : Space} {w : ℝ}
    (hwdef : Work.Drive.sweepW' D σ = w) (hwne : w ≠ 0) (ξ : ℝ) :
    nclmMarg r D lam δ₁ δ₂ ε v (Work.Drive.sweepArc' r D σ ξ)
        (((1 - 2 * lam) * (2 / period) * w) •
          velocity r (Work.Drive.taR D σ + ξ * Work.Drive.sweepW' D σ))
      = ((1 - 2 * lam) * (2 / period)) * nclmArcBracket r D lam δ₁ δ₂ ε σ v ξ := by
  have h1 : inner ℝ (Work.Drive.sweepArc' r D σ ξ
      - Work.Drive.chartC r D lam δ₁ δ₂ ε v) (Work.Drive.chartE r D lam δ₁ δ₂ ε v)
      = nclmAH r D lam δ₁ δ₂ ε σ v ξ := rfl
  have h2 : inner ℝ (Work.Drive.sweepArc' r D σ ξ
      - Work.Drive.chartC r D lam δ₁ δ₂ ε v) v = nclmAX r D lam δ₁ δ₂ ε σ v ξ := rfl
  rw [nclmMarg, nclmArcBracket, h1, h2, real_inner_smul_left, real_inner_smul_left,
    nclm_deriv_nclmAX hr, nclm_deriv_nclmAH hr, hwdef]
  field_simp
  try ring

/-- **The arc piece, on the closed interval.** -/
theorem nclm_arc_margin_closed {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : Work.Drive.SweepData d) {lam δ₁ δ₂ ε σ : ℝ} {v : Space} {w m kap : ℝ}
    (hlam0 : 0 < lam) (hlam4 : lam ≤ 1 / 4) (hw : 0 < w) (hm : 0 < m) (hkap : 0 < kap)
    (hwdef : Work.Drive.sweepW' D σ = w)
    (hmono : StrictMonoOn (nclmAX r D lam δ₁ δ₂ ε σ v) (Set.Icc (0 : ℝ) 1))
    (hxpos : ∀ ξ ∈ Set.Ioo (0 : ℝ) 1, m * w / 8 ≤ deriv (nclmAX r D lam δ₁ δ₂ ε σ v) ξ)
    (hdiff : ∀ ξ ∈ Set.Ioo (0 : ℝ) 1, DifferentiableAt ℝ (nclmAH r D lam δ₁ δ₂ ε σ v) ξ)
    (hchord : ∀ ξ₁ ∈ Set.Icc (0 : ℝ) 1, ∀ ξ₂ ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ ξ ∈ Set.Icc (0 : ℝ) 1,
        nclmAX r D lam δ₁ δ₂ ε σ v ξ
            = t * nclmAX r D lam δ₁ δ₂ ε σ v ξ₁
              + (1 - t) * nclmAX r D lam δ₁ δ₂ ε σ v ξ₂ →
        t * nclmAH r D lam δ₁ δ₂ ε σ v ξ₁
            + (1 - t) * nclmAH r D lam δ₁ δ₂ ε σ v ξ₂ ≤ nclmAH r D lam δ₁ δ₂ ε σ v ξ)
    (hξ₀ : ∃ ξ₀ ∈ Set.Ioo lam (1 - lam),
      nclmAX r D lam δ₁ δ₂ ε σ v ξ₀ = 0
        ∧ kap * w ^ 2 / 2 ≤ nclmAH r D lam δ₁ δ₂ ε σ v ξ₀)
    {ξ : ℝ} (hξ : ξ ∈ Set.Icc lam (1 - lam)) :
    kap * m * w ^ 3 / (16 * period)
      ≤ nclmMarg r D lam δ₁ δ₂ ε v (Work.Drive.sweepArc' r D σ ξ)
          (((1 - 2 * lam) * (2 / period) * w) •
            velocity r (Work.Drive.taR D σ + ξ * Work.Drive.sweepW' D σ)) := by
  have hwne : w ≠ 0 := ne_of_gt hw
  have hid : ∀ ξ : ℝ, nclmMarg r D lam δ₁ δ₂ ε v (Work.Drive.sweepArc' r D σ ξ)
      (((1 - 2 * lam) * (2 / period) * w) •
        velocity r (Work.Drive.taR D σ + ξ * Work.Drive.sweepW' D σ))
      = ((1 - 2 * lam) * (2 / period)) * nclmArcBracket r D lam δ₁ δ₂ ε σ v ξ :=
    fun ξ => nclm_marg_arc_eq hr D hwdef hwne ξ
  have hint : ∀ ξ ∈ Set.Ioo lam (1 - lam), kap * m * w ^ 3 / (16 * period)
      ≤ nclmMarg r D lam δ₁ δ₂ ε v (Work.Drive.sweepArc' r D σ ξ)
          (((1 - 2 * lam) * (2 / period) * w) •
            velocity r (Work.Drive.taR D σ + ξ * Work.Drive.sweepW' D σ)) :=
    fun ξ hξ => nclm_arc_margin hr D hlam0 hlam4 hw hm hkap hwdef hmono hxpos hdiff hchord hξ₀ hξ
  have hcont := continuous_nclmArcBracket hr D lam δ₁ δ₂ ε σ v
  rcases eq_or_lt_of_le hξ.1 with h | h
  · rw [← h, hid lam]
    refine ge_of_tendsto ((continuous_const.mul hcont).continuousAt.mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi lam))) ?_
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Ioo_mem_nhds (show lam - 1 < lam by linarith)
      (show lam < 1 - lam by linarith)] with x hx hxgt
    change kap * m * w ^ 3 / (16 * period)
      ≤ ((1 - 2 * lam) * (2 / period)) * nclmArcBracket r D lam δ₁ δ₂ ε σ v x
    rw [← hid x]
    exact (hint x ⟨hxgt, hx.2⟩)
  rcases eq_or_lt_of_le hξ.2 with h2 | h2
  · rw [h2, hid (1 - lam)]
    refine ge_of_tendsto ((continuous_const.mul hcont).continuousAt.mono_left
      (nhdsWithin_le_nhds (s := Set.Iio (1 - lam)))) ?_
    · rw [eventually_nhdsWithin_iff]
      filter_upwards [Ioo_mem_nhds (show lam < 1 - lam by linarith)
        (show 1 - lam < 1 - lam + 1 by linarith)] with x hx hxlt
      change kap * m * w ^ 3 / (16 * period)
        ≤ ((1 - 2 * lam) * (2 / period)) * nclmArcBracket r D lam δ₁ δ₂ ε σ v x
      rw [← hid x]
      exact (hint x ⟨hx.1, hxlt⟩)
  · exact hint ξ ⟨h, h2⟩


/-! ## The four branch formulas of the chamfered loop -/

lemma sweepLoopChamfer_arc₁ {r : ℝ → Space} {d : BandArcData} (D : Work.Drive.SweepData d)
    {lam σ t : ℝ} (h : sweepParam t ≤ 1 / 2) :
    sweepLoopChamfer r D lam σ t
      = sweepArc' r D σ (lam + (1 - 2 * lam) * (2 * sweepParam t)) :=
  sweepLoopChamfer_arcZone' D h

lemma chamferVel_arc₁ {r : ℝ → Space} {d : BandArcData} (D : Work.Drive.SweepData d)
    {lam σ t : ℝ} (h : sweepParam t ≤ 1 / 2) :
    chamferVel r D lam σ t
      = (((1 - 2 * lam) * (2 / period)) * sweepW' D σ) •
          velocity r (taR D σ + (lam + (1 - 2 * lam) * (2 * sweepParam t)) * sweepW' D σ) := by
  simp only [chamferVel]
  rw [if_pos h]

lemma sweepLoopChamfer_chamfer₁ {r : ℝ → Space} {d : BandArcData} (D : Work.Drive.SweepData d)
    {lam σ t : ℝ} (h1 : ¬ sweepParam t ≤ 1 / 2) (h2 : sweepParam t ≤ 1 / 2 + lam / 2) :
    sweepLoopChamfer r D lam σ t
      = (1 - (2 * sweepParam t - 1) / lam) • sweepArc' r D σ (1 - lam)
        + ((2 * sweepParam t - 1) / lam) • sweepChord' r D σ (1 - lam) := by
  simp only [sweepLoopChamfer]
  rw [if_neg h1, if_pos h2]

lemma chamferVel_chamfer₁ {r : ℝ → Space} {d : BandArcData} (D : Work.Drive.SweepData d)
    {lam σ t : ℝ} (h1 : ¬ sweepParam t ≤ 1 / 2) (h2 : sweepParam t ≤ 1 / 2 + lam / 2) :
    chamferVel r D lam σ t
      = -(2 / (lam * period)) • loopDev r D σ (1 - lam) := by
  simp only [chamferVel]
  rw [if_neg h1, if_pos h2]
  rw [show (2 / lam) * (1 / period) = 2 / (lam * period) from by ring]
  rw [show sweepChord' r D σ (1 - lam) - sweepArc' r D σ (1 - lam)
      = -(sweepArc' r D σ (1 - lam) - sweepChord' r D σ (1 - lam)) from by abel]
  rw [smul_neg, neg_smul]
  rfl

lemma sweepLoopChamfer_chord {r : ℝ → Space} {d : BandArcData} (D : Work.Drive.SweepData d)
    {lam σ t : ℝ} (h1 : ¬ sweepParam t ≤ 1 / 2) (h2 : ¬ sweepParam t ≤ 1 / 2 + lam / 2)
    (h3 : sweepParam t ≤ 1 - lam / 2) :
    sweepLoopChamfer r D lam σ t
      = sweepChord' r D σ ((1 - lam)
          - ((sweepParam t - (1 / 2 + lam / 2)) / (1 / 2 - lam)) * (1 - 2 * lam)) := by
  simp only [sweepLoopChamfer]
  rw [if_neg h1, if_neg h2, if_pos h3]

lemma chamferVel_chord {r : ℝ → Space} {d : BandArcData} (D : Work.Drive.SweepData d)
    {lam σ t : ℝ} (h1 : ¬ sweepParam t ≤ 1 / 2) (h2 : ¬ sweepParam t ≤ 1 / 2 + lam / 2)
    (h3 : sweepParam t ≤ 1 - lam / 2) :
    chamferVel r D lam σ t
      = -((1 - 2 * lam) / ((1 / 2 - lam) * period)) •
          (r (tbR D σ) - r (taR D σ)) := by
  simp only [chamferVel]
  rw [if_neg h1, if_neg h2, if_pos h3]

lemma sweepLoopChamfer_chamfer₂ {r : ℝ → Space} {d : BandArcData} (D : Work.Drive.SweepData d)
    {lam σ t : ℝ} (h1 : ¬ sweepParam t ≤ 1 / 2) (h2 : ¬ sweepParam t ≤ 1 / 2 + lam / 2)
    (h3 : ¬ sweepParam t ≤ 1 - lam / 2) :
    sweepLoopChamfer r D lam σ t
      = (1 - (sweepParam t - (1 - lam / 2)) / (lam / 2)) • sweepChord' r D σ lam
        + ((sweepParam t - (1 - lam / 2)) / (lam / 2)) • sweepArc' r D σ lam := by
  simp only [sweepLoopChamfer]
  rw [if_neg h1, if_neg h2, if_neg h3]

lemma chamferVel_chamfer₂ {r : ℝ → Space} {d : BandArcData} (D : Work.Drive.SweepData d)
    {lam σ t : ℝ} (h1 : ¬ sweepParam t ≤ 1 / 2) (h2 : ¬ sweepParam t ≤ 1 / 2 + lam / 2)
    (h3 : ¬ sweepParam t ≤ 1 - lam / 2) :
    chamferVel r D lam σ t
      = (2 / (lam * period)) • loopDev r D σ lam := by
  simp only [chamferVel]
  rw [if_neg h1, if_neg h2, if_neg h3]
  rw [show (2 / lam) * (1 / period) = 2 / (lam * period) from by ring]
  rfl


/-! ## The assembly -/

theorem nclm_assemblyC {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : Work.Drive.SweepData d) {lam δ₁ δ₂ ε : ℝ} {v : Space} {cℓ Cℓ ch Ch cm cE cK : ℝ}
    (hlam0 : 0 < lam) (hlam2 : lam < 1 / 2) (hlam4 : lam ≤ 1 / 4)
    (hδ₁0 : 0 < δ₁) (hδ₁16 : δ₁ ≤ LeanEval.KnotTheory.Quadrisecant.period / 16)
    (hδ₂0 : 0 < δ₂) (hv : ‖v‖ = 1)
    (hcℓ : 0 < cℓ) (hCℓ : 0 < Cℓ) (hch : 0 < ch) (hCh : 0 < Ch) (hcm : 0 < cm)
    (hcE : 0 < cE) (hcK : 0 ≤ cK)
    (hdataC : nclmDataC r D lam δ₁ δ₂ ε v cℓ Cℓ ch Ch cm cE cK) :
    0 < min (ch * cm * (Work.Drive.sweepW' D ε) ^ 3
          / (1024 * LeanEval.KnotTheory.Quadrisecant.period))
        (min (3 * cℓ * ch * (Work.Drive.sweepW' D ε) ^ 3
            / (16 * LeanEval.KnotTheory.Quadrisecant.period))
          (cℓ * cE * (Work.Drive.sweepW' D ε) ^ 3
            / (64 * LeanEval.KnotTheory.Quadrisecant.period))) ∧
      ∀ (σ s : ℝ), ε - δ₂ ≤ σ → σ ≤ ε + δ₂ →
        min (ch * cm * (Work.Drive.sweepW' D ε) ^ 3
            / (1024 * LeanEval.KnotTheory.Quadrisecant.period))
          (min (3 * cℓ * ch * (Work.Drive.sweepW' D ε) ^ 3
              / (16 * LeanEval.KnotTheory.Quadrisecant.period))
            (cℓ * cE * (Work.Drive.sweepW' D ε) ^ 3
              / (64 * LeanEval.KnotTheory.Quadrisecant.period)))
          ≤ nclmMarg r D lam δ₁ δ₂ ε v (sweepLoopChamfer r D lam σ s)
            (chamferVel r D lam σ s) := by
  have hp : (0 : ℝ) < LeanEval.KnotTheory.Quadrisecant.period := period_pos
  simp only [nclmDataC] at hdataC
  obtain ⟨hWp, hws, hℓpos, hℓlo, hℓhi, hE1, hEv, htan, hacc, hhlo, hhhi, hmono, hxpos0, hxposb,
    hdiff, hchord, hξ₀, hHbd, hend, hdev, hbr⟩ := hdataC
  set W : ℝ := sweepW' D ε with hWdef
  have hWpos : 0 < W := hWp
  set Lc : ℝ := ‖Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε‖ with hLcdef
  have hLcpos : 0 < Lc := hℓpos
  have hchUp : 0 < ‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖ := by
    have h1 : ch * W ^ 2 ≤ ‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖ / 2 := hhlo
    have h2 : (0:ℝ) < ch * W ^ 2 := mul_pos hch (pow_pos hWpos 2)
    linarith
  have hbr' : 2 * ‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖ * cK ≤ Lc * cE / 8 := by
    have h := hbr
    rw [hLcdef]
    nlinarith [hbr, hcK]
  refine ⟨?_, ?_⟩
  · refine lt_min (by positivity) (lt_min (by positivity) (by positivity))
  intro σ s hσlo hσhi
  obtain ⟨hwslo, hwshi⟩ := hws σ hσlo hσhi
  have hwpos : 0 < sweepW' D σ := lt_of_lt_of_le (half_pos hWpos) hwslo
  have hsqlo : (W / 2) ^ 2 ≤ (sweepW' D σ) ^ 2 := by
    have h : W / 2 ≤ sweepW' D σ := hwslo
    nlinarith [h, hWpos, hwpos]
  have hsqhi : (sweepW' D σ) ^ 2 ≤ 4 * W ^ 2 := by
    have h : sweepW' D σ ≤ 2 * W := hwshi
    nlinarith [h, hWpos, hwpos]
  have hcub : W ^ 3 / 8 ≤ (sweepW' D σ) ^ 3 := by
    have h : W / 2 ≤ sweepW' D σ := hwslo
    nlinarith [h, hWpos, hwpos]
  have huw0 : 0 ≤ sweepParam s := (sweepParam_mem s).1
  have huw1 : sweepParam s < 1 := (sweepParam_mem s).2
  obtain ⟨hXA, hXB, hcA, hcB, hhA, hhB, hxW, hhW, hcAl, hcBl, hhAl, hhBl⟩ := hend σ hσlo hσhi
  by_cases hu : sweepParam s ≤ 1 / 2
  · -- **the arc branch**
    rw [sweepLoopChamfer_arc₁ D hu, chamferVel_arc₁ D hu]
    have hξ : (lam + (1 - 2 * lam) * (2 * sweepParam s)) ∈ Set.Icc lam (1 - lam) := by
      constructor
      · nlinarith [huw0, hlam4]
      · nlinarith [hu, hlam4]
    have hxpos : ∀ ξ ∈ Set.Ioo (0 : ℝ) 1, cm * sweepW' D σ / 8 ≤
        deriv (nclmAX r D lam δ₁ δ₂ ε σ v) ξ := by
      intro ξ hξI
      have hξI' : ξ ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hξI.1, le_of_lt hξI.2⟩
      rw [nclm_deriv_nclmAX hr]
      have htab : Work.Drive.taR D σ ≤ Work.Drive.tbR D σ := by
        have h := hwpos
        rw [Work.Drive.sweepW'] at h
        linarith
      have hsweq : Work.Drive.sweepW' D σ
          = Work.Drive.tbR D σ - Work.Drive.taR D σ := rfl
      have hxmem : Work.Drive.taR D σ + ξ * Work.Drive.sweepW' D σ
          ∈ Set.Icc (Work.Drive.taR D σ) (Work.Drive.tbR D σ) := by
        constructor
        · rw [hsweq]; nlinarith [hξI'.1, hξI'.2]
        · rw [hsweq]; nlinarith [hξI'.1, hξI'.2, htab]
      have h := htan σ hσlo hσhi _ hxmem
      nlinarith [h, hwpos, hcm]
    have hξ₀' : ∃ ξ₀ ∈ Set.Ioo lam (1 - lam),
        nclmAX r D lam δ₁ δ₂ ε σ v ξ₀ = 0
          ∧ (ch / 8) * (sweepW' D σ) ^ 2 / 2 ≤ nclmAH r D lam δ₁ δ₂ ε σ v ξ₀ := by
      obtain ⟨ξ₀, hξ₀mem, hX0, hH0⟩ := hξ₀ σ hσlo hσhi
      refine ⟨ξ₀, hξ₀mem, hX0, ?_⟩
      nlinarith [hH0, hch, hsqhi, hWpos]
    refine le_trans ?_ (nclm_arc_margin_closed hr D hlam0 hlam4 hwpos hcm (by positivity)
      rfl (hmono σ hσlo hσhi) hxpos (hdiff σ hσlo hσhi) (hchord σ hσlo hσhi) hξ₀' hξ)
    refine le_trans (min_le_left _ _) ?_
    have hB : (ch / 8) * cm * (sweepW' D σ) ^ 3
          / (16 * LeanEval.KnotTheory.Quadrisecant.period)
        = ch * cm * (sweepW' D σ) ^ 3
          / (128 * LeanEval.KnotTheory.Quadrisecant.period) := by ring
    rw [hB]
    have h1 : W ^ 3 ≤ 8 * (sweepW' D σ) ^ 3 := by nlinarith [hcub, hWpos]
    field_simp
    nlinarith [h1, hch, hcm, hp]
  · by_cases hu2 : sweepParam s ≤ 1 / 2 + lam / 2
    · -- **the first chamfer**
      have h1u : 1 / 2 < sweepParam s := lt_of_not_ge hu
      rw [sweepLoopChamfer_chamfer₁ D hu hu2, chamferVel_chamfer₁ D hu hu2]
      have ht0 : 0 ≤ (2 * sweepParam s - 1) / lam := by
        apply div_nonneg _ hlam0.le
        linarith
      have ht1 : (2 * sweepParam s - 1) / lam ≤ 1 := by
        rw [div_le_one hlam0]
        linarith
      have hH1 : |inner ℝ (Work.Drive.sweepArc' r D σ (1 - lam)
          - Work.Drive.chartC r D lam δ₁ δ₂ ε v) (Work.Drive.chartE r D lam δ₁ δ₂ ε v)|
          ≤ 2 * ‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖ :=
        hHbd σ hσlo hσhi (1 - lam) ⟨by linarith, le_rfl⟩
      have hH2 : |inner ℝ (Work.Drive.sweepChord' r D σ (1 - lam)
          - Work.Drive.chartC r D lam δ₁ δ₂ ε v) (Work.Drive.chartE r D lam δ₁ δ₂ ε v)|
          ≤ 2 * ‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖ := by
        have h := hhBl
        nlinarith [h]
      have hdevE := (hdev σ hσlo hσhi).1
      have hdevV := (hdev σ hσlo hσhi).2.2.1
      have hP : (sweepW' D σ) ^ 2 * Lc * cE
            / (16 * LeanEval.KnotTheory.Quadrisecant.period)
          ≤ nclmMarg r D lam δ₁ δ₂ ε v (Work.Drive.sweepArc' r D σ (1 - lam))
              (-(2 / (lam * LeanEval.KnotTheory.Quadrisecant.period)) •
                Work.Drive.loopDev r D σ (1 - lam)) :=
        nclm_chamfer_fwd_margin D hlam0 hlam2 hLcpos hchUp hwpos hcE hcK hbr'
          hXA hH1 hdevE hdevV
      have hQ : (sweepW' D σ) ^ 2 * Lc * cE
            / (16 * LeanEval.KnotTheory.Quadrisecant.period)
          ≤ nclmMarg r D lam δ₁ δ₂ ε v (Work.Drive.sweepChord' r D σ (1 - lam))
              (-(2 / (lam * LeanEval.KnotTheory.Quadrisecant.period)) •
                Work.Drive.loopDev r D σ (1 - lam)) :=
        nclm_chamfer_fwd_margin D hlam0 hlam2 hLcpos hchUp hwpos hcE hcK hbr'
          hcBl hH2 hdevE hdevV
      refine le_trans ?_ (nclm_marg_seg D ht0 ht1 hP hQ)
      refine le_trans (min_le_right _ _ |>.trans (min_le_right _ _)) ?_
      have hB : (sweepW' D σ) ^ 2 * Lc * cE
            / (16 * LeanEval.KnotTheory.Quadrisecant.period)
          = (sweepW' D σ) ^ 2 * Lc * cE
            / (16 * LeanEval.KnotTheory.Quadrisecant.period) := rfl
      rw [hB]
      have hL : cℓ * W ≤ Lc := hℓlo
      have hmm : cℓ * W * (W / 2) ^ 2 ≤ Lc * (sweepW' D σ) ^ 2 :=
        mul_le_mul hL hsqlo (by positivity) (by positivity)
      field_simp
      nlinarith [hmm, hcℓ, hcE, hp, hWpos, hwpos,
        mul_nonneg (mul_nonneg hcℓ.le hcE.le) hp.le]
    · by_cases hu3 : sweepParam s ≤ 1 - lam / 2
      · -- **the chord branch**
        have h2u : 1 / 2 + lam / 2 < sweepParam s := lt_of_not_ge hu2
        rw [sweepLoopChamfer_chord D hu hu2 hu3, chamferVel_chord D hu hu2 hu3]
        set r0 : ℝ := (sweepParam s - (1 / 2 + lam / 2)) / (1 / 2 - lam) with hr0def
        have hr0 : 0 ≤ r0 := by
          rw [hr0def]
          exact div_nonneg (by linarith) (by linarith)
        have hr1 : r0 ≤ 1 := by
          rw [hr0def]
          rw [div_le_one (by linarith)]
          linarith
        have hξ0 : 0 ≤ (1 - lam) - r0 * (1 - 2 * lam) := by nlinarith [hr0, hr1, hlam4]
        have hξ1 : (1 - lam) - r0 * (1 - 2 * lam) ≤ 1 := by nlinarith [hr0, hr1, hlam4]
        have hhA' : inner ℝ (r (Work.Drive.taR D σ)
            - Work.Drive.chartC r D lam δ₁ δ₂ ε v) (Work.Drive.chartE r D lam δ₁ δ₂ ε v)
            ≤ -(‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖ / 2) / 2 := by linarith [hhA]
        have hhB' : inner ℝ (r (Work.Drive.tbR D σ)
            - Work.Drive.chartC r D lam δ₁ δ₂ ε v) (Work.Drive.chartE r D lam δ₁ δ₂ ε v)
            ≤ -(‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖ / 2) / 2 := by linarith [hhB]
        -- the chord margin at the *rescaled* chord length `3 Lc / 2` and height `‖chartUp‖/2`,
        -- the scale at which the slacked endpoint clauses of the chart data apply
        have hcA' : |inner ℝ (r (Work.Drive.taR D σ)
            - Work.Drive.chartC r D lam δ₁ δ₂ ε v) v|
            ≤ (3 * Lc / 2) / 2 := by
          rw [hLcdef]; nlinarith [hcA]
        have hcB' : |inner ℝ (r (Work.Drive.tbR D σ)
            - Work.Drive.chartC r D lam δ₁ δ₂ ε v) v|
            ≤ (3 * Lc / 2) / 2 := by
          rw [hLcdef]; nlinarith [hcB]
        have hxW' : (3 * Lc / 2) / 2
            ≤ inner ℝ (r (Work.Drive.tbR D σ) - r (Work.Drive.taR D σ)) v := by
          rw [hLcdef]; nlinarith [hxW]
        have hhW' : |inner ℝ (r (Work.Drive.tbR D σ) - r (Work.Drive.taR D σ))
            (Work.Drive.chartE r D lam δ₁ δ₂ ε v)|
            ≤ (‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖ / 2) / 8 := by
          linarith [hhW]
        refine le_trans ?_ (nclm_chord_margin D hlam0 hlam4 hξ0 hξ1 (by positivity)
          (half_pos hchUp) hcA' hcB' hhA' hhB' hxW' hhW')
        refine le_trans (min_le_right _ _ |>.trans (min_le_left _ _)) ?_
        have hchUp2 : 2 * ch * W ^ 2 ≤ ‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖ := by
          have h := hhlo
          nlinarith [h]
        have hB : 3 * (3 * Lc / 2) * (‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖ / 2)
              / (16 * LeanEval.KnotTheory.Quadrisecant.period)
            = 9 * Lc * ‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖
              / (64 * LeanEval.KnotTheory.Quadrisecant.period) := by ring
        rw [hB]
        have hmul : cℓ * W * (2 * ch * W ^ 2) ≤ Lc * ‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖ :=
          mul_le_mul hℓlo hchUp2 (by positivity) (by positivity)
        field_simp
        nlinarith [hmul, hcℓ, hch, hp, hWpos, mul_nonneg (mul_nonneg hcℓ.le hch.le) hWpos.le]
      · -- **the second chamfer**
        have h3u : 1 - lam / 2 < sweepParam s := lt_of_not_ge hu3
        rw [sweepLoopChamfer_chamfer₂ D hu hu2 hu3, chamferVel_chamfer₂ D hu hu2 hu3]
        have ht0 : 0 ≤ (sweepParam s - (1 - lam / 2)) / (lam / 2) := by
          apply div_nonneg _ (by linarith)
          linarith
        have ht1 : (sweepParam s - (1 - lam / 2)) / (lam / 2) ≤ 1 := by
          rw [div_le_one (by linarith)]
          linarith
        have hH1 : |inner ℝ (Work.Drive.sweepChord' r D σ lam
            - Work.Drive.chartC r D lam δ₁ δ₂ ε v) (Work.Drive.chartE r D lam δ₁ δ₂ ε v)|
            ≤ 2 * ‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖ := by
          have h := hhAl
          nlinarith [h]
        have hH2 : |inner ℝ (Work.Drive.sweepArc' r D σ lam
            - Work.Drive.chartC r D lam δ₁ δ₂ ε v) (Work.Drive.chartE r D lam δ₁ δ₂ ε v)|
            ≤ 2 * ‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖ :=
          hHbd σ hσlo hσhi lam ⟨le_rfl, by linarith⟩
        have hdevE := (hdev σ hσlo hσhi).2.1
        have hdevV := (hdev σ hσlo hσhi).2.2.2
        have hQ : (sweepW' D σ) ^ 2 * Lc * cE
              / (16 * LeanEval.KnotTheory.Quadrisecant.period)
            ≤ nclmMarg r D lam δ₁ δ₂ ε v (Work.Drive.sweepArc' r D σ lam)
                ((2 / (lam * LeanEval.KnotTheory.Quadrisecant.period)) •
                  Work.Drive.loopDev r D σ lam) :=
          nclm_chamfer_bwd_margin D hlam0 hlam2 hLcpos hchUp hwpos hcE hcK hbr'
            (by have h := hXB
                rw [show -(Lc / 4) = -Lc / 4 from by ring] at h
                exact h)
            hH2 hdevE hdevV
        have hP : (sweepW' D σ) ^ 2 * Lc * cE
              / (16 * LeanEval.KnotTheory.Quadrisecant.period)
            ≤ nclmMarg r D lam δ₁ δ₂ ε v (Work.Drive.sweepChord' r D σ lam)
                ((2 / (lam * LeanEval.KnotTheory.Quadrisecant.period)) •
                  Work.Drive.loopDev r D σ lam) :=
          nclm_chamfer_bwd_margin D hlam0 hlam2 hLcpos hchUp hwpos hcE hcK hbr'
            (by have h := hcAl
                rw [show -(Lc / 4) = -Lc / 4 from by ring] at h
                exact h)
            hH1 hdevE hdevV
        refine le_trans ?_ (nclm_marg_seg D ht0 ht1 hP hQ)
        refine le_trans (min_le_right _ _ |>.trans (min_le_right _ _)) ?_
        have hL : cℓ * W ≤ Lc := hℓlo
        have hB : (sweepW' D σ) ^ 2 * Lc * cE
              / (16 * LeanEval.KnotTheory.Quadrisecant.period)
            = (sweepW' D σ) ^ 2 * Lc * cE
              / (16 * LeanEval.KnotTheory.Quadrisecant.period) := rfl
        rw [hB]
        have hmm : cℓ * W * (W / 2) ^ 2 ≤ Lc * (sweepW' D σ) ^ 2 :=
          mul_le_mul hL hsqlo (by positivity) (by positivity)
        field_simp
        nlinarith [hmm, hcℓ, hcE, hp, hWpos, hwpos,
          mul_nonneg (mul_nonneg hcℓ.le hcE.le) hp.le]

/-- **The assembly at a fixed box, in the existential form.**  This is `nclm_assemblyC` with the
constants of the chart data unpacked: the per-loop margin follows from the package `nclmData`. -/
theorem nclm_assembly {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : Work.Drive.SweepData d) {lam δ₁ δ₂ ε : ℝ} {v : Space}
    (hlam0 : 0 < lam) (hlam2 : lam < 1 / 2) (hlam4 : lam ≤ 1 / 4)
    (hδ₁0 : 0 < δ₁) (hδ₁16 : δ₁ ≤ LeanEval.KnotTheory.Quadrisecant.period / 16)
    (hδ₂0 : 0 < δ₂) (hv : ‖v‖ = 1) (hdata : nclmData r D lam δ₁ δ₂ ε v) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (σ s : ℝ), ε - δ₂ ≤ σ → σ ≤ ε + δ₂ →
      κ ≤ nclmMarg r D lam δ₁ δ₂ ε v (sweepLoopChamfer r D lam σ s)
        (chamferVel r D lam σ s) := by
  obtain ⟨cℓ, Cℓ, ch, Ch, cm, cE, cK, hcℓ, hCℓ, hch, hCh, hcm, hcE, hcK, hC⟩ :=
    exists_nclmDataC hdata
  have hmain := nclm_assemblyC hr D hlam0 hlam2 hlam4 hδ₁0 hδ₁16 hδ₂0 hv
    hcℓ hCℓ hch hCh hcm hcE hcK hC
  exact ⟨_, hmain.1, fun σ s h1 h2 => hmain.2 σ s h1 h2⟩

end Work.Drive.Generic

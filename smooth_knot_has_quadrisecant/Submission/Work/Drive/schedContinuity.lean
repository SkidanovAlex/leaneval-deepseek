import Mathlib
import Submission.Work.Drive.chamferSchedule
import Submission.Work.Drive.chamferChordNoPiCorner

/-!
# Continuity of the schedules, pointwise and after the window clamp

`Work.Drive.schedAlpha` and `Work.Drive.schedBeta` are the depth/target schedules of the scheduled
chamfer loop (`NOTES_LEAD_scheduledBlur.md` §3).  The workspace's global lemmas

* `Work.Drive.continuous_schedAlpha` (ContinuousOn on `{σ | sweepW' D σ ≠ 0}`) and
* `Work.Drive.continuous_schedBeta` (ContinuousOn on the same set, but with a **global** hypothesis
  `∀ σ, sweepW' D σ ≠ 0 → ‖r (tbR D σ) - r (taR D σ)‖ ≠ 0`, which is *false* for `σ ≥ 1`, where
  `sweepW' D σ = period` but the chord degenerates)

are not in the shape the assembled blur layer needs.  What is needed (see the MISSING list of
`NOTES_LEAD_scheduledBlur.md` §4) is the *pointwise* `ContinuousAt` form — `schedBeta` is built from
the globally continuous `schedDep`, `schedPsi` and the chord length `‖r (tbR ·) - r (taR ·)‖`, the
latter being non-zero at the points in question — together with the **composition with the window
clamp** `s ↦ max (a/2) (min s ((1+b)/2))`, which is what makes the clamped loop `Γc` of
`NOTES_LEAD_scheduledBlur.md` §3 a loop to which `Work.Drive.continuous_chamferLoopGen` applies.

Nothing here is knot-geometric beyond the continuity of `r` and the non-vanishing of the chord
length at the clamped parameters (supplied by, e.g., `Work.Drive.sweepW'_pos_lt` + injectivity of `r`
on a period, or as a hypothesis).
-/

noncomputable section

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-- The cut depth `schedDep` is continuous without any hypothesis on `δs` (its only division is by
the *constant* `δs`).  The workspace's `Work.Drive.continuous_schedDep` carries an unused `δs ≠ 0`. -/
lemma continuous_schedDep' {d : BandArcData} (D : SweepData d) (lay ρ δs : ℝ) :
    Continuous (fun σ : ℝ => schedDep lay ρ δs D σ) :=
  (continuous_const.mul (sweepLoopChamfer_sweepW'_continuous D)).max
    (continuous_const.mul (schedPhi_continuous.comp ((continuous_schedC D).div_const δs)))

/-- **Pointwise continuity of the depth fraction `schedAlpha`** at a parameter where the retained
width does not vanish.  (`schedAlpha = schedDep / sweepW'`.) -/
lemma continuousAt_schedAlpha {d : BandArcData} (D : SweepData d) (lay ρ δs : ℝ) {σ₀ : ℝ}
    (hW : sweepW' D σ₀ ≠ 0) :
    ContinuousAt (fun σ : ℝ => schedAlpha lay ρ δs D σ) σ₀ :=
  (continuous_schedDep' D lay ρ δs).continuousAt.div
    (sweepLoopChamfer_sweepW'_continuous D).continuousAt hW

/-- **Pointwise continuity of the chord target `schedBeta`** at a parameter where the chord does not
degenerate.  No hypothesis on `δs` is needed. -/
lemma continuousAt_schedBeta {r : ℝ → Space} {d : BandArcData} (D : SweepData d)
    {lay ρ δs cQ : ℝ} (hr : Continuous r) {σ₀ : ℝ}
    (hL : ‖r (tbR D σ₀) - r (taR D σ₀)‖ ≠ 0) :
    ContinuousAt (fun σ : ℝ => schedBeta r lay ρ δs cQ D σ) σ₀ := by
  have hLc : Continuous (fun σ : ℝ => ‖r (tbR D σ) - r (taR D σ)‖) :=
    ((hr.comp (sweepLoopChamfer_tbR_continuous D)).sub
      (hr.comp (sweepLoopChamfer_taR_continuous D))).norm
  have hdep : Continuous (fun σ : ℝ => schedDep lay ρ δs D σ) := continuous_schedDep' D lay ρ δs
  have hpsi : Continuous (fun σ : ℝ => schedPsi D δs σ) :=
    schedPhi_continuous.comp (((continuous_const.mul (continuous_schedC D)).div_const δs))
  have hmin : ContinuousAt (fun σ : ℝ => min lay (cQ * schedDep lay ρ δs D σ
      / ‖r (tbR D σ) - r (taR D σ)‖)) σ₀ :=
    continuousAt_const.min ((continuousAt_const.mul hdep.continuousAt).div hLc.continuousAt hL)
  have h : ContinuousAt (fun σ : ℝ => (1 - schedPsi D δs σ) * lay
      + schedPsi D δs σ * min lay
        (cQ * schedDep lay ρ δs D σ / ‖r (tbR D σ) - r (taR D σ)‖)) σ₀ :=
    ((continuousAt_const.sub hpsi.continuousAt).mul continuousAt_const).add
      (hpsi.continuousAt.mul hmin)
  simpa only [schedBeta] using h

/-! ## The window clamp and the composition -/

/-- The window clamp `s ↦ max (a/2) (min s ((1+b)/2))` used to keep the `σ`-blur window of a slice
`σ ∈ [a,b]` inside `(0,1)` (`NOTES_LEAD_scheduledBlur.md` §3). -/
def schedClamp (a b s : ℝ) : ℝ := max (a / 2) (min s ((1 + b) / 2))

lemma continuous_schedClamp (a b : ℝ) : Continuous (schedClamp a b) :=
  continuous_const.max (continuous_id.min continuous_const)

lemma schedClamp_mem {a b s : ℝ} (hab : a / 2 ≤ (1 + b) / 2) :
    schedClamp a b s ∈ Set.Icc (a / 2) ((1 + b) / 2) :=
  ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩

/-- The window clamp fixes exactly its own range `[a/2, (1+b)/2]`. -/
lemma schedClamp_eq_self {a b x : ℝ} (hab : a / 2 ≤ (1 + b) / 2)
    (hx : x ∈ Set.Icc (a / 2) ((1 + b) / 2)) : schedClamp a b x = x := by
  rw [schedClamp, min_eq_left hx.2, max_eq_right hx.1]

/-- The window clamp is **idempotent** (its range is exactly `[a/2, (1+b)/2]`). -/
lemma schedClamp_idem {a b : ℝ} (hab : a / 2 ≤ (1 + b) / 2) (s : ℝ) :
    schedClamp a b (schedClamp a b s) = schedClamp a b s := by
  have h := schedClamp_mem (a := a) (b := b) (s := s) hab
  simp only [schedClamp] at h ⊢
  rw [min_eq_left h.2, max_eq_right h.1]

/-- **The composition of `schedBeta` with the window clamp is continuous**, as soon as the chord stays
non-degenerate on the clamped window.  This is the continuity input of the clamped loop `Γc` of
`NOTES_LEAD_scheduledBlur.md` §3 (via `Work.Drive.continuous_chamferLoopGen`). -/
lemma continuous_schedBeta_comp_clamp {r : ℝ → Space} {d : BandArcData} (D : SweepData d)
    {lay ρ δs cQ a b : ℝ} (hr : Continuous r) (hab : a / 2 ≤ (1 + b) / 2)
    (hne : ∀ σ ∈ Set.Icc (a / 2) ((1 + b) / 2), ‖r (tbR D σ) - r (taR D σ)‖ ≠ 0) :
    Continuous (fun s : ℝ => schedBeta r lay ρ δs cQ D (schedClamp a b s)) := by
  rw [continuous_iff_continuousAt]
  intro s
  exact (continuousAt_schedBeta D hr (hne _ (schedClamp_mem hab))).comp
    (continuous_schedClamp a b).continuousAt

/-- **The composition of `schedAlpha` with the window clamp is continuous**, as soon as the retained
width stays non-zero on the clamped window. -/
lemma continuous_schedAlpha_comp_clamp {d : BandArcData} (D : SweepData d)
    {lay ρ δs a b : ℝ} (hab : a / 2 ≤ (1 + b) / 2)
    (hne : ∀ σ ∈ Set.Icc (a / 2) ((1 + b) / 2), sweepW' D σ ≠ 0) :
    Continuous (fun s : ℝ => schedAlpha lay ρ δs D (schedClamp a b s)) := by
  rw [continuous_iff_continuousAt]
  intro s
  exact (continuousAt_schedAlpha D lay ρ δs (hne _ (schedClamp_mem hab))).comp
    (continuous_schedClamp a b).continuousAt

end Work.Drive

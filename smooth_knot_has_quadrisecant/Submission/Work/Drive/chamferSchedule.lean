import Mathlib
import Submission.Work.Drive.chamferLoopGenDefs
import Submission.Work.Drive.chamferLoopGenBlur
import Submission.Work.Drive.quadrisecantSpreadDefs
import Submission.Work.Drive.components_bounded_of_no_spreadQuad
import Submission.Work.Drive.sweepLoopChamfer_locallyIntegrable

/-!
# The depth/target schedules of the uniform-`ρ₀` design

`NOTES_LEAD_endgameUniform.md` §3 replaces the single chamfer fraction `λ` of the old design by a
**schedule** on the sweep: the *cut depth* `dep σ` of the retained arc is an absolute length
(`dep σ = max (lay · W_σ) (ρ · φ (c_σ / δs))`), and the *chord target* `β σ` is the fraction of the
chord at which the connectors land (`β σ = (1 - ψ) · lay + ψ · cQ · dep σ / L_σ`).  Here

* `W_σ = sweepW' D σ` is the parameter length of the slice's chord,
* `c_σ = min W_σ (period - W_σ)` is the *circular* length of the chord,
* `L_σ = ‖r (tb σ) - r (ta σ)‖` is its Euclidean length,
* `δs` is the short-chord scale of `E3′` (`Work.Drive.ShortMid`),
* `φ x = min 1 (max 0 (2x - 1))` is the ramp, and `cQ` a uniform fraction of the speed floor.

The two ramps are what make the design work:

* in the **short zone** `c_σ ≤ δs/2` the depth is exactly `lay · W_σ` and the target is exactly
  `lay` — i.e. the loop *is* the ordinary chamfered loop `sweepLoopChamfer r D lay`, whose
  retained arc is chord-free thanks to `ShortMid`-avoidance (no middle at all on a chord of
  parameter length `≤ δs`), **with no constraint relating `ρ` to `W_σ`**;
* in the **deep zone** `δs ≤ c_σ` the depth is `max (lay · W_σ) ρ ≥ ρ`, so the retained arc is
  chord-free by the `OFatR`-avoidance at scale `ρ`, at an *absolute* depth;
* in the **trough** `c_σ ≤ δs/4` both ramps vanish, so `α σ = β σ = lay`: this is the zone where
  the needle end and the wide-end estimate (both stated for the ordinary chamfered loop) apply.

This module only *defines* the schedules and proves their elementary properties (monotonicity and
the endpoint values of the ramp, the zone identities, continuity on a window where the chord is
non-degenerate).  The verification of the hypotheses of `Work.Drive.chamferLoopGenInjOnBall`
(deep zones) and `Work.Drive.chamferLoopGenInjOnNt` (short zones) is the bookkeeping brick.
-/

noncomputable section

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-- The ramp `φ x = min 1 (max 0 (2x - 1))` of the depth schedule. -/
def schedPhi (x : ℝ) : ℝ := min 1 (max 0 (2 * x - 1))

/-- The *circular* parameter length of the chord of a slice: `min W (period - W)`. -/
def schedC {d : BandArcData} (D : SweepData d) (σ : ℝ) : ℝ :=
  min (sweepW' D σ) (period - sweepW' D σ)

/-- **The cut depth**: `max (lay · W_σ) (ρ · φ (c_σ / δs))`. -/
def schedDep (lay ρ δs : ℝ) {d : BandArcData} (D : SweepData d) (σ : ℝ) : ℝ :=
  max (lay * sweepW' D σ) (ρ * schedPhi (schedC D σ / δs))

/-- **The arc-depth fraction** `α σ = dep σ / W_σ`. -/
def schedAlpha (lay ρ δs : ℝ) {d : BandArcData} (D : SweepData d) (σ : ℝ) : ℝ :=
  schedDep lay ρ δs D σ / sweepW' D σ

/-- The second ramp `ψ σ = φ (2 c_σ / δs)` of the target schedule. -/
def schedPsi {d : BandArcData} (D : SweepData d) (δs σ : ℝ) : ℝ :=
  schedPhi (2 * schedC D σ / δs)

/-- **The chord target** `β σ = (1 - ψ) · lay + ψ · min lay (cQ · dep σ / L_σ)`.

The `min lay` **clamp is essential** (and is a correction to the first version of the design, which
used the bare spatial target `cQ · dep σ / L_σ`): when the chord is spatially short (which happens
for the *wrap-around* slices `period - W_σ ≤ δs`, where `L_σ` is tiny although `W_σ ≈ period`) the
bare target `cQ · dep σ / L_σ` is far larger than `lay` and in fact larger than `1/2`, at which point
`Work.Drive.chamferLoopGen` degenerates (its chord branch is traversed backwards and is constant on
an interval).  With the clamp one has `β σ ≤ lay` always, and the two consumers of `β` are then both
satisfied:

* `Work.Drive.chamferLoopGenInjOnNt` (`Lemma B`, used wherever `α σ = lay`) wants
  `κ₁ lay ≤ β σ ≤ κ₂ lay` — true with `κ₁ := cQ/M`, `κ₂ := 1` (`M` a speed bound), since `β` is a
  blend of `lay` and of `min lay (cQ dep σ / L_σ) ≥ min lay (cQ · lay · W_σ / L_σ)` and `L_σ ≤ M W_σ`;
* `Work.Drive.chamferLoopGenInjOnBall` (`Lemma A`, used wherever the depth is the absolute `ρ φ`)
  wants `β σ · L_σ ≤ ‖sweepArc' (α σ) - r (taR)‖` — true because `β σ · L_σ ≤ cQ · dep σ` and
  `‖sweepArc' (α σ) - r (taR)‖ ≥ (m/2) · dep σ` with `cQ ≤ m/2`.

Also, `ψ σ = 0` still gives `β σ = lay` exactly (the *trough*), so the needle end and the wide-end
estimate continue to apply verbatim. -/
def schedBeta (r : ℝ → Space) (lay ρ δs cQ : ℝ) {d : BandArcData} (D : SweepData d)
    (σ : ℝ) : ℝ :=
  (1 - schedPsi D δs σ) * lay
    + schedPsi D δs σ
      * min lay (cQ * schedDep lay ρ δs D σ / ‖r (tbR D σ) - r (taR D σ)‖)

/-! ## Elementary properties of the ramp -/

lemma schedPhi_nonneg (x : ℝ) : 0 ≤ schedPhi x := le_min (by norm_num) (le_max_left _ _)

lemma schedPhi_le_one (x : ℝ) : schedPhi x ≤ 1 := min_le_left _ _

lemma schedPhi_mono : Monotone schedPhi := by
  intro x y hxy
  rw [schedPhi, schedPhi]
  exact min_le_min le_rfl (max_le_max le_rfl (by linarith))

lemma schedPhi_continuous : Continuous schedPhi :=
  continuous_const.min (continuous_const.max (by fun_prop))

lemma schedPhi_eq_zero_iff {x : ℝ} : schedPhi x = 0 ↔ x ≤ 1 / 2 := by
  rw [schedPhi]
  constructor
  · intro h
    have hy1 : max 0 (2 * x - 1) ≤ 1 := by
      by_contra hc
      have hc' : 1 ≤ max 0 (2 * x - 1) := le_of_lt (lt_of_not_ge hc)
      rw [min_eq_left hc'] at h
      norm_num at h
    have hy : max 0 (2 * x - 1) = 0 := by
      rw [min_eq_right hy1] at h
      exact h
    have : 2 * x - 1 ≤ 0 := le_trans (le_max_right _ _) (le_of_eq hy)
    linarith
  · intro h
    have h1 : max 0 (2 * x - 1) = 0 := max_eq_left (by linarith)
    rw [h1, min_eq_right (by norm_num : (0 : ℝ) ≤ 1)]

lemma schedPhi_eq_one_iff {x : ℝ} : schedPhi x = 1 ↔ 1 ≤ x := by
  rw [schedPhi]
  constructor
  · intro h
    have h1 : (1 : ℝ) ≤ max 0 (2 * x - 1) := by
      have h2 : min (1 : ℝ) (max 0 (2 * x - 1)) ≤ max 0 (2 * x - 1) := min_le_right _ _
      rw [h] at h2
      exact h2
    have h4 : (0 : ℝ) ≤ 2 * x - 1 := by
      by_contra hc
      have hc' : 2 * x - 1 ≤ 0 := le_of_lt (lt_of_not_ge hc)
      rw [max_eq_left hc'] at h1
      norm_num at h1
    rw [max_eq_right h4] at h1
    linarith
  · intro h
    have h1 : (1 : ℝ) ≤ max 0 (2 * x - 1) := le_max_of_le_right (by linarith)
    rw [min_eq_left h1]

/-! ## The zone identities -/

lemma schedDep_short {lay ρ δs : ℝ} {d : BandArcData} (D : SweepData d) {σ : ℝ}
    (hδs : 0 < δs) (hlay : 0 ≤ lay) (hW0 : 0 ≤ sweepW' D σ) (hc : schedC D σ ≤ δs / 2) :
    schedDep lay ρ δs D σ = lay * sweepW' D σ := by
  have h1 : schedC D σ / δs ≤ 1 / 2 := by
    rw [div_le_iff₀ hδs]; linarith
  rw [schedDep, schedPhi_eq_zero_iff.mpr h1, mul_zero, max_eq_left (mul_nonneg hlay hW0)]

lemma schedDep_deep {lay ρ δs : ℝ} {d : BandArcData} (D : SweepData d) {σ : ℝ}
    (hδs : 0 < δs) (hc : δs ≤ schedC D σ) :
    schedDep lay ρ δs D σ = max (lay * sweepW' D σ) ρ := by
  rw [schedDep]
  have h1 : 1 ≤ schedC D σ / δs := by rw [le_div_iff₀ hδs]; linarith
  rw [schedPhi_eq_one_iff.mpr h1, mul_one]

/-- **The trough**: if the chord is at most a quarter of a `period`-circle shorter than `δs` from
either end (`c ≤ δs/4`) both ramps vanish, so the loop is the ordinary chamfered loop with fraction
`lay`: the schedule is *constant* there. -/
lemma schedPsi_eq_zero_of_trough {d : BandArcData} (D : SweepData d) {δs σ : ℝ} (hδs : 0 < δs)
    (hc : schedC D σ ≤ δs / 4) : schedPsi D δs σ = 0 := by
  rw [schedPsi, schedPhi_eq_zero_iff]
  rw [div_le_iff₀ hδs]
  linarith

lemma schedBeta_trough {r : ℝ → Space} {lay ρ δs cQ : ℝ} {d : BandArcData} (D : SweepData d)
    {σ : ℝ} (hδs : 0 < δs) (hc : schedC D σ ≤ δs / 4) :
    schedBeta r lay ρ δs cQ D σ = lay := by
  simp only [schedBeta, schedPsi_eq_zero_of_trough D hδs hc]
  ring

lemma schedAlpha_trough {lay ρ δs : ℝ} {d : BandArcData} (D : SweepData d) {σ : ℝ}
    (hδs : 0 < δs) (hlay : 0 < lay) (hW : sweepW' D σ ≠ 0) (hW0 : 0 ≤ sweepW' D σ)
    (hc : schedC D σ ≤ δs / 4) :
    schedAlpha lay ρ δs D σ = lay := by
  have hc2 : schedC D σ ≤ δs / 2 := by linarith
  rw [schedAlpha, schedDep_short D hδs hlay.le hW0 hc2]
  exact mul_div_cancel_right₀ lay hW

/-- In the short zone the loop *is* the ordinary chamfered loop with fraction `lay`. -/
lemma chamferLoopGen_of_trough {r : ℝ → Space} {d : BandArcData} (D : SweepData d)
    {lay ρ δs cQ : ℝ} (hδs : 0 < δs) (hlay : 0 < lay) {σ : ℝ}
    (hW : sweepW' D σ ≠ 0) (hW0 : 0 ≤ sweepW' D σ) (hc : schedC D σ ≤ δs / 4) :
    chamferLoopGen r D lay (schedAlpha lay ρ δs D) (schedBeta r lay ρ δs cQ D) σ
      = sweepLoopChamfer r D lay σ :=
  chamferLoopGen_eq_chamfer_of_eq D (schedAlpha_trough D hδs hlay hW hW0 hc)
    (schedBeta_trough D hδs hc)

/-! ## Continuity of the schedules -/

lemma continuous_schedC {d : BandArcData} (D : SweepData d) : Continuous (schedC D) :=
  ((sweepLoopChamfer_sweepW'_continuous D).min
    (continuous_const.sub (sweepLoopChamfer_sweepW'_continuous D)))

lemma continuous_schedPsi {d : BandArcData} (D : SweepData d) {δs : ℝ} (hδs : δs ≠ 0) :
    Continuous (schedPsi D δs) :=
  schedPhi_continuous.comp (((continuous_const.mul (continuous_schedC D)).div_const δs))

lemma continuous_schedDep {d : BandArcData} (D : SweepData d) (lay ρ δs : ℝ) (hδs : δs ≠ 0) :
    Continuous (fun σ : ℝ => schedDep lay ρ δs D σ) :=
  ((continuous_const.mul (sweepLoopChamfer_sweepW'_continuous D)).max
    (continuous_const.mul (schedPhi_continuous.comp
      ((continuous_schedC D).div_const δs))))

lemma continuous_schedAlpha {d : BandArcData} (D : SweepData d) {lay ρ δs : ℝ}
    (hδs : δs ≠ 0) : ContinuousOn (fun σ : ℝ => schedAlpha lay ρ δs D σ)
      {σ | sweepW' D σ ≠ 0} :=
  (continuous_schedDep D lay ρ δs hδs).continuousOn.div
    (sweepLoopChamfer_sweepW'_continuous D).continuousOn (fun σ hσ => hσ)

lemma continuous_schedBeta {r : ℝ → Space} {d : BandArcData} (D : SweepData d)
    {lay ρ δs cQ : ℝ} (hδs : δs ≠ 0)
    {hσ0 : ∀ σ : ℝ, sweepW' D σ ≠ 0 → ‖r (tbR D σ) - r (taR D σ)‖ ≠ 0}
    (hr : Continuous r) :
    ContinuousOn (fun σ : ℝ => schedBeta r lay ρ δs cQ D σ)
      {σ | sweepW' D σ ≠ 0} := by
  have hL : Continuous (fun σ : ℝ => ‖r (tbR D σ) - r (taR D σ)‖) :=
    (((hr.comp (sweepLoopChamfer_tbR_continuous D)).sub
      (hr.comp (sweepLoopChamfer_taR_continuous D))).norm)
  have hnum : Continuous (fun σ : ℝ => cQ * schedDep lay ρ δs D σ) :=
    continuous_const.mul (continuous_schedDep D lay ρ δs hδs)
  have h1 : ContinuousOn (fun σ : ℝ => cQ * schedDep lay ρ δs D σ / ‖r (tbR D σ) - r (taR D σ)‖)
      {σ | sweepW' D σ ≠ 0} :=
    hnum.continuousOn.div hL.continuousOn (fun σ hσ => hσ0 σ hσ)
  have h2 : ContinuousOn (fun σ : ℝ =>
      min lay (cQ * schedDep lay ρ δs D σ / ‖r (tbR D σ) - r (taR D σ)‖))
      {σ | sweepW' D σ ≠ 0} := by
    have heq : (fun σ : ℝ =>
        min lay (cQ * schedDep lay ρ δs D σ / ‖r (tbR D σ) - r (taR D σ)‖))
        = fun σ : ℝ => (lay + (cQ * schedDep lay ρ δs D σ / ‖r (tbR D σ) - r (taR D σ)‖)
            - abs (lay - (cQ * schedDep lay ρ δs D σ / ‖r (tbR D σ) - r (taR D σ)‖))) / 2 := by
      funext σ
      rcases le_total lay (cQ * schedDep lay ρ δs D σ / ‖r (tbR D σ) - r (taR D σ)‖) with h | h
      · rw [min_eq_left h, abs_of_nonpos (by linarith)]
        ring
      · rw [min_eq_right h, abs_of_nonneg (by linarith)]
        ring
    rw [heq]
    exact ((continuousOn_const.add h1).sub (continuousOn_const.sub h1).abs).div_const 2
  have h3 : ContinuousOn (fun σ : ℝ =>
      (1 - schedPsi D δs σ) * lay
        + schedPsi D δs σ
          * min lay (cQ * schedDep lay ρ δs D σ / ‖r (tbR D σ) - r (taR D σ)‖))
      {σ | sweepW' D σ ≠ 0} :=
    ContinuousOn.add
      (ContinuousOn.mul (ContinuousOn.sub continuousOn_const
        (continuous_schedPsi D hδs).continuousOn) continuousOn_const)
      (ContinuousOn.mul (continuous_schedPsi D hδs).continuousOn h2)
  exact h3


/-! ## Transfer lemmas: the crosscut data ⟹ the hypotheses of `Lemma A`/`Lemma B`

The four clauses of `Work.Drive.bandArcData_sweepData_of_stripCrosscutOFatS` are stated with the
*chord endpoints* `D.ta s`, `D.tb s` and the *scales* `ρ`, `δs`; the two injectivity lemmas
(`chamferLoopGenInjOnBall` for the deep zones, `chamferLoopGenInjOnNt` for the short zones) want
them at the *cut depth* `dep = α σ * W_σ`.  The lemmas below are that conversion, plus the two
elementary length estimates the ball/disjointness conditions of `Lemma A` consume. -/

/-- **Middle-freeness at the cut depth, from the `ShortMid` clause.**  If the *whole* chord carries
no middle at all (`c ≤ δs` and `ShortMid`-avoidance), then the retained arc at any non-negative
depth is chord-free. -/
lemma hnoFat_of_short {r : ℝ → Space} {d : BandArcData} (D : SweepData d) {σ dep δs : ℝ}
    (hdep : 0 ≤ dep)
    (hshortmid : ∀ u : ℝ, taR D σ ≤ u → u ≤ tbR D σ →
      r u ∉ openSegment ℝ (r (taR D σ)) (r (tbR D σ))) :
    ∀ u : ℝ, taR D σ + dep ≤ u → u ≤ tbR D σ - dep →
      r u ∉ openSegment ℝ (r (taR D σ)) (r (tbR D σ)) :=
  fun u hu1 hu2 => hshortmid u (by linarith) (by linarith)

/-- **Middle-freeness at the cut depth, from the `OFatR` clause.**  If there is no middle of the
chord at parameter distance `≥ ρ` from both ends and `ρ ≤ dep`, then the retained arc at depth
`dep` is chord-free. -/
lemma hnoFat_of_deep {r : ℝ → Space} {d : BandArcData} (D : SweepData d) {σ dep ρ : ℝ}
    (hρdep : ρ ≤ dep)
    (hfatmid : ∀ u : ℝ, taR D σ + ρ ≤ u → u ≤ tbR D σ - ρ →
      r u ∉ openSegment ℝ (r (taR D σ)) (r (tbR D σ))) :
    ∀ u : ℝ, taR D σ + dep ≤ u → u ≤ tbR D σ - dep →
      r u ∉ openSegment ℝ (r (taR D σ)) (r (tbR D σ)) :=
  fun u hu1 hu2 => hfatmid u (by linarith) (by linarith)

/-- **A lower bound for the chord length from the far-parameter separation.**  If the circular
separation of the two endpoints is at least `ρ`, the chord is at least `s` long
(`s` = the separation constant of `Work.Drive.separation_of_far_parameters`). -/
lemma chord_length_ge_of_sep {r : ℝ → Space} (hr : IsSmoothKnot r) {ρ s : ℝ}
    (hsep : ∀ a b : KnotParam, ρ ≤ dist a b → s ≤ ‖knotMap r a - knotMap r b‖)
    {d : BandArcData} (D : SweepData d) {σ : ℝ}
    (hσ : ρ ≤ circSep (taR D σ) (tbR D σ)) :
    s ≤ ‖r (tbR D σ) - r (taR D σ)‖ := by
  have h1 : ρ ≤ dist ((taR D σ : ℝ) : KnotParam) ((tbR D σ : ℝ) : KnotParam) := by
    rw [← circSep]; exact hσ
  have h2 := hsep _ _ h1
  rw [knotMap_eq_r hr (taR D σ), knotMap_eq_r hr (tbR D σ), norm_sub_rev] at h2
  exact h2

/-- **The circular separation from a sub-interval condition** (the form in which the schedule's
`c_σ = min W (period - W)` produces it). -/
lemma circSep_ge_of_mem {x y ρ : ℝ} (hρ : 0 < ρ)
    (h1 : ρ ≤ y - x) (h2 : y - x ≤ period - ρ) : ρ ≤ circSep y x :=
  circSep_ge_of_sub_mem hρ h1 h2

end Work.Drive

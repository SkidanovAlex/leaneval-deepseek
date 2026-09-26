import Mathlib
import Submission.Work.Drive.chamferLoopGenDepth
import Submission.Work.Drive.chamferSchedule

/-!
# A *globally continuous* scheduled chamfer loop

The depth-parametrised loop `Work.Drive.chamferLoopGenD` of `chamferLoopGenDepth.lean` is jointly
continuous as soon as the two schedules (`dep` = the absolute cut depth, `b` = the chord target
fraction) are.  The depth `Work.Drive.schedDep` is globally continuous; the target
`Work.Drive.schedBeta` is the design's `β`, but it contains the quotient `dep / ‖r tb - r ta‖`,
which is degenerate at the two *seams* `σ = 0`, `σ = 1` of the sweep (there `ta` and `tb` differ by
a full `period`, so `r ta = r tb`).

This module replaces the target by the **denominator-clamped** schedule

`Work.Drive.schedBetaC r lay ρ δs cQ D χ σ
   = (1 - ψ σ) * lay + ψ σ * min lay (cQ * dep σ / max ‖r tb - r ta‖ χ)`

(`χ > 0` a uniform lower bound on the *non-degenerate* chords' lengths, i.e. the separation constant
`s` of `Work.Drive.separation_of_far_parameters`).  Two facts make this an honest replacement:

* `Work.Drive.continuous_schedBetaC` — it is globally continuous (the denominator is `≥ χ > 0`);
* `Work.Drive.schedBetaC_eq_schedBeta` — where the ramp `ψ` is *nonzero* the two expressions
  coincide (`ψ > 0` forces the circular chord length `c > δs/4 ≥ ρ`, hence `‖r tb - r ta‖ ≥ χ` by
  the far-parameter separation); where `ψ = 0` both reduce to `lay`.

Consequently `Γ := chamferLoopGenD r D lay schedDep (schedBetaC …)` is **globally continuous**
(`Work.Drive.continuous_chamferLoopGenCont`) and coincides with the design's loop
`chamferLoopGen r D lay schedAlpha schedBeta` on the whole window `σ ∈ (0, 1)`
(`Work.Drive.chamferLoopGenCont_eq`), which is where the per-slice injectivity of the design is
available.  This is what removes the "discontinuous at `σ = 0`" trap of the `S`-lane without
touching the design's own definitions.
-/

noncomputable section

set_option linter.unusedVariables false

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-- **The clamped chord-target schedule**: the design's `β` with the denominator bounded below by a
positive constant `χ`, so that it is globally continuous. -/
def schedBetaC (r : ℝ → Space) (lay ρ δs cQ χ : ℝ) {d : BandArcData} (D : SweepData d) (σ : ℝ) :
    ℝ :=
  (1 - schedPsi D δs σ) * lay
    + schedPsi D δs σ * min lay
        (cQ * schedDep lay ρ δs D σ / max (‖r (tbR D σ) - r (taR D σ)‖) χ)

/-- **The clamped target is globally continuous.** -/
theorem continuous_schedBetaC {r : ℝ → Space} {d : BandArcData} (D : SweepData d)
    {lay ρ δs cQ χ : ℝ} (hδs : δs ≠ 0) (hχ : 0 < χ) (hr : Continuous r) :
    Continuous (schedBetaC r lay ρ δs cQ χ D) := by
  have hL : Continuous (fun σ : ℝ => ‖r (tbR D σ) - r (taR D σ)‖) :=
    (((hr.comp (sweepLoopChamfer_tbR_continuous D)).sub
      (hr.comp (sweepLoopChamfer_taR_continuous D))).norm)
  have hden : Continuous (fun σ : ℝ => max (‖r (tbR D σ) - r (taR D σ)‖) χ) :=
    hL.max continuous_const
  have hdenne : ∀ σ : ℝ, max (‖r (tbR D σ) - r (taR D σ)‖) χ ≠ 0 := by
    intro σ h0
    have h1 : χ ≤ max (‖r (tbR D σ) - r (taR D σ)‖) χ := le_max_right _ _
    exact absurd h0 (ne_of_gt (lt_of_lt_of_le hχ h1))
  have hnum : Continuous (fun σ : ℝ => cQ * schedDep lay ρ δs D σ) :=
    continuous_const.mul (continuous_schedDep D lay ρ δs hδs)
  have h1 : Continuous (fun σ : ℝ =>
      cQ * schedDep lay ρ δs D σ / max (‖r (tbR D σ) - r (taR D σ)‖) χ) :=
    hnum.div hden hdenne
  have h2 : Continuous (fun σ : ℝ =>
      min lay (cQ * schedDep lay ρ δs D σ / max (‖r (tbR D σ) - r (taR D σ)‖) χ)) := by
    have heq : (fun σ : ℝ =>
        min lay (cQ * schedDep lay ρ δs D σ / max (‖r (tbR D σ) - r (taR D σ)‖) χ))
        = fun σ : ℝ => (lay + (cQ * schedDep lay ρ δs D σ
              / max (‖r (tbR D σ) - r (taR D σ)‖) χ)
            - abs (lay - (cQ * schedDep lay ρ δs D σ
              / max (‖r (tbR D σ) - r (taR D σ)‖) χ))) / 2 := by
      funext σ
      rcases le_total lay (cQ * schedDep lay ρ δs D σ
          / max (‖r (tbR D σ) - r (taR D σ)‖) χ) with h | h
      · rw [min_eq_left h, abs_of_nonpos (by linarith)]
        ring
      · rw [min_eq_right h, abs_of_nonneg (by linarith)]
        ring
    rw [heq]
    exact ((continuous_const.add h1).sub (continuous_const.sub h1).abs).div_const 2
  have h3 : Continuous (fun σ : ℝ =>
      (1 - schedPsi D δs σ) * lay
        + schedPsi D δs σ * min lay (cQ * schedDep lay ρ δs D σ
            / max (‖r (tbR D σ) - r (taR D σ)‖) χ)) :=
    Continuous.add
      (Continuous.mul (Continuous.sub continuous_const (continuous_schedPsi D hδs))
        continuous_const)
      (Continuous.mul (continuous_schedPsi D hδs) h2)
  exact h3

/-- **The clamped target is the design's target** as soon as the non-degenerate chords are longer
than `χ`: where `ψ = 0` both are `lay`, and where `ψ > 0` the clamped denominator is the true chord
length. -/
theorem schedBetaC_eq_schedBeta {r : ℝ → Space} {d : BandArcData} (D : SweepData d)
    {lay ρ δs cQ χ : ℝ}
    (hsep : ∀ σ : ℝ, 0 < schedPsi D δs σ →
      χ ≤ ‖r (tbR D σ) - r (taR D σ)‖) :
    schedBetaC r lay ρ δs cQ χ D = schedBeta r lay ρ δs cQ D := by
  funext σ
  by_cases hψ : schedPsi D δs σ = 0
  · rw [schedBetaC, schedBeta, hψ]
    ring
  · have hψpos : 0 < schedPsi D δs σ := lt_of_le_of_ne (schedPhi_nonneg _) (Ne.symm hψ)
    have hχL : χ ≤ ‖r (tbR D σ) - r (taR D σ)‖ := hsep σ hψpos
    rw [schedBetaC, schedBeta, max_eq_left hχL]

/-! ## The globally continuous scheduled loop -/

/-- **The globally continuous scheduled chamfer loop**: the depth-parametrised loop at the design's
absolute depth `schedDep` and the clamped target `schedBetaC`. -/
def chamferLoopGenCont (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (lay ρ δs cQ χ : ℝ)
    (s t : ℝ) : Space :=
  chamferLoopGenD r D lay (schedDep lay ρ δs D) (schedBetaC r lay ρ δs cQ χ D) s t

/-- **The continuous scheduled loop is jointly continuous.** -/
theorem continuous_chamferLoopGenCont {r : ℝ → Space} (hr : Continuous r) {d : BandArcData}
    (D : SweepData d) {lay ρ δs cQ χ : ℝ} (hlay0 : 0 < lay) (hlay1 : lay < 1 / 2)
    (hδs : δs ≠ 0) (hχ : 0 < χ) :
    Continuous (fun p : ℝ × ℝ => chamferLoopGenCont r D lay ρ δs cQ χ p.1 p.2) :=
  continuous_chamferLoopGenD hr D hlay0 hlay1 (continuous_schedDep D lay ρ δs hδs)
    (continuous_schedBetaC D hδs hχ hr)

/-- **The depth identity**: the design's fraction times the chord width is the absolute depth,
everywhere (at the seams both sides vanish). -/
lemma schedAlpha_mul_sweepW (lay ρ δs : ℝ) {d : BandArcData} (D : SweepData d) (s : ℝ) :
    schedAlpha lay ρ δs D s * sweepW' D s = schedDep lay ρ δs D s := by
  by_cases hW : sweepW' D s = 0
  · have hc : schedC D s = 0 := by
      rw [schedC, hW, sub_zero]; exact min_eq_left period_pos.le
    have hdep0 : schedDep lay ρ δs D s = 0 := by
      rw [schedDep, hW, hc, schedPhi]; norm_num
    rw [hdep0, schedAlpha, hdep0, hW]; norm_num
  · rw [schedAlpha, div_mul_cancel₀ _ hW]

/-- **The continuous scheduled loop is the design's loop** on `σ ∈ (0, 1)`. -/
theorem chamferLoopGenCont_eq {r : ℝ → Space} {d : BandArcData} (D : SweepData d)
    {lay ρ δs cQ χ : ℝ} (hχsep : ∀ σ : ℝ, 0 < schedPsi D δs σ →
      χ ≤ ‖r (tbR D σ) - r (taR D σ)‖)
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    chamferLoopGenCont r D lay ρ δs cQ χ σ
      = chamferLoopGen r D lay (schedAlpha lay ρ δs D) (schedBeta r lay ρ δs cQ D) σ := by
  show chamferLoopGenD r D lay (schedDep lay ρ δs D) (schedBetaC r lay ρ δs cQ χ D) σ
      = chamferLoopGen r D lay (schedAlpha lay ρ δs D) (schedBeta r lay ρ δs cQ D) σ
  rw [schedBetaC_eq_schedBeta D hχsep]
  have h := chamferLoopGenD_eq_chamferLoopGen (r := r) D (lay := lay)
    (dep := schedDep lay ρ δs D) (b := schedBeta r lay ρ δs cQ D)
    (a := schedAlpha lay ρ δs D) (b' := schedBeta r lay ρ δs cQ D)
    (fun s => schedAlpha_mul_sweepW lay ρ δs D s) (fun s => rfl)
  exact congrFun h σ

/-! ## Relating the clamped denominator to the chord length -/

/-- The circular chord length `schedC` is at most the circular separation of the two chord
endpoints. -/
private lemma circSep_comm' (x y : ℝ) : circSep x y = circSep y x := by
  rw [circSep, circSep, dist_comm]

lemma schedC_le_circSep {d : BandArcData} (D : SweepData d) (σ : ℝ) :
    schedC D σ ≤ circSep (tbR D σ) (taR D σ) := by
  rcases lt_or_ge 0 (schedC D σ) with h | h
  · have hWpos : 0 < sweepW' D σ := by
      rw [schedC] at h
      exact lt_of_lt_of_le h (min_le_left (sweepW' D σ) (period - sweepW' D σ))
    have h1 : schedC D σ ≤ sweepW' D σ := by
      rw [schedC]; exact min_le_left (sweepW' D σ) (period - sweepW' D σ)
    have h2 : schedC D σ ≤ period - sweepW' D σ := by
      rw [schedC]; exact min_le_right (sweepW' D σ) (period - sweepW' D σ)
    refine circSep_ge_of_sub_mem (x := taR D σ) (u := tbR D σ) h ?_ ?_
    · simp only [sweepW'] at h1; linarith
    · simp only [sweepW'] at h2; linarith
  · rw [circSep]; exact le_trans h dist_nonneg

/-- **The separation constant bounds every chord whose ramp `ψ` is nonzero.**  A nonzero ramp forces
the circular chord length above `δs/4 ≥ ρ`, hence the two endpoints are `≥ ρ` apart on the parameter
circle, and the far-parameter separation gives the bound on the Euclidean chord. -/
lemma schedPsi_pos_chord_bound {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : SweepData d) {ρ δs s : ℝ} (hδs : 0 < δs) (hρδs : ρ ≤ δs / 4)
    (hsep : ∀ a b : KnotParam, ρ ≤ dist a b →
      s ≤ ‖knotMap r a - knotMap r b‖) :
    ∀ σ : ℝ, 0 < schedPsi D δs σ → s ≤ ‖r (tbR D σ) - r (taR D σ)‖ := by
  intro σ hψ
  have hx : 1 / 2 < 2 * schedC D σ / δs := by
    by_contra hcon
    push_neg at hcon
    have h0 : schedPsi D δs σ = 0 := by
      rw [schedPsi, schedPhi_eq_zero_iff]; linarith
    exact absurd h0 (ne_of_gt hψ)
  have hc : δs / 4 < schedC D σ := by
    rw [lt_div_iff₀ hδs] at hx
    linarith
  have hρc : ρ < circSep (taR D σ) (tbR D σ) := by
    rw [circSep_comm']
    exact lt_of_le_of_lt hρδs (lt_of_lt_of_le hc (schedC_le_circSep D σ))
  exact chord_length_ge_of_sep hr hsep D hρc.le

end Work.Drive

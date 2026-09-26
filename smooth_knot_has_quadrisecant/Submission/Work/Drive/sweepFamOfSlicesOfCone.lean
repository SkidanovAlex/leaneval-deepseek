import Mathlib
import Submission.Work.Drive.uniformCone_of_localCone
import Submission.Work.Drive.sweepFamOf_cone
import Submission.Work.Drive.velocity_ne_zero_of_secant_growth
import Submission.Work.Drive.farSep_real_of_Ico
import Submission.Work.Drive.sweepFamOf_slices_of_cone
import Submission.Work.Drive.sweepFamOf
import Submission.Work.Drive.chordSweepDefs

/-!
# The abstract blur package for a scheduled loop: cone ⇒ slices clause

This module is the **package** of the blur layer of
`Submission/Work/Drive/NOTES_LEAD_scheduledBlur.md` §2–§3 (lane H2): the five pieces

* `Work.Drive.uniformCone_of_localCone` — a *pointwise* local cone on the compact box
  `[a,b] × [0,period]` can be made uniform in the rate (`∃ ε c > 0` with the direction still
  depending on the point);
* `Work.Drive.sweepFamOf_cone` — the *double bump-blur* `Work.Drive.sweepFamOf Γ δ₁ δ₂ σ` of a
  continuous cone-loop inherits the same cone (same direction, same rate) on the shrunken
  `t`-window, as soon as `δ₂ ≤ ε`;
* `Work.Drive.velocity_ne_zero_of_secant_growth` — a one-sided forward-secant growth rate forces
  the velocity to be non-zero;
* `Work.Drive.farSep_real_of_Ico` — far separation on `Ico 0 period` extends to all real pairs for a
  `period`-periodic family;
* `Work.Drive.sweepFamOf_slices_of_cone` — **the assembly**: a uniform cone plus the injectivity of
  the *raw* loop gives, for all small widths, the injectivity of every blurred slice on one period
  and the non-vanishing of its velocity.

Nothing here is knot-geometric: `Γ` is an arbitrary continuous `period`-periodic loop family.  The
geometric content is isolated in the two *interface* hypotheses of the consumer

  `Work.Drive.sweepFamOf_slices_of_localCone` (this file),

namely the pointwise local cone `hloc` (for the scheduled chamfer loop
`Work.Drive.chamferLoopGen r D lay (schedAlpha …) (schedBeta …)` this is
`chamferLoopGen_localCone`, whose content is `ChamferJunctionOK`) and the injectivity `hinj` of the
**raw** loop on the window.  That is exactly the interface consumed by the top end of the chord
sweep (`sweepToNeedleStrictNT_gen`-shaped statements): the widths `δ₁, δ₂` are *chosen by* the
consumer, so this statement supplies them after the geometric data are fixed.

The `σ`-regularity of a *scheduled* loop is not available (`Work.Drive.SweepData` lifts are only
continuous), which is why the closeness of the blur is obtained by uniform continuity on the compact
window (`Work.Drive.sweepFamOf_close_uc`) rather than by a Lipschitz constant in `σ`.
-/

noncomputable section

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-- **The slices clause from a pointwise local cone.**  Let `Γ` be a jointly continuous,
`period`-periodic loop family, `M`-Lipschitz in the loop parameter, whose raw slices on the compact
window `[a,b] ⊂ (0,1)` are injective on one period, and suppose that at every `(σ₀, t₀)` of the box
`[a,b] × [0,period]` there is a direction `n` and a cone of radius `ε,` rate `c > 0` for the loops
`Γ s`, `s ∈ [σ₀-ε, σ₀+ε]`.  Then there is `L > 0` such that for all widths `0 < δ₁, δ₂ ≤ L` every
slice of the double bump-blur is injective on one period and has nowhere-vanishing velocity.

This is the composition of `Work.Drive.uniformCone_of_localCone` (compactness: a single `ε`, `c`
suffices) with `Work.Drive.sweepFamOf_slices_of_cone` (the blur assembly). -/
theorem sweepFamOf_slices_of_localCone {Γ : ℝ → ℝ → Space}
    (hΓ : Continuous (fun p : ℝ × ℝ => Γ p.1 p.2))
    (hper : ∀ s t : ℝ, Γ s (t + period) = Γ s t) {M : ℝ} (hMnn : 0 ≤ M)
    (hM : ∀ s t₁ t₂ : ℝ, ‖Γ s t₁ - Γ s t₂‖ ≤ M * |t₂ - t₁|)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (hinj : ∀ s ∈ Set.Icc a b, Set.InjOn (Γ s) (Set.Ico (0 : ℝ) period))
    (hloc : ∀ σ₀ ∈ Set.Icc a b, ∀ t₀ ∈ Set.Icc (0 : ℝ) period,
      ∃ (n : Space) (ε c : ℝ), 0 < ε ∧ 0 < c ∧
        ∀ s ∈ Set.Icc (σ₀ - ε) (σ₀ + ε), ∀ t₁ t₂ : ℝ, t₀ - ε ≤ t₁ → t₁ ≤ t₂ → t₂ ≤ t₀ + ε →
          c * (t₂ - t₁) ≤ inner ℝ n (Γ s t₂ - Γ s t₁)) :
    ∃ L : ℝ, 0 < L ∧ ∀ δ₁ δ₂ : ℝ, 0 < δ₁ → δ₁ ≤ L → 0 < δ₂ → δ₂ ≤ L → ∀ σ ∈ Set.Icc a b,
      Set.InjOn (fun t : ℝ => sweepFamOf Γ δ₁ δ₂ σ t) (Set.Ico (0 : ℝ) period) ∧
      ∀ t : ℝ, velocity (fun t : ℝ => sweepFamOf Γ δ₁ δ₂ σ t) t ≠ 0 := by
  obtain ⟨ε, c, hε, hc, hcone⟩ := uniformCone_of_localCone hper hab.le hloc
  exact sweepFamOf_slices_of_cone hΓ hper hMnn hM ha hab hb hinj hε hc hcone

/-- **The same, with the width budget of the clamped window.**  The consumers of the slices clause
for a *scheduled* loop (`chamferLoopGen_blurSlices` of `NOTES_LEAD_scheduledBlur.md` §3) need the
width budget `L ≤ a/2`, `L ≤ (1-b)/2` so that the `σ`-blur window `[σ-δ₂, σ+δ₂]` of a point
`σ ∈ [a,b]` stays inside the clamped window `[a/2, (1+b)/2]` on which the schedule is regular.  Since
`L` is existential this is just a shrinking of the `L` of `sweepFamOf_slices_of_localCone`. -/
theorem sweepFamOf_slices_of_localCone_window {Γ : ℝ → ℝ → Space}
    (hΓ : Continuous (fun p : ℝ × ℝ => Γ p.1 p.2))
    (hper : ∀ s t : ℝ, Γ s (t + period) = Γ s t) {M : ℝ} (hMnn : 0 ≤ M)
    (hM : ∀ s t₁ t₂ : ℝ, ‖Γ s t₁ - Γ s t₂‖ ≤ M * |t₂ - t₁|)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (hinj : ∀ s ∈ Set.Icc a b, Set.InjOn (Γ s) (Set.Ico (0 : ℝ) period))
    (hloc : ∀ σ₀ ∈ Set.Icc a b, ∀ t₀ ∈ Set.Icc (0 : ℝ) period,
      ∃ (n : Space) (ε c : ℝ), 0 < ε ∧ 0 < c ∧
        ∀ s ∈ Set.Icc (σ₀ - ε) (σ₀ + ε), ∀ t₁ t₂ : ℝ, t₀ - ε ≤ t₁ → t₁ ≤ t₂ → t₂ ≤ t₀ + ε →
          c * (t₂ - t₁) ≤ inner ℝ n (Γ s t₂ - Γ s t₁)) :
    ∃ L : ℝ, 0 < L ∧ L ≤ a / 2 ∧ L ≤ (1 - b) / 2 ∧
      ∀ δ₁ δ₂ : ℝ, 0 < δ₁ → δ₁ ≤ L → 0 < δ₂ → δ₂ ≤ L → ∀ σ ∈ Set.Icc a b,
        Set.InjOn (fun t : ℝ => sweepFamOf Γ δ₁ δ₂ σ t) (Set.Ico (0 : ℝ) period) ∧
        ∀ t : ℝ, velocity (fun t : ℝ => sweepFamOf Γ δ₁ δ₂ σ t) t ≠ 0 := by
  obtain ⟨L, hL, hmain⟩ := sweepFamOf_slices_of_localCone hΓ hper hMnn hM ha hab hb hinj hloc
  refine ⟨min L (min (a / 2) ((1 - b) / 2)), lt_min hL (lt_min (by linarith) (by linarith)),
    (min_le_right _ _).trans (min_le_left _ _),
    (min_le_right _ _).trans (min_le_right _ _), ?_⟩
  intro δ₁ δ₂ h1 h2 h3 h4 σ hσ
  exact hmain δ₁ δ₂ h1 (le_trans h2 (min_le_left _ _)) h3 (le_trans h4 (min_le_left _ _)) σ hσ

end Work.Drive

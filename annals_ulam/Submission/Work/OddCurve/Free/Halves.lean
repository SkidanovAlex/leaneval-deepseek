import Submission.Work.OddCurve.Free.Reduction
import Submission.Work.OddCurve.LowSlope.Extension
import Submission.Work.OddCurve.Strong
import Submission.Work.OddVolterra.Existence.curve_data_three_defs

/-!
# The two halves of the corrected (free-tip) odd chord curve

`Work.OddCurve.LowSlope.Extension` splits the odd chord curve into the paper's two steps,

* `AnchorWindow n` — Step 2: from a small flat bump produce the *anchor* curve `(X,Y)`, an
  envelope curve satisfying the two moment equations on the transition slopes `1-3τ < s ≤ 1`;
* `LowSlopeExtension n` — Step 3: from the anchor produce a curve satisfying them on **all**
  slopes `0 < s ≤ 1`.

Both are stated there with `Work.OddEnvelope.IsEnvelopeCurve` in the conclusion, whose fields
`x_tendsto_one`, `y_tendsto_one` require the two **tips** of the final body to be at
`(±1, 0, …, 0)`.  The paper's Step 3 does *not* produce tips at `±1`: the tips are the values at
`±e₁` of the inverse spherical Radon transform of the glued datum, which is a *determined*
functional of the bump — see `Submission/Work/OddCurve/NOTES_SESSION5.md`, the rigidity lemmas
`Work.OddCurve.LowSlope.datum_ball_of_section_ball` and
`Work.OddCurve.LowSlope.anchor_agreement_forced` (both proved), and the paper itself
(`paper_src/W3.tex`, end of the odd case: the profile is defined on `[-r(0), R(0)]` and is only
*close to* the semicircle).  So Step 3 must be stated in the corrected interface
`Work.OddCurve.Free.IsEnvelopeCurveFree` — the same structure with the tip normalisation replaced
by "the curve has *some* positive limit at `0⁺`".

This file assembles the corrected chain at the bump class `IsSmallFlatBumpThree n` (`C^{n+3}`
smallness), which is the class in which the construction actually runs and in which the proved
Step 2 lives (`Work.OddVolterra.Existence.WindowSolutionThree`); the C²-class statements of the
literal request are *weaker* in their hypotheses, but the construction cannot be run at `C²` (the
curve's second derivative sees `h^{(n+3)}`).  The lemmas
`SmallSlopeCurveExistsFreeThree_of_smallSlopeCurveExistsFree`,
`OddCurveExistsFreeThree_of_oddCurveExistsFree` record that the corrected statements follow from
the C²-class ones, so nothing is lost by moving to the higher class.

## Contents

* `AnchorWindowFree` — Step 2, as an alias of the interface
  `Work.OddVolterra.Existence.AnchorWindowThree`;
* `LowSlopeExtensionFree` — Step 3 with free tips (**the single remaining input**);
* `SmallSlopeCurveExistsFreeThree`, `OddCurveExistsFreeThree` — the corrected transition-slope
  curve and the corrected deliverable, and their assembly
  (`smallSlopeCurveExistsFreeThree_of_halves`, `oddCurveExistsFreeThree_of_halves`);
* `odd_curve_exists_free_written_three` — the corrected deliverable written out textually, in the
  shape of the request with `IsEnvelopeCurve` replaced by `IsEnvelopeCurveFree` and the bump class
  `C^{n+3}` (so that `Submission.Odd.BumpData.exists_odd_bump (n+3) ε` instantiates it);
* `lowSlopeExtensionFree_of_lowSlopeExtension` — the tip-normalised Step 3 (at the C^{n+2} class)
  implies the free-tip one, so no proved result is lost by this relaxation.
-/


/-!
## Caveat: the truncated profile

`Work.OddEnvelope.envelopeProfile` is defined to be `0` outside `[-1, 1]`; for a *free-tip* curve
(whose body has tips at `±ρ(±1)`, `ρ(±1) ≠ 1`) the profile of the body is the **untruncated**
profile `Work.OddVolterra.Free.envProfileFree` (`Submission/Work/OddVolterra/Free/Defs.lean`) —
the two agree on `|t| < 1` (`envProfileFree_eq_envelopeProfile`).  Statements in this file that
mention `envelopeProfile` are therefore the *tip-normalised* ones (correct only when the tips are
`±1`, i.e. `R₁ = R₂ = 1`); the free-tip statements in terms of `envProfileFree` are the sibling's
(`Submission/Work/OddCurveB/FreeTip.lean`, `Submission/Work/OddVolterra/Free/Defs.lean`, which
records `LowSlopeThreeFree`).  The general-interval endgame of this chapter
(`Submission/Work/OddCurve/Free/Endgame.lean`) takes the profile as an explicit hypothesis, so it
is agnostic to this distinction.
-/

namespace Work.OddCurve
namespace Free

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Pointwise Interval

/-- **The transition-window half (paper Step 2), in the free-tip chain.**  This is literally
`Work.OddVolterra.Existence.AnchorWindowThree`: the anchor's curve *is* the semicircle's near
`s = 0` (its low-slope part is chosen, not determined), so its tips are at `±1` and the
tip-normalised interface is correct for the anchor.  Only Step 3 needs the relaxation. -/
def AnchorWindowFree (n : ℕ) : Prop := Work.OddVolterra.Existence.AnchorWindowThree n

theorem anchorWindowFree_of_anchorWindowThree {n : ℕ}
    (H : Work.OddVolterra.Existence.AnchorWindowThree n) : AnchorWindowFree n := H

theorem anchorWindowThree_of_anchorWindowFree {n : ℕ}
    (H : AnchorWindowFree n) : Work.OddVolterra.Existence.AnchorWindowThree n := H

/-- **The low-slope half of the odd construction (paper Step 3), with free tips.**  The same
statement as `Work.OddCurve.LowSlope.LowSlopeExtension`, except that the conclusion is the
free-tip envelope structure `IsEnvelopeCurveFree` instead of `IsEnvelopeCurve` — i.e. the tips of
the reconstructed body are *not* required to be at `(±1, 0, …, 0)`, which is exactly what the
paper's glued-datum construction gives. -/
def LowSlopeExtensionFree (n : ℕ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ h X Y : ℝ → ℝ, Work.OddVolterra.Existence.IsSmallFlatBumpThree n ε h →
    Work.OddEnvelope.IsEnvelopeCurve h X Y → LowSlope.CloseToProfileX X →
    LowSlope.CloseToProfileX Y →
    (∀ s : ℝ, 1 - 3 * tau < s → s ≤ 1 →
      Work.OddCurve.momentA n h X Y (Work.OddEnvelope.envelopeProfile h X Y) s =
        refConst n / Real.sqrt (1 + s ^ 2)) →
    (∀ s : ℝ, 1 - 3 * tau < s → s ≤ 1 →
      Work.OddCurve.momentB n h X Y (Work.OddEnvelope.envelopeProfile h X Y) s = 0) →
    ∃ x y : ℝ → ℝ,
      (∀ s : ℝ, 1 - 3 * tau ≤ s → x s = X s ∧ y s = Y s) ∧
        IsEnvelopeCurveFree h x y ∧
        LowSlope.CloseToProfileX x ∧ LowSlope.CloseToProfileX y ∧
        (∀ s : ℝ, 0 < s → s ≤ 1 →
          Work.OddCurve.momentA n h x y (Work.OddEnvelope.envelopeProfile h x y) s =
            refConst n / Real.sqrt (1 + s ^ 2)) ∧
        (∀ s : ℝ, 0 < s → s ≤ 1 →
          Work.OddCurve.momentB n h x y (Work.OddEnvelope.envelopeProfile h x y) s = 0)

/-- The `C^{n+3}` class is contained in the `C^{n+2}` class
`Work.OddCurve.IsSmallFlatBumpStrong`. -/
theorem isSmallFlatBumpStrong_of_three {n : ℕ} {ε : ℝ} {h : ℝ → ℝ}
    (hb : Work.OddVolterra.Existence.IsSmallFlatBumpThree n ε h) :
    IsSmallFlatBumpStrong n ε h :=
  ⟨hb.1, hb.2.1, fun k hk s => hb.2.2.1 k (by omega) s, hb.2.2.2⟩

/-- To the right of the window the bump vanishes: the support is contained in
`Ioo (1-2τ) (1-τ)`. -/
theorem isSmallFlatBumpThree_eventuallyEq_zero_of_gt {n : ℕ} {ε : ℝ} {h : ℝ → ℝ}
    (hb : Work.OddVolterra.Existence.IsSmallFlatBumpThree n ε h) {s : ℝ}
    (hs : 1 - Work.OddVolterra.tau < s) : h =ᶠ[𝓝 s] (fun _ : ℝ => 0) := by
  filter_upwards [isOpen_Ioi.mem_nhds (show (1 - Work.OddVolterra.tau) < s from hs)]
    with t ht
  by_contra hne
  exact absurd (hb.2.1 (Function.mem_support.mpr hne)).2 (not_lt.mpr ht.le)

/-- **The tip-normalised Step 3 implies the free-tip one.**  `Work.OddCurve.LowSlope.LowSlopeExtension`
is stated at the (larger) `C^{n+2}` bump class; its conclusion implies the free-tip one, so a
proof of it loses nothing. -/
theorem lowSlopeExtensionFree_of_lowSlopeExtension (n : ℕ)
    (H : LowSlope.LowSlopeExtension n) : LowSlopeExtensionFree n := by
  obtain ⟨ε, hε, H'⟩ := H
  refine ⟨ε, hε, fun h X Y hb hX hcX hcY hA hB => ?_⟩
  obtain ⟨x, y, hagree, hIC, hcx, hcy, hma, hmb⟩ :=
    H' h X Y (isSmallFlatBumpStrong_of_three hb) hX hcX hcY hA hB
  exact ⟨x, y, hagree, isEnvelopeCurveFree_of_isEnvelopeCurve hIC, hcx, hcy, hma, hmb⟩

/-- The free-tip transition-slope curve, at the bump class of the construction. -/
def SmallSlopeCurveExistsFreeThree (n : ℕ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ h : ℝ → ℝ, Work.OddVolterra.Existence.IsSmallFlatBumpThree n ε h →
    h ≠ 0 → ∃ x y : ℝ → ℝ, IsEnvelopeCurveFree h x y ∧ SmallSlopeEqs n h x y

/-- **The two halves give the corrected transition-slope curve.** -/
theorem smallSlopeCurveExistsFreeThree_of_halves (n : ℕ) (hn : 1 ≤ n)
    (ha : AnchorWindowFree n) (he : LowSlopeExtensionFree n) :
    SmallSlopeCurveExistsFreeThree n := by
  obtain ⟨ε₁, hε₁, ha⟩ := ha
  obtain ⟨ε₂, hε₂, he⟩ := he
  have hτ : (0 : ℝ) < tau := by norm_num [Work.OddCurve.tau]
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun h hb hne => ?_⟩
  have hb₁ : Work.OddVolterra.Existence.IsSmallFlatBumpThree n ε₁ h :=
    ⟨hb.1, hb.2.1, fun k hk s => le_trans (hb.2.2.1 k hk s) (min_le_left _ _), hb.2.2.2⟩
  have hb₂ : Work.OddVolterra.Existence.IsSmallFlatBumpThree n ε₂ h :=
    ⟨hb.1, hb.2.1, fun k hk s => le_trans (hb.2.2.1 k hk s) (min_le_right _ _), hb.2.2.2⟩
  obtain ⟨X, Y, hX, hcX, hcY, hma, hmb⟩ := ha h hb₁ hne
  obtain ⟨x, y, _, hx, hxc, hyc, hmA, hmB⟩ := he h X Y hb₂ hX hcX hcY hma hmb
  refine ⟨x, y, hx, fun s hs => ?_, fun s hs => ?_⟩
  · obtain ⟨hs0, hs1⟩ := hs
    exact hmA s hs0 (by linarith)
  · obtain ⟨hs0, hs1⟩ := hs
    exact hmB s hs0 (by linarith)

/-- **The corrected deliverable** (`d = 2n+1`, `n ≥ 1`): for every sufficiently small flat bump
(in the construction's regularity class `C^{n+3}`) there is a chord curve with the free-tip
envelope structure and the two moment equations on `(0,1]`. -/
def OddCurveExistsFreeThree (n : ℕ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ h : ℝ → ℝ, Work.OddVolterra.Existence.IsSmallFlatBumpThree n ε h →
    h ≠ 0 → ∃ C : ℝ, ∃ x y : ℝ → ℝ, IsOddCurveFree n C h x y

/-- The corrected transition-slope curve gives the corrected deliverable, using the free-tip
tail `Work.OddCurve.Free.momentEqsOn_Ioc_one_of_smallSlopes_free`. -/
theorem oddCurveExistsFreeThree_of_smallSlopeCurveExistsFreeThree (n : ℕ)
    (H : SmallSlopeCurveExistsFreeThree n) : OddCurveExistsFreeThree n := by
  obtain ⟨ε, hε, H'⟩ := H
  refine ⟨ε, hε, fun h hb hne => ?_⟩
  obtain ⟨x, y, hIC, hsl⟩ := H' h hb hne
  exact ⟨refConst n, x, y, hIC,
    momentEqsOn_Ioc_one_of_smallSlopes_free n hIC
      (fun s hs => isSmallFlatBumpThree_eventuallyEq_zero_of_gt hb hs) hsl⟩

/-- **The two halves give the corrected deliverable.** -/
theorem oddCurveExistsFreeThree_of_halves (n : ℕ) (hn : 1 ≤ n)
    (ha : AnchorWindowFree n) (he : LowSlopeExtensionFree n) :
    OddCurveExistsFreeThree n :=
  oddCurveExistsFreeThree_of_smallSlopeCurveExistsFreeThree n
    (smallSlopeCurveExistsFreeThree_of_halves n hn ha he)

/-- The C²-class free-tip transition-slope statement of the literal request implies the
`C^{n+3}`-class one (the class is larger, so the statement is stronger). -/
theorem smallSlopeCurveExistsFreeThree_of_smallSlopeCurveExistsFree (n : ℕ) :
    SmallSlopeCurveExistsFree n → SmallSlopeCurveExistsFreeThree n := by
  intro H
  obtain ⟨ε, hε, H'⟩ := H
  refine ⟨min ε (1 / 100), lt_min hε (by norm_num), fun h hb hne => ?_⟩
  have hbC2 : IsSmallFlatBump ε h :=
    ⟨hb.1, hb.2.1,
      fun s => le_trans (hb.2.2.1 0 (by omega) s) (min_le_left _ _),
      fun s => by
        rw [← iteratedDeriv_one (f := h)]
        exact le_trans (hb.2.2.1 1 (by omega) s) (min_le_left _ _),
      fun s => by
        have h2 : iteratedDeriv 2 h s = deriv (deriv h) s := by
          rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]
        rw [← h2]
        exact le_trans (hb.2.2.1 2 (by omega) s) (min_le_left _ _),
      hb.2.2.2⟩
  exact H' h hbC2 hne

/-- The C²-class corrected deliverable of the literal request implies the `C^{n+3}`-class one. -/
theorem oddCurveExistsFreeThree_of_oddCurveExistsFree (n : ℕ) :
    OddCurveExistsFree n → OddCurveExistsFreeThree n := by
  intro H
  obtain ⟨ε, hε, H'⟩ := H
  refine ⟨min ε (1 / 100), lt_min hε (by norm_num), fun h hb hne => ?_⟩
  have hbC2 : IsSmallFlatBump ε h :=
    ⟨hb.1, hb.2.1,
      fun s => le_trans (hb.2.2.1 0 (by omega) s) (min_le_left _ _),
      fun s => by
        rw [← iteratedDeriv_one (f := h)]
        exact le_trans (hb.2.2.1 1 (by omega) s) (min_le_left _ _),
      fun s => by
        have h2 : iteratedDeriv 2 h s = deriv (deriv h) s := by
          rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]
        rw [← h2]
        exact le_trans (hb.2.2.1 2 (by omega) s) (min_le_left _ _),
      hb.2.2.2⟩
  exact H' h hbC2 hne

/-- **The corrected deliverable, written out textually** in the shape of the request, with
`IsEnvelopeCurve` replaced by `IsEnvelopeCurveFree` and the bump class `C^{n+3}` of the
construction (so that the bump `Submission.Odd.BumpData.exists_odd_bump (n+3) ε` instantiates it). -/
theorem odd_curve_exists_free_written_three (n : ℕ) (hn : 1 ≤ n)
    (H : OddCurveExistsFreeThree n) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ h : ℝ → ℝ,
      ContDiff ℝ ∞ h →
      Function.support h ⊆ Set.Ioo (1 - 2 * (1 / 10)) (1 - (1 / 10)) →
      (∀ k : ℕ, k ≤ n + 3 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ ε) →
      (∃ η : ℝ, 0 < η ∧ ∀ s : ℝ, 1 - 2 * (1 / 10) ≤ s →
        s < 1 - 2 * (1 / 10) + η → h s = 0) →
      h ≠ 0 →
      ∃ C : ℝ, ∃ x y : ℝ → ℝ,
        IsEnvelopeCurveFree h x y ∧
        (∀ s : ℝ, 0 < s → s ≤ 1 →
          (∫ t in (-x s)..(y s),
            (Work.OddEnvelope.envelopeProfile h x y t ^ 2 - (s * t + h s) ^ 2) ^ n *
              Real.sqrt (Work.OddEnvelope.envelopeProfile h x y t ^ 2 -
                (s * t + h s) ^ 2)) =
            C / Real.sqrt (1 + s ^ 2)) ∧
        (∀ s : ℝ, 0 < s → s ≤ 1 →
          (∫ t in (-x s)..(y s),
            (Work.OddEnvelope.envelopeProfile h x y t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) *
              Real.sqrt (Work.OddEnvelope.envelopeProfile h x y t ^ 2 -
                (s * t + h s) ^ 2) *
              (t + deriv h s)) = 0) := by
  obtain ⟨ε, hε, H'⟩ := H
  refine ⟨ε, hε, fun h hcont hsupp hbnd hflat hne => ?_⟩
  have hsuppIcc : Function.support h ⊆ Set.Icc (1 - 2 * (1 / 10)) (1 - (1 / 10)) :=
    fun t ht => ⟨(hsupp ht).1.le, (hsupp ht).2.le⟩
  have hsuppIoo : Function.support h ⊆
      Set.Ioo (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau) := by
    intro t ht
    have h := hsupp ht
    simpa [Work.OddVolterra.tau] using h
  have hflat' : ∃ η : ℝ, 0 < η ∧ ∀ s : ℝ, 1 - 2 * Work.OddVolterra.tau ≤ s →
      s < 1 - 2 * Work.OddVolterra.tau + η → h s = 0 := by
    obtain ⟨η, hη, hf⟩ := hflat
    exact ⟨η, hη, fun s hs hs' => hf s (by simpa [Work.OddVolterra.tau] using hs)
      (by simpa [Work.OddVolterra.tau] using hs')⟩
  have hb : Work.OddVolterra.Existence.IsSmallFlatBumpThree n ε h :=
    ⟨hcont, hsuppIoo, hbnd, hflat'⟩
  obtain ⟨C, x, y, hfr, hme⟩ := H' h hb hne
  obtain ⟨hA, hB⟩ :=
    (momentEqsOn_Ioc_iff n C h x y (Work.OddEnvelope.envelopeProfile h x y)).mp hme
  exact ⟨C, x, y, hfr, hA, hB⟩

end

end Free
end Work.OddCurve

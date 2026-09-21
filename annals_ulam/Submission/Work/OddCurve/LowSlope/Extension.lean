import Mathlib
import Submission.Work.OddCurve.LowSlope.reduction
import Submission.Work.OddCurve.Strong

/-!
# The two halves of the odd chord curve, as interfaces

The construction of the chord curve of the odd case (`d = 2n+1`) splits into the paper's two steps:

* **`AnchorWindow n`** — Step 2: for a sufficiently small flat bump there is an envelope curve,
  `C²`-close to the semicircle's, satisfying both moment equations on the *transition* slopes
  `1 - 3τ < s ≤ 1`.  This is the Volterra/Abel construction (`Work.OddVolterra`, exposed in this
  workspace as `Work.OddVolterra.Existence.curve_anchor_exists`).
* **`LowSlopeExtension n`** — Step 3: from such a curve one produces a curve agreeing with it on
  `s ≥ 1 - 3τ` and satisfying both moment equations on *all* slopes `0 < s ≤ 1`.  This is the
  spherical-Radon construction (see `LowSlope/README.md`, and the isolated crux
  `Work.OddCurve.LowSlope.radon_data_eq_inertiaIntegral`).

The theorem `smallSlopeCurveExistsStrong_of_halves` assembles the two into the deliverable's
transition-slope statement `Work.OddCurve.SmallSlopeCurveExistsStrong`; no tail machinery is
needed, since `(0, 1-3τ] ∪ (1-3τ, 1] = (0,1]` already covers the slopes `0 < s ≤ 1 - τ` asked for
there, and the semicircular tail `[1-τ, 1]` is handled downstream by
`Work.OddCurve.momentEqsOn_Ioc_one_of_smallSlopes`.
-/

namespace Work.OddCurve.LowSlope

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

/-- The `C²`-closeness of a chord function to the semicircle's `profileX`. -/
def CloseToProfileX (x : ℝ → ℝ) : Prop :=
  ∀ s : ℝ, 0 < s →
    |x s - Work.OddEnvelope.profileX s| ≤ 1 / 100 ∧
      |deriv x s - deriv Work.OddEnvelope.profileX s| ≤ 1 / 100 ∧
      |deriv (deriv x) s - deriv (deriv Work.OddEnvelope.profileX) s| ≤ 1 / 100

/-- **The transition-window part of the odd construction** (paper Step 2): for every sufficiently
small flat bump there is an envelope curve, `C²`-close to the semicircle's, satisfying both moment
equations on the slopes `1 - 3τ < s ≤ 1`. -/
def AnchorWindow (n : ℕ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ h : ℝ → ℝ, IsSmallFlatBumpStrong n ε h → h ≠ 0 →
    ∃ X Y : ℝ → ℝ,
      Work.OddEnvelope.IsEnvelopeCurve h X Y ∧ CloseToProfileX X ∧ CloseToProfileX Y ∧
        (∀ s : ℝ, 1 - 3 * tau < s → s ≤ 1 →
          Work.OddCurve.momentA n h X Y (Work.OddEnvelope.envelopeProfile h X Y) s =
            refConst n / Real.sqrt (1 + s ^ 2)) ∧
        (∀ s : ℝ, 1 - 3 * tau < s → s ≤ 1 →
          Work.OddCurve.momentB n h X Y (Work.OddEnvelope.envelopeProfile h X Y) s = 0)

/-- **The low-slope part of the odd construction** (paper Step 3): from an envelope curve
satisfying the two moment equations on the transition window, produce one agreeing with it on
`s ≥ 1 - 3τ` and satisfying them on all slopes `0 < s ≤ 1`. -/
def LowSlopeExtension (n : ℕ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ h X Y : ℝ → ℝ, IsSmallFlatBumpStrong n ε h →
    Work.OddEnvelope.IsEnvelopeCurve h X Y → CloseToProfileX X → CloseToProfileX Y →
    (∀ s : ℝ, 1 - 3 * tau < s → s ≤ 1 →
      Work.OddCurve.momentA n h X Y (Work.OddEnvelope.envelopeProfile h X Y) s =
        refConst n / Real.sqrt (1 + s ^ 2)) →
    (∀ s : ℝ, 1 - 3 * tau < s → s ≤ 1 →
      Work.OddCurve.momentB n h X Y (Work.OddEnvelope.envelopeProfile h X Y) s = 0) →
    ∃ x y : ℝ → ℝ,
      (∀ s : ℝ, 1 - 3 * tau ≤ s → x s = X s ∧ y s = Y s) ∧
        Work.OddEnvelope.IsEnvelopeCurve h x y ∧
        CloseToProfileX x ∧ CloseToProfileX y ∧
        (∀ s : ℝ, 0 < s → s ≤ 1 →
          Work.OddCurve.momentA n h x y (Work.OddEnvelope.envelopeProfile h x y) s =
            refConst n / Real.sqrt (1 + s ^ 2)) ∧
        (∀ s : ℝ, 0 < s → s ≤ 1 →
          Work.OddCurve.momentB n h x y (Work.OddEnvelope.envelopeProfile h x y) s = 0)

/-- **The two halves give the deliverable's transition-slope statement.** -/
theorem smallSlopeCurveExistsStrong_of_halves (n : ℕ) (hn : 1 ≤ n)
    (ha : AnchorWindow n) (he : LowSlopeExtension n) : SmallSlopeCurveExistsStrong n := by
  obtain ⟨ε₁, hε₁, ha⟩ := ha
  obtain ⟨ε₂, hε₂, he⟩ := he
  have hτ : (0 : ℝ) < tau := by norm_num [Work.OddCurve.tau]
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun h hb hne => ?_⟩
  have hb₁ : IsSmallFlatBumpStrong n ε₁ h :=
    ⟨hb.1, hb.2.1, fun k hk s => le_trans (hb.2.2.1 k hk s) (min_le_left _ _), hb.2.2.2⟩
  have hb₂ : IsSmallFlatBumpStrong n ε₂ h :=
    ⟨hb.1, hb.2.1, fun k hk s => le_trans (hb.2.2.1 k hk s) (min_le_right _ _), hb.2.2.2⟩
  obtain ⟨X, Y, hX, hc1, hc2, hma, hmb⟩ := ha h hb₁ hne
  obtain ⟨x, y, _, hx, hxc, hyc, hmA, hmB⟩ := he h X Y hb₂ hX hc1 hc2 hma hmb
  refine ⟨x, y, hx, ?_⟩
  refine ⟨fun s hs => ?_, fun s hs => ?_⟩
  · obtain ⟨hs0, hs1⟩ := hs
    exact hmA s hs0 (by linarith)
  · obtain ⟨hs0, hs1⟩ := hs
    exact hmB s hs0 (by linarith)

end

end Work.OddCurve.LowSlope

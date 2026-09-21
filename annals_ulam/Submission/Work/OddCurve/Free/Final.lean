import Submission.Work.OddCurve.Free.Step3Class
import Submission.Work.OddCurve.Free.lowSlopeThreeFreeC

/-!
# The chord curve of the odd-dimensional case: the unconditional statements

`Work.OddCurve.Free.lowSlopeThreeFreeC` (Ryabogin's Step 3, free tips, bump class `C^{2n+2}`) is
proved; this file records the unconditional consequences:

* `lowSlopeExtensionFreeClass n hn` — paper Step 3 in the interface
  `Work.OddCurve.Free.LowSlopeExtensionFreeClass`;
* `oddCurveExistsFreeClass n hn` — the corrected deliverable;
* `odd_curve_exists_free_written n hn` — the corrected deliverable written out textually in the
  shape of the request (with the three documented corrections: bump class `C^{2n+2}`, free tips
  `IsEnvelopeCurveFree`, and the untruncated profile `Work.OddVolterra.Free.envProfileFree`).

The endgame from `oddCurveExistsFreeClass` to `Submission.Odd.OddFamilyData d` is
`Work.OddCurve.Free.oddFamilyData_of_momentEquationsGeneralFull`, fed with
`f := Work.OddVolterra.Free.envProfileFree h x y`, `R₁ := ρ (-1)`, `R₂ := ρ (1)` and the bump
`Submission.Odd.exists_odd_bump (2 * n + 2) ε`.
-/

namespace Work.OddCurve
namespace Free

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Pointwise Interval

/-- **Paper Step 3 of the odd case, unconditionally.** -/
theorem lowSlopeExtensionFreeClass (n : ℕ) (hn : 1 ≤ n) : LowSlopeExtensionFreeClass n :=
  lowSlopeExtensionFreeClass_of_lowSlopeThreeFreeC n (lowSlopeThreeFreeC n hn)

/-- **The corrected deliverable, unconditionally.** -/
theorem oddCurveExistsFreeClass (n : ℕ) (hn : 1 ≤ n) : OddCurveExistsFreeClass n :=
  oddCurveExistsFreeClass_of_lowSlopeThreeFreeC n hn (lowSlopeThreeFreeC n hn)

/-- **The corrected deliverable, written out textually, unconditionally.** -/
theorem odd_curve_exists_free_written_unconditional (n : ℕ) (hn : 1 ≤ n) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ h : ℝ → ℝ, h ≠ 0 →
      ContDiff ℝ ∞ h →
      Function.support h ⊆ Set.Ioo (1 - 2 * (1 / 10)) (1 - (1 / 10)) →
      (∀ k : ℕ, k ≤ 2 * n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ ε) →
      (∃ η : ℝ, 0 < η ∧ ∀ s : ℝ, 1 - 2 * (1 / 10) ≤ s →
        s < 1 - 2 * (1 / 10) + η → h s = 0) →
      ∃ C : ℝ, ∃ x y : ℝ → ℝ,
        IsEnvelopeCurveFree h x y ∧
        (∀ s : ℝ, 0 < s → s ≤ 1 →
          (∫ t in (-x s)..(y s),
            (Work.OddVolterra.Free.envProfileFree h x y t ^ 2 - (s * t + h s) ^ 2) ^ n *
              Real.sqrt (Work.OddVolterra.Free.envProfileFree h x y t ^ 2 -
                (s * t + h s) ^ 2)) =
            C / Real.sqrt (1 + s ^ 2)) ∧
        (∀ s : ℝ, 0 < s → s ≤ 1 →
          (∫ t in (-x s)..(y s),
            (Work.OddVolterra.Free.envProfileFree h x y t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) *
              Real.sqrt (Work.OddVolterra.Free.envProfileFree h x y t ^ 2 -
                (s * t + h s) ^ 2) *
              (t + deriv h s)) = 0) :=
  odd_curve_exists_free_written_class n hn (oddCurveExistsFreeClass n hn)

end

end Free
end Work.OddCurve

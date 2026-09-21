import Mathlib
import Submission.Work.OddCurve.Free
import Submission.Work.OddCurve.LowSlope.Extension
import Submission.Work.OddCurve.LowSlope.momentEqs_transfer
import Submission.Work.OddVolterra.Free.Defs
import Submission.Work.OddVolterra.Free.envProfileFree_chord
import Submission.Work.OddVolterra.Free.momentEqs_transfer_free
import Submission.Work.OddVolterra.Free.free_moment_continuous

namespace Work.OddVolterra.Free

/-- **The transfer of the two moment equations to the reconstructed curve, free tips** (corrected
restatement of `momentEqs_transfer_free`; the constant is `Work.OddCurve.refConst n`).

`Work.OddCurve.LowSlope.momentEqs_transfer` (proved) says: if two envelope curves for the same
perturbation `h` agree on the slopes `s ≥ a` with `a ≥ 1 - 3τ`, and the anchor `(X, Y)` satisfies
the two moment equations on `(1-3τ, 1]`, then so does the other curve, on `[a,1]`.

This is the same statement with `Work.OddEnvelope.IsEnvelopeCurve` replaced by
`Work.OddCurve.Free.IsEnvelopeCurveFree` and `Work.OddEnvelope.envelopeProfile` replaced by
`Work.OddVolterra.Free.envProfileFree` (the untruncated envelope profile).  Needed because the
paper's reconstruction produces tips at `1 + O(ε)`, not `1`
(`Submission/Work/OddVolterra/Free/NOTES_free_tips.md`).

ROUTE.  `IsEnvelopeCurveFree` carries every field of `IsEnvelopeCurve` except the two tip limits.
The profile identification step: for `t ∈ (0, y s]` the realising slope `σ` satisfies `σ ≥ s ≥ a`
by strict antitonicity, hence `Y σ = y σ = t`, and by uniqueness of that slope the two untruncated
envelopes agree there.  NOTE: not a pure rename — `IsChordCurve.lt_one` fails for free tips, so
`slopeRight_eq_of_agree` must be rebuilt from `StrictAntiOn` injectivity, and the endpoint case
`s = a = 1 - 3τ` in the source uses `Work.OddCurve.hasDerivAt_momentA`/`continuousAt_momentB`
(proved for `IsEnvelopeCurve` only); free analogues must be re-proved. -/
theorem momentEqs_transfer_free_const (n : ℕ) (hn : 1 ≤ n) {h X Y x y : ℝ → ℝ} {a : ℝ}
    (hX : Work.OddCurve.Free.IsEnvelopeCurveFree h X Y)
    (hx : Work.OddCurve.Free.IsEnvelopeCurveFree h x y)
    (ha : 1 - 3 * Work.OddVolterra.tau ≤ a)
    (hagree : ∀ s : ℝ, a ≤ s → x s = X s ∧ y s = Y s)
    (hA : ∀ s : ℝ, 1 - 3 * Work.OddVolterra.tau < s → s ≤ 1 →
      Work.OddCurve.momentA n h X Y (Work.OddVolterra.Free.envProfileFree h X Y) s =
        Work.OddCurve.refConst n / Real.sqrt (1 + s ^ 2))
    (hB : ∀ s : ℝ, 1 - 3 * Work.OddVolterra.tau < s → s ≤ 1 →
      Work.OddCurve.momentB n h X Y (Work.OddVolterra.Free.envProfileFree h X Y) s = 0) :
    (∀ s : ℝ, a ≤ s → s ≤ 1 →
      Work.OddCurve.momentA n h x y (Work.OddVolterra.Free.envProfileFree h x y) s =
        Work.OddCurve.refConst n / Real.sqrt (1 + s ^ 2)) ∧
    (∀ s : ℝ, a ≤ s → s ≤ 1 →
      Work.OddCurve.momentB n h x y (Work.OddVolterra.Free.envProfileFree h x y) s = 0) := by
  have hτ : (0 : ℝ) < 1 - 3 * Work.OddVolterra.tau := by norm_num [Work.OddVolterra.tau]
  have hτ1 : 1 - 3 * Work.OddVolterra.tau < 1 := by norm_num [Work.OddVolterra.tau]
  have hconst_cont : ContinuousAt (fun u : ℝ =>
      Work.OddCurve.refConst n / Real.sqrt (1 + u ^ 2)) (1 - 3 * Work.OddVolterra.tau) :=
    (continuous_const.div (Real.continuous_sqrt.comp (by fun_prop))
      (fun u => ne_of_gt (Real.sqrt_pos.mpr (by positivity)))).continuousAt
  constructor
  · intro s has hs1
    have hs0 : 0 < s := by linarith [hτ, ha, has]
    rw [Work.OddVolterra.Free.momentA_eq_of_agree_free (n := n) hX hx hagree has hs0]
    by_cases hgt : 1 - 3 * Work.OddVolterra.tau < s
    · exact hA s hgt hs1
    · have hseq : s = 1 - 3 * Work.OddVolterra.tau :=
        le_antisymm (le_of_not_gt hgt) (le_trans ha has)
      rw [hseq]
      exact Work.OddCurve.LowSlope.eq_at_of_continuousAt_of_eqOn_Ioc (s := 1 - 3 * Work.OddVolterra.tau)
        (T := 1) hτ1
        (Work.OddVolterra.Free.continuousAt_momentA_envProfileFree n hX hτ) hconst_cont
        (fun u hu hu1 => hA u hu hu1)
  · intro s has hs1
    have hs0 : 0 < s := by linarith [hτ, ha, has]
    rw [Work.OddVolterra.Free.momentB_eq_of_agree_free (n := n) hX hx hagree has hs0]
    by_cases hgt : 1 - 3 * Work.OddVolterra.tau < s
    · exact hB s hgt hs1
    · have hseq : s = 1 - 3 * Work.OddVolterra.tau :=
        le_antisymm (le_of_not_gt hgt) (le_trans ha has)
      rw [hseq]
      exact Work.OddCurve.LowSlope.eq_at_of_continuousAt_of_eqOn_Ioc (s := 1 - 3 * Work.OddVolterra.tau)
        (T := 1) hτ1
        (Work.OddVolterra.Free.continuousAt_momentB_envProfileFree n hX hτ) continuousAt_const
        (fun u hu hu1 => hB u hu hu1)

end Work.OddVolterra.Free

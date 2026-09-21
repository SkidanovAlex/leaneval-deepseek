import Mathlib
import Submission.Work.OddCurve.Free
import Submission.Work.OddCurve.LowSlope.Extension
import Submission.Work.OddCurve.LowSlope.momentEqs_transfer
import Submission.Work.OddVolterra.Free.Defs
import Submission.Work.OddVolterra.Free.envProfileFree_chord
import Submission.Work.OddVolterra.Free.free_slope_api
import Submission.Work.OddVolterra.Free.rad_nonpos_outside_free
import Submission.Work.OddVolterra.Free.free_profile_continuity
import Submission.Work.OddVolterra.Free.free_moment_continuity

/-!
# Transfer of the moment equations to the reconstructed curve, free tips

The free-tip analogue of `Work.OddCurve.LowSlope.momentEqs_transfer`, with
`Work.OddEnvelope.IsEnvelopeCurve` replaced by `Work.OddCurve.Free.IsEnvelopeCurveFree` and
`Work.OddEnvelope.envelopeProfile` replaced by the *untruncated* profile
`Work.OddVolterra.Free.envProfileFree`.

The two new ingredients with respect to the fixed-tip source are

* `envProfileFree_eqOn_of_agree` below: if two free-tip envelope curves for the same bump agree on
  the slopes `σ ≥ s`, then their untruncated envelope profiles agree on the whole section
  `[-(x s), y s]`.  The realising slope of a point of the section is `≥ s`, hence once more in the
  region of agreement, and it is *unique* (`IsEnvelopeCurveFree.slopeRight_eq_of` built from
  injectivity of the two strictly antitone curves — the fixed-tip proof used surjectivity of the
  chord curve onto `(0,1)`, which free tips do not give);
* the endpoint `s = 1 - 3τ`, where the moment equation at the single slope not covered by the
  hypotheses is obtained as a limit from the right (see `endpointA_free`/`endpointB_free`).
-/

namespace Work.OddCurve

/-- **The reference constant of the free-tip reconstruction.**  This is the constant appearing on
the right-hand side of the moment equation `(A)` for the reconstructed curve.  The reconstruction
does not change the constant: the transfer below shows that the two moment integrals of the two
curves *coincide* at every slope on which the curves agree, so the constant of the anchor
(`refConst n`) is also the constant of the reconstruction.  It is defined here because the
statement of `Work.OddVolterra.Free.momentEqs_transfer_free` names it; it is definitionally
`refConst n`. -/
noncomputable def refCostfree (n : ℕ) : ℝ := refConst n

end Work.OddCurve

namespace Work.OddVolterra.Free

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

/-! ## Agreement of the untruncated profiles on the section -/

/-- **The untruncated envelope profiles agree on the whole section.**  If two free-tip envelope
curves for the same bump agree at the slope `s` and on all the slopes above it, then their
untruncated envelope profiles agree on `[-(x s), y s]`.

For `t ∈ (0, y s]` the realising slope `σ` of `t` satisfies `σ ≥ s` (the curve is strictly
decreasing, so a point of the section is realised by a slope at least `s`), and the same holds for
the second curve; uniqueness of the realising slope (`strict antitonicity` + `slopeRight_eq_of`)
identifies the two slopes, and the two envelopes coincide there.  The left half is the same
argument with `x`. -/
lemma envProfileFree_eqOn_of_agree {h X Y x y : ℝ → ℝ}
    (hX : Work.OddCurve.Free.IsEnvelopeCurveFree h X Y)
    (hx : Work.OddCurve.Free.IsEnvelopeCurveFree h x y)
    {s : ℝ} (hs : 0 < s) (hxs : x s = X s) (hys : y s = Y s)
    (hag : ∀ σ : ℝ, s ≤ σ → x σ = X σ ∧ y σ = Y σ) :
    Set.EqOn (envProfileFree h x y) (envProfileFree h X Y) (Set.Icc (-(x s)) (y s)) := by
  intro t ht
  rcases lt_trichotomy t 0 with hneg | heq | hpos
  · -- the left branch
    have htpos : 0 < -t := by linarith
    have htlec : -t ≤ x s := by linarith [ht.1]
    have htlecX : -t ≤ X s := by rw [← hxs]; exact htlec
    obtain ⟨σ, hsσ, hσpos, hxσ⟩ := hx.exists_slope_x hs htpos htlec
    obtain ⟨τ, hsτ, hτpos, hXτ⟩ := hX.exists_slope_x hs htpos htlecX
    have hστ : σ = τ :=
      hx.strictAntiOn_x.injOn hσpos hτpos (by rw [hxσ, ← hXτ, ← (hag τ hsτ).1])
    have hsl : Work.OddEnvelope.slopeLeft x t = σ := hx.slopeLeft_eq_of hσpos hxσ
    have hsl' : Work.OddEnvelope.slopeLeft X t = τ := hX.slopeLeft_eq_of hτpos hXτ
    rw [envProfileFree, if_neg (not_lt.mpr hneg.le), if_pos hneg,
      envProfileFree, if_neg (not_lt.mpr hneg.le), if_pos hneg,
      Work.OddEnvelope.envelopeLeft, Work.OddEnvelope.envelopeLeft, hsl, hsl', hστ]
  · rw [heq, envProfileFree, if_neg (lt_irrefl 0), if_neg (lt_irrefl 0),
      envProfileFree, if_neg (lt_irrefl 0), if_neg (lt_irrefl 0)]
  · -- the right branch
    have hty : t ≤ y s := ht.2
    have htyX : t ≤ Y s := by rw [← hys]; exact hty
    obtain ⟨σ, hsσ, hσpos, hyσ⟩ := hx.exists_slope_y hs hpos hty
    obtain ⟨τ, hsτ, hτpos, hYτ⟩ := hX.exists_slope_y hs hpos htyX
    have hστ : σ = τ :=
      hx.strictAntiOn_y.injOn hσpos hτpos (by rw [hyσ, ← hYτ, ← (hag τ hsτ).2])
    rw [envProfileFree, if_pos hpos, envProfileFree, if_pos hpos,
      Work.OddEnvelope.envelopeRight, Work.OddEnvelope.envelopeRight,
      hx.slopeRight_eq_of hσpos hyσ, hX.slopeRight_eq_of hτpos hYτ, hστ]

/-! ## Transfer of the two moment integrals -/

/-- **Transfer of `(A)`.**  If `(x, y)` agrees with `(X, Y)` on the slopes `σ ≥ a` then the two
volume moment integrals coincide for every slope `s ≥ a`, `s > 0`. -/
lemma momentA_eq_of_agree_free {n : ℕ} {h X Y x y : ℝ → ℝ}
    (hX : Work.OddCurve.Free.IsEnvelopeCurveFree h X Y)
    (hx : Work.OddCurve.Free.IsEnvelopeCurveFree h x y)
    {a s : ℝ} (hag : ∀ σ : ℝ, a ≤ σ → x σ = X σ ∧ y σ = Y σ) (has : a ≤ s) (hs0 : 0 < s) :
    Work.OddCurve.momentA n h x y (envProfileFree h x y) s =
      Work.OddCurve.momentA n h X Y (envProfileFree h X Y) s := by
  have hxs : x s = X s := (hag s has).1
  have hys : y s = Y s := (hag s has).2
  have hle : -(X s) ≤ Y s := by
    rw [← hxs, ← hys]
    have h1 := hx.pos_x hs0
    have h2 := hx.pos_y hs0
    linarith
  have heq := envProfileFree_eqOn_of_agree hX hx hs0 hxs hys
    (fun σ hσ => hag σ (le_trans has hσ))
  rw [Work.OddCurve.momentA_def, Work.OddCurve.momentA_def, hxs, hys]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le hle] at ht
  have ht' : t ∈ Set.Icc (-(x s)) (y s) := by rwa [← hxs, ← hys] at ht
  have hft : envProfileFree h x y t = envProfileFree h X Y t := heq ht'
  simp only [Work.OddCurve.rad_def, hft]

/-- **Transfer of `(B)`.**  Same statement for the centroid moment integral. -/
lemma momentB_eq_of_agree_free {n : ℕ} {h X Y x y : ℝ → ℝ}
    (hX : Work.OddCurve.Free.IsEnvelopeCurveFree h X Y)
    (hx : Work.OddCurve.Free.IsEnvelopeCurveFree h x y)
    {a s : ℝ} (hag : ∀ σ : ℝ, a ≤ σ → x σ = X σ ∧ y σ = Y σ) (has : a ≤ s) (hs0 : 0 < s) :
    Work.OddCurve.momentB n h x y (envProfileFree h x y) s =
      Work.OddCurve.momentB n h X Y (envProfileFree h X Y) s := by
  have hxs : x s = X s := (hag s has).1
  have hys : y s = Y s := (hag s has).2
  have hle : -(X s) ≤ Y s := by
    rw [← hxs, ← hys]
    have h1 := hx.pos_x hs0
    have h2 := hx.pos_y hs0
    linarith
  have heq := envProfileFree_eqOn_of_agree hX hx hs0 hxs hys
    (fun σ hσ => hag σ (le_trans has hσ))
  rw [Work.OddCurve.momentB_def, Work.OddCurve.momentB_def, hxs, hys]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le hle] at ht
  have ht' : t ∈ Set.Icc (-(x s)) (y s) := by rwa [← hxs, ← hys] at ht
  have hft : envProfileFree h x y t = envProfileFree h X Y t := heq ht'
  simp only [Work.OddCurve.rad_def, hft]


/-! ## The endpoint slope `1 - 3τ`

At the single slope not covered by the hypotheses `hA`/`hB` the two moment integrals are obtained
from the right by continuity (`Work.OddVolterra.Free.continuousAt_momentA_free` and
`continuousAt_momentB_free`), exactly as in the fixed-tip source, where the same role was played
by `Work.OddCurve.hasDerivAt_momentA` and `Work.OddCurve.LowSlope.continuousAt_momentB`. -/

/-- **The transfer of the two moment equations to the reconstructed curve, free tips.**

`Work.OddCurve.LowSlope.momentEqs_transfer` (proved) says: if two envelope curves for the same
perturbation `h` agree on the slopes `s ≥ a` with `a ≥ 1 - 3τ`, and the anchor `(X, Y)` satisfies
the two moment equations on `(1-3τ, 1]`, then so does the other curve, on `[a,1]`.  Its conclusion
is stated with `Work.OddEnvelope.envelopeProfile` and `Work.OddEnvelope.IsEnvelopeCurve`.

This is the same statement with `Work.OddEnvelope.IsEnvelopeCurve` replaced by
`Work.OddCurve.Free.IsEnvelopeCurveFree` and `Work.OddEnvelope.envelopeProfile` replaced by
`Work.OddVolterra.Free.envProfileFree` (the untruncated envelope profile).  It is needed because the
paper's reconstruction produces tips at `1 + O(ε)`, not `1`
(`Submission/Work/OddVolterra/Free/NOTES_free_tips.md`), so `IsEnvelopeCurve` is not available; and
because the truncated profile is the wrong profile on `(1, y 0⁺)` when the tip exceeds `1`.

ROUTE FOR THE PROVER.  Copy `Submission/Work/OddCurve/LowSlope/momentEqs_transfer.lean` and rename
the structure projections: `IsEnvelopeCurveFree` carries the *same* fields as `IsEnvelopeCurve`
except `x_tendsto_one`/`y_tendsto_one`, which are replaced by
`x_tendsto_free`/`y_tendsto_free`.  The profile identification step is available: for `t ∈ (0, y s]`
the realising slope `σ` satisfies `σ ≥ s ≥ a` by strict antitonicity, hence `Y σ = y σ = t`, and by
the uniqueness of that slope the two untruncated envelopes agree there.  NOTE (reviewers): this is
*not* a pure rename — `IsChordCurve.lt_one` fails for free tips, so `slopeRight_eq_of_agree` must be
rebuilt from `StrictAntiOn` injectivity, and the endpoint case `s = a = 1 - 3τ` in the source uses
`Work.OddCurve.hasDerivAt_momentA`/`continuousAt_momentB`, which are stated for `IsEnvelopeCurve`;
free analogues do not exist yet and must be re-proved (a copy of the moving-endpoint argument).
Those are the real work items. -/
theorem momentEqs_transfer_free (n : ℕ) (hn : 1 ≤ n) {h X Y x y : ℝ → ℝ} {a : ℝ}
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
        Work.OddCurve.refCostfree n / Real.sqrt (1 + s ^ 2)) ∧
    (∀ s : ℝ, a ≤ s → s ≤ 1 →
      Work.OddCurve.momentB n h x y (Work.OddVolterra.Free.envProfileFree h x y) s = 0) := by
  have hτ : (0 : ℝ) < 1 - 3 * Work.OddVolterra.tau := by norm_num [Work.OddVolterra.tau]
  have hτ1 : 1 - 3 * Work.OddVolterra.tau < 1 := by norm_num [Work.OddVolterra.tau]
  have hcontG : ContinuousAt (fun u : ℝ =>
      Work.OddCurve.refCostfree n / Real.sqrt (1 + u ^ 2))
      (1 - 3 * Work.OddVolterra.tau) :=
    (continuous_const.div (Real.continuous_sqrt.comp (by fun_prop))
      (fun u => ne_of_gt (Real.sqrt_pos.mpr (by positivity)))).continuousAt
  constructor
  · intro s has hs1
    have hs0 : 0 < s := lt_of_lt_of_le hτ (le_trans ha has)
    rw [momentA_eq_of_agree_free hX hx hagree has hs0]
    by_cases hgt : 1 - 3 * Work.OddVolterra.tau < s
    · rw [hA s hgt hs1]
      rfl
    · have hseq : s = 1 - 3 * Work.OddVolterra.tau :=
        le_antisymm (le_of_not_gt hgt) (le_trans ha has)
      rw [hseq]
      exact Work.OddCurve.LowSlope.eq_at_of_continuousAt_of_eqOn_Ioc hτ1
        (continuousAt_momentA_free hX hτ) hcontG
        (fun u hu hu1 => hA u hu hu1)
  · intro s has hs1
    have hs0 : 0 < s := lt_of_lt_of_le hτ (le_trans ha has)
    rw [momentB_eq_of_agree_free hX hx hagree has hs0]
    by_cases hgt : 1 - 3 * Work.OddVolterra.tau < s
    · exact hB s hgt hs1
    · have hseq : s = 1 - 3 * Work.OddVolterra.tau :=
        le_antisymm (le_of_not_gt hgt) (le_trans ha has)
      rw [hseq]
      exact Work.OddCurve.LowSlope.eq_at_of_continuousAt_of_eqOn_Ioc hτ1
        (continuousAt_momentB_free hX hτ) continuousAt_const
        (fun u hu hu1 => hB u hu hu1)

end

end Work.OddVolterra.Free

import Mathlib
import Submission.Work.OddVolterra.Free.Defs
import Submission.Work.OddVolterra.Free.free_slope_api
import Submission.Work.OddVolterra.Free.momentEqs_transfer_free_const

/-!
# Shared vocabulary of the free-tip low-slope step (`Work.OddVolterra.Free`)

This module collects the definitions and the elementary interface lemmas used by
`Work.OddVolterra.Free.lowSlopeThreeFree` (Ryabogin's Step 3 at the free-tip interface).  It is
imported both by the target module and by the helpers delegated for it, so it must contain no
`sorry` and no dependence on those helpers.
-/

namespace Work.OddVolterra.Free

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

/-- **`ρ` is the radial function of the anchor's envelope profile.**  This is the full package
that `Work.OddCurve.LowSlope.anchorRadialFunction` produces for a tip-normalised anchor curve
`(X, Y)`: positivity, smoothness, strict monotonicity of `u ↦ ρ u * u` (the radial
parametrisation is injective), the graph identity, and `ρ 0 = 1`. -/
def IsAnchorRadial (h X Y ρ : ℝ → ℝ) : Prop :=
  (∀ u ∈ Set.Ioo (-1 : ℝ) 1, 0 < ρ u) ∧
  ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Ioo (-1 : ℝ) 1) ∧
  StrictMonoOn (fun u : ℝ => ρ u * u) (Set.Ioo (-1 : ℝ) 1) ∧
  (∀ u ∈ Set.Ioo (-1 : ℝ) 1,
    ρ u * Real.sqrt (1 - u ^ 2) = Work.OddEnvelope.envelopeProfile h X Y (ρ u * u)) ∧
  ρ 0 = 1

/-- **The anchor's moment equations may be evaluated with the untruncated profile.**  For a
tip-normalised anchor the cutting sections lie in `(-1, 1)`
(`Work.OddEnvelope.envelopeProfile_spec`), where the two profiles agree
(`envProfileFree_eq_envelopeProfile`); hence the two moment integrals coincide. -/
theorem momentA_anchor_eq_free (n : ℕ) {h X Y : ℝ → ℝ}
    (H : Work.OddEnvelope.IsEnvelopeCurve h X Y) {s : ℝ} (hs : 0 < s) :
    Work.OddCurve.momentA n h X Y (envProfileFree h X Y) s =
      Work.OddCurve.momentA n h X Y (Work.OddEnvelope.envelopeProfile h X Y) s := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hinside, -⟩ :=
    Work.OddEnvelope.envelopeProfile_spec (h := h) (x := X) (y := Y) H
  obtain ⟨hx, hy⟩ := hinside s hs
  have hmem : ∀ t ∈ Set.uIcc (-(X s)) (Y s), t ∈ Set.Ioo (-1 : ℝ) 1 := by
    intro t ht
    rw [Set.uIcc] at ht
    exact ⟨lt_of_lt_of_le (lt_min hx.1 hy.1) ht.1, lt_of_le_of_lt ht.2 (max_lt hx.2 hy.2)⟩
  simp only [Work.OddCurve.momentA, Work.OddCurve.rad]
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [envProfileFree_eq_envelopeProfile (hmem t ht)]

/-- **The anchor's moment equations may be evaluated with the untruncated profile** (second
equation). -/
theorem momentB_anchor_eq_free (n : ℕ) {h X Y : ℝ → ℝ}
    (H : Work.OddEnvelope.IsEnvelopeCurve h X Y) {s : ℝ} (hs : 0 < s) :
    Work.OddCurve.momentB n h X Y (envProfileFree h X Y) s =
      Work.OddCurve.momentB n h X Y (Work.OddEnvelope.envelopeProfile h X Y) s := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hinside, -⟩ :=
    Work.OddEnvelope.envelopeProfile_spec (h := h) (x := X) (y := Y) H
  obtain ⟨hx, hy⟩ := hinside s hs
  have hmem : ∀ t ∈ Set.uIcc (-(X s)) (Y s), t ∈ Set.Ioo (-1 : ℝ) 1 := by
    intro t ht
    rw [Set.uIcc] at ht
    exact ⟨lt_of_lt_of_le (lt_min hx.1 hy.1) ht.1, lt_of_le_of_lt ht.2 (max_lt hx.2 hy.2)⟩
  simp only [Work.OddCurve.momentB, Work.OddCurve.rad]
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [envProfileFree_eq_envelopeProfile (hmem t ht)]

/-- The two moment equations of the anchor, in the untruncated-profile form. -/
theorem anchorMomentEqs_free (n : ℕ) {h X Y : ℝ → ℝ}
    (H : Work.OddEnvelope.IsEnvelopeCurve h X Y)
    (hA : ∀ s : ℝ, 1 - 3 * Work.OddVolterra.tau < s → s ≤ 1 →
      Work.OddCurve.momentA n h X Y (Work.OddEnvelope.envelopeProfile h X Y) s =
        Work.OddCurve.refConst n / Real.sqrt (1 + s ^ 2))
    (hB : ∀ s : ℝ, 1 - 3 * Work.OddVolterra.tau < s → s ≤ 1 →
      Work.OddCurve.momentB n h X Y (Work.OddEnvelope.envelopeProfile h X Y) s = 0) :
    (∀ s : ℝ, 1 - 3 * Work.OddVolterra.tau < s → s ≤ 1 →
      Work.OddCurve.momentA n h X Y (envProfileFree h X Y) s =
        Work.OddCurve.refConst n / Real.sqrt (1 + s ^ 2)) ∧
    (∀ s : ℝ, 1 - 3 * Work.OddVolterra.tau < s → s ≤ 1 →
      Work.OddCurve.momentB n h X Y (envProfileFree h X Y) s = 0) := by
  have hτ : (0 : ℝ) < 1 - 3 * Work.OddVolterra.tau := by norm_num [Work.OddVolterra.tau]
  refine ⟨fun s h1 h2 => ?_, fun s h1 h2 => ?_⟩
  · rw [momentA_anchor_eq_free n H (by linarith)]; exact hA s h1 h2
  · rw [momentB_anchor_eq_free n H (by linarith)]; exact hB s h1 h2

end

end Work.OddVolterra.Free

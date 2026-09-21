import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.Assembly
import Submission.Work.OddEnvelope.Defs
import Submission.Work.OddCurve.LowSlope.Extension

/-!
# The `C^{n+3}` interfaces for `Work.OddVolterra.Existence.curve_data_three`

The workspace's odd-case interfaces (`Work.OddCurve.IsSmallFlatBumpStrong`,
`Work.OddCurve.LowSlope.AnchorWindow`, `...LowSlopeExtension`,
`Work.OddVolterra.WindowBridge.WindowSolution`) are all stated with the bump class

`∀ k ≤ n + 2, ∀ s, |iteratedDeriv k h s| ≤ ε`   (`C^{n+2}`),

which is **too weak** for a conclusion asserting the `C²`-closeness of the chord curve to the
semicircle's chord function: the curve's second derivative sees `h^{(n+3)}` through a
non-vanishing coefficient (see `Existence/NOTES_curve_with_moment_eqs_REFUTED.md` and
`Existence/WindowBridge/NOTES_C2_CLASS_TOO_WEAK.md`, both with machine-checked counterexamples).

The target `Work.OddVolterra.Existence.curve_data_three` is stated with the class

`∀ k ≤ n + 3, ∀ s, |iteratedDeriv k h s| ≤ ε`   (`C^{n+3}`),

which *is* the right class (the state `(x, y, x', y')` is `C¹`-close as soon as the data — which
involve `h^{(0..n+2)}` — are `C¹`-close, i.e. as soon as `h` is small in `C^{n+3}`).

This file fixes the `C^{n+3}` vocabulary, so that the two halves of the construction (the
transition window of Step 2 and the low slopes of Step 3) can be requested and proved
independently of each other and of the assembly.
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

namespace Work.OddVolterra.Existence

open Work.OddVolterra

noncomputable section

/-- **The `C^{n+3}` bump class.**  Smooth, supported in the open transition window
`(1 - 2τ, 1 - τ)`, all derivatives up to order `n + 3` bounded by `ε`, and flat on a right
neighbourhood of the left edge of the window. -/
def IsSmallFlatBumpThree (n : ℕ) (ε : ℝ) (h : ℝ → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) h ∧ Function.support h ⊆ Set.Ioo (1 - 2 * tau) (1 - tau) ∧
    (∀ k : ℕ, k ≤ n + 3 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ ε) ∧
    (∃ η : ℝ, 0 < η ∧ ∀ s : ℝ, 1 - 2 * tau ≤ s → s < 1 - 2 * tau + η → h s = 0)

lemma IsSmallFlatBumpThree.contDiff {n : ℕ} {ε : ℝ} {h : ℝ → ℝ}
    (hb : IsSmallFlatBumpThree n ε h) : ContDiff ℝ (⊤ : ℕ∞) h := hb.1

lemma IsSmallFlatBumpThree.support_subset {n : ℕ} {ε : ℝ} {h : ℝ → ℝ}
    (hb : IsSmallFlatBumpThree n ε h) :
    Function.support h ⊆ Set.Ioo (1 - 2 * tau) (1 - tau) := hb.2.1

lemma IsSmallFlatBumpThree.deriv_bound {n : ℕ} {ε : ℝ} {h : ℝ → ℝ}
    (hb : IsSmallFlatBumpThree n ε h) {k : ℕ} (hk : k ≤ n + 3) (s : ℝ) :
    |iteratedDeriv k h s| ≤ ε := hb.2.2.1 k hk s

lemma IsSmallFlatBumpThree.flat {n : ℕ} {ε : ℝ} {h : ℝ → ℝ}
    (hb : IsSmallFlatBumpThree n ε h) :
    ∃ η : ℝ, 0 < η ∧ ∀ s : ℝ, 1 - 2 * tau ≤ s → s < 1 - 2 * tau + η → h s = 0 := hb.2.2.2

/-- The class is monotone in the smallness bound. -/
lemma IsSmallFlatBumpThree.mono {n : ℕ} {ε ε' : ℝ} (hε : ε ≤ ε') {h : ℝ → ℝ}
    (hb : IsSmallFlatBumpThree n ε h) : IsSmallFlatBumpThree n ε' h :=
  ⟨hb.1, hb.2.1, fun k hk s => le_trans (hb.2.2.1 k hk s) hε, hb.2.2.2⟩

/-- The `C^{n+3}` class implies the three `C²`-bounds on `h` when `ε ≤ 1/100`. -/
lemma IsSmallFlatBumpThree.close_h {n : ℕ} {ε : ℝ} (hε : ε ≤ 1 / 100) {h : ℝ → ℝ}
    (hb : IsSmallFlatBumpThree n ε h) (hn : 1 ≤ n) :
    ∀ s : ℝ, |h s| ≤ 1 / 100 ∧ |deriv h s| ≤ 1 / 100 ∧ |deriv (deriv h) s| ≤ 1 / 100 := by
  intro s
  have h0 : |iteratedDeriv 0 h s| ≤ ε := hb.deriv_bound (by omega) s
  have h1 : |iteratedDeriv 1 h s| ≤ ε := hb.deriv_bound (by omega) s
  have h2 : |iteratedDeriv 2 h s| ≤ ε := hb.deriv_bound (by omega) s
  have e1 : iteratedDeriv 1 h s = deriv h s := by rw [iteratedDeriv_one]
  have e2 : iteratedDeriv 2 h s = deriv (deriv h) s := by
    rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]
  exact ⟨le_trans (by simpa using h0) hε, le_trans (le_of_eq (by rw [e1])) (le_trans h1 hε),
    le_trans (le_of_eq (by rw [e2])) (le_trans h2 hε)⟩

/-! ## The two halves and the state-level window solution, at class `C^{n+3}` -/

/-- **The state-level window solution of Step 2, at class `C^{n+3}`.**  This is
`Work.OddVolterra.WindowBridge.WindowSolution` with the bump class raised from `C^{n+2}` to
`C^{n+3}` (which is what makes the two `1/1000`-bounds on the derivatives of the state components
`2`, `3` — i.e. the `C²`-closeness of the curve — true).

`Z` is a `C^∞` state on `(0, ∞)` solving the paper's system `(hah44)` on the slope window
`(1/4, 1)`, equal to the ball's state past the transition window, `1/1000`-close to the ball's
state *together with the derivatives of its last two components*, with the last two components
equal to the derivatives of the first two, and with the sign pattern.  The `C^∞` regularity on all
of `(0, ∞)` is what the gluing lemma `exists_isEnvelopeCurve_of_window_solution` consumes.

ROUTE (for the prover).  The engine produces the state only on a window `[a, 1]` with `a > 0`;
here `a = 1/4`.  To obtain a `Z` which is `C^∞` on all of `(0, ∞)` *and* agrees with the window
solution on `[1/4, ∞)`, extend the first two components `Z·0`, `Z·1` of the window solution below
`a` by `Work.Anchor.extension` (the Borel/Seeley series; it asks for the `1/200`-closeness of
`Z·0`, `Z·1` to `profileX` on `[a, ∞)`, which the `1/1000`-closeness below supplies) and set the
last two components to the derivatives of the first two.  The result is globally `C^∞` and agrees
with the window solution above `1/4`, so it solves the system there, satisfies the tail, the
closeness and the signs, while the two derivative rows collapse to `F' = F'`.  (The gluing lemma
only ever evaluates `Z` above `1/4` anyway: `gluePhi_gt_quarter`.) -/
def WindowSolutionThree (n : ℕ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ h : ℝ → ℝ, IsSmallFlatBumpThree n ε h → h 0 = 0 → h ≠ 0 →
    ∃ Z : ℝ → Work.OddVolterra.St,
      ContDiffOn ℝ (⊤ : ℕ∞) Z (Set.Ioi (0 : ℝ)) ∧
      (∀ s ∈ Set.Ioo (1 / 4 : ℝ) 1,
        Work.OddVolterra.Godd n h s (Z s) =
          (∫ σ in s..(1 : ℝ), Work.OddVolterra.Theta n h s σ (Z σ)) +
            Work.OddVolterra.Xi n h s) ∧
      (∀ s : ℝ, 1 - Work.OddVolterra.tau ≤ s → Z s = Work.OddVolterra.baseState s) ∧
      (∀ s : ℝ, 1 / 4 ≤ s →
        |Z s 0 - Commons.Geometry.Ulam.profileX s| ≤ 1 / 1000 ∧
        |Z s 2 - deriv Commons.Geometry.Ulam.profileX s| ≤ 1 / 1000 ∧
        |deriv (fun u : ℝ => Z u 2) s - deriv (deriv Commons.Geometry.Ulam.profileX) s|
          ≤ 1 / 1000 ∧
        |Z s 1 - Commons.Geometry.Ulam.profileX s| ≤ 1 / 1000 ∧
        |Z s 3 - deriv Commons.Geometry.Ulam.profileX s| ≤ 1 / 1000 ∧
        |deriv (fun u : ℝ => Z u 3) s - deriv (deriv Commons.Geometry.Ulam.profileX) s|
          ≤ 1 / 1000) ∧
      (∀ s : ℝ, 1 / 4 ≤ s →
        deriv (fun u : ℝ => Z u 0) s = Z s 2 ∧ deriv (fun u : ℝ => Z u 1) s = Z s 3) ∧
      (∀ s : ℝ, 1 / 4 ≤ s → 0 < Z s 0 ∧ 0 < Z s 1 ∧ Z s 2 < 0 ∧ Z s 3 < 0)

/-- **The transition-window half of the odd construction, at class `C^{n+3}`** (the paper's
Step 2): for every sufficiently small `C^{n+3}` bump there is an envelope curve, `C²`-close to the
semicircle's, satisfying both moment equations on the slopes `1 - 3τ < s ≤ 1`. -/
def AnchorWindowThree (n : ℕ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ h : ℝ → ℝ, IsSmallFlatBumpThree n ε h → h ≠ 0 →
    ∃ X Y : ℝ → ℝ,
      Work.OddEnvelope.IsEnvelopeCurve h X Y ∧
        Work.OddCurve.LowSlope.CloseToProfileX X ∧ Work.OddCurve.LowSlope.CloseToProfileX Y ∧
        (∀ s : ℝ, 1 - 3 * tau < s → s ≤ 1 →
          Work.OddCurve.momentA n h X Y (Work.OddEnvelope.envelopeProfile h X Y) s =
            Work.OddCurve.refConst n / Real.sqrt (1 + s ^ 2)) ∧
        (∀ s : ℝ, 1 - 3 * tau < s → s ≤ 1 →
          Work.OddCurve.momentB n h X Y (Work.OddEnvelope.envelopeProfile h X Y) s = 0)

/-- **The low-slope half of the odd construction, at class `C^{n+3}`** (the paper's Step 3, the
spherical-Radon step, without the agreement clause above `1 - 3τ`, which no consumer uses): from an
envelope curve satisfying the two moment equations on the transition window, produce one
satisfying them on all slopes `0 < s ≤ 1`.

ROUTE (for the prover).  `Work.OddCurve.LowSlope.README.md` records the pipeline: the anchor's
radial data are the ball's on the cap `tan α ≤ 1 - 2τ` (they depend only on the jet of `h` at the
slope, and `h ≡ 0` there), so the data of the reconstruction can be taken equal to the ball's on
that cap and equal to the anchor's elsewhere; the inverse spherical Radon transform of
`Work.OddRadon` (`radonInverse`, `radialSystem_exists_C2`, `exists_profile_of_radial_data_strict`)
then produces the radial functions `R`, `r` of the reconstructed profile, and
`Work.OddCurve.LowSlope.lowSlope_momentEqs` turns the section conditions `(cmass)`, `(i1)`
(obtained from the Radon data by `radon_data_eq_inertiaIntegral` and
`radon_data_eq_centIntegral_Ioo`, both proved) into the two moment equations on the low-slope
range.  The constant agrees with the anchor's by `Work.OddCurve.LowSlope.refConst_eq_inertia`.
The outer part `|t| ≥ profileX (1 - 2τ)` of the reconstructed profile is the semicircle's, by
`Work.OddRadon.radialSystem_eq_ball`; the sign/curvature (`CloseToProfileX`) of the reconstruction
is the content of `Work.OddRadon.exists_profile_of_radial_data_strict`. -/
def LowSlopeThree (n : ℕ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ h X Y : ℝ → ℝ, IsSmallFlatBumpThree n ε h →
    Work.OddEnvelope.IsEnvelopeCurve h X Y →
    Work.OddCurve.LowSlope.CloseToProfileX X → Work.OddCurve.LowSlope.CloseToProfileX Y →
    (∀ s : ℝ, 1 - 3 * tau < s → s ≤ 1 →
      Work.OddCurve.momentA n h X Y (Work.OddEnvelope.envelopeProfile h X Y) s =
        Work.OddCurve.refConst n / Real.sqrt (1 + s ^ 2)) →
    (∀ s : ℝ, 1 - 3 * tau < s → s ≤ 1 →
      Work.OddCurve.momentB n h X Y (Work.OddEnvelope.envelopeProfile h X Y) s = 0) →
    ∃ x y : ℝ → ℝ,
      Work.OddEnvelope.IsEnvelopeCurve h x y ∧
        Work.OddCurve.LowSlope.CloseToProfileX x ∧ Work.OddCurve.LowSlope.CloseToProfileX y ∧
        (∀ s : ℝ, 0 < s → s ≤ 1 →
          Work.OddCurve.momentA n h x y (Work.OddEnvelope.envelopeProfile h x y) s =
            Work.OddCurve.refConst n / Real.sqrt (1 + s ^ 2)) ∧
        (∀ s : ℝ, 0 < s → s ≤ 1 →
          Work.OddCurve.momentB n h x y (Work.OddEnvelope.envelopeProfile h x y) s = 0)

end

end Work.OddVolterra.Existence

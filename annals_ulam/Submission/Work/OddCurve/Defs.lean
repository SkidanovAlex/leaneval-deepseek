import Mathlib
import Submission.Work.OddEnvelope.Main
import Submission.Odd.BumpData

/-!
# `Work.OddCurve` — the chord curve of the odd-dimensional case

This chapter is the interface and reduction layer for the last missing input of Ryabogin's
odd-dimensional construction (`d = 2n+1`, `n ≥ 1`): the *chord curve* `(x, y)` of the family of
lines `L_s t = s t + h s` for a small flat bump `h`.

The mathematics.  For a profile `f` and a perturbation `h`, with `P := f` and
`L_s t = s * t + h s`, the two conditions that the cap cut off by the hyperplane
`{z = L_s t}` be the cutting hyperplane at half volume (with the centroid condition) are

* `(A)  ∫_{-x s}^{y s} (f t ^ 2 - L_s t ^ 2) ^ n * √(f t ^ 2 - L_s t ^ 2) dt = C / √(1+s²)`,
* `(B)  ∫_{-x s}^{y s} (f t ^ 2 - L_s t ^ 2) ^ (n-1) * √(f t ^ 2 - L_s t ^ 2) * (t + h' s) dt = 0`,

where `-x s`, `y s` are the two intersections of the line `L_s` with `±f`.  The profile is
recovered from the curve as the envelope `Work.OddEnvelope.envelopeProfile h x y`
(`f (y s) = L_s (y s)`, `f (-x s) = -L_s (-x s)`).

## What this chapter provides

* `Work.OddCurve.rad`, `momentA`, `momentB`, `MomentEqsOn` — the two moment equations, spelled
  exactly as in the consumer's statement.
* `Work.OddCurve.IsOddCurve n C h x y` — the full package: `IsEnvelopeCurve h x y` plus both
  equations for every slope `0 < s ≤ 1`, with `f = envelopeProfile h x y`.
* `Work.OddCurve.IsSmallFlatBump ε h` — the hypothesis package on the bump `h` of the
  consumer's statement (smooth, supported in the window `(1-2τ, 1-τ)`, `|h|`, `|h'|`, `|h''| ≤ ε`,
  flat on a right neighbourhood of the left edge of the window).
* `Work.OddCurve.exists_isSmallFlatBump` — the bump construction `Submission.Odd.exists_odd_bump`
  produces an `h` satisfying this package (regularity index `∞`, not `⊤`: see the trap below).
* `Work.OddCurve.IsOddCurveSmallSlopes`, `Work.OddCurve.SmallSlopeCurveExists` — the same data with
  the moment equations imposed only on the *transition* slopes `0 < s ≤ 1 - τ`; the remaining
  slopes `[1-τ, 1]` are the semicircle's and carry no information.
* `Work.OddCurve.OddCurveExists n` — the exact conclusion of the consumer's request, as a `Prop`.

## Traps recorded here

1. The regularity index is `∞` (`= (↑(⊤ : ℕ∞) : WithTop ℕ∞)`, smoothness), **not** `⊤`
   (which is `ω`, analyticity, in this Mathlib revision).  `ContDiff ℝ ∞ h` is what the bump
   construction supplies; `ContDiff ℝ ⊤ h` would be uninhabitable next to compact support and
   `h ≠ 0`.
2. The moment equations are vacuous if the section is empty (`Real.sqrt` of a non-positive
   number is `0`).  With `IsEnvelopeCurve` this cannot happen:
   `Work.OddCurve.section_nondegenerate` records that the radicand is strictly positive on the
   open section.
-/

namespace Work.OddCurve

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

/-- The threshold `τ = 1/10` of the paper. -/
def tau : ℝ := 1 / 10

lemma tau_eq : tau = Work.OddEnvelope.tau := rfl

/-- The radicand `f t ^ 2 - (s * t + h s) ^ 2` of both moment equations. -/
def rad (h f : ℝ → ℝ) (s t : ℝ) : ℝ := f t ^ 2 - (s * t + h s) ^ 2

/-- The volume moment integral `(A)` of the odd case. -/
def momentA (n : ℕ) (h x y f : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ t in (-x s)..(y s), rad h f s t ^ n * Real.sqrt (rad h f s t)

/-- The centroid moment integral `(B)` of the odd case. -/
def momentB (n : ℕ) (h x y f : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ t in (-x s)..(y s), rad h f s t ^ (n - 1) * Real.sqrt (rad h f s t) * (t + deriv h s)

/-- The reference constant of the odd case: the value of `(A)` for the unit ball at slope `0`. -/
def refConst (n : ℕ) : ℝ := ∫ u in (-1 : ℝ)..1, (1 - u ^ 2) ^ n * Real.sqrt (1 - u ^ 2)

/-- The two moment equations on a set of slopes `S`. -/
def MomentEqsOn (n : ℕ) (C : ℝ) (h x y f : ℝ → ℝ) (S : Set ℝ) : Prop :=
  (∀ s ∈ S, momentA n h x y f s = C / Real.sqrt (1 + s ^ 2)) ∧
  (∀ s ∈ S, momentB n h x y f s = 0)

/-- **The chord curve of the odd case, at exponent `n`.**  `(x, y)` is the chord-endpoint curve
of the envelope `Work.OddEnvelope.envelopeProfile h x y` for the family of lines
`t ↦ s * t + h s`, and the two moment equations `(A)`, `(B)` hold for every slope `0 < s ≤ 1`
with the constant `C`. -/
def IsOddCurve (n : ℕ) (C : ℝ) (h x y : ℝ → ℝ) : Prop :=
  Work.OddEnvelope.IsEnvelopeCurve h x y ∧
    MomentEqsOn n C h x y (Work.OddEnvelope.envelopeProfile h x y) (Set.Ioc 0 1)

/-- The hypothesis package on the bump `h`: smooth, supported in the open window
`(1-2τ, 1-τ)`, with `h`, `h'`, `h''` bounded by `ε` in absolute value and `h` flat on a right
neighbourhood of the left edge of the window.  This is exactly the hypothesis list of the
consumer's statement (with `h ≠ 0` kept separate). -/
def IsSmallFlatBump (ε : ℝ) (h : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ h ∧
    Function.support h ⊆ Set.Ioo (1 - 2 * tau) (1 - tau) ∧
    (∀ s : ℝ, |h s| ≤ ε) ∧
    (∀ s : ℝ, |deriv h s| ≤ ε) ∧
    (∀ s : ℝ, |deriv (deriv h) s| ≤ ε) ∧
    (∃ η : ℝ, 0 < η ∧ ∀ s : ℝ, 1 - 2 * tau ≤ s → s < 1 - 2 * tau + η → h s = 0)

/-- **The conclusion of the consumer's request**, as a `Prop`. -/
def OddCurveExists (n : ℕ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ h : ℝ → ℝ, IsSmallFlatBump ε h → h ≠ 0 →
    ∃ C : ℝ, ∃ x y : ℝ → ℝ, IsOddCurve n C h x y

/-! ## The two moment equations on the transition slopes only -/

/-- The two moment equations on the *transition* slopes `0 < s ≤ 1 - τ`, with an arbitrary
constant `C`.  On the remaining slopes `1 - τ < s ≤ 1` the configuration is the semicircle's and the
equations are the ball identity (`Work.OddCurve.Tail`); at `s = 1 - τ` itself the equations are part
of this package (the bump may still be nonzero on a left neighbourhood of `1-τ`). -/
def SmallSlopeEqsC (n : ℕ) (C : ℝ) (h x y : ℝ → ℝ) : Prop :=
  MomentEqsOn n C h x y (Work.OddEnvelope.envelopeProfile h x y) (Set.Ioc 0 (1 - tau))

/-- The two moment equations on the transition slopes, with the constant normalised to the ball's
`refConst n`.  This normalisation loses no generality: the equations at `s = 1 - τ` force
`C = refConst n` (`Work.OddCurve.const_eq_refConst_of_smallSlope`, for bumps whose support is
contained in the *open* window). -/
def SmallSlopeEqs (n : ℕ) (h x y : ℝ → ℝ) : Prop :=
  SmallSlopeEqsC n (refConst n) h x y

/-- The curve data restricted to the transition slopes. -/
def IsOddCurveSmallSlopes (n : ℕ) (h x y : ℝ → ℝ) : Prop :=
  Work.OddEnvelope.IsEnvelopeCurve h x y ∧ SmallSlopeEqs n h x y

/-- The transition-window existence statement.  **This is the one remaining mathematical input of
the whole project** (the paper's Step 2 and Step 3): for every sufficiently small flat bump there
is a chord curve satisfying `IsEnvelopeCurve` and the two moment equations on the transition
slopes. -/
def SmallSlopeCurveExists (n : ℕ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ h : ℝ → ℝ, IsSmallFlatBump ε h → h ≠ 0 →
    ∃ x y : ℝ → ℝ, IsOddCurveSmallSlopes n h x y

/-- The same, with the constant left free (it is then forced to be `refConst n` by
`Work.OddCurve.const_eq_refConst_of_smallSlope`).  This is the form in which a construction of the
transition-slope curve should be attempted: it does not have to normalise `C`. -/
def SmallSlopeCurveExistsC (n : ℕ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ h : ℝ → ℝ, IsSmallFlatBump ε h → h ≠ 0 →
    ∃ C : ℝ, ∃ x y : ℝ → ℝ,
      Work.OddEnvelope.IsEnvelopeCurve h x y ∧ SmallSlopeEqsC n C h x y

/-! ## Elementary API -/

lemma rad_def (h f : ℝ → ℝ) (s t : ℝ) : rad h f s t = f t ^ 2 - (s * t + h s) ^ 2 := rfl

lemma momentA_def (n : ℕ) (h x y f : ℝ → ℝ) (s : ℝ) :
    momentA n h x y f s =
      ∫ t in (-x s)..(y s), rad h f s t ^ n * Real.sqrt (rad h f s t) := rfl

lemma momentB_def (n : ℕ) (h x y f : ℝ → ℝ) (s : ℝ) :
    momentB n h x y f s =
      ∫ t in (-x s)..(y s), rad h f s t ^ (n - 1) * Real.sqrt (rad h f s t) *
        (t + deriv h s) := rfl

lemma refConst_def (n : ℕ) :
    refConst n = ∫ u in (-1 : ℝ)..1, (1 - u ^ 2) ^ n * Real.sqrt (1 - u ^ 2) := rfl

/-- Unfolding of `MomentEqsOn` on `Ioc 0 1` in the exact shape of the consumer's statement. -/
lemma momentEqsOn_Ioc_iff (n : ℕ) (C : ℝ) (h x y f : ℝ → ℝ) :
    MomentEqsOn n C h x y f (Set.Ioc 0 1) ↔
      ((∀ s : ℝ, 0 < s → s ≤ 1 → momentA n h x y f s = C / Real.sqrt (1 + s ^ 2)) ∧
       (∀ s : ℝ, 0 < s → s ≤ 1 → momentB n h x y f s = 0)) := by
  constructor
  · intro ⟨h1, h2⟩
    exact ⟨fun s hs hs1 => h1 s ⟨hs, hs1⟩, fun s hs hs1 => h2 s ⟨hs, hs1⟩⟩
  · intro ⟨h1, h2⟩
    exact ⟨fun s hs => h1 s hs.1 hs.2, fun s hs => h2 s hs.1 hs.2⟩

/-- Unfolding of `SmallSlopeEqs`. -/
lemma smallSlopeEqs_iff (n : ℕ) (h x y : ℝ → ℝ) :
    SmallSlopeEqs n h x y ↔
      ((∀ s : ℝ, 0 < s → s ≤ 1 - tau →
          momentA n h x y (Work.OddEnvelope.envelopeProfile h x y) s =
            refConst n / Real.sqrt (1 + s ^ 2)) ∧
       (∀ s : ℝ, 0 < s → s ≤ 1 - tau →
          momentB n h x y (Work.OddEnvelope.envelopeProfile h x y) s = 0)) := by
  constructor
  · intro ⟨h1, h2⟩
    exact ⟨fun s hs hs1 => h1 s ⟨hs, hs1⟩, fun s hs hs1 => h2 s ⟨hs, hs1⟩⟩
  · intro ⟨h1, h2⟩
    exact ⟨fun s hs => h1 s hs.1 hs.2, fun s hs => h2 s hs.1 hs.2⟩

/-! ## Accessors for `IsSmallFlatBump` -/

lemma IsSmallFlatBump.contDiff {ε : ℝ} {h : ℝ → ℝ} (hb : IsSmallFlatBump ε h) :
    ContDiff ℝ ∞ h := hb.1

lemma IsSmallFlatBump.support_subset {ε : ℝ} {h : ℝ → ℝ} (hb : IsSmallFlatBump ε h) :
    Function.support h ⊆ Set.Ioo (1 - 2 * tau) (1 - tau) := hb.2.1

lemma IsSmallFlatBump.abs_le {ε : ℝ} {h : ℝ → ℝ} (hb : IsSmallFlatBump ε h) (s : ℝ) :
    |h s| ≤ ε := hb.2.2.1 s

lemma IsSmallFlatBump.abs_deriv_le {ε : ℝ} {h : ℝ → ℝ} (hb : IsSmallFlatBump ε h) (s : ℝ) :
    |deriv h s| ≤ ε := hb.2.2.2.1 s

lemma IsSmallFlatBump.abs_deriv2_le {ε : ℝ} {h : ℝ → ℝ} (hb : IsSmallFlatBump ε h) (s : ℝ) :
    |deriv (deriv h) s| ≤ ε := hb.2.2.2.2.1 s

/-- A bump of support inside `(1-2τ, 1-τ)` vanishes identically on a neighbourhood of every
`s > 1-τ` (the open ray `(1-τ, ∞)` is a neighbourhood of `s` and is contained in the complement of
the support). -/
lemma IsSmallFlatBump.eventuallyEq_zero_of_gt {ε : ℝ} {h : ℝ → ℝ} (hb : IsSmallFlatBump ε h)
    {s : ℝ} (hs : 1 - tau < s) : h =ᶠ[𝓝 s] (fun _ : ℝ => 0) := by
  filter_upwards [isOpen_Ioi.mem_nhds hs] with u hu
  have hu' : 1 - tau < u := hu
  by_contra hne
  have hmem : u ∈ Function.support h := by simpa [Function.mem_support] using hne
  have hsub := hb.support_subset hmem
  linarith [hsub.2, hu']

lemma tau_pos : 0 < tau := by norm_num [tau]

lemma one_sub_tau_eq : 1 - tau = 9 / 10 := by norm_num [tau]

lemma one_sub_two_tau_eq : 1 - 2 * tau = 4 / 5 := by norm_num [tau]

/-- The bump construction of `Submission.Odd` produces a function satisfying `IsSmallFlatBump`.
(Regularity index `∞`: the bump is smooth but not analytic.) -/
theorem exists_isSmallFlatBump (ε : ℝ) (hε : 0 < ε) :
    ∃ h : ℝ → ℝ, IsSmallFlatBump ε h ∧ h ≠ 0 ∧ h 0 = 0 ∧ (∃ s : ℝ, 0 < s ∧ h s ≠ 0) := by
  obtain ⟨h, hh, hsupp, _hsuppIcc, hne, h0, hflat, hbnd, hpos⟩ :=
    Submission.Odd.exists_odd_bump 2 ε hε
  have hbound : ∀ s : ℝ, |h s| ≤ ε ∧ |deriv h s| ≤ ε ∧ |deriv (deriv h) s| ≤ ε := by
    intro s
    have h0' : |iteratedDeriv 0 h s| ≤ ε := hbnd 0 (by omega) s
    have h1' : |iteratedDeriv 1 h s| ≤ ε := hbnd 1 (by omega) s
    have h2' : |iteratedDeriv 2 h s| ≤ ε := hbnd 2 (by omega) s
    have e0 : iteratedDeriv 0 h s = h s := by simp
    have e1 : iteratedDeriv 1 h s = deriv h s := congrFun iteratedDeriv_one s
    have e2 : iteratedDeriv 2 h s = deriv (deriv h) s := by
      rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]
    refine ⟨?_, ?_, ?_⟩
    · rw [← e0]; exact h0'
    · rw [← e1]; exact h1'
    · rw [← e2]; exact h2'
  exact ⟨h, ⟨hh, hsupp, fun s => (hbound s).1, fun s => (hbound s).2.1,
    fun s => (hbound s).2.2, hflat⟩, hne, h0, hpos⟩

/-- **Anti-vacuity.**  Any curve in the hypothesis package produces a genuinely cut section: the
radicand of the two moment equations is strictly positive at an interior point.  (Without this the
equations hold trivially, since `Real.sqrt` of a non-positive real number is `0`.) -/
theorem section_nondegenerate {h x y : ℝ → ℝ} (H : Work.OddEnvelope.IsEnvelopeCurve h x y)
    {s : ℝ} (hs : 0 < s) :
    ∃ t ∈ Set.Ioo (-(x s)) (y s),
      0 < rad h (Work.OddEnvelope.envelopeProfile h x y) s t := by
  have hxpos : 0 < x s := (Work.OddEnvelope.IsEnvelopeCurve.toChordCurve_x H).pos hs
  have hypos : 0 < y s := (Work.OddEnvelope.IsEnvelopeCurve.toChordCurve_y H).pos hs
  refine ⟨0, ⟨by linarith, by linarith⟩, ?_⟩
  have h := Work.OddEnvelope.envelopeProfile_sub_sq_pos H
    (Work.OddEnvelope.concaveOn_envelopeProfile H) hs 0 ⟨by linarith, by linarith⟩
  simpa [rad] using h

end

end Work.OddCurve

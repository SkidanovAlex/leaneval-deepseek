import Mathlib
import Submission.Work.OddEnvelope.Main
import Submission.Commons.Geometry.Ulam.exists_odd_section_solution

/-!
# `Work.OddCurveB` — the chord curve of the odd-dimensional case (third attack)

This chapter is an independent attack on the one remaining mathematical input of the
`annals_ulam` project: the *chord curve* `(x, y)` of the odd-dimensional case (`d = 2n+1`,
`n ≥ 1`) of Ryabogin's theorem, i.e. the deliverable

```
theorem odd_curve_exists (n : ℕ) (hn : 1 ≤ n) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ h : ℝ → ℝ, ContDiff ℝ ∞ h →
      Function.support h ⊆ Set.Ioo (1 - 2 * (1 / 10)) (1 - (1 / 10)) →
      (∀ s, |h s| ≤ ε) → (∀ s, |deriv h s| ≤ ε) → (∀ s, |deriv (deriv h) s| ≤ ε) →
      flat-at-the-left-edge → h ≠ 0 →
      ∃ C : ℝ, ∃ x y : ℝ → ℝ, IsEnvelopeCurve h x y ∧ (A) ∧ (B)
```

of `Submission/Odd/Composition.lean`.

## What this file fixes

* `rad`, `momentA`, `momentB` — the two moment integrals `(A)`, `(B)` of the paper, with the
  profile realised as `Work.OddEnvelope.envelopeProfile h x y`;
* `MomentEqs` — both equations on the slopes `0 < s ≤ 1`, in the exact shape consumed by
  `Submission.Odd.Composition`;
* `IsOddBump` — the hypothesis package on the bump `h` *exactly as in the deliverable*
  (`C²`-smallness only);
* `IsOddBumpCn2` — the same package with `C^{n+2}`-smallness, which is what the paper's
  argument actually uses (see `Work.OddCurveB.Smallness`, and the module README);
* `scX`, `scY`, `scD` — the *shifted-chord curve of the semicircle*: the intersections of the
  line `t ↦ s t + h s` with the unit semicircle.  Its profile is the semicircle; it is the
  naive candidate for the deliverable's curve, and `Work.OddCurveB.Semicircle` proves that it
  satisfies the two moment equations for *no* compactly supported `h ≠ 0`.

## Conventions

`f` is the profile (the deliverable uses `Work.OddEnvelope.envelopeProfile h x y`); `s` is the
slope; `t` is the first coordinate.  `tau = 1/10` is the paper's threshold:
`1 - 2 * (1/10) = 4/5 = 1 - 2τ` is the window's left edge and `1 - (1/10) = 9/10 = 1 - τ` its
right edge.
-/

namespace Work.OddCurveB

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

/-- The paper's threshold `τ = 1/10`. -/
def tau : ℝ := 1 / 10

/-- The left edge `1 - 2τ = 4/5` of the perturbation window. -/
def lo : ℝ := 1 - 2 * (1 / 10 : ℝ)

/-- The right edge `1 - τ = 9/10` of the perturbation window. -/
def hi : ℝ := 1 - (1 / 10 : ℝ)

/-- The radicand `f t ^ 2 - (s t + h s) ^ 2` of both moment equations. -/
def rad (h f : ℝ → ℝ) (s t : ℝ) : ℝ := f t ^ 2 - (s * t + h s) ^ 2

/-- The volume moment integral `(A)`: `∫_{-x s}^{y s} (f² - L²)^{n+1/2}`. -/
def momentA (n : ℕ) (h x y f : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ t in (-x s)..(y s), rad h f s t ^ n * Real.sqrt (rad h f s t)

/-- The centroid moment integral `(B)`: `∫_{-x s}^{y s} (f² - L²)^{n-1/2} ∂_s L`. -/
def momentB (n : ℕ) (h x y f : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ t in (-x s)..(y s), rad h f s t ^ (n - 1) * Real.sqrt (rad h f s t) * (t + deriv h s)

/-- The two moment equations for the envelope profile, on the slopes `0 < s ≤ 1`, in the exact
shape of the deliverable. -/
def MomentEqs (n : ℕ) (C : ℝ) (h x y : ℝ → ℝ) : Prop :=
  (∀ s : ℝ, 0 < s → s ≤ 1 →
      momentA n h x y (Work.OddEnvelope.envelopeProfile h x y) s = C / Real.sqrt (1 + s ^ 2)) ∧
    (∀ s : ℝ, 0 < s → s ≤ 1 →
      momentB n h x y (Work.OddEnvelope.envelopeProfile h x y) s = 0)

/-- **The hypothesis package of the deliverable on the bump `h`** (smoothness, support inside
the open window `(4/5, 9/10)`, the three `ε`-bounds, flatness on a right neighbourhood of
`4/5`). -/
def IsOddBump (ε : ℝ) (h : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ h ∧
    Function.support h ⊆ Set.Ioo (1 - 2 * (1 / 10 : ℝ)) (1 - (1 / 10 : ℝ)) ∧
    (∀ s : ℝ, |h s| ≤ ε) ∧
    (∀ s : ℝ, |deriv h s| ≤ ε) ∧
    (∀ s : ℝ, |deriv (deriv h) s| ≤ ε) ∧
    (∃ η : ℝ, 0 < η ∧ ∀ s : ℝ, 1 - 2 * (1 / 10 : ℝ) ≤ s →
      s < 1 - 2 * (1 / 10 : ℝ) + η → h s = 0)

/-- The same package with `C^{n+2}`-smallness: this is what the paper's perturbation argument
actually needs (its inhomogeneities `Θ`, `𝚵` involve `h^{(n+1)}` and `h^{(n+2)}`). -/
def IsOddBumpCn2 (n : ℕ) (ε : ℝ) (h : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ h ∧
    Function.support h ⊆ Set.Ioo (1 - 2 * (1 / 10 : ℝ)) (1 - (1 / 10 : ℝ)) ∧
    (∀ k : ℕ, k ≤ n + 3 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ ε) ∧
    (∃ η : ℝ, 0 < η ∧ ∀ s : ℝ, 1 - 2 * (1 / 10 : ℝ) ≤ s →
      s < 1 - 2 * (1 / 10 : ℝ) + η → h s = 0)

lemma IsOddBumpCn2.toIsOddBump {n : ℕ} {ε : ℝ} {h : ℝ → ℝ} (H : IsOddBumpCn2 n ε h) :
    IsOddBump ε h := by
  obtain ⟨hc, hs, hb, hf⟩ := H
  refine ⟨hc, hs, fun s => ?_, fun s => ?_, fun s => ?_, hf⟩
  · simpa using hb 0 (Nat.zero_le _) s
  · simpa [iteratedDeriv_one] using hb 1 (by omega) s
  · have h2 : iteratedDeriv 2 h s = deriv (deriv h) s := by
      rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]
    rw [← h2]
    exact hb 2 (by omega) s

/-- The "distance" factor `√(1 + s² - h s²)` of the shifted chord: half the chord length times
`√(1+s²)`. -/
def scD (h : ℝ → ℝ) (s : ℝ) : ℝ := Real.sqrt (1 + s ^ 2 - h s ^ 2)

/-- The right endpoint of the shifted chord: the larger root of
`semicircle t = s t + h s`. -/
def scY (h : ℝ → ℝ) (s : ℝ) : ℝ := (scD h s - s * h s) / (1 + s ^ 2)

/-- The left endpoint of the shifted chord (`-scX h s` is the smaller root of
`semicircle t = s t + h s`). -/
def scX (h : ℝ → ℝ) (s : ℝ) : ℝ := (scD h s + s * h s) / (1 + s ^ 2)

/-- The first coordinate of the foot of the perpendicular from the origin to the line
`t ↦ s t + h s`. -/
def scT (h : ℝ → ℝ) (s : ℝ) : ℝ := -(s * h s) / (1 + s ^ 2)

/-- The squared distance from the origin to the line `t ↦ s t + h s`. -/
def scDelta2 (h : ℝ → ℝ) (s : ℝ) : ℝ := h s ^ 2 / (1 + s ^ 2)

lemma tau_eq : tau = 1 / 10 := rfl
lemma lo_eq : lo = 4 / 5 := by norm_num [lo]
lemma hi_eq : hi = 9 / 10 := by norm_num [hi]

lemma rad_def (h f : ℝ → ℝ) (s t : ℝ) : rad h f s t = f t ^ 2 - (s * t + h s) ^ 2 := rfl

lemma momentA_def (n : ℕ) (h x y f : ℝ → ℝ) (s : ℝ) :
    momentA n h x y f s =
      ∫ t in (-x s)..(y s), rad h f s t ^ n * Real.sqrt (rad h f s t) := rfl

lemma momentB_def (n : ℕ) (h x y f : ℝ → ℝ) (s : ℝ) :
    momentB n h x y f s =
      ∫ t in (-x s)..(y s), rad h f s t ^ (n - 1) * Real.sqrt (rad h f s t) *
        (t + deriv h s) := rfl

lemma MomentEqs_def (n : ℕ) (C : ℝ) (h x y : ℝ → ℝ) :
    MomentEqs n C h x y ↔
      ((∀ s : ℝ, 0 < s → s ≤ 1 →
        ∫ t in (-x s)..(y s),
            (Work.OddEnvelope.envelopeProfile h x y t ^ 2 - (s * t + h s) ^ 2) ^ n *
              Real.sqrt (Work.OddEnvelope.envelopeProfile h x y t ^ 2 - (s * t + h s) ^ 2)
          = C / Real.sqrt (1 + s ^ 2)) ∧
       (∀ s : ℝ, 0 < s → s ≤ 1 →
        ∫ t in (-x s)..(y s),
            (Work.OddEnvelope.envelopeProfile h x y t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) *
              Real.sqrt (Work.OddEnvelope.envelopeProfile h x y t ^ 2 - (s * t + h s) ^ 2) *
              (t + deriv h s) = 0)) := by
  constructor
  · intro H
    exact ⟨fun s hs hs1 => H.1 s hs hs1, fun s hs hs1 => H.2 s hs hs1⟩
  · intro H
    exact ⟨fun s hs hs1 => H.1 s hs hs1, fun s hs hs1 => H.2 s hs hs1⟩

/-- The radicand of the semicircle profile cut by the shifted line: pure algebra, `1 - |P|²`
with `P` on the line `t ↦ s t + h s`, written about the foot of the perpendicular. -/
lemma rad_semicircle_eq (h : ℝ → ℝ) (s t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    rad h Work.OddEnvelope.semicircle s t
      = (1 - h s ^ 2 / (1 + s ^ 2)) - (1 + s ^ 2) * (t - scT h s) ^ 2 := by
  have hle : (0 : ℝ) ≤ 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
  have hsq : Work.OddEnvelope.semicircle t ^ 2 = 1 - t ^ 2 := by
    rw [Work.OddEnvelope.semicircle]; exact Real.sq_sqrt hle
  have hs : (0 : ℝ) < 1 + s ^ 2 := by positivity
  simp only [rad, scT]
  rw [hsq]
  field_simp
  ring

/-- The right endpoint of the shifted chord is the foot of the perpendicular plus
`scD / (1+s²)`; the left endpoint `-scX` is the foot minus the same quantity. -/
lemma scY_eq (h : ℝ → ℝ) (s : ℝ) :
    scY h s = scT h s + scD h s / (1 + s ^ 2) := by
  simp only [scY, scT]; ring

lemma neg_scX_eq (h : ℝ → ℝ) (s : ℝ) :
    -(scX h s) = scT h s - scD h s / (1 + s ^ 2) := by
  simp only [scX, scT]; ring

/-- The squared distance from the origin to the shifted chord: `scD² / (1+s²)`. -/
lemma scDelta2_eq (h : ℝ → ℝ) (s : ℝ) :
    scDelta2 h s = h s ^ 2 / (1 + s ^ 2) := rfl

end

end Work.OddCurveB

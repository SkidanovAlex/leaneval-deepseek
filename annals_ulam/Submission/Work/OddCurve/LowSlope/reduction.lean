import Mathlib
import Submission.Work.OddCurve.LowSlope.Defs
import Submission.Work.OddCurve.LowSlope.cl1

/-!
# The low-slope step of the odd case: from the section conditions to the moment equations

On a slope range `[a,b] ⊂ (0,∞)` where the bump vanishes (`h s = 0`, `h' s = 0`), the two
equations that the spherical-Radon construction of the paper's Step 3 produces are the *centroid*
condition `centIntegral = 0` (`(cmass)`) and the *inertia* condition
`(1+s²)^{3/2} inertiaIntegral = ballInertiaConst n` (`(i1)`).  `Work.OddCurve.LowSlope.cl1` then
converts them — together with the moment equation `(A)` at the single slope `b`, which the
transition-window construction supplies — into the moment equations `(A)`, `(B)` with the constant
`(2n+1) * ballInertiaConst n` on the whole range.

This file is the bookkeeping between the two vocabularies: the section integrals (unshifted, with
`rad0`) and the moment integrals `Work.OddCurve.momentA`/`momentB` (with `rad` and `h`).
-/

namespace Work.OddCurve.LowSlope

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

/-- On the range where `h` vanishes, the shifted inertia integrand is the unshifted one. -/
lemma inertiaIntegral_eq_shifted {n : ℕ} {h f x y : ℝ → ℝ} {s : ℝ} (hs : h s = 0)
    (hds : deriv h s = 0) :
    (∫ t in (-(x s))..(y s), (t + deriv h s) ^ 2 *
        Work.OddCurve.rad h f s t ^ (n - 1) * Real.sqrt (Work.OddCurve.rad h f s t)) =
      inertiaIntegral n f x y s := by
  rw [inertiaIntegral]
  apply intervalIntegral.integral_congr
  intro t _
  show (t + deriv h s) ^ 2 * Work.OddCurve.rad h f s t ^ (n - 1) *
      Real.sqrt (Work.OddCurve.rad h f s t) =
      t ^ 2 * rad0 f s t ^ (n - 1) * Real.sqrt (rad0 f s t)
  rw [rad0_eq_rad h f hs t, hds, add_zero]

/-- **The low-slope moment equations** from the two section conditions and the value of `(A)` at
the right end of the range. -/
theorem lowSlope_momentEqs (n : ℕ) (hn : 1 ≤ n) {h x y : ℝ → ℝ}
    (H : Work.OddEnvelope.IsEnvelopeCurve h x y)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hzero : ∀ s ∈ Set.Icc a b, h s = 0) (hder0 : ∀ s ∈ Set.Icc a b, deriv h s = 0)
    (hcent : ∀ s ∈ Set.Icc a b,
      centIntegral n (Work.OddEnvelope.envelopeProfile h x y) x y s = 0)
    (hiner : ∀ s ∈ Set.Icc a b,
      (1 + s ^ 2) * Real.sqrt (1 + s ^ 2) *
        inertiaIntegral n (Work.OddEnvelope.envelopeProfile h x y) x y s = ballInertiaConst n)
    (hvalb : Work.OddCurve.momentA n h x y (Work.OddEnvelope.envelopeProfile h x y) b =
      ((2 * (n : ℝ) + 1) * ballInertiaConst n) / Real.sqrt (1 + b ^ 2)) :
    (∀ s ∈ Set.Icc a b,
        Work.OddCurve.momentA n h x y (Work.OddEnvelope.envelopeProfile h x y) s =
          ((2 * (n : ℝ) + 1) * ballInertiaConst n) / Real.sqrt (1 + s ^ 2)) ∧
      (∀ s ∈ Set.Icc a b,
        Work.OddCurve.momentB n h x y (Work.OddEnvelope.envelopeProfile h x y) s = 0) := by
  refine ⟨?_, ?_⟩
  · refine cl1 n hn H ha hab (fun s hs => ?_)
      (fun s hs => ?_) hvalb
    · rw [momentB_eq_centIntegral (hzero s hs) (hder0 s hs)]
      exact hcent s hs
    · rw [inertiaIntegral_eq_shifted (hzero s hs) (hder0 s hs)]
      exact hiner s hs
  · intro s hs
    rw [momentB_eq_centIntegral (hzero s hs) (hder0 s hs)]
    exact hcent s hs

end

end Work.OddCurve.LowSlope

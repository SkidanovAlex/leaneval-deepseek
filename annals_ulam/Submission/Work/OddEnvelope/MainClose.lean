import Submission.Work.OddEnvelope.Main
import Submission.Work.OddEnvelope.Close.isEnvelopeCurve_of_close

/-!
# The envelope profile from a `C²`-close chord curve

This is the form of the deliverable in which the four shape conditions of `IsEnvelopeCurve`
(`mono_x`, `mono_y`, `shape_x`, `shape_y`) are *derived* from `C²`-closeness of the chord curve
to the semicircle.  This is the hypothesis that the Volterra construction of the odd case
(`Work.OddVolterra`) is expected to produce: `x`, `y` are `C²`-close to `profileX`, `h` is a small
bump, and `x = y = profileX` outside the perturbed window.
-/

namespace Work.OddEnvelope

noncomputable section

open Set Filter
open scoped Topology ContDiff

/-- **The deliverable of `Work.OddEnvelope`, from `C²`-closeness to the semicircle.** -/
theorem odd_envelope_profile_of_close {h x y : ℝ → ℝ} {δ : ℝ} (hδ : δ ≤ 1 / 100)
    (hx_smooth : ContDiffOn ℝ ∞ x (Set.Ioi 0))
    (hy_smooth : ContDiffOn ℝ ∞ y (Set.Ioi 0))
    (hh_smooth : ContDiffOn ℝ ∞ h (Set.Ioi 0))
    (hx_deriv : ∀ s, 0 < s → deriv x s < 0) (hy_deriv : ∀ s, 0 < s → deriv y s < 0)
    (hx_tend : Tendsto x (𝓝[>] (0 : ℝ)) (𝓝 1))
    (hy_tend : Tendsto y (𝓝[>] (0 : ℝ)) (𝓝 1))
    (hx_tail : ∀ s, 1 - tau ≤ s → x s = profileX s)
    (hy_tail : ∀ s, 1 - tau ≤ s → y s = profileX s)
    (hh_zero : h 0 = 0)
    (hh_supp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau))
    (hx_close : ∀ s, 0 < s → |x s - profileX s| ≤ δ ∧
      |deriv x s - deriv profileX s| ≤ δ ∧
      |deriv (deriv x) s - deriv (deriv profileX) s| ≤ δ)
    (hy_close : ∀ s, 0 < s → |y s - profileX s| ≤ δ ∧
      |deriv y s - deriv profileX s| ≤ δ ∧
      |deriv (deriv y) s - deriv (deriv profileX) s| ≤ δ)
    (hh_close : ∀ s, |h s| ≤ δ ∧ |deriv h s| ≤ δ ∧ |deriv (deriv h) s| ≤ δ) :
    ∃ f : ℝ → ℝ,
      Function.support f ⊆ Set.Icc (-1 : ℝ) 1 ∧ f (-1) = 0 ∧ f 1 = 0 ∧
      (∀ t ∈ Set.Ioo (-1 : ℝ) 1, 0 < f t) ∧
      ContDiffOn ℝ ∞ f (Set.Ioo (-1 : ℝ) 1) ∧
      StrictConcaveOn ℝ (Set.Icc (-1 : ℝ) 1) f ∧
      ContinuousOn f (Set.Icc (-1 : ℝ) 1) ∧
      (∀ s, 0 < s → f (y s) = s * y s + h s) ∧
      (∀ s, 0 < s → f (-(x s)) = -(s * (-(x s)) + h s)) ∧
      (∀ s, 0 < s → -(x s) ∈ Set.Ioo (-1 : ℝ) 1 ∧ y s ∈ Set.Ioo (-1 : ℝ) 1) ∧
      (∀ s, 0 < s → ∀ t ∈ Set.Ioo (-(x s)) (y s), 0 < f t ^ 2 - (s * t + h s) ^ 2) ∧
      ((∀ t : ℝ, f (-t) = f t) ↔
        ∀ u : ℝ, 0 < u →
          y u * (slopeRight x (y u) - u) - h (slopeRight x (y u)) - h u = 0) :=
  odd_envelope_profile (Work.OddEnvelope.Close.isEnvelopeCurve_of_close hδ hx_smooth hy_smooth
    hh_smooth hx_deriv hy_deriv hx_tend hy_tend hx_tail hy_tail hh_zero hh_supp
    hx_close hy_close hh_close)

end

end Work.OddEnvelope

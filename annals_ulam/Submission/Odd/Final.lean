import Mathlib
import Submission.Odd.AllSlopes
import Submission.Odd.Assembly
import Submission.Work.OddEnvelope.Main

/-!
# Endgame of the odd-dimensional case

Given

* the two moment equations on the slopes `0 < s ≤ 1` (the output of the Volterra step),
* the chord-endpoint curve `(x, y)` agreeing with the semicircle for `s ≥ 1 - 1/10`, and
* the profile data of `f` (strictly concave, positive inside, vanishing at the ends),

`odd_floating_family_data_of_curve` produces `Submission.Odd.OddFamilyData`: for `s ≥ 1` the
profile is the semicircle on the corresponding chord, so `moment_equations_all_slopes` upgrades
the two equations to all slopes `s > 0`, and `family_data_of_moment_equations` converts those
plus the geometry into the family data.

`odd_floating_family_data_of_envelope_curve` is the same statement with the profile supplied by
the chapter `Work.OddEnvelope` (`Work.OddEnvelope.envelopeProfile` and its specification), so
that the only remaining input of the odd case of Ryabogin's theorem is the curve `(x, y)` solving
the odd Volterra system together with its two moment equations on `(0,1]`.
-/

namespace Submission.Odd

open MeasureTheory
open scoped BigOperators ContDiff Pointwise RealInnerProductSpace

set_option autoImplicit false

variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

theorem odd_floating_family_data_of_curve
    (hd : 3 ≤ d) [NeZero d] (hdodd : Odd d) (n : ℕ) (hdn : d = 2 * n + 1) (hn : 1 ≤ n)
    {C : ℝ} {f h x y : ℝ → ℝ}
    (hf_support : Function.support f ⊆ Set.Icc (-1 : ℝ) 1)
    (hf_cont : ContDiffOn ℝ ∞ f (Set.Ioo (-1 : ℝ) 1))
    (hf_strict : StrictConcaveOn ℝ (Set.Icc (-1 : ℝ) 1) f)
    (hf_contIcc : ContinuousOn f (Set.Icc (-1 : ℝ) 1))
    (hf_left : f (-1) = 0) (hf_right : f 1 = 0)
    (hf_pos : ∀ t ∈ Set.Ioo (-1 : ℝ) 1, 0 < f t)
    (hh_cont : ContDiff ℝ ∞ h) (h0 : h 0 = 0) (hhne : ∃ s : ℝ, 0 < s ∧ h s ≠ 0)
    (hh_supp : Function.support h ⊆ Set.Icc (1 - 2 * (1 / 10 : ℝ)) (1 - (1 / 10 : ℝ)))
    (hh_zero : ∀ s : ℝ, 1 - (1 / 10 : ℝ) ≤ s → h s = 0)
    (hx_pos : ∀ s : ℝ, 0 < s → 0 < x s) (hy_pos : ∀ s : ℝ, 0 < s → 0 < y s)
    (hx_eq : ∀ s : ℝ, 1 - (1 / 10 : ℝ) ≤ s → x s = 1 / Real.sqrt (1 + s ^ 2))
    (hy_eq : ∀ s : ℝ, 1 - (1 / 10 : ℝ) ≤ s → y s = 1 / Real.sqrt (1 + s ^ 2))
    (hinside : ∀ s : ℝ, 0 < s → -x s ∈ Set.Ioo (-1 : ℝ) 1 ∧ y s ∈ Set.Ioo (-1 : ℝ) 1)
    (hroot_l : ∀ s : ℝ, 0 < s → f (-x s) = -(s * (-x s) + h s))
    (hroot_r : ∀ s : ℝ, 0 < s → f (y s) = s * y s + h s)
    (hA_small : ∀ s : ℝ, 0 < s → s ≤ 1 →
      (∫ t in (-x s)..(y s),
        (f t ^ 2 - (s * t + h s) ^ 2) ^ n * Real.sqrt (f t ^ 2 - (s * t + h s) ^ 2)) =
        C / Real.sqrt (1 + s ^ 2))
    (hB_small : ∀ s : ℝ, 0 < s → s ≤ 1 →
      (∫ t in (-x s)..(y s),
        (f t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - (s * t + h s) ^ 2) *
          (t + deriv h s)) = 0) :
    OddFamilyData d := by
  obtain ⟨hA, hB, _hC⟩ := moment_equations_all_slopes (f := f) (h := h) (x := x) (y := y)
    (C := C) n hx_eq hy_eq hh_zero hroot_l hroot_r hf_contIcc hA_small hB_small
  exact family_data_of_moment_equations (d := d) hd hdodd n hdn hn hf_support hf_cont
    hf_strict hf_contIcc hf_left hf_right hf_pos hh_cont h0 hhne hh_supp hx_pos hy_pos
    hinside hroot_l hroot_r hA hB

/-- The endgame with the profile built by `Work.OddEnvelope.envelopeProfile`. -/
theorem odd_floating_family_data_of_envelope_curve
    (hd : 3 ≤ d) [NeZero d] (hdodd : Odd d) (n : ℕ) (hdn : d = 2 * n + 1) (hn : 1 ≤ n)
    {C : ℝ} {h x y : ℝ → ℝ}
    (hh_cont : ContDiff ℝ ∞ h) (hhne : ∃ s : ℝ, 0 < s ∧ h s ≠ 0)
    (hh_zero : ∀ s : ℝ, 1 - (1 / 10 : ℝ) ≤ s → h s = 0)
    (H : Work.OddEnvelope.IsEnvelopeCurve h x y)
    (hA_small : ∀ s : ℝ, 0 < s → s ≤ 1 →
      (∫ t in (-x s)..(y s),
        (Work.OddEnvelope.envelopeProfile h x y t ^ 2 - (s * t + h s) ^ 2) ^ n *
          Real.sqrt (Work.OddEnvelope.envelopeProfile h x y t ^ 2 - (s * t + h s) ^ 2)) =
        C / Real.sqrt (1 + s ^ 2))
    (hB_small : ∀ s : ℝ, 0 < s → s ≤ 1 →
      (∫ t in (-x s)..(y s),
        (Work.OddEnvelope.envelopeProfile h x y t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) *
          Real.sqrt (Work.OddEnvelope.envelopeProfile h x y t ^ 2 - (s * t + h s) ^ 2) *
          (t + deriv h s)) = 0) :
    OddFamilyData d := by
  obtain ⟨hf_supp, hf_l, hf_r, hf_pos, hf_sm, hf_strict, hf_contIcc, hroot_r, hroot_l,
    hinside, _hnondeg, _hev, _hev2⟩ :=
    Work.OddEnvelope.envelopeProfile_spec (h := h) (x := x) (y := y) H
  have hx_pos : ∀ s : ℝ, 0 < s → 0 < x s :=
    fun s hs => (Work.OddEnvelope.IsEnvelopeCurve.toChordCurve_x H).pos hs
  have hy_pos : ∀ s : ℝ, 0 < s → 0 < y s :=
    fun s hs => (Work.OddEnvelope.IsEnvelopeCurve.toChordCurve_y H).pos hs
  have hx_eq : ∀ s : ℝ, 1 - (1 / 10 : ℝ) ≤ s → x s = 1 / Real.sqrt (1 + s ^ 2) := by
    intro s hs
    exact H.x_tail s (by rw [Work.OddEnvelope.tau]; exact hs)
  have hy_eq : ∀ s : ℝ, 1 - (1 / 10 : ℝ) ≤ s → y s = 1 / Real.sqrt (1 + s ^ 2) := by
    intro s hs
    exact H.y_tail s (by rw [Work.OddEnvelope.tau]; exact hs)
  exact odd_floating_family_data_of_curve (d := d) hd hdodd n hdn hn
    (f := Work.OddEnvelope.envelopeProfile h x y)
    hf_supp hf_sm hf_strict hf_contIcc hf_l hf_r hf_pos hh_cont H.h_zero hhne H.h_support
    hh_zero hx_pos hy_pos hx_eq hy_eq hinside hroot_l hroot_r hA_small hB_small

end Submission.Odd

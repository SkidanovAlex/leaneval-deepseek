import Mathlib
import Submission.Work.Odd.odd_semicircle_moment_equations
import Submission.Work.Odd.profile_eq_semicircle_of_roots
import Submission.Work.Odd.ball_moment_identity

/-!
# The two moment equations for every slope

The constructive part of the odd case produces the curve `x, y` and the two moment equations
on `(0,1]`.  For the remaining slopes `s ≥ 1` the profile coincides with the semicircle on the
corresponding chord: the roots are the semicircle's and `h` vanishes there, so
`profile_eq_semicircle_of_roots` applies and `odd_semicircle_moment_equations` evaluates both
integrals.  Comparing at `s = 1` identifies the constant with the one coming from the reference
lemma `ball_moment_identity`.
-/

namespace Submission.Odd

open MeasureTheory
open scoped ContDiff Pointwise

set_option autoImplicit false

theorem moment_equations_all_slopes {f h x y : ℝ → ℝ} {C : ℝ} (n : ℕ)
    (hx_eq : ∀ s : ℝ, 1 - (1 / 10 : ℝ) ≤ s → x s = 1 / Real.sqrt (1 + s ^ 2))
    (hy_eq : ∀ s : ℝ, 1 - (1 / 10 : ℝ) ≤ s → y s = 1 / Real.sqrt (1 + s ^ 2))
    (hh_zero : ∀ s : ℝ, 1 - (1 / 10 : ℝ) ≤ s → h s = 0)
    (hroot_l : ∀ s : ℝ, 0 < s → f (-x s) = -(s * (-x s) + h s))
    (hroot_r : ∀ s : ℝ, 0 < s → f (y s) = s * y s + h s)
    (hf_cont : ContinuousOn f (Set.Icc (-1 : ℝ) 1))
    (hA_small : ∀ s : ℝ, 0 < s → s ≤ 1 →
      (∫ t in (-x s)..(y s),
        (f t ^ 2 - (s * t + h s) ^ 2) ^ n * Real.sqrt (f t ^ 2 - (s * t + h s) ^ 2)) =
        C / Real.sqrt (1 + s ^ 2))
    (hB_small : ∀ s : ℝ, 0 < s → s ≤ 1 →
      (∫ t in (-x s)..(y s),
        (f t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - (s * t + h s) ^ 2) *
          (t + deriv h s)) = 0) :
    (∀ s : ℝ, 0 < s →
      (∫ t in (-x s)..(y s),
        (f t ^ 2 - (s * t + h s) ^ 2) ^ n * Real.sqrt (f t ^ 2 - (s * t + h s) ^ 2)) =
        (∫ u in (-1 : ℝ)..1, (1 - u ^ 2) ^ n * Real.sqrt (1 - u ^ 2)) / Real.sqrt (1 + s ^ 2)) ∧
    (∀ s : ℝ, 0 < s →
      (∫ t in (-x s)..(y s),
        (f t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - (s * t + h s) ^ 2) *
          (t + deriv h s)) = 0) ∧
    C = ∫ u in (-1 : ℝ)..1, (1 - u ^ 2) ^ n * Real.sqrt (1 - u ^ 2) := by
  have ha : (0 : ℝ) < 1 - (1 / 10 : ℝ) := by norm_num
  -- the profile is the semicircle on the chord interval of the large slopes
  have hprof := Work.Odd.profile_eq_semicircle_of_roots (f := f) (h := h) (x := x) (y := y)
    (a := 1 - (1 / 10 : ℝ)) ha hx_eq hy_eq hh_zero hroot_l hroot_r hf_cont
  -- hence both equations hold for `s ≥ 1`
  have hbig := Work.Odd.odd_semicircle_moment_equations (f := f) (h := h) (x := x) (y := y) n
    hprof hx_eq hy_eq (fun s hs => hh_zero s hs.le)
  have hC : C = ∫ u in (-1 : ℝ)..1, (1 - u ^ 2) ^ n * Real.sqrt (1 - u ^ 2) := by
    have h1 := hA_small 1 (by norm_num) (le_refl 1)
    have h2 := (hbig.1 1 (le_refl 1))
    rw [show (1:ℝ) + 1 ^ 2 = 2 by norm_num] at h1 h2
    have hsqrt2 : Real.sqrt 2 ≠ 0 := by positivity
    have : C / Real.sqrt 2 = (∫ u in (-1 : ℝ)..1, (1 - u ^ 2) ^ n * Real.sqrt (1 - u ^ 2)) / Real.sqrt 2 := by
      rw [← h1, h2]
    exact (div_left_inj' hsqrt2).mp this
  refine ⟨fun s hs => ?_, fun s hs => ?_, hC⟩
  · rcases lt_or_ge s 1 with hlt | hge
    · rw [hA_small s hs hlt.le, hC]
    · exact hbig.1 s hge
  · rcases lt_or_ge s 1 with hlt | hge
    · exact hB_small s hs hlt.le
    · exact hbig.2 s hge

end Submission.Odd

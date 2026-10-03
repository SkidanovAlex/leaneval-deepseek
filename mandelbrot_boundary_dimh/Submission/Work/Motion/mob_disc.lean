import Mathlib
import Submission.Work.Motion.disc_autom

/-!
# `mob a` maps the unit disc into itself and is holomorphic there

For `‖a‖ < 1`, the Möbius transformation `mob a t = (t - a) / (1 - conj a * t)`
sends the open unit disc into itself, is complex differentiable on the disc, and
sends `a` to `0`.

The key elementary identity is

`normSq (1 - conj a * t) - normSq (t - a) = (1 - normSq a) * (1 - normSq t)`,

which shows both that the denominator does not vanish on the disc and that
`‖t - a‖ < ‖1 - conj a * t‖` there.
-/

namespace Work.Motion

open Metric Set
open scoped ComplexConjugate

/-- The elementary identity underlying the fact that `mob a` preserves the unit
disc: the difference of the squared norms of denominator and numerator. -/
theorem normSq_one_sub_conj_mul (a t : ℂ) :
    Complex.normSq (1 - conj a * t) - Complex.normSq (t - a)
      = (1 - Complex.normSq a) * (1 - Complex.normSq t) := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

/-- The denominator `1 - conj a * t` does not vanish on the unit disc. -/
theorem one_sub_conj_mul_ne_zero {a t : ℂ} (ha : ‖a‖ < 1) (ht : ‖t‖ < 1) :
    1 - conj a * t ≠ 0 := by
  have haSq : Complex.normSq a < 1 := by
    rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg a]
  have htSq : Complex.normSq t < 1 := by
    rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg t]
  have hpos : 0 < Complex.normSq (1 - conj a * t) := by
    have h2 : 0 < (1 - Complex.normSq a) * (1 - Complex.normSq t) :=
      mul_pos (by linarith) (by linarith)
    have h3 := normSq_one_sub_conj_mul a t
    nlinarith [Complex.normSq_nonneg (t - a)]
  intro h
  rw [h, Complex.normSq_zero] at hpos
  exact lt_irrefl 0 hpos

theorem mob_disc {a : ℂ} (ha : ‖a‖ < 1) :
    Set.MapsTo (mob a) (Metric.ball 0 1) (Metric.ball 0 1) ∧
    DifferentiableOn ℂ (mob a) (Metric.ball 0 1) ∧
    mob a a = 0 := by
  have haSq : Complex.normSq a < 1 := by
    rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg a]
  have hnorm : ∀ t : ℂ, ‖t‖ < 1 → ‖mob a t‖ < 1 := by
    intro t ht
    have htSq : Complex.normSq t < 1 := by
      rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg t]
    have hlt : Complex.normSq (t - a) < Complex.normSq (1 - conj a * t) := by
      have h2 : 0 < (1 - Complex.normSq a) * (1 - Complex.normSq t) :=
        mul_pos (by linarith) (by linarith)
      have h3 := normSq_one_sub_conj_mul a t
      linarith
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hlt
    have hlt2 : ‖t - a‖ < ‖1 - conj a * t‖ := by
      rw [sq_lt_sq, abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] at hlt
      exact hlt
    rw [mob_apply, norm_div,
      div_lt_one (norm_pos_iff.mpr (one_sub_conj_mul_ne_zero ha ht))]
    exact hlt2
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    rw [Metric.mem_ball, dist_zero_right] at ht ⊢
    exact hnorm t ht
  · refine DifferentiableOn.div ?_ ?_ ?_
    · exact (differentiable_id.sub_const a).differentiableOn
    · exact ((differentiable_const (1 : ℂ)).sub
        ((differentiable_const (conj a)).mul differentiable_id)).differentiableOn
    · intro t ht
      rw [Metric.mem_ball, dist_zero_right] at ht
      exact one_sub_conj_mul_ne_zero ha ht
  · simp [mob_apply]

end Work.Motion

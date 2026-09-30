import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open MeasureTheory intervalIntegral
open scoped ComplexConjugate

/-- Conjugation commutes with the interval integral (both orientations of the interval). -/
private lemma intervalIntegral_conj' (f : ℝ → ℂ) (a b : ℝ) :
    (∫ x in a..b, (starRingEnd ℂ) (f x)) = (starRingEnd ℂ) (∫ x in a..b, f x) := by
  rcases le_total a b with hab | hab
  · rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
    exact integral_conj
  · rw [intervalIntegral.integral_of_ge hab, intervalIntegral.integral_of_ge hab]
    rw [integral_conj]
    simp

set_option linter.unusedVariables false in
/-- The squared modulus of an interval integral expands as the real part of the double integral
of `f t * conj (f s)`. -/
theorem frozen_l2_sq_expand (c d : ℝ) (f : ℝ → ℂ) (hf : Continuous f) :
    ‖∫ t in c..d, f t‖ ^ 2
      = (∫ t in c..d, ∫ s in c..d, f t * (starRingEnd ℂ) (f s)).re := by
  set I : ℂ := ∫ t in c..d, f t with hI
  -- The inner integral factors: `∫ s, f t * conj (f s) = f t * conj I`.
  have hinner : ∀ t : ℝ, (∫ s in c..d, f t * (starRingEnd ℂ) (f s))
      = f t * (starRingEnd ℂ) I := by
    intro t
    rw [intervalIntegral.integral_const_mul, hI, intervalIntegral_conj']
  -- The outer integral factors: `∫ t, f t * conj I = I * conj I`.
  have houter : (∫ t in c..d, ∫ s in c..d, f t * (starRingEnd ℂ) (f s))
      = I * (starRingEnd ℂ) I := by
    rw [show (∫ t in c..d, ∫ s in c..d, f t * (starRingEnd ℂ) (f s))
          = ∫ t in c..d, f t * (starRingEnd ℂ) I from
        intervalIntegral.integral_congr (fun t _ => hinner t)]
    rw [hI, intervalIntegral.integral_mul_const]
  rw [houter]
  -- `I * conj I = (‖I‖^2 : ℂ)`.
  have hz : (I * (starRingEnd ℂ) I).re = ‖I‖ ^ 2 := by
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  rw [hz]

end Work.BMF

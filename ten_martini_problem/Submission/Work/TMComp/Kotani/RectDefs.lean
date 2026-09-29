import Mathlib

/-!
# The boundary integral of a rectangle

This file introduces the integral of a function `f : ℂ → ℂ` around the boundary of the rectangle
`[a,b] × [c,d]` (oriented counterclockwise), together with the elementary linearity lemmas needed
to manipulate it.
-/

namespace Work.TMComp.Kotani

noncomputable section

open MeasureTheory intervalIntegral Set

/-- The integral of `f` around the boundary of the rectangle `[a,b] × [c,d]`, oriented
counterclockwise.  This is the left-hand side of `Complex.integral_boundary_rect_eq_zero_of_differentiableOn`. -/
def rectBdIntegral (a b c d : ℝ) (f : ℂ → ℂ) : ℂ :=
  (∫ x : ℝ in a..b, f ((x : ℂ) + (c : ℂ) * Complex.I))
    - (∫ x : ℝ in a..b, f ((x : ℂ) + (d : ℂ) * Complex.I))
    + Complex.I * (∫ y : ℝ in c..d, f ((b : ℂ) + (y : ℂ) * Complex.I))
    - Complex.I * (∫ y : ℝ in c..d, f ((a : ℂ) + (y : ℂ) * Complex.I))

@[simp] lemma rectBdIntegral_zero (a b c d : ℝ) :
    rectBdIntegral a b c d (fun _ => 0) = 0 := by
  simp [rectBdIntegral]

lemma rectBdIntegral_add (a b c d : ℝ) (f g : ℂ → ℂ)
    (hf1 : IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (c : ℂ) * Complex.I)) volume a b)
    (hg1 : IntervalIntegrable (fun x : ℝ => g ((x : ℂ) + (c : ℂ) * Complex.I)) volume a b)
    (hf2 : IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (d : ℂ) * Complex.I)) volume a b)
    (hg2 : IntervalIntegrable (fun x : ℝ => g ((x : ℂ) + (d : ℂ) * Complex.I)) volume a b)
    (hf3 : IntervalIntegrable (fun y : ℝ => f ((b : ℂ) + (y : ℂ) * Complex.I)) volume c d)
    (hg3 : IntervalIntegrable (fun y : ℝ => g ((b : ℂ) + (y : ℂ) * Complex.I)) volume c d)
    (hf4 : IntervalIntegrable (fun y : ℝ => f ((a : ℂ) + (y : ℂ) * Complex.I)) volume c d)
    (hg4 : IntervalIntegrable (fun y : ℝ => g ((a : ℂ) + (y : ℂ) * Complex.I)) volume c d) :
    rectBdIntegral a b c d (fun w => f w + g w)
      = rectBdIntegral a b c d f + rectBdIntegral a b c d g := by
  simp only [rectBdIntegral, Pi.add_apply]
  rw [intervalIntegral.integral_add hf1 hg1, intervalIntegral.integral_add hf2 hg2,
    intervalIntegral.integral_add hf3 hg3, intervalIntegral.integral_add hf4 hg4]
  ring

lemma rectBdIntegral_sub (a b c d : ℝ) (f g : ℂ → ℂ)
    (hf1 : IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (c : ℂ) * Complex.I)) volume a b)
    (hg1 : IntervalIntegrable (fun x : ℝ => g ((x : ℂ) + (c : ℂ) * Complex.I)) volume a b)
    (hf2 : IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (d : ℂ) * Complex.I)) volume a b)
    (hg2 : IntervalIntegrable (fun x : ℝ => g ((x : ℂ) + (d : ℂ) * Complex.I)) volume a b)
    (hf3 : IntervalIntegrable (fun y : ℝ => f ((b : ℂ) + (y : ℂ) * Complex.I)) volume c d)
    (hg3 : IntervalIntegrable (fun y : ℝ => g ((b : ℂ) + (y : ℂ) * Complex.I)) volume c d)
    (hf4 : IntervalIntegrable (fun y : ℝ => f ((a : ℂ) + (y : ℂ) * Complex.I)) volume c d)
    (hg4 : IntervalIntegrable (fun y : ℝ => g ((a : ℂ) + (y : ℂ) * Complex.I)) volume c d) :
    rectBdIntegral a b c d (fun w => f w - g w)
      = rectBdIntegral a b c d f - rectBdIntegral a b c d g := by
  simp only [rectBdIntegral, Pi.sub_apply]
  rw [intervalIntegral.integral_sub hf1 hg1, intervalIntegral.integral_sub hf2 hg2,
    intervalIntegral.integral_sub hf3 hg3, intervalIntegral.integral_sub hf4 hg4]
  ring

lemma rectBdIntegral_const_mul (a b c d : ℝ) (k : ℂ) (f : ℂ → ℂ) :
    rectBdIntegral a b c d (fun w => k * f w) = k * rectBdIntegral a b c d f := by
  simp only [rectBdIntegral, Pi.mul_apply]
  have h1 : (∫ x : ℝ in a..b, k * f ((x : ℂ) + (c : ℂ) * Complex.I))
      = k * ∫ x : ℝ in a..b, f ((x : ℂ) + (c : ℂ) * Complex.I) :=
    intervalIntegral.integral_const_mul k _
  have h2 : (∫ x : ℝ in a..b, k * f ((x : ℂ) + (d : ℂ) * Complex.I))
      = k * ∫ x : ℝ in a..b, f ((x : ℂ) + (d : ℂ) * Complex.I) :=
    intervalIntegral.integral_const_mul k _
  have h3 : (∫ y : ℝ in c..d, k * f ((b : ℂ) + (y : ℂ) * Complex.I))
      = k * ∫ y : ℝ in c..d, f ((b : ℂ) + (y : ℂ) * Complex.I) :=
    intervalIntegral.integral_const_mul k _
  have h4 : (∫ y : ℝ in c..d, k * f ((a : ℂ) + (y : ℂ) * Complex.I))
      = k * ∫ y : ℝ in c..d, f ((a : ℂ) + (y : ℂ) * Complex.I) :=
    intervalIntegral.integral_const_mul k _
  rw [h1, h2, h3, h4]; ring

lemma rectBdIntegral_congr {a b c d : ℝ} {f g : ℂ → ℂ}
    (h : ∀ w, f w = g w) : rectBdIntegral a b c d f = rectBdIntegral a b c d g := by
  have h1 : (fun x : ℝ => f ((x : ℂ) + (c : ℂ) * Complex.I))
      = fun x : ℝ => g ((x : ℂ) + (c : ℂ) * Complex.I) := funext fun x => h _
  have h2 : (fun x : ℝ => f ((x : ℂ) + (d : ℂ) * Complex.I))
      = fun x : ℝ => g ((x : ℂ) + (d : ℂ) * Complex.I) := funext fun x => h _
  have h3 : (fun y : ℝ => f ((b : ℂ) + (y : ℂ) * Complex.I))
      = fun y : ℝ => g ((b : ℂ) + (y : ℂ) * Complex.I) := funext fun y => h _
  have h4 : (fun y : ℝ => f ((a : ℂ) + (y : ℂ) * Complex.I))
      = fun y : ℝ => g ((a : ℂ) + (y : ℂ) * Complex.I) := funext fun y => h _
  simp only [rectBdIntegral, h1, h2, h3, h4]

end

end Work.TMComp.Kotani

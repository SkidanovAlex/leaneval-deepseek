import Mathlib
import Submission.Work.FatouL1.hcIntegralSechSq
import Submission.Work.FatouL1.hcIntegralSinhCosh3

/-!
# The two Cauchy-derivative kernels on a vertical line half a unit to the left of the pole

Both halves of Shishikura's `∂/∂w (π / sin (π w)²)`-kernel estimate along the vertical line
`Re w = Re z - 1/2`.  For `w = c + i y` with `z.re = c + 1/2` one has
`w - z = -1/2 + i (y - z.im)`, and on this half-plane boundary

* `sin (π (w - z)) = -cosh (π (y - z.im))`,
* `cos (π (w - z)) = i sinh (π (y - z.im))`,

so that the two kernels (the conjugate Poisson kernel `π / sin²` and its `w`-derivative
`-2π² cos / sin³`) are dominated by `π / cosh²` resp. `2π² |sinh| / cosh³`, whose integrals over
`ℝ` are `2` resp. `2π`.  Since `h` is only assumed *bounded* on the line (it is not assumed
measurable), the comparison is made through `MeasureTheory.norm_integral_le_of_norm_le`, which
needs the majorant alone to be integrable.
-/

namespace Work.FatouL1

open MeasureTheory

/-- The sine at the points `π (-1/2 + i t)` of the boundary line `Re = -1/2` of the strip. -/
lemma sin_pi_negHalf_add (t : ℝ) :
    Complex.sin (Real.pi * ((-1/2 : ℂ) + (t : ℂ) * Complex.I))
      = -((Real.cosh (Real.pi * t) : ℝ) : ℂ) := by
  have hz : Real.pi * ((-1/2 : ℂ) + (t : ℂ) * Complex.I)
      = -((Real.pi : ℂ)/2) + ((Real.pi : ℂ) * (t : ℂ)) * Complex.I := by ring
  rw [hz, Complex.sin_add_mul_I, Complex.sin_neg, Complex.cos_neg, Complex.sin_pi_div_two,
    Complex.cos_pi_div_two]
  rw [← Complex.ofReal_mul, ← Complex.ofReal_cosh]
  ring

/-- The cosine at the points `π (-1/2 + i t)` of the boundary line `Re = -1/2` of the strip. -/
lemma cos_pi_negHalf_add (t : ℝ) :
    Complex.cos (Real.pi * ((-1/2 : ℂ) + (t : ℂ) * Complex.I))
      = ((Real.sinh (Real.pi * t) : ℝ) : ℂ) * Complex.I := by
  have hz : Real.pi * ((-1/2 : ℂ) + (t : ℂ) * Complex.I)
      = -((Real.pi : ℂ)/2) + ((Real.pi : ℂ) * (t : ℂ)) * Complex.I := by ring
  rw [hz, Complex.cos_add_mul_I, Complex.sin_neg, Complex.cos_neg, Complex.sin_pi_div_two,
    Complex.cos_pi_div_two]
  rw [← Complex.ofReal_mul, ← Complex.ofReal_sinh]
  ring

/-- The point `c + i y` of the vertical line `Re = c` differs from `z` (with `z.re = c + 1/2`) by
`-1/2 + i (y - z.im)`. -/
lemma line_sub_eq (c : ℝ) {z : ℂ} (hz : z.re = c + 1 / 2) (y : ℝ) :
    (c : ℂ) + (y : ℂ) * Complex.I - z
      = (-1/2 : ℂ) + ((y - z.im : ℝ) : ℂ) * Complex.I := by
  nth_rewrite 1 [← Complex.re_add_im z]
  rw [hz]
  push_cast
  ring

/-- Norm of the conjugate Poisson kernel `π / sin (π w)²` on the line `Re w = c`,
`Re z = c + 1/2`. -/
lemma normPiDivSinSq (c : ℝ) {z : ℂ} (hz : z.re = c + 1 / 2) (y : ℝ) :
    ‖(Real.pi : ℂ) / (Complex.sin (Real.pi * ((c : ℂ) + (y : ℂ) * Complex.I - z))) ^ 2‖
      = Real.pi / Real.cosh (Real.pi * (y - z.im)) ^ 2 := by
  have hsq : (Complex.sin (Real.pi * ((c : ℂ) + (y : ℂ) * Complex.I - z))) ^ 2
      = ((Real.cosh (Real.pi * (y - z.im)) ^ 2 : ℝ) : ℂ) := by
    rw [line_sub_eq c hz y, sin_pi_negHalf_add (y - z.im), pow_two, pow_two, neg_mul_neg,
      ← Complex.ofReal_mul]
  rw [hsq, ← Complex.ofReal_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]

/-- Norm of the `w`-derivative kernel `2π² cos (π w) / sin (π w)³` on the line `Re w = c`,
`Re z = c + 1/2`. -/
lemma normCosDivSin3 (c : ℝ) {z : ℂ} (hz : z.re = c + 1 / 2) (y : ℝ) :
    ‖(2 : ℂ) * (Real.pi : ℂ) ^ 2 * Complex.cos (Real.pi * ((c : ℂ) + (y : ℂ) * Complex.I - z)) /
        (Complex.sin (Real.pi * ((c : ℂ) + (y : ℂ) * Complex.I - z))) ^ 3‖
      = 2 * Real.pi ^ 2 *
          (|Real.sinh (Real.pi * (y - z.im))| / Real.cosh (Real.pi * (y - z.im)) ^ 3) := by
  have hcub : (Complex.sin (Real.pi * ((c : ℂ) + (y : ℂ) * Complex.I - z))) ^ 3
      = -((Real.cosh (Real.pi * (y - z.im)) ^ 3 : ℝ) : ℂ) := by
    rw [line_sub_eq c hz y, sin_pi_negHalf_add (y - z.im), neg_pow]
    rw [← Complex.ofReal_pow]
    ring
  have hval : (2 : ℂ) * (Real.pi : ℂ) ^ 2
        * Complex.cos (Real.pi * ((c : ℂ) + (y : ℂ) * Complex.I - z)) /
        (Complex.sin (Real.pi * ((c : ℂ) + (y : ℂ) * Complex.I - z))) ^ 3
      = -(((2 * Real.pi ^ 2 * Real.sinh (Real.pi * (y - z.im))
          / Real.cosh (Real.pi * (y - z.im)) ^ 3 : ℝ)) : ℂ) * Complex.I := by
    rw [hcub, line_sub_eq c hz y, cos_pi_negHalf_add (y - z.im)]
    push_cast
    ring
  rw [hval, norm_mul, Complex.norm_I, mul_one, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_div, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi ^ 2),
    abs_of_pos (pow_pos (Real.cosh_pos _) 3), mul_div_assoc]

theorem hcDerivKernel :
    (∀ {c : ℝ} {z : ℂ}, z.re = c + 1 / 2 → ∀ {S : ℝ}, 0 ≤ S → ∀ {h : ℂ → ℂ},
      (∀ y : ℝ, ‖h ((c : ℂ) + (y : ℂ) * Complex.I)‖ ≤ S) →
      ‖∫ y : ℝ, h ((c : ℂ) + (y : ℂ) * Complex.I) *
          ((Real.pi : ℂ) / (Complex.sin (Real.pi * ((c : ℂ) + (y : ℂ) * Complex.I - z))) ^ 2)‖
        ≤ 2 * S) ∧
    (∀ {c : ℝ} {z : ℂ}, z.re = c + 1 / 2 → ∀ {S : ℝ}, 0 ≤ S → ∀ {h : ℂ → ℂ},
      (∀ y : ℝ, ‖h ((c : ℂ) + (y : ℂ) * Complex.I)‖ ≤ S) →
      ‖∫ y : ℝ, h ((c : ℂ) + (y : ℂ) * Complex.I) *
          ((2 : ℂ) * (Real.pi : ℂ) ^ 2 * Complex.cos (Real.pi * ((c : ℂ) + (y : ℂ) * Complex.I - z)) /
            (Complex.sin (Real.pi * ((c : ℂ) + (y : ℂ) * Complex.I - z))) ^ 3)‖
        ≤ 2 * Real.pi * S) := by
  constructor
  · intro c z hz S hS h hh
    have hgint : Integrable
        (fun y : ℝ => S * (Real.pi * (1 / Real.cosh (Real.pi * (y - z.im)) ^ 2))) :=
      ((hcIntegralSechSq z.im).1.const_mul Real.pi).const_mul S
    have hpt : ∀ y : ℝ,
        ‖h ((c : ℂ) + (y : ℂ) * Complex.I) *
            ((Real.pi : ℂ) / (Complex.sin (Real.pi * ((c : ℂ) + (y : ℂ) * Complex.I - z))) ^ 2)‖
          ≤ S * (Real.pi * (1 / Real.cosh (Real.pi * (y - z.im)) ^ 2)) := by
      intro y
      rw [norm_mul, normPiDivSinSq c hz y, mul_one_div]
      exact mul_le_mul (hh y) le_rfl (by positivity) hS
    refine le_trans (norm_integral_le_of_norm_le hgint (Filter.Eventually.of_forall hpt)) ?_
    rw [integral_const_mul, integral_const_mul, (hcIntegralSechSq z.im).2]
    have hp : Real.pi * (2 / Real.pi) = 2 := by field_simp
    rw [hp]
    exact le_of_eq (mul_comm S 2)
  · intro c z hz S hS h hh
    have hgint : Integrable
        (fun y : ℝ => S * (2 * Real.pi ^ 2 *
          (|Real.sinh (Real.pi * (y - z.im))| / Real.cosh (Real.pi * (y - z.im)) ^ 3))) :=
      ((hcIntegralSinhCosh3 z.im).1.const_mul (2 * Real.pi ^ 2)).const_mul S
    have hpt : ∀ y : ℝ,
        ‖h ((c : ℂ) + (y : ℂ) * Complex.I) *
            ((2 : ℂ) * (Real.pi : ℂ) ^ 2 *
                Complex.cos (Real.pi * ((c : ℂ) + (y : ℂ) * Complex.I - z)) /
              (Complex.sin (Real.pi * ((c : ℂ) + (y : ℂ) * Complex.I - z))) ^ 3)‖
          ≤ S * (2 * Real.pi ^ 2 *
              (|Real.sinh (Real.pi * (y - z.im))| / Real.cosh (Real.pi * (y - z.im)) ^ 3)) := by
      intro y
      rw [norm_mul, normCosDivSin3 c hz y]
      exact mul_le_mul (hh y) le_rfl (by positivity) hS
    refine le_trans (norm_integral_le_of_norm_le hgint (Filter.Eventually.of_forall hpt)) ?_
    rw [integral_const_mul, integral_const_mul, (hcIntegralSinhCosh3 z.im).2]
    have hp : 2 * Real.pi ^ 2 * (1 / Real.pi) = 2 * Real.pi := by field_simp
    rw [hp]
    exact le_of_eq (mul_comm S (2 * Real.pi))

end Work.FatouL1

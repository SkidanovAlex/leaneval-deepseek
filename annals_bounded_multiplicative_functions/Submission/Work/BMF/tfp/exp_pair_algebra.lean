import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.tfp

open Complex

/-- Purely algebraic/trigonometric identity: for `u ≠ 0`, with `c = 2πiu`,
`(e^{c} + e^{-c} - 2)/c² = (sinc (πu))²`.  Indeed `e^{c} + e^{-c} = 2cos(2πu) = 2 - 4sin²(πu)`
so the numerator is `-4 sin²(πu)`, while `c² = -4π²u²`, and `sinc(πu) = sin(πu)/(πu)`.
Useful lemmas: `Complex.exp_mul_I`, `Complex.ofReal_cos`, `Complex.ofReal_sin`,
`Real.cos_two_mul`, `Real.sin_sq`, `Real.sinc_of_ne_zero`, `Real.pi_ne_zero`. -/
lemma exp_pair_algebra (u : ℝ) (hu : u ≠ 0) :
    (Complex.exp (2 * Real.pi * Complex.I * u) + Complex.exp (-(2 * Real.pi * Complex.I * u)) - 2)
      / (2 * Real.pi * Complex.I * u) ^ 2 = ((Real.sinc (Real.pi * u)) ^ 2 : ℂ) := by
  have hpu : Real.pi * u ≠ 0 := mul_ne_zero Real.pi_ne_zero hu
  -- Rewrite `2πiu = (2πu) * I` so that `Complex.exp_ofReal_mul_I` applies.
  have harg : 2 * Real.pi * Complex.I * u = ((2 * Real.pi * u : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  have hargneg : -(2 * Real.pi * Complex.I * u) = ((-(2 * Real.pi * u) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  -- Euler's formula for both exponentials.
  have h1 : Complex.exp (2 * Real.pi * Complex.I * u)
      = ((Real.cos (2 * Real.pi * u) : ℂ)) + (Real.sin (2 * Real.pi * u) : ℂ) * Complex.I := by
    rw [harg, Complex.exp_ofReal_mul_I]
  have h2 : Complex.exp (-(2 * Real.pi * Complex.I * u))
      = ((Real.cos (2 * Real.pi * u) : ℂ)) - (Real.sin (2 * Real.pi * u) : ℂ) * Complex.I := by
    rw [hargneg, Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  -- Numerator: `e^c + e^{-c} - 2 = -4 sin²(πu)`.
  have hnum : Complex.exp (2 * Real.pi * Complex.I * u)
        + Complex.exp (-(2 * Real.pi * Complex.I * u)) - 2
      = -4 * ((Real.sin (Real.pi * u)) ^ 2 : ℂ) := by
    rw [h1, h2]
    have hc : Real.cos (2 * Real.pi * u) = 1 - 2 * (Real.sin (Real.pi * u))^2 := by
      rw [show 2 * Real.pi * u = 2 * (Real.pi * u) by ring, Real.cos_two_mul, Real.cos_sq']
      ring
    rw [hc]
    push_cast
    ring
  -- Denominator: `(2πiu)² = -4π²u²`.
  have hden : (2 * Real.pi * Complex.I * u) ^ 2 = ((-4 * (Real.pi * u)^2 : ℝ) : ℂ) := by
    rw [harg, mul_pow, Complex.I_sq]
    push_cast
    ring
  rw [hnum, hden, Real.sinc_of_ne_zero hpu]
  push_cast
  field_simp

end Work.BMF.tfp

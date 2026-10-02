import Mathlib
import Submission.Work.LinnikContract.Defs

namespace Work.LinnikContract.API

/-- Rewrite HB's test function `F₂(z) = ((1 − e^{−Kz})/z)²` in the `exp·sinh` form
`F₂(z) = K² e^{−Kz} (sinh(Kz/2)/(Kz/2))²`, which is what makes `‖F₂‖` computable:
from `1 − e^{−2A} = 2 e^{−A} sinh A` with `A = Kz/2`. -/
theorem F2_eq_exp_sinh (K : ℝ) (hK : K ≠ 0) (z : ℂ) (hz : z ≠ 0) :
    Work.LinnikContract.F2 K z = (K : ℂ) ^ 2 * Complex.exp (-(K : ℂ) * z) *
      (Complex.sinh ((K : ℂ) * z / 2) / ((K : ℂ) * z / 2)) ^ 2 := by
  have hKc : (K : ℂ) ≠ 0 := by exact_mod_cast hK
  unfold Work.LinnikContract.F2
  rw [Complex.sinh]
  field_simp
  ring_nf
  -- After clearing denominators and normalising, it remains to use the exponential identities
  -- `e^{Kz/2}e^{-Kz/2} = 1`, `e^{-Kz}e^{Kz} = 1`, `e^{-Kz}e^{-Kz} = (e^{-Kz})^2`.
  have hab : Complex.exp (↑K * z * (1 / 2)) * Complex.exp (↑K * z * (-1 / 2)) = 1 := by
    rw [← Complex.exp_add]
    rw [show ↑K * z * (1 / 2) + ↑K * z * (-1 / 2) = 0 by ring, Complex.exp_zero]
  have ha2 : Complex.exp (-(↑K * z)) * Complex.exp (↑K * z * (1 / 2)) ^ 2 = 1 := by
    rw [pow_two, ← Complex.exp_add, ← Complex.exp_add]
    rw [show -(↑K * z) + (↑K * z * (1 / 2) + ↑K * z * (1 / 2)) = 0 by ring, Complex.exp_zero]
  have hb2 : Complex.exp (-(↑K * z)) * Complex.exp (↑K * z * (-1 / 2)) ^ 2
      = Complex.exp (-(↑K * z)) ^ 2 := by
    rw [pow_two, ← Complex.exp_add, ← Complex.exp_add]
    rw [show -(↑K * z) + (↑K * z * (-1 / 2) + ↑K * z * (-1 / 2)) = -(↑K * z) + -(↑K * z) by ring,
      Complex.exp_add]
    ring
  have hR : -(Complex.exp (-(↑K * z)) * Complex.exp (↑K * z * (1 / 2)) * Complex.exp (↑K * z * (-1 / 2)) * 2)
        + Complex.exp (-(↑K * z)) * Complex.exp (↑K * z * (1 / 2)) ^ 2
        + Complex.exp (-(↑K * z)) * Complex.exp (↑K * z * (-1 / 2)) ^ 2
      = 1 - Complex.exp (-(↑K * z)) * 2 + Complex.exp (-(↑K * z)) ^ 2 := by
    rw [show Complex.exp (-(↑K * z)) * Complex.exp (↑K * z * (1 / 2)) * Complex.exp (↑K * z * (-1 / 2)) * 2
        = (Complex.exp (-(↑K * z)) * (Complex.exp (↑K * z * (1 / 2)) * Complex.exp (↑K * z * (-1 / 2)))) * 2 by ring]
    rw [hab, ha2, hb2]
    ring
  exact hR.symm

end Work.LinnikContract.API

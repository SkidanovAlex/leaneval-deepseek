import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-- For positive naturals `A`, `B` and a real `s`, the pair `B^{is} * conj(A^{is})`
(`^` = `Complex.cpow`, `starRingEnd ℂ` = complex conjugation) has modulus `1`. -/
lemma n4_cpow_norm (A B : ℕ) (hA : 0 < A) (hB : 0 < B) (s : ℝ) :
    ‖(B : ℂ) ^ (Complex.I * (s : ℂ)) * starRingEnd ℂ ((A : ℂ) ^ (Complex.I * (s : ℂ)))‖ = 1 := by
  have hA0 : (0 : ℝ) < A := by exact_mod_cast hA
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  -- The modulus is multiplicative and conjugation preserves it.
  rw [norm_mul]
  have h1 : ‖(B : ℂ) ^ (Complex.I * (s : ℂ))‖ = 1 := by
    rw [← Complex.ofReal_natCast B, Complex.norm_cpow_eq_rpow_re_of_pos hB0]
    have : (Complex.I * (s : ℂ)).re = 0 := by simp [Complex.mul_re]
    rw [this, Real.rpow_zero]
  have h2 : ‖starRingEnd ℂ ((A : ℂ) ^ (Complex.I * (s : ℂ)))‖ = 1 := by
    rw [show starRingEnd ℂ ((A : ℂ) ^ (Complex.I * (s : ℂ)))
          = star ((A : ℂ) ^ (Complex.I * (s : ℂ))) from rfl, norm_star]
    rw [← Complex.ofReal_natCast A, Complex.norm_cpow_eq_rpow_re_of_pos hA0]
    have : (Complex.I * (s : ℂ)).re = 0 := by simp [Complex.mul_re]
    rw [this, Real.rpow_zero]
  rw [h1, h2, mul_one]

end Work.BMF

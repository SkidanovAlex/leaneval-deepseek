import Mathlib.Analysis.Complex.Trigonometric

namespace Commons.Analysis.Complex


private lemma one_sub_exp_mul_I_complex (z : ℂ) :
    1 - Complex.exp (z * Complex.I) =
      -2 * Complex.I * Complex.exp ((z / 2) * Complex.I) * Complex.sin (z / 2) := by
  let w : ℂ := Complex.exp ((z / 2) * Complex.I)
  have hw_ne : w ≠ 0 := Complex.exp_ne_zero _
  have h1 : Complex.exp (-(z / 2) * Complex.I) = w⁻¹ := by
    dsimp [w]
    rw [← Complex.exp_neg]
    congr 1
    ring
  have h2s : 2 * Complex.sin (z / 2) = (w⁻¹ - w) * Complex.I := by
    calc
      2 * Complex.sin (z / 2)
          = (Complex.exp (-(z / 2) * Complex.I) - Complex.exp ((z / 2) * Complex.I)) * Complex.I :=
            Complex.two_sin (x := z / 2)
      _ = (w⁻¹ - w) * Complex.I := by rw [h1]
  have hz : z * Complex.I = (z / 2) * Complex.I + (z / 2) * Complex.I := by ring
  have h_exp : Complex.exp (z * Complex.I) = w * w := by
    rw [hz, Complex.exp_add]
  have hRHS : -2 * Complex.I * w * Complex.sin (z / 2) = w * (w⁻¹ - w) := by
    calc
      -2 * Complex.I * w * Complex.sin (z / 2) = -Complex.I * w * (2 * Complex.sin (z / 2)) := by ring
      _ = -Complex.I * w * ((w⁻¹ - w) * Complex.I) := by rw [h2s]
      _ = w * (w⁻¹ - w) := by
        field_simp [hw_ne]
        ring_nf
        rw [pow_two, Complex.I_mul_I]
        ring
  have hLHS : 1 - w * w = w * (w⁻¹ - w) := by
    calc
      1 - w * w = w * w⁻¹ - w * w := by rw [mul_inv_cancel₀ hw_ne]
      _ = w * (w⁻¹ - w) := by ring
  rw [h_exp, hRHS]
  exact hLHS

theorem one_sub_exp_mul_I (θ : ℝ) :
    1 - Complex.exp (θ * Complex.I) =
      -2 * Complex.I * Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I) * (Real.sin (θ / 2) : ℂ) := by
  rw [Complex.ofReal_sin, Complex.ofReal_div]
  exact one_sub_exp_mul_I_complex ((θ : ℂ))

end Commons.Analysis.Complex
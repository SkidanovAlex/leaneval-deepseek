import Mathlib

/-!
# A lower bound for `‖Γ(1/2 + iT)‖`

We prove

`√π * exp (-(π/2) * |T|) ≤ ‖Γ (1/2 + iT)‖`

by evaluating the modulus exactly.  Euler's reflection formula
`Γ z * Γ (1 - z) = π / sin (π z)` applied at `z = 1/2 + iT` gives, since
`1 - z = conj z` and `Γ (conj z) = conj (Γ z)`,

`‖Γ (1/2 + iT)‖ ^ 2 = π / cosh (π T)`.

Taking square roots and using `cosh x ≤ exp |x|` yields the claim.
-/

namespace Work.FIArea5.S16Hecke

/-- `sin (π/2 + i x) = cosh x`. -/
lemma sin_pi_div_two_add_mul_I (x : ℝ) :
    Complex.sin ((Real.pi : ℂ) * ((1 / 2 : ℂ) + (x : ℂ) * Complex.I)) =
      (Real.cosh (Real.pi * x) : ℂ) := by
  have h : (Real.pi : ℂ) * ((1 / 2 : ℂ) + (x : ℂ) * Complex.I) =
      (Real.pi : ℂ) / 2 + ((Real.pi * x : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h, Complex.sin_add, Complex.sin_pi_div_two, Complex.cos_pi_div_two, Complex.cos_mul_I]
  simp

/-- The exact modulus squared: `‖Γ (1/2 + iT)‖ ^ 2 = π / cosh (π T)`. -/
lemma normSq_Gamma_half_add_mul_I (T : ℝ) :
    ‖Complex.Gamma ((1 / 2 : ℂ) + (T : ℂ) * Complex.I)‖ ^ 2 =
      Real.pi / Real.cosh (Real.pi * T) := by
  set s : ℂ := (1 / 2 : ℂ) + (T : ℂ) * Complex.I with hs
  have hconj : (1 : ℂ) - s = (starRingEnd ℂ) s := by
    apply Complex.ext
    · simp [hs]; ring
    · simp [hs]
  have hsin : Complex.sin ((Real.pi : ℂ) * s) = (Real.cosh (Real.pi * T) : ℂ) := by
    rw [hs]; exact sin_pi_div_two_add_mul_I T
  have hprod : Complex.Gamma s * (starRingEnd ℂ) (Complex.Gamma s) =
      (Real.pi : ℂ) / (Real.cosh (Real.pi * T) : ℂ) := by
    have h := Complex.Gamma_mul_Gamma_one_sub s
    rw [hconj, Complex.Gamma_conj, hsin] at h
    exact h
  have hn : ‖Complex.Gamma s‖ ^ 2 =
      ‖(Real.pi : ℂ) / (Real.cosh (Real.pi * T) : ℂ)‖ := by
    rw [← hprod, norm_mul, Complex.norm_conj]; ring
  rw [hn, norm_div, Complex.norm_of_nonneg Real.pi_pos.le,
    Complex.norm_of_nonneg (Real.cosh_pos _).le]

/-- `cosh x ≤ exp |x|`. -/
lemma cosh_le_exp_abs (x : ℝ) : Real.cosh x ≤ Real.exp |x| := by
  rw [← Real.cosh_abs x, Real.cosh_eq]
  have h2 : Real.exp (-|x|) ≤ Real.exp |x| :=
    Real.exp_le_exp.mpr (neg_le_self (abs_nonneg x))
  calc (Real.exp |x| + Real.exp (-|x|)) / 2
      ≤ (Real.exp |x| + Real.exp |x|) / 2 := by
        apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 2)
        exact add_le_add (le_refl _) h2
    _ = Real.exp |x| := by ring

/-- The remaining arithmetic step. -/
lemma sqrt_pi_mul_exp_le_sqrt_pi_div_cosh (T : ℝ) :
    Real.sqrt Real.pi * Real.exp (-(Real.pi / 2) * |T|) ≤
      Real.sqrt (Real.pi / Real.cosh (Real.pi * T)) := by
  have hb : 0 ≤ Real.pi / Real.cosh (Real.pi * T) :=
    div_nonneg Real.pi_pos.le (Real.cosh_pos _).le
  have ha : 0 ≤ Real.sqrt Real.pi * Real.exp (-(Real.pi / 2) * |T|) := by positivity
  rw [Real.le_sqrt ha hb]
  have hexp2 : Real.exp (-(Real.pi / 2) * |T|) ^ 2 = Real.exp (-(Real.pi * |T|)) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have hch : Real.cosh (Real.pi * T) ≤ Real.exp (Real.pi * |T|) := by
    have h1 := cosh_le_exp_abs (Real.pi * T)
    rwa [abs_mul, abs_of_pos Real.pi_pos] at h1
  have hle : Real.exp (-(Real.pi * |T|)) ≤ 1 / Real.cosh (Real.pi * T) := by
    rw [Real.exp_neg]
    simpa [one_div] using one_div_le_one_div_of_le (Real.cosh_pos _) hch
  calc (Real.sqrt Real.pi * Real.exp (-(Real.pi / 2) * |T|)) ^ 2
      = Real.pi * Real.exp (-(Real.pi / 2) * |T|) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt Real.pi_pos.le]
    _ = Real.pi * Real.exp (-(Real.pi * |T|)) := by rw [hexp2]
    _ ≤ Real.pi * (1 / Real.cosh (Real.pi * T)) :=
        mul_le_mul_of_nonneg_left hle Real.pi_pos.le
    _ = Real.pi / Real.cosh (Real.pi * T) := by ring

theorem normGammaHalfAddILower (T : ℝ) :
    Real.sqrt Real.pi * Real.exp (-(Real.pi / 2) * |T|) ≤
      ‖Complex.Gamma ((1 / 2 : ℂ) + (T : ℂ) * Complex.I)‖ := by
  have hsq := normSq_Gamma_half_add_mul_I T
  have hnorm : ‖Complex.Gamma ((1 / 2 : ℂ) + (T : ℂ) * Complex.I)‖ =
      Real.sqrt (Real.pi / Real.cosh (Real.pi * T)) := by
    have h2 : Real.sqrt (‖Complex.Gamma ((1 / 2 : ℂ) + (T : ℂ) * Complex.I)‖ ^ 2) =
        ‖Complex.Gamma ((1 / 2 : ℂ) + (T : ℂ) * Complex.I)‖ :=
      Real.sqrt_sq (norm_nonneg _)
    rw [hsq] at h2
    exact h2.symm
  rw [hnorm]
  exact sqrt_pi_mul_exp_le_sqrt_pi_div_cosh T

end Work.FIArea5.S16Hecke

import Mathlib.Analysis.SpecialFunctions.Pow.Complex

namespace Commons.NumberTheory.DirichletPolynomial

/-- For a nonnegative real `x` and complex exponent `z`, conjugation commutes with
complex exponentiation: `conj (x^z) = x^(conj z)`. -/
lemma starRingEnd_cpow_ofReal_nonneg (x : ℝ) (hx : 0 ≤ x) (z : ℂ) :
    (starRingEnd ℂ) ((x : ℂ) ^ z) = (x : ℂ) ^ ((starRingEnd ℂ) z) := by
  have harg : (x : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hx]
    exact Real.pi_ne_zero.symm
  have h := Complex.cpow_conj (x : ℂ) z harg
  rw [Complex.conj_ofReal] at h
  exact h.symm

theorem dirPolyA_neg_eq_conj (a : ℤ → ℂ) (X t : ℝ) (hreal : ∀ m : ℤ, (a m).im = 0) :
    (∑ m ∈ Finset.Icc (⌈X⌉ : ℤ) ⌊4 * X⌋, a m * (m : ℂ) ^ (-(1 + Complex.I * (-t))))
      = (starRingEnd ℂ)
          (∑ m ∈ Finset.Icc (⌈X⌉ : ℤ) ⌊4 * X⌋,
            a m * (m : ℂ) ^ (-(1 + Complex.I * t))) := by
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro m hm
  rw [map_mul]
  have hm0 : (0 : ℤ) ≤ m := by
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hm
    have hXm : X ≤ (m : ℝ) := le_trans (Int.le_ceil X) (by exact_mod_cast h1)
    have hm4X : (m : ℝ) ≤ 4 * X := le_trans (by exact_mod_cast h2) (Int.floor_le (4 * X))
    have hreal0 : (0 : ℝ) ≤ (m : ℝ) := by linarith
    exact_mod_cast hreal0
  have hm0' : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm0
  rw [Complex.conj_eq_iff_im.mpr (hreal m)]
  rw [(Complex.ofReal_intCast m).symm]
  rw [starRingEnd_cpow_ofReal_nonneg (m : ℝ) hm0']
  rw [show (starRingEnd ℂ) (-(1 + Complex.I * t)) = -(1 + Complex.I * (-t)) by
        simp [Complex.conj_I]]

end Commons.NumberTheory.DirichletPolynomial
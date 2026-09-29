import Mathlib

namespace Work.CNum.CircleParam

/-- Every point of the unit circle is `e^{2πit}` for some `t ∈ [0,1]`. -/
lemma unitCircle_param (z : ℂ) (hz : ‖z‖ = 1) :
    ∃ t ∈ Set.Icc (0 : ℝ) 1, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) = z := by
  have hze : z = Complex.exp ((Complex.arg z : ℂ) * Complex.I) := by
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I z]
    rw [hz]
    simp
  have key : ∀ θ : ℝ, θ ∈ Set.Ioc (-Real.pi) Real.pi →
      ∃ t ∈ Set.Icc (0 : ℝ) 1,
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) =
          Complex.exp ((θ : ℂ) * Complex.I) := by
    intro θ hθ
    by_cases h : 0 ≤ θ
    · refine ⟨θ / (2 * Real.pi), ⟨?_, ?_⟩, ?_⟩
      · positivity
      · rw [div_le_one (by positivity)]
        linarith [hθ.2, Real.pi_pos]
      · rw [Complex.exp_eq_exp_iff_exists_int]
        exact ⟨0, by push_cast; field_simp; try ring⟩
    · have hneg : θ < 0 := not_le.mp h
      refine ⟨θ / (2 * Real.pi) + 1, ⟨?_, ?_⟩, ?_⟩
      · have h1 : (-1 : ℝ) ≤ θ / (2 * Real.pi) := by
          rw [le_div_iff₀ (by positivity)]
          linarith [hθ.1]
        linarith
      · have h1 : θ / (2 * Real.pi) ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg hneg.le (by positivity)
        linarith
      · rw [Complex.exp_eq_exp_iff_exists_int]
        exact ⟨1, by push_cast; field_simp; try ring⟩
  obtain ⟨t, ht, hexp⟩ := key (Complex.arg z) ⟨Complex.neg_pi_lt_arg z, Complex.arg_le_pi z⟩
  exact ⟨t, ht, by rw [hexp]; exact hze.symm⟩

end Work.CNum.CircleParam

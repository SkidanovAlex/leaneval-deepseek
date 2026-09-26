import Mathlib
import Submission.Work.Core.Torus

namespace Work.Core

/-- The first component of the torus parametrisation. -/
lemma torusMap_apply_zero (θ φ : ℝ) :
    torusMap θ φ (0 : Fin 3) = (2 + Real.cos φ) * Real.cos θ := by
  simp only [torusMap, WithLp.ofLp_toLp]
  simp

/-- The second component of the torus parametrisation. -/
lemma torusMap_apply_one (θ φ : ℝ) :
    torusMap θ φ (1 : Fin 3) = (2 + Real.cos φ) * Real.sin θ := by
  simp only [torusMap, WithLp.ofLp_toLp]
  simp

/-- The third component of the torus parametrisation. -/
lemma torusMap_apply_two (θ φ : ℝ) :
    torusMap θ φ (2 : Fin 3) = Real.sin φ := by
  simp only [torusMap, WithLp.ofLp_toLp]
  simp

/-- The two angles `(cos θ, sin θ)` and `(cos θ', sin θ')` coincide exactly when
`θ` and `θ'` differ by an integer multiple of `2π`. -/
lemma cos_sin_eq_iff_exists_int (a b : ℝ) :
    Real.cos a = Real.cos b ∧ Real.sin a = Real.sin b ↔
      ∃ k : ℤ, a = b + k * (2 * Real.pi) := by
  constructor
  · rintro ⟨hcos, hsin⟩
    have hc : Real.cos (a - b) = 1 := by
      rw [Real.cos_sub, ← hcos, ← hsin]
      nlinarith [Real.sin_sq_add_cos_sq a]
    rw [Real.cos_eq_one_iff] at hc
    obtain ⟨n, hn⟩ := hc
    exact ⟨n, by linarith⟩
  · rintro ⟨k, rfl⟩
    exact ⟨Real.cos_add_int_mul_two_pi b k, Real.sin_add_int_mul_two_pi b k⟩

theorem torusMap_eq_iff (θ φ θ' φ' : ℝ) :
    Work.Core.torusMap θ φ = Work.Core.torusMap θ' φ' ↔
      (∃ k : ℤ, θ = θ' + k * (2 * Real.pi)) ∧ (∃ k : ℤ, φ = φ' + k * (2 * Real.pi)) := by
  constructor
  · intro h
    have h0 : (2 + Real.cos φ) * Real.cos θ = (2 + Real.cos φ') * Real.cos θ' := by
      rw [← torusMap_apply_zero θ φ, ← torusMap_apply_zero θ' φ', h]
    have h1 : (2 + Real.cos φ) * Real.sin θ = (2 + Real.cos φ') * Real.sin θ' := by
      rw [← torusMap_apply_one θ φ, ← torusMap_apply_one θ' φ', h]
    have h2 : Real.sin φ = Real.sin φ' := by
      rw [← torusMap_apply_two θ φ, ← torusMap_apply_two θ' φ', h]
    have hd : 0 < 2 + Real.cos φ := by linarith [Real.neg_one_le_cos φ]
    have hd' : 0 < 2 + Real.cos φ' := by linarith [Real.neg_one_le_cos φ']
    -- squared norms: `(2 + cos φ)² = (2 + cos φ')²`
    have hsq : (2 + Real.cos φ) ^ 2 = (2 + Real.cos φ') ^ 2 := by
      have h0sq : (((2 + Real.cos φ) * Real.cos θ)) ^ 2
          = (((2 + Real.cos φ') * Real.cos θ')) ^ 2 := by rw [h0]
      have h1sq : (((2 + Real.cos φ) * Real.sin θ)) ^ 2
          = (((2 + Real.cos φ') * Real.sin θ')) ^ 2 := by rw [h1]
      nlinarith [h0sq, h1sq, Real.sin_sq_add_cos_sq θ, Real.sin_sq_add_cos_sq θ']
    have hAB : 2 + Real.cos φ = 2 + Real.cos φ' := by
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hh | hh
      · exact hh
      · linarith
    have hcos_phi : Real.cos φ = Real.cos φ' := by linarith
    have hdne : (2 + Real.cos φ) ≠ 0 := ne_of_gt hd
    have hcos_theta : Real.cos θ = Real.cos θ' := by
      apply mul_left_cancel₀ hdne
      rw [← hAB] at h0
      exact h0
    have hsin_theta : Real.sin θ = Real.sin θ' := by
      apply mul_left_cancel₀ hdne
      rw [← hAB] at h1
      exact h1
    exact ⟨(cos_sin_eq_iff_exists_int θ θ').mp ⟨hcos_theta, hsin_theta⟩,
      (cos_sin_eq_iff_exists_int φ φ').mp ⟨hcos_phi, h2⟩⟩
  · rintro ⟨⟨k, hk⟩, ⟨m, hm⟩⟩
    rw [hk, hm]
    simp only [torusMap, Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]

end Work.Core

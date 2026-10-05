import Mathlib

namespace Work.RPB1a.Caratheodory.Brouwer

/-- Fixed points of continuous self-maps of a closed ball of radius `R > 0` in a real normed space,
deduced from the unit-ball case by rescaling. -/
lemma brouwer_ball_of_unit_ball {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {R : ℝ}
    (hR : 0 < R)
    (hunit : ∀ g : E → E, Continuous g → (∀ x, ‖x‖ ≤ 1 → ‖g x‖ ≤ 1) →
      ∃ x, ‖x‖ ≤ 1 ∧ g x = x)
    (g : E → E) (hg : Continuous g) (hmaps : ∀ x, ‖x‖ ≤ R → ‖g x‖ ≤ R) :
    ∃ x, ‖x‖ ≤ R ∧ g x = x := by
  have hcont : Continuous (fun x : E => R⁻¹ • g (R • x)) :=
    (hg.comp (continuous_const_smul R)).const_smul R⁻¹
  have hmaps' : ∀ x : E, ‖x‖ ≤ 1 → ‖R⁻¹ • g (R • x)‖ ≤ 1 := by
    intro x hx
    have hxR : ‖R • x‖ ≤ R := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hR]
      nlinarith [norm_nonneg x]
    have h1 : ‖g (R • x)‖ ≤ R := hmaps (R • x) hxR
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
    calc R⁻¹ * ‖g (R • x)‖ ≤ R⁻¹ * R :=
          mul_le_mul_of_nonneg_left h1 (le_of_lt (inv_pos.mpr hR))
      _ = 1 := by rw [inv_mul_cancel₀ (ne_of_gt hR)]
  obtain ⟨x, hx1, hx2⟩ := hunit (fun x : E => R⁻¹ • g (R • x)) hcont hmaps'
  refine ⟨R • x, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos hR]
    nlinarith [norm_nonneg x]
  · have h := congrArg (fun y : E => R • y) hx2
    simp only [smul_smul, mul_inv_cancel₀ (ne_of_gt hR), one_smul] at h
    exact h

end Work.RPB1a.Caratheodory.Brouwer

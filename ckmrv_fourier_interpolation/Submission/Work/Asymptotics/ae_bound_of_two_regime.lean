import Mathlib

namespace Work.Asymptotics

/-- **From a two-regime bound to a single exponential bound.**  If `‖h‖` is polynomially bounded on
the window `[1,B]` (`B ≥ 1`) and decays like `e^{-πt}` beyond `B`, then `h` satisfies the single
bound `C t^M e^{-πt}` on all of `[1,∞)`; the constant `C = D₁(1+B)^{M₁}e^{πB} + D₂` contains the
finite (but we do not care how large) factor `e^{πB}`, and `M = M₁ + M₂`. -/
theorem ae_bound_of_two_regime (h : ℝ → ℂ) {B D₁ D₂ M₁ M₂ : ℝ} (hB : 1 ≤ B)
    (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hb₁ : ∀ t : ℝ, 1 ≤ t → t ≤ B → ‖h t‖ ≤ D₁ * (1 + t) ^ M₁)
    (hb₂ : ∀ t : ℝ, B ≤ t → ‖h t‖ ≤ D₂ * t ^ M₂ * Real.exp (-(Real.pi * t))) :
    ∃ C M : ℝ, 0 ≤ C ∧ 0 ≤ M ∧ ∀ t : ℝ, 1 ≤ t →
      ‖h t‖ ≤ C * t ^ M * Real.exp (-(Real.pi * t)) := by
  refine ⟨D₁ * (1 + B) ^ M₁ * Real.exp (Real.pi * B) + D₂, M₁ + M₂, ?_, ?_, ?_⟩
  · have h1 : 0 ≤ (1 + B) ^ M₁ := Real.rpow_nonneg (by linarith) M₁
    have h2 : 0 ≤ Real.exp (Real.pi * B) := le_of_lt (Real.exp_pos _)
    have h3 : 0 ≤ D₁ * (1 + B) ^ M₁ * Real.exp (Real.pi * B) := mul_nonneg (mul_nonneg hD₁ h1) h2
    linarith
  · linarith
  · intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le one_pos ht
    have hM : 0 ≤ M₁ + M₂ := by linarith
    have hT : 1 ≤ t ^ (M₁ + M₂) := Real.one_le_rpow ht hM
    have hT0 : 0 ≤ t ^ (M₁ + M₂) := Real.rpow_nonneg (le_of_lt ht0) _
    have hE : 0 ≤ Real.exp (Real.pi * B) := le_of_lt (Real.exp_pos _)
    have hF : 0 ≤ Real.exp (-(Real.pi * t)) := le_of_lt (Real.exp_pos _)
    have hA : 0 ≤ D₁ * (1 + B) ^ M₁ := mul_nonneg hD₁ (Real.rpow_nonneg (by linarith) M₁)
    by_cases htB : t ≤ B
    · -- Regime 1: `1 ≤ t ≤ B`, use the polynomial bound together with `t^M ≥ 1`
      -- and `e^{πB} e^{-πt} ≥ 1`.
      have h1 : (1 + t) ^ M₁ ≤ (1 + B) ^ M₁ :=
        Real.rpow_le_rpow (by linarith) (by linarith) hM₁
      have hb : ‖h t‖ ≤ D₁ * (1 + B) ^ M₁ :=
        le_trans (hb₁ t ht htB) (mul_le_mul_of_nonneg_left h1 hD₁)
      have hEF : 1 ≤ Real.exp (Real.pi * B) * Real.exp (-(Real.pi * t)) := by
        rw [← Real.exp_add]
        exact Real.one_le_exp (by nlinarith [Real.pi_pos])
      have hETF : 1 ≤ Real.exp (Real.pi * B) * t ^ (M₁ + M₂) * Real.exp (-(Real.pi * t)) := by
        have h := mul_le_mul hEF hT (le_of_lt one_pos) (le_trans zero_le_one hEF)
        nlinarith [h]
      have hstep1 : D₁ * (1 + B) ^ M₁ ≤ D₁ * (1 + B) ^ M₁ *
          (Real.exp (Real.pi * B) * t ^ (M₁ + M₂) * Real.exp (-(Real.pi * t))) :=
        le_mul_of_one_le_right hA hETF
      have hstep2 : D₁ * (1 + B) ^ M₁ *
          (Real.exp (Real.pi * B) * t ^ (M₁ + M₂) * Real.exp (-(Real.pi * t))) ≤
          (D₁ * (1 + B) ^ M₁ * Real.exp (Real.pi * B) + D₂) * t ^ (M₁ + M₂) *
            Real.exp (-(Real.pi * t)) := by
        have hDTF : 0 ≤ D₂ * t ^ (M₁ + M₂) * Real.exp (-(Real.pi * t)) :=
          mul_nonneg (mul_nonneg hD₂ hT0) hF
        nlinarith [hDTF]
      exact le_trans hb (le_trans hstep1 hstep2)
    · -- Regime 2: `B ≤ t`, use the exponential bound and `t^{M₂} ≤ t^{M₁+M₂}`.
      have htB' : B < t := not_le.mp htB
      have hb : ‖h t‖ ≤ D₂ * t ^ M₂ * Real.exp (-(Real.pi * t)) := hb₂ t (le_of_lt htB')
      have h2 : t ^ M₂ ≤ t ^ (M₁ + M₂) := Real.rpow_le_rpow_of_exponent_le ht (by linarith)
      have hstep1 : ‖h t‖ ≤ D₂ * t ^ (M₁ + M₂) * Real.exp (-(Real.pi * t)) := by
        calc ‖h t‖ ≤ D₂ * t ^ M₂ * Real.exp (-(Real.pi * t)) := hb
          _ ≤ D₂ * t ^ (M₁ + M₂) * Real.exp (-(Real.pi * t)) := by
              apply mul_le_mul_of_nonneg_right _ hF
              exact mul_le_mul_of_nonneg_left h2 hD₂
      have hstep2 : D₂ * t ^ (M₁ + M₂) * Real.exp (-(Real.pi * t)) ≤
          (D₁ * (1 + B) ^ M₁ * Real.exp (Real.pi * B) + D₂) * t ^ (M₁ + M₂) *
            Real.exp (-(Real.pi * t)) := by
        have hAE : 0 ≤ D₁ * (1 + B) ^ M₁ * Real.exp (Real.pi * B) := mul_nonneg hA hE
        have hTF : 0 ≤ t ^ (M₁ + M₂) * Real.exp (-(Real.pi * t)) := mul_nonneg hT0 hF
        have hpos : 0 ≤ D₁ * (1 + B) ^ M₁ * Real.exp (Real.pi * B) *
            (t ^ (M₁ + M₂) * Real.exp (-(Real.pi * t))) := mul_nonneg hAE hTF
        nlinarith [hpos]
      exact le_trans hstep1 hstep2

end Work.Asymptotics

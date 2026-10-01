import Mathlib

namespace Work.LinnikAreas.TuranOther

/-- **Non-negativity of the Turán/log-derivative coefficient.**  For any Dirichlet characters
`χ₀ χ` modulo `q`, any real `γ` and any `n : ℕ`,

`(1 + Re χ₀(n)) * (1 + Re (χ(n)·n^{-iγ})) ≥ 0`.

Both factors are non-negative because a Dirichlet character takes values in the closed unit disc
(so its real part is `≥ -1`), and `n^{-iγ}` has modulus `≤ 1`.  The hypothesis `χ₀ * χ₀ = 1` is
not needed: the bound `‖χ₀(n)‖ ≤ 1` is all that is used. -/
theorem chiCoeffPos {q : ℕ} [NeZero q] (χ₀ χ : DirichletCharacter ℂ q) (h₀sq : χ₀ * χ₀ = 1)
    (γ : ℝ) (n : ℕ) :
    0 ≤ (1 + (χ₀ (n : ZMod q)).re) * (1 + (χ (n : ZMod q) * (n : ℂ) ^ (-(Complex.I * (γ : ℂ)))).re) := by
  have h1 : 0 ≤ 1 + (χ₀ (n : ZMod q)).re := by
    have h : |(χ₀ (n : ZMod q)).re| ≤ 1 := by
      calc |(χ₀ (n : ZMod q)).re| ≤ ‖χ₀ (n : ZMod q)‖ := Complex.abs_re_le_norm _
        _ ≤ 1 := χ₀.norm_le_one _
    linarith [neg_le_of_abs_le h]
  have h2 : 0 ≤ 1 + (χ (n : ZMod q) * (n : ℂ) ^ (-(Complex.I * (γ : ℂ)))).re := by
    have hb : |(χ (n : ZMod q) * (n : ℂ) ^ (-(Complex.I * (γ : ℂ)))).re| ≤ 1 := by
      have h1' : |(χ (n : ZMod q) * (n : ℂ) ^ (-(Complex.I * (γ : ℂ)))).re|
          ≤ ‖χ (n : ZMod q) * (n : ℂ) ^ (-(Complex.I * (γ : ℂ)))‖ := Complex.abs_re_le_norm _
      have h2' : ‖χ (n : ZMod q) * (n : ℂ) ^ (-(Complex.I * (γ : ℂ)))‖
          ≤ ‖χ (n : ZMod q)‖ * ‖(n : ℂ) ^ (-(Complex.I * (γ : ℂ)))‖ := norm_mul_le _ _
      have h3' : ‖χ (n : ZMod q)‖ ≤ 1 := χ.norm_le_one _
      have h4' : ‖(n : ℂ) ^ (-(Complex.I * (γ : ℂ)))‖ ≤ 1 := by
        rcases eq_or_ne n 0 with rfl | hn0
        · rcases eq_or_ne (-(Complex.I * (γ : ℂ))) 0 with hw | hw
          · rw [Nat.cast_zero, hw]; norm_num
          · rw [Nat.cast_zero, Complex.zero_cpow hw, norm_zero]; norm_num
        · have hpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
          have hgoal : ‖(((n : ℝ)) : ℂ) ^ (-(Complex.I * (γ : ℂ)))‖ ≤ 1 := by
            rw [Complex.norm_cpow_eq_rpow_re_of_pos hpos (-(Complex.I * (γ : ℂ)))]
            have hzero : (-(Complex.I * (γ : ℂ))).re = 0 := by simp
            rw [hzero]; norm_num
          simpa using hgoal
      calc |(χ (n : ZMod q) * (n : ℂ) ^ (-(Complex.I * (γ : ℂ)))).re|
          ≤ ‖χ (n : ZMod q) * (n : ℂ) ^ (-(Complex.I * (γ : ℂ)))‖ := h1'
        _ ≤ ‖χ (n : ZMod q)‖ * ‖(n : ℂ) ^ (-(Complex.I * (γ : ℂ)))‖ := h2'
        _ ≤ 1 * 1 := mul_le_mul h3' h4' (norm_nonneg _) (by norm_num)
        _ = 1 := mul_one 1
    linarith [neg_le_of_abs_le hb]
  exact mul_nonneg h1 h2

end Work.LinnikAreas.TuranOther

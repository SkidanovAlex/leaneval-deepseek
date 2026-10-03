import Mathlib

namespace Work.KMTAreas.A4

/-- Pointwise single-scale decay bound for a Schwartz function `φ` on `ℝ` whose value is
bounded by `D` everywhere and by `C / |y|^2` for `|y| ≥ 1`:

  `N⁻¹ * ‖φ (m / N)‖ ≤ (4 D + 4 C) * N / (N + |m|)^2`  for every `N ≥ 1` and `m : ℤ`.

Indeed, if `|m| ≤ N` then `N + |m| ≤ 2N` and the uniform bound `‖φ‖ ≤ D` gives
`N⁻¹ D ≤ D/N ≤ (4D+4C) N/(N+|m|)^2`; while if `|m| ≥ N` then `|m/N| ≥ 1`,
`N + |m| ≤ 2|m|` and `‖φ(m/N)‖ ≤ C/(m/N)^2 = C N^2/m^2` gives
`N⁻¹ ‖φ(m/N)‖ ≤ C N/m^2 ≤ (4D+4C) N/(N+|m|)^2`. -/
theorem winPointwiseLe {φ : SchwartzMap ℝ ℂ} {D C : ℝ} (hD : 0 ≤ D) (hC : 0 ≤ C)
    (hDb : ∀ y : ℝ, ‖φ y‖ ≤ D) (hCb : ∀ y : ℝ, 1 ≤ |y| → ‖φ y‖ ≤ C / |y| ^ 2)
    {N : ℝ} (hN : 1 ≤ N) (m : ℤ) :
    N⁻¹ * ‖φ ((m : ℝ) / N)‖ ≤ (4 * D + 4 * C) * N / (N + |(m : ℝ)|) ^ 2 := by
  have hNpos : (0:ℝ) < N := by linarith
  have hNnn : (0:ℝ) ≤ N := le_of_lt hNpos
  set M : ℝ := |(m : ℝ)| with hM
  have hMnn : 0 ≤ M := by rw [hM]; exact abs_nonneg _
  have hden : 0 < (N + M) ^ 2 := by positivity
  by_cases hcase : M ≤ N
  · have hb : ‖φ ((m : ℝ) / N)‖ ≤ D := hDb _
    have hNM : (N + M) ^ 2 ≤ 4 * N ^ 2 := by nlinarith [hNnn, hMnn]
    have hterm : N⁻¹ * D ≤ (4 * D + 4 * C) * N / (N + M) ^ 2 := by
      rw [show N⁻¹ * D = D / N by ring, div_le_iff₀ hNpos, div_mul_eq_mul_div,
        le_div_iff₀ hden]
      nlinarith [mul_le_mul_of_nonneg_left hNM hD, sq_nonneg N, hD, hC,
        mul_nonneg hC (sq_nonneg N)]
    calc N⁻¹ * ‖φ ((m : ℝ) / N)‖ ≤ N⁻¹ * D :=
          mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hNnn)
      _ ≤ _ := hterm
  · have hcase' : N < M := lt_of_not_ge hcase
    have hMpos : 0 < M := lt_trans hNpos hcase'
    have hx : 1 ≤ |(m : ℝ) / N| := by
      rw [abs_div, abs_of_pos hNpos, ← hM, le_div_iff₀ hNpos]
      linarith
    have hb : ‖φ ((m : ℝ) / N)‖ ≤ C / |(m : ℝ) / N| ^ 2 := hCb _ hx
    have hx2 : |(m : ℝ) / N| ^ 2 = M ^ 2 / N ^ 2 := by
      rw [abs_div, abs_of_pos hNpos, ← hM, div_pow]
    have hstep : N⁻¹ * (C / |(m : ℝ) / N| ^ 2) = C * N / M ^ 2 := by
      rw [hx2]
      field_simp
    have hNM2 : (N + M) ^ 2 ≤ 4 * M ^ 2 := by nlinarith [hNnn, hMnn]
    have hterm : C * N / M ^ 2 ≤ (4 * D + 4 * C) * N / (N + M) ^ 2 := by
      rw [div_le_iff₀ (pow_pos hMpos 2), div_mul_eq_mul_div, le_div_iff₀ hden]
      nlinarith [mul_le_mul_of_nonneg_left hNM2 (mul_nonneg hC hNnn),
        mul_nonneg (mul_nonneg hNnn (pow_nonneg (le_of_lt hMpos) 2)) hD,
        sq_nonneg N]
    calc N⁻¹ * ‖φ ((m : ℝ) / N)‖ ≤ N⁻¹ * (C / |(m : ℝ) / N| ^ 2) :=
          mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hNnn)
      _ = C * N / M ^ 2 := hstep
      _ ≤ _ := hterm

end Work.KMTAreas.A4

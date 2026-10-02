import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Nibble.threshold_tools

namespace Work.Deep.Nibble

/-- **Clause 3 of the asymptotic side conditions of `cor:sparse_egj`** (threshold form).
For every `E > 0` and `κ > 0` there is `N > 0` such that for all `n ≥ N` and all
`D ≥ n^{1/100}` one has `((1+κ)D)^{-E} ≤ κ`.

Route: `((1+κ)D)^{-E} = (((1+κ)D)^E)⁻¹`, and `((1+κ)D)^E ≥ D^E ≥ (n^{1/100})^E = n^{E/100}`;
take `N := (1/κ)^(100/E)` (rewriting with `Real.rpow_mul`: `((1/κ)^(100/E))^(E/100) = 1/κ`).
All `rpow` bases are positive because `n ≥ 1` (from `N > 0`). -/
theorem threshold_cond3 {E κ : ℝ} (hE : 0 < E) (hκ : 0 < κ) :
    ∃ N : ℝ, 0 < N ∧ ∀ n : ℕ, N ≤ (n : ℝ) → ∀ D : ℝ, (n : ℝ) ^ ((1 : ℝ) / 100) ≤ D →
      ((1 + κ) * D) ^ (-E) ≤ κ := by
  have hκinv : 0 < 1 / κ := by positivity
  have hexppos : 0 < (1:ℝ)/100 * E := by positivity
  refine ⟨(1 / κ) ^ ((100:ℝ) / E), Real.rpow_pos_of_pos hκinv _, ?_⟩
  intro n hn D hD
  -- positivity of all the rpow bases involved
  have hnpos : 0 < (n : ℝ) := lt_of_lt_of_le (Real.rpow_pos_of_pos hκinv _) hn
  have hnR : (0:ℝ) ≤ (n : ℝ) := hnpos.le
  have hDpos : 0 < D := lt_of_lt_of_le (Real.rpow_pos_of_pos hnpos _) hD
  have hADpos : 0 < (1 + κ) * D := by positivity
  -- `N ^ ((1/100) * E) = (1/κ) ^ ((100/E) * ((1/100) * E)) = (1/κ) ^ 1 = 1/κ`
  have hNE : ((1/κ) ^ ((100:ℝ)/E)) ^ ((1:ℝ)/100 * E) = 1/κ := by
    rw [← Real.rpow_mul hκinv.le ((100:ℝ)/E) ((1:ℝ)/100 * E),
      show ((100:ℝ)/E) * ((1:ℝ)/100 * E) = 1 by
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div]; field_simp,
      Real.rpow_one]
  -- hence `1/κ ≤ n ^ (E/100)`
  have h1 : 1/κ ≤ (n:ℝ) ^ ((1:ℝ)/100 * E) := by
    have h := Real.rpow_le_rpow (le_of_lt (Real.rpow_pos_of_pos hκinv _)) hn hexppos.le
    rwa [hNE] at h
  -- `n ^ (E/100) = (n ^ (1/100)) ^ E ≤ ((1+κ) * D) ^ E`
  have h2 : (n:ℝ) ^ ((1:ℝ)/100 * E) = ((n:ℝ) ^ ((1:ℝ)/100)) ^ E := Real.rpow_mul hnR _ _
  have h3 : ((n:ℝ) ^ ((1:ℝ)/100)) ^ E ≤ ((1+κ)*D) ^ E :=
    Real.rpow_le_rpow (Real.rpow_pos_of_pos hnpos _).le
      (hD.trans (le_mul_of_one_le_left hDpos.le (by linarith))) hE.le
  have hchain : 1/κ ≤ ((1+κ)*D) ^ E := by
    calc 1/κ ≤ (n:ℝ) ^ ((1:ℝ)/100 * E) := h1
      _ = ((n:ℝ) ^ ((1:ℝ)/100)) ^ E := h2
      _ ≤ ((1+κ)*D) ^ E := h3
  -- invert: `((1+κ)D)^(-E) = (((1+κ)D)^E)⁻¹ ≤ (1/κ)⁻¹ = κ`
  have hle : 1 / (((1+κ)*D)^E) ≤ 1 / (1/κ) := one_div_le_one_div_of_le hκinv hchain
  rw [one_div_one_div] at hle
  calc ((1+κ)*D) ^ (-E) = (((1+κ)*D)^E)⁻¹ := Real.rpow_neg hADpos.le E
    _ = 1 / (((1+κ)*D)^E) := (one_div _).symm
    _ ≤ κ := hle

end Work.Deep.Nibble

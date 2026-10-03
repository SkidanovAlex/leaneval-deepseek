import Mathlib

namespace Work.Pert.Pin

/-- Pure real arithmetic for the seed-error budget of `Work.Pert.Pin.band_goodP_sqrt`: the three
summands of `Cseed * (A2/(M*M) + u0v/M + av)` are budgeted by `R/(24·Camp·M·M)` each, giving
`R/(8·Camp·M·M)`; with `R ≤ 4` that is `< 1/(Camp·M*M)`, and `Camp·M*M·(R/(8·Camp·M*M)) ≤ R/4`. -/
theorem seed_bound_arith {A2 A3 u0v av R M Camp Cseed : ℝ}
    (hM : 0 < M) (hCamp : 1 ≤ Camp) (hCseed : 0 < Cseed) (hR : 0 < R) (hR4 : R ≤ 4)
    (hA : A2 ≤ A3)
    (hdev : Cseed * (2 * (A3 / (M * M))) ≤ R / (12 * Camp * M * M))
    (hu0 : u0v ≤ R / (24 * Cseed * Camp * M))
    (ha : av ≤ R / (24 * Cseed * Camp * M * M)) :
    Cseed * (A2 / (M * M) + u0v / M + av) ≤ R / (8 * Camp * M * M) ∧
      Camp * M * M * (R / (8 * Camp * M * M)) ≤ R / 4 ∧
      R / (8 * Camp * M * M) < 1 / (Camp * M * M) := by
  -- positive denominators, available throughout
  have hM2 : (0 : ℝ) < M * M := by positivity
  have h12 : (0 : ℝ) < 12 * Camp * M * M := by positivity
  have h24 : (0 : ℝ) < 24 * Camp * M * M := by positivity
  have h8 : (0 : ℝ) < 8 * Camp * M * M := by positivity
  have h24c : (0 : ℝ) < 24 * Cseed * Camp * M := by positivity
  have h24cc : (0 : ℝ) < 24 * Cseed * Camp * M * M := by positivity
  -- each of the three summands is budgeted by `R / (24 * Camp * M * M)`
  have hb1 : Cseed * (A2 / (M * M)) ≤ R / (24 * Camp * M * M) := by
    have hle : A2 / (M * M) ≤ A3 / (M * M) :=
      div_le_div_of_nonneg_right hA (le_of_lt hM2)
    have hmul : Cseed * (A2 / (M * M)) ≤ Cseed * (A3 / (M * M)) :=
      mul_le_mul_of_nonneg_left hle (le_of_lt hCseed)
    have hdev2 : Cseed * (A3 / (M * M)) ≤ R / (24 * Camp * M * M) := by
      have h0 : Cseed * (2 * (A3 / (M * M))) * (12 * Camp * M * M) ≤ R :=
        (le_div_iff₀ h12).mp hdev
      rw [le_div_iff₀ h24]
      nlinarith [h0]
    exact le_trans hmul hdev2
  have hb2 : Cseed * (u0v / M) ≤ R / (24 * Camp * M * M) := by
    have h0 : u0v * (24 * Cseed * Camp * M) ≤ R := (le_div_iff₀ h24c).mp hu0
    rw [le_div_iff₀ h24]
    have key : Cseed * (u0v / M) * (24 * Camp * M * M) = u0v * (24 * Cseed * Camp * M) := by
      field_simp
    rw [key]
    exact h0
  have hb3 : Cseed * av ≤ R / (24 * Camp * M * M) := by
    have h0 : av * (24 * Cseed * Camp * M * M) ≤ R := (le_div_iff₀ h24cc).mp ha
    rw [le_div_iff₀ h24]
    have key : Cseed * av * (24 * Camp * M * M) = av * (24 * Cseed * Camp * M * M) := by
      ring
    rw [key]
    exact h0
  refine ⟨?_, ?_, ?_⟩
  · have hexp : Cseed * (A2 / (M * M) + u0v / M + av) =
        Cseed * (A2 / (M * M)) + Cseed * (u0v / M) + Cseed * av := by ring
    rw [hexp]
    have h3 : 3 * (R / (24 * Camp * M * M)) = R / (8 * Camp * M * M) := by
      field_simp
      ring
    rw [← h3]
    linarith [hb1, hb2, hb3]
  · have hkey : Camp * M * M * (R / (8 * Camp * M * M)) = R / 8 := by field_simp
    rw [hkey]
    linarith
  · have hkey : (1 : ℝ) / (Camp * M * M) = 8 / (8 * Camp * M * M) := by field_simp
    rw [hkey]
    exact (div_lt_div_iff_of_pos_right h8).mpr (by linarith)

end Work.Pert.Pin

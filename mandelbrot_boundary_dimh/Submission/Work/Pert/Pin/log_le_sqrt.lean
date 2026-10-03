import Mathlib

/-!
# `Work.Pert.Pin.log_mul_add_le_sqrt`

Growth comparison used to glue the two height bands of `Work.Pert.Pin.strip_of_pin_v2`: for every
`c > 0` the inequality `c * log M + c ≤ √M` holds for all sufficiently large `M`.

Proof: for `M ≥ 1` put `s := √√M`, so `s ^ 2 = √M`, `s > 0` and `log M = 4 log s ≤ 4 s`.  For
`M ≥ (8c)^4` one has `8c ≤ s`, whence `c log M ≤ 4 c s ≤ s ^ 2 / 2 = √M / 2`, and for
`M ≥ 4c^2` one has `c ≤ √M / 2`.
-/

namespace Work.Pert.Pin

/-- For every `c > 0`, `c * log M + c ≤ √M` eventually. -/
theorem log_mul_add_le_sqrt (c : ℝ) (hc : 0 < c) :
    ∃ M₀ : ℝ, 0 < M₀ ∧ ∀ M : ℝ, M₀ ≤ M → c * Real.log M + c ≤ Real.sqrt M := by
  refine ⟨max 1 (max ((8 * c) ^ 4) (4 * c ^ 2)), by positivity, ?_⟩
  intro M hM
  have hM1 : 1 ≤ M := le_trans (le_max_left _ _) hM
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM1
  have h8c : (8 * c) ^ 4 ≤ M := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hM
  have h4c : 4 * c ^ 2 ≤ M := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hM
  set s : ℝ := Real.sqrt (Real.sqrt M) with hs
  have hsq : s ^ 2 = Real.sqrt M := by rw [hs]; exact Real.sq_sqrt (Real.sqrt_nonneg M)
  have hspos : 0 < s := by
    rw [hs]; exact Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hMpos)
  have h8cs : 8 * c ≤ s := by
    have heq : ((8 * c) ^ 2) ^ 2 = (8 * c) ^ 4 := by ring
    have h2 : ((8 * c) ^ 2) ^ 2 ≤ M := by rw [heq]; exact h8c
    have h1 : (8 * c) ^ 2 ≤ Real.sqrt M := by
      have h2' : ((8 * c) ^ 2) ^ 2 ≤ (Real.sqrt M) ^ 2 := by
        rw [Real.sq_sqrt (le_of_lt hMpos)]; exact h2
      calc (8 * c) ^ 2 = Real.sqrt (((8 * c) ^ 2) ^ 2) :=
            (Real.sqrt_sq (by positivity)).symm
        _ ≤ Real.sqrt ((Real.sqrt M) ^ 2) := Real.sqrt_le_sqrt h2'
        _ = Real.sqrt M := Real.sqrt_sq (Real.sqrt_nonneg M)
    have h1' : (8 * c) ^ 2 ≤ s ^ 2 := by rw [hsq]; exact h1
    calc 8 * c = Real.sqrt ((8 * c) ^ 2) := (Real.sqrt_sq (by linarith : (0 : ℝ) ≤ 8 * c)).symm
      _ ≤ Real.sqrt (s ^ 2) := Real.sqrt_le_sqrt h1'
      _ = s := Real.sqrt_sq (le_of_lt hspos)
  have hlog : Real.log M ≤ 4 * s := by
    have h1 : Real.log M = 4 * Real.log s := by
      have h3 : Real.sqrt M = s ^ 2 := hsq.symm
      have h4 : Real.log (Real.sqrt M) = 2 * Real.log s := by
        rw [h3, Real.log_pow]; ring
      have h5 : Real.log M = 2 * Real.log (Real.sqrt M) := by
        have h6 : M = (Real.sqrt M) ^ 2 := by rw [Real.sq_sqrt (le_of_lt hMpos)]
        rw [h6]
        simpa using Real.log_pow (Real.sqrt M) 2
      rw [h5, h4]; ring
    have h5 : Real.log s ≤ s - 1 := Real.log_le_sub_one_of_pos hspos
    linarith
  have h4cs : 4 * c * s ≤ Real.sqrt M / 2 := by
    have h2 : 8 * c * s ≤ s ^ 2 := by nlinarith [h8cs, hspos]
    rw [hsq] at h2
    linarith
  have h6 : c * Real.log M ≤ 4 * c * s := by nlinarith [hlog, hc]
  have hc2 : c ≤ Real.sqrt M / 2 := by
    have h1 : 4 * c ^ 2 ≤ (Real.sqrt M) ^ 2 := by
      rw [Real.sq_sqrt (le_of_lt hMpos)]; exact h4c
    nlinarith [h1, hc, Real.sqrt_nonneg M]
  linarith

/-- **Glue of the two height bands.**  For every `Ξ > 0` and `c ≥ 0` the inequality
`Ξ + c * (1 + log M) ≤ √M` holds for all sufficiently large `M`; this is what makes the band
`|Im w| ≤ √M` meet the half-strip `Ξ + c * (1 + log M) ≤ |Im w|`. -/
theorem log_le_sqrt_glue (Ξ c : ℝ) (hΞ : 0 < Ξ) (hc : 0 ≤ c) :
    ∃ M₀ : ℝ, 0 < M₀ ∧ ∀ M : ℝ, M₀ ≤ M →
      Ξ + c * (1 + Real.log M) ≤ Real.sqrt M := by
  obtain ⟨M₁, hM₁pos, hM₁⟩ := log_mul_add_le_sqrt (c + Ξ + 1) (by linarith)
  refine ⟨max M₁ 1, by positivity, fun M hM => ?_⟩
  have h1 : M₁ ≤ M := le_trans (le_max_left _ _) hM
  have h2 : (1 : ℝ) ≤ M := le_trans (le_max_right _ _) hM
  have h3 : (c + Ξ + 1) * Real.log M + (c + Ξ + 1) ≤ Real.sqrt M := hM₁ M h1
  have h4 : 0 ≤ Real.log M := Real.log_nonneg h2
  nlinarith [h3, h4, hΞ, hc, Real.sqrt_nonneg M]

end Work.Pert.Pin

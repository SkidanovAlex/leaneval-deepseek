import Mathlib

namespace Work.GM.Energy.EnergyCore2

/-- Absorbing the error term of GM Lemma 11.4: with `K = Θ·N^{1/mm}`, `Θ ≥ 1`, `N ≥ 1`, `mm ≥ 1`
and `400·C₄·(C_loc+1)² ≤ Θ²`, the coefficient of `E(W)` in Lemma 11.4 is at most `1/2`. -/
theorem beta_le {N C4 CS Θ V : ℝ} {mm : ℕ}
    (hC4 : 0 ≤ C4) (hCS : 0 ≤ CS) (hΘ : 1 ≤ Θ) (hV : 1 ≤ V) (hN : 1 ≤ N) (hm : 1 ≤ mm)
    (hΘsq : 400 * C4 * (CS + 1) ^ 2 ≤ Θ ^ 2) :
    C4 * (CS + 1) ^ 2 * ((2 * N + 1) / (Θ * N ^ (1 / (mm : ℝ))) ^ (mm : ℝ)) ^ 2 / V ^ 2
      ≤ 1 / 2 := by
  -- Positivity of the parameters.
  have hΘpos : 0 < Θ := lt_of_lt_of_le zero_lt_one hΘ
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hmmne : (mm : ℝ) ≠ 0 := by positivity
  have hNpowpos : 0 < N ^ (1 / (mm : ℝ)) := Real.rpow_pos_of_pos hNpos _
  -- `(N^{1/mm})^{mm} = N` and hence `K^{mm} = Θ^{mm}·N`, where `K = Θ·N^{1/mm}`.
  have hNpow : (N ^ (1 / (mm : ℝ))) ^ (mm : ℝ) = N := by
    rw [← Real.rpow_mul (le_of_lt hNpos) (1 / (mm : ℝ)) (mm : ℝ)]
    rw [show (1 / (mm : ℝ)) * (mm : ℝ) = 1 by field_simp]
    rw [Real.rpow_one]
  have hKpow : (Θ * N ^ (1 / (mm : ℝ))) ^ (mm : ℝ) = Θ ^ (mm : ℝ) * N := by
    rw [Real.mul_rpow (le_of_lt hΘpos) (le_of_lt hNpowpos), hNpow]
  have hKpowpos : 0 < (Θ * N ^ (1 / (mm : ℝ))) ^ (mm : ℝ) :=
    Real.rpow_pos_of_pos (mul_pos hΘpos hNpowpos) _
  -- `Θ^{mm} ≥ Θ`, hence `Θ·N ≤ K^{mm}`.
  have hΘmm : Θ ≤ Θ ^ (mm : ℝ) := by
    rw [Real.rpow_natCast]
    simpa using pow_le_pow_right₀ hΘ hm
  have hKn : Θ * N ≤ (Θ * N ^ (1 / (mm : ℝ))) ^ (mm : ℝ) := by
    rw [hKpow]
    exact mul_le_mul_of_nonneg_right hΘmm (le_of_lt hNpos)
  -- The coefficient `a = C₄(C_loc+1)²` satisfies `a ≤ Θ²/400`.
  have ha : 0 ≤ C4 * (CS + 1) ^ 2 := by positivity
  have hab : C4 * (CS + 1) ^ 2 ≤ Θ ^ 2 / 400 := by nlinarith [hΘsq]
  -- `q = (2N+1)/K^{mm} ≤ 3/Θ`.
  set q : ℝ := (2 * N + 1) / (Θ * N ^ (1 / (mm : ℝ))) ^ (mm : ℝ) with hqdef
  have hq : q ≤ 3 / Θ := by
    rw [hqdef]
    have h2N : 2 * N + 1 ≤ 3 * N := by nlinarith
    have h1 : (2 * N + 1) / (Θ * N ^ (1 / (mm : ℝ))) ^ (mm : ℝ) ≤ 3 * N / (Θ * N) :=
      div_le_div₀ (by positivity) h2N (mul_pos hΘpos hNpos) hKn
    have h2 : 3 * N / (Θ * N) = 3 / Θ := by field_simp
    linarith
  have hq2 : q ^ 2 ≤ (3 / Θ) ^ 2 :=
    pow_le_pow_left₀ (le_of_lt (div_pos (by positivity) hKpowpos)) hq 2
  have h32 : 0 ≤ (3 / Θ) ^ 2 := by positivity
  have hV2 : (1 : ℝ) ≤ V ^ 2 := by nlinarith
  -- `a·(3/Θ)² ≤ (Θ²/400)·(9/Θ²) = 9/400`.
  have hstep : C4 * (CS + 1) ^ 2 * (3 / Θ) ^ 2 ≤ 9 / 400 := by
    have h3 : (3 / Θ) ^ 2 = 9 / Θ ^ 2 := by ring
    rw [h3]
    have h1 : C4 * (CS + 1) ^ 2 * (9 / Θ ^ 2) ≤ (Θ ^ 2 / 400) * (9 / Θ ^ 2) :=
      mul_le_mul_of_nonneg_right hab (by positivity)
    have h2 : (Θ ^ 2 / 400) * (9 / Θ ^ 2) = 9 / 400 := by field_simp
    linarith
  -- Finally `a·q²/V² ≤ a·(3/Θ)² ≤ 9/400 ≤ 1/2` since `V² ≥ 1`.
  have hA : C4 * (CS + 1) ^ 2 * q ^ 2 / V ^ 2 ≤ C4 * (CS + 1) ^ 2 * (3 / Θ) ^ 2 := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < V ^ 2)]
    have h1 : C4 * (CS + 1) ^ 2 * q ^ 2 ≤ C4 * (CS + 1) ^ 2 * (3 / Θ) ^ 2 :=
      mul_le_mul_of_nonneg_left hq2 ha
    nlinarith [h1, hV2, mul_nonneg ha h32]
  linarith [hA, hstep]

end Work.GM.Energy.EnergyCore2

import Mathlib

/-!
# A uniform lower bound for `sin (π λ)²` on `[1/8, 7/8]`

`sin²` is symmetric about `1/2` and increasing on `[0, 1/2]`, so on `[1/8, 7/8]` the least
value of `sin (π λ)²` is attained at the endpoints `λ = 1/8`, `λ = 7/8`, where it equals
`sin (π/8)² = (2 - √2)/4`.  Since `(2 - √2)/4 ≥ 1/7` (equivalently `√2 ≤ 10/7`), the stated
bound `1/7` holds.
-/

namespace Work.FatouL1

private lemma sin_pi_eighth_nonneg : 0 ≤ Real.sin (Real.pi / 8) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith [Real.pi_pos])

/-- `1/7 ≤ sin (π/8)²`, i.e. `1/7 ≤ (2 - √2)/4`. -/
private lemma sin_pi_eighth_sq_lower : (1 : ℝ) / 7 ≤ Real.sin (Real.pi / 8) ^ 2 := by
  rw [Real.sin_pi_div_eight]
  have hnonneg : 0 ≤ 2 - Real.sqrt 2 := by
    have : Real.sqrt 2 ≤ 2 := by rw [Real.sqrt_le_iff]; norm_num
    linarith
  have hsq : (Real.sqrt (2 - Real.sqrt 2) / 2) ^ 2 = (2 - Real.sqrt 2) / 4 := by
    rw [div_pow, Real.sq_sqrt hnonneg]
    norm_num
  rw [hsq]
  have h2 : Real.sqrt 2 ≤ 10 / 7 := by
    rw [Real.sqrt_le_iff]; norm_num
  nlinarith

/-- On `[1/8, 1/2]` the value `sin (π μ)²` dominates `sin (π/8)²`: `sin` is increasing on
`[-π/2, π/2]` and nonnegative there. -/
private lemma sin_sq_mono_eighth (μ : ℝ) (hμ1 : 1 / 8 ≤ μ) (hμ2 : μ ≤ 1 / 2) :
    Real.sin (Real.pi / 8) ^ 2 ≤ Real.sin (Real.pi * μ) ^ 2 := by
  have hle : Real.sin (Real.pi / 8) ≤ Real.sin (Real.pi * μ) := by
    have h1 : Real.pi / 8 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
    have h2 : Real.pi * μ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      refine ⟨by nlinarith [Real.pi_pos, hμ1], ?_⟩
      have := mul_le_mul_of_nonneg_left hμ2 Real.pi_pos.le
      linarith
    exact Real.monotoneOn_sin h1 h2 (by
      have := mul_le_mul_of_nonneg_left hμ1 Real.pi_pos.le
      linarith)
  exact pow_le_pow_left₀ sin_pi_eighth_nonneg hle 2

theorem sinSqPiLamLower {lam : ℝ} (h1 : 1 / 8 ≤ lam) (h2 : lam ≤ 7 / 8) :
    1 / 7 ≤ Real.sin (Real.pi * lam) ^ 2 := by
  rcases le_or_gt lam (1 / 2) with hcase | hcase
  · exact le_trans sin_pi_eighth_sq_lower (sin_sq_mono_eighth lam h1 hcase)
  · -- replace `lam` by `1 - lam ∈ [1/8, 1/2]`, using `sin (π - x) = sin x`
    have hμ1 : 1 / 8 ≤ 1 - lam := by linarith
    have hμ2 : 1 - lam ≤ 1 / 2 := by linarith
    have hsin : Real.sin (Real.pi * lam) = Real.sin (Real.pi * (1 - lam)) := by
      have : Real.pi * lam = Real.pi - Real.pi * (1 - lam) := by ring
      rw [this, Real.sin_pi_sub]
    rw [hsin]
    exact le_trans sin_pi_eighth_sq_lower (sin_sq_mono_eighth (1 - lam) hμ1 hμ2)

end Work.FatouL1

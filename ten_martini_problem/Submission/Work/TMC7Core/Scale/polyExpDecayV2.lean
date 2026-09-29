import Mathlib

namespace Work.TMC7Core.Scale

/-- Auxiliary explicit bound: for `a > 0` and `q ≥ 1`,
`(q + 1)^2 * exp (-(a*q)) ≤ 24 / a^3`.

This is proved from the Taylor lower bound `exp x ≥ x^3 / 6` for `x ≥ 0`
applied at `x = a*q`, together with `(q+1)^2 ≤ 4 q^2` for `q ≥ 1`. -/
private lemma quad_exp_neg_bound (a q : ℝ) (ha : 0 < a) (hq : 1 ≤ q) :
    (q + 1)^2 * Real.exp (-(a*q)) ≤ 24 / a^3 := by
  have hq0 : 0 ≤ q := by linarith
  have haq0 : 0 ≤ a*q := mul_nonneg ha.le hq0
  have h3 : (a*q)^3 / 6 ≤ Real.exp (a*q) := by
    have h := Real.pow_div_factorial_le_exp (x := a*q) haq0 3
    norm_num [Nat.factorial] at h
    exact h
  have hpos3 : (0:ℝ) < (a*q)^3 / 6 := by positivity
  have h1 : Real.exp (-(a*q)) ≤ 6/(a*q)^3 := by
    rw [Real.exp_neg]
    calc (Real.exp (a*q))⁻¹ ≤ ((a*q)^3/6)⁻¹ := (inv_le_inv₀ (Real.exp_pos _) hpos3).mpr h3
      _ = 6/(a*q)^3 := by rw [inv_div]
  have h2 : (q+1)^2 * Real.exp (-(a*q)) ≤ (q+1)^2 * (6/(a*q)^3) :=
    mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
  refine h2.trans ?_
  have h4 : (q+1)^2 ≤ 4 * q^2 := by nlinarith [hq]
  have hqpos : 0 < q := by linarith
  rw [le_div_iff₀ (by positivity : (0:ℝ) < a^3)]
  have hsimp : 6 / (a*q)^3 * a^3 = 6/q^3 := by field_simp
  rw [mul_assoc, hsimp]
  rw [show (q+1)^2 * (6/q^3) = 6*(q+1)^2/q^3 by ring]
  rw [div_le_iff₀ (by positivity : (0:ℝ) < q^3)]
  nlinarith [h4, hq, hqpos]

theorem polyExpDecayV2 (a : ℝ) (ha : 0 < a) :
    ∃ B T : ℝ, 0 < B ∧ ∀ Q : ℕ, T ≤ (Q : ℝ) →
      ((Q : ℝ) + 1) ^ 2 * Real.exp (-(a * (Q : ℝ))) ≤ B := by
  refine ⟨24 / a^3, 1, by positivity, ?_⟩
  intro Q hQ
  exact quad_exp_neg_bound a (Q:ℝ) ha hQ

end Work.TMC7Core.Scale

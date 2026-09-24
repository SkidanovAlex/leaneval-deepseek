import Mathlib

namespace Work.NumberTheory.Chen.APSwitchUpper

/-! Auxiliary analytic inequality, half 1 of 2, for the crude supersolution pair of the
Rosser–Iwaniec delay system in `Work.NumberTheory.Chen.APSwitchUpper.riPhiSharpCrude`.

`σ ∈ [1,2]` is the variable `s - 1` of the supersolution condition
`∫_{s-1}^b crudeU ≤ s · crudeV s`, where `crudeU u = (9-u)/u` for `u ∈ [1,3]` and
`crudeV s = 6·exp (2-s)`.

Proof route (all constants explicit):
* `9 log (3/σ) = 9 log 2 + 9 log (3/(2σ)) ≤ 9 log 2 + 9 (3/(2σ) - 1) ≤ 27/(2σ) - 69/25`,
  using `Real.log_le_sub_one_of_pos` (i.e. `log x ≤ x - 1`) at `x = 3/(2σ)` and
  Mathlib's `Real.log_two_lt_d9` to bound `log 2 ≤ 6.24/9`.
* With `t = σ - 1 ∈ [0,1]`, convexity of `t ↦ exp (-t)` gives the tangent bound
  `exp (-t) ≥ exp (-t₀) * (1 + t₀ - t)` (from `Real.add_one_le_exp`);
  taking `t₀ = 1/2` gives `exp (1 - σ) ≥ exp (-1/2) * (5/2 - σ)`.
* `exp (-1/2) ≥ 29/48 = 1 - 1/2 + 1/8 - 1/48`: `Real.exp_bound'` at `x = 1/2`, `n = 4`
  gives `exp (1/2) ≤ 2533/1536 ≤ 48/29`, and `exp (-1/2) = (exp (1/2))⁻¹`.
* After multiplying by `σ > 0` the remaining claim is the cubic inequality
  `27/2 + σ² - (94/25)σ ≤ (29/8)σ(σ+1)(5/2-σ)` on `[1,2]`, i.e.
  `-1450σ³ + 1775σ² + 5129σ - 5400 ≥ 0`, which follows by writing it as
  `54 + (σ-1)·(1450(σ-1)(2-σ) + 8354 - 4025σ)` with every factor nonnegative.
No `sorry` in helpers, no new axioms. -/

/-- The tangent (convexity) lower bound for the crude exponential pair. -/
theorem exp_neg_half_ge : (29 : ℝ) / 48 ≤ Real.exp (-(1 / 2)) := by
  have hb := Real.exp_bound' (x := (1 : ℝ) / 2) (by norm_num) (by norm_num) (n := 4)
    (by norm_num)
  have hle : Real.exp (1 / 2) ≤ 48 / 29 := by
    have hsum : ∑ m ∈ Finset.range 4, ((1 : ℝ) / 2) ^ m / (m.factorial : ℝ) = 79 / 48 := by
      norm_num [Finset.sum_range_succ]
    have hrem : ((1 : ℝ) / 2) ^ 4 * ((4 : ℝ) + 1) / ((Nat.factorial 4 : ℝ) * 4) = 5 / 1536 := by
      norm_num [Nat.factorial]
    linarith [hb, hsum, hrem]
  have h := one_div_le_one_div_of_le (Real.exp_pos (1 / 2)) hle
  rw [Real.exp_neg]
  simp only [one_div] at h
  norm_num at h
  exact h

theorem logExpLeft (σ : ℝ) (h1 : 1 ≤ σ) (h2 : σ ≤ 2) :
    9 * Real.log (3 / σ) + σ - 1 ≤ 6 * (σ + 1) * Real.exp (1 - σ) := by
  have hσpos : 0 < σ := by linarith
  -- (1) the logarithmic term is dominated by `27/(2σ) - 69/25`
  have hlog : 9 * Real.log (3 / σ) ≤ 27 / (2 * σ) - 69 / 25 := by
    have hx : 0 < 3 / (2 * σ) := by positivity
    have hsplit : Real.log (3 / σ) = Real.log 2 + Real.log (3 / (2 * σ)) := by
      have he : (3 : ℝ) / σ = 2 * (3 / (2 * σ)) := by field_simp
      rw [he, Real.log_mul (by norm_num) (by positivity)]
    have htan : Real.log (3 / (2 * σ)) ≤ 3 / (2 * σ) - 1 := Real.log_le_sub_one_of_pos hx
    have e9 : 9 * Real.log (3 / σ) = 9 * Real.log 2 + 9 * Real.log (3 / (2 * σ)) := by
      rw [hsplit]; ring
    have htan9 : 9 * Real.log (3 / (2 * σ)) ≤ 9 * (3 / (2 * σ) - 1) := by linarith [htan]
    have h2b : 9 * Real.log 2 ≤ 6.24 := by nlinarith [Real.log_two_lt_d9]
    have e : 9 * (3 / (2 * σ) - 1) = 27 / (2 * σ) - 9 := by ring
    linarith [e9, htan9, h2b, e]
  -- (2) the tangent lower bound for `exp (1 - σ)`
  have hexp : Real.exp (-(1 / 2)) * (5 / 2 - σ) ≤ Real.exp (1 - σ) := by
    have h := Real.add_one_le_exp (3 / 2 - σ)
    have h2 := mul_le_mul_of_nonneg_left h (Real.exp_pos (-(1 / 2))).le
    have he : Real.exp (-(1 / 2)) * Real.exp (3 / 2 - σ) = Real.exp (1 - σ) := by
      rw [← Real.exp_add]; congr 1; ring
    nlinarith [h2, he]
  -- (3) the cubic inequality on `[1,2]`, after multiplying by `σ > 0`
  have hpoly : 27 / 2 + σ ^ 2 - (94 / 25) * σ ≤ 6 * (σ + 1) * (29 / 48) * σ * (5 / 2 - σ) := by
    have hprod : 0 ≤ (σ - 1) * (2 - σ) := mul_nonneg (by linarith) (by linarith)
    nlinarith [hprod]
  have hmain : 27 / (2 * σ) ≤ 6 * (σ + 1) * (29 / 48) * (5 / 2 - σ) - (σ - 94 / 25) := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < 2 * σ)]
    nlinarith [hpoly]
  have hcrude : 9 * Real.log (3 / σ) + σ - 1 ≤ 6 * (σ + 1) * (29 / 48) * (5 / 2 - σ) := by
    linarith [hlog, hmain]
  -- (4) replace `29/48` by `exp (-1/2)` and use the tangent bound
  have hpos : 0 < 6 * (σ + 1) * (5 / 2 - σ) := by
    have : (0 : ℝ) < 5 / 2 - σ := by linarith
    positivity
  have step1 : 6 * (σ + 1) * (29 / 48) * (5 / 2 - σ)
      ≤ 6 * (σ + 1) * Real.exp (-(1 / 2)) * (5 / 2 - σ) := by
    have h := mul_le_mul_of_nonneg_left exp_neg_half_ge (le_of_lt hpos)
    nlinarith [h]
  have step2 : 6 * (σ + 1) * Real.exp (-(1 / 2)) * (5 / 2 - σ)
      ≤ 6 * (σ + 1) * Real.exp (1 - σ) := by
    have h6 : (0 : ℝ) < 6 * (σ + 1) := by positivity
    have h := mul_le_mul_of_nonneg_left hexp (le_of_lt h6)
    nlinarith [h]
  linarith [hcrude, step1, step2]

end Work.NumberTheory.Chen.APSwitchUpper

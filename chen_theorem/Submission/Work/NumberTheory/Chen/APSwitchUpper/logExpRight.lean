import Mathlib

namespace Work.NumberTheory.Chen.APSwitchUpper

/-! Auxiliary analytic inequality, half 2 of 2, for the crude supersolution pair of the
Rosser–Iwaniec delay system in `Work.NumberTheory.Chen.APSwitchUpper.riPhiSharpCrude`.

`σ ∈ [2,3]` is the variable `s - 1` of the supersolution condition
`∫_{s-1}^b crudeU ≤ s · crudeV s`, where `crudeU u = (9-u)/u` for `u ∈ [1,3]` and
`crudeV s = 6·exp (2-s)`.

The proof follows the route sketched in the original request, with all constants explicit:

* `9 log (3/σ) ≤ 9 (3/σ - 1) = 27/σ - 9` by `Real.log_le_sub_one_of_pos` at `x = 3/σ`
  (the tangent of the concave function `log` at `1`).
* With `t = σ - 1 ∈ [1,2]`, convexity of `t ↦ exp (-t)` gives the tangent bound
  `exp (-t) ≥ exp (-t₀)(1 + t₀ - t)` (from `Real.add_one_le_exp`); taking `t₀ = 3/2` yields
  `exp (1-σ) ≥ exp (-3/2) * (7/2 - σ)` (valid for every `σ`, in fact).
* `exp (-3/2) ≥ 11/50`: `exp (-3/2) = (exp (-1/2))³`, and `Real.exp_bound` at `x = -1/2`
  with `n = 5` gives `exp (-1/2) ≥ 233/384 - 1/3200 = 2911/4800`, whose cube exceeds `11/50`.
* After multiplying by `σ > 0` the claim is a cubic inequality on `[2,3]`; it is written as
  its value `22/25` at `σ = 2` plus `(σ-2)` times a factor that is positive on `[2,3]`. -/

/-- `exp (-3/2) ≥ 11/50`, by the exponential series bound `Real.exp_bound` at `x = -1/2`. -/
private theorem exp_neg_three_halves_ge : (11 : ℝ) / 50 ≤ Real.exp (-(3 / 2 : ℝ)) := by
  have hb : |Real.exp (-(1 / 2 : ℝ)) -
        ∑ m ∈ Finset.range 5, (-(1 / 2 : ℝ)) ^ m / (m.factorial : ℝ)| ≤ (1 : ℝ) / 3200 := by
    have h := Real.exp_bound (x := -(1 / 2 : ℝ)) (by norm_num) (n := 5) (by norm_num)
    have hR : |(-(1 / 2 : ℝ))| ^ 5 *
        ((↑(Nat.succ 5) : ℝ) / (↑(Nat.factorial 5) * ↑(5 : ℕ))) = (1 : ℝ) / 3200 := by
      norm_num
    rw [hR] at h
    exact h
  have hsum : (∑ m ∈ Finset.range 5, (-(1 / 2 : ℝ)) ^ m / (m.factorial : ℝ)) = 233 / 384 := by
    norm_num [Finset.sum_range_succ]
  have hge : (233 : ℝ) / 384 - 1 / 3200 ≤ Real.exp (-(1 / 2 : ℝ)) := by
    have h := (abs_sub_le_iff.1 hb).2
    rw [hsum] at h
    linarith
  have hnum : (11 : ℝ) / 50 ≤ ((233 : ℝ) / 384 - 1 / 3200) ^ 3 := by norm_num
  have hpow : ((233 : ℝ) / 384 - 1 / 3200) ^ 3 ≤ (Real.exp (-(1 / 2 : ℝ))) ^ 3 :=
    pow_le_pow_left₀ (by norm_num) hge 3
  calc (11 : ℝ) / 50 ≤ ((233 : ℝ) / 384 - 1 / 3200) ^ 3 := hnum
    _ ≤ (Real.exp (-(1 / 2 : ℝ))) ^ 3 := hpow
    _ = Real.exp (-(3 / 2 : ℝ)) := by
        rw [← Real.exp_nat_mul]
        rw [show (↑(3 : ℕ) : ℝ) * (-(1 / 2)) = -(3 / 2) by norm_num]

/-- The tangent bound for the exponential: `exp (1-σ) ≥ exp (-3/2) * (7/2 - σ)`, the tangent
of `t ↦ exp (-t)` at `t = 3/2` evaluated at `t = σ - 1`. -/
private theorem exp_tangent (σ : ℝ) :
    Real.exp (-(3 / 2)) * (7 / 2 - σ) ≤ Real.exp (1 - σ) := by
  have hsplit : Real.exp (-(3 / 2)) * (7 / 2 - σ)
      ≤ Real.exp (-(3 / 2)) * Real.exp (5 / 2 - σ) := by
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    have h := Real.add_one_le_exp (5 / 2 - σ)
    linarith
  have heq : Real.exp (-(3 / 2)) * Real.exp (5 / 2 - σ) = Real.exp (1 - σ) := by
    rw [← Real.exp_add]
    congr 1
    ring
  linarith [hsplit, heq]

/-- The cubic part of the estimate: for `σ ∈ [2,3]`,
`27 + σ² - 10σ ≤ 6σ(σ+1)(11/50)(7/2 - σ)`.  Written as its value `22/25` at `σ = 2` plus
`(σ-2)` times the positive factor `(33/25)(-σ² + σ/2 + 9/2) + (8-σ)`, which itself equals
`26/25 + (3-σ)((33/25)(σ+5/2) + 1)` on `[2,3]`. -/
private theorem cubic_le (σ : ℝ) (h1 : 2 ≤ σ) (h2 : σ ≤ 3) :
    27 + σ ^ 2 - 10 * σ ≤ 6 * σ * (σ + 1) * ((11 : ℝ) / 50) * (7 / 2 - σ) := by
  have hq : 0 ≤ (33 / 25 : ℝ) * (-σ ^ 2 + σ / 2 + 9 / 2) + (8 - σ) := by
    have hfac : (33 / 25 : ℝ) * (-σ ^ 2 + σ / 2 + 9 / 2) + (8 - σ)
        = 26 / 25 + (3 - σ) * ((33 / 25) * (σ + 5 / 2) + 1) := by ring
    rw [hfac]
    have hg : (0 : ℝ) ≤ (33 / 25) * (σ + 5 / 2) + 1 := by linarith
    exact add_nonneg (by norm_num) (mul_nonneg (by linarith) hg)
  have hgd : 6 * σ * (σ + 1) * ((11 : ℝ) / 50) * (7 / 2 - σ) - (27 + σ ^ 2 - 10 * σ)
      = (σ - 2) * ((33 / 25 : ℝ) * (-σ ^ 2 + σ / 2 + 9 / 2) + (8 - σ)) + 22 / 25 := by ring
  have h3 : (0 : ℝ) ≤ σ - 2 := by linarith
  have h4 : (0 : ℝ) ≤
      (σ - 2) * ((33 / 25 : ℝ) * (-σ ^ 2 + σ / 2 + 9 / 2) + (8 - σ)) + 22 / 25 := by
    have h5 := mul_nonneg h3 hq
    linarith
  linarith [hgd, h4]

theorem logExpRight (σ : ℝ) (h1 : 2 ≤ σ) (h2 : σ ≤ 3) :
    9 * Real.log (3 / σ) + σ - 1 ≤ 6 * (σ + 1) * Real.exp (1 - σ) := by
  have hσpos : 0 < σ := by linarith
  -- Step 1: bound the logarithm by its tangent at `1`, clearing the `9`.
  have hlog : 9 * Real.log (3 / σ) ≤ 27 / σ - 9 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 / σ by positivity)
    have hm := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 9)
    have heq : 9 * ((3 : ℝ) / σ - 1) = 27 / σ - 9 := by
      field_simp
      ring
    linarith [hm, heq]
  -- Step 2: the cubic, after multiplying by `σ > 0`.
  have hcub : 27 + σ ^ 2 - 10 * σ ≤ 6 * σ * (σ + 1) * ((11 : ℝ) / 50) * (7 / 2 - σ) :=
    cubic_le σ h1 h2
  have hstep2 : 27 / σ + σ - 10 ≤ 6 * (σ + 1) * ((11 : ℝ) / 50) * (7 / 2 - σ) := by
    have heq : (27 / σ + σ - 10) * σ = 27 + σ ^ 2 - 10 * σ := by field_simp
    have hmul : (27 / σ + σ - 10) * σ
        ≤ (6 * (σ + 1) * ((11 : ℝ) / 50) * (7 / 2 - σ)) * σ := by
      rw [heq]
      calc 27 + σ ^ 2 - 10 * σ ≤ 6 * σ * (σ + 1) * ((11 : ℝ) / 50) * (7 / 2 - σ) := hcub
        _ = (6 * (σ + 1) * ((11 : ℝ) / 50) * (7 / 2 - σ)) * σ := by ring
    exact le_of_mul_le_mul_right hmul hσpos
  -- Step 3: the exponential lower bound.
  have hprod : ((11 : ℝ) / 50) * (7 / 2 - σ) ≤ Real.exp (1 - σ) := by
    have h37 : (0 : ℝ) ≤ 7 / 2 - σ := by linarith
    have h1' := mul_le_mul_of_nonneg_right exp_neg_three_halves_ge h37
    linarith [h1', exp_tangent σ]
  have h6 : (0 : ℝ) ≤ 6 * (σ + 1) := by linarith
  have hstep3 : 6 * (σ + 1) * ((11 : ℝ) / 50) * (7 / 2 - σ)
      ≤ 6 * (σ + 1) * Real.exp (1 - σ) := by
    calc 6 * (σ + 1) * ((11 : ℝ) / 50) * (7 / 2 - σ)
        = 6 * (σ + 1) * (((11 : ℝ) / 50) * (7 / 2 - σ)) := by ring
      _ ≤ 6 * (σ + 1) * Real.exp (1 - σ) := mul_le_mul_of_nonneg_left hprod h6
  linarith [hlog, hstep2, hstep3]

end Work.NumberTheory.Chen.APSwitchUpper

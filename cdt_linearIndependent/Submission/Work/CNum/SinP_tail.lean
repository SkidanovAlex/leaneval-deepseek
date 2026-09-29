import Mathlib
import Submission.Work.CNum.cosT_bound

/-!
# Two-sided bound for the sine Taylor polynomial `sinP x 11` on `[0, π/4]`

For `0 ≤ x ≤ π/4` we show that the partial sum
`sinP x 11 = Σ_{i ≤ 11} (-1)^i x^{2i+1}/(2i+1)!` brackets `sin x`:
`sinP x 11 ≤ sin x ≤ sinP x 11 + 2/25!`.

The proof goes through the Lagrange remainder bound `sin_bound` at `P = 12`
(so the remainder is controlled by `x^26/26!`) together with the increment
identity `sinP x 12 = sinP x 11 + x^25/25!` (the `i = 12` term is positive).
With `0 ≤ x ≤ 1` this gives `0 ≤ sin x - sinP x 11` on the one hand and
`sin x - sinP x 11 ≤ x^25/25! + x^26/26! ≤ 2/25!` on the other.
-/

namespace Work.CNum

/-- Successor relation for the sine partial sums. -/
lemma sinP_succ (x : ℝ) (P : ℕ) :
    sinP x (P + 1) =
      sinP x P + (-1 : ℝ) ^ (P + 1) * x ^ (2 * P + 3) / ((2 * P + 3).factorial : ℝ) := by
  rw [sinP, sinP, Finset.sum_range_succ]
  rw [show 2 * (P + 1) + 1 = 2 * P + 3 from by ring]

theorem SinP_tail {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ Real.pi / 4) :
    sinP x 11 ≤ Real.sin x ∧ Real.sin x ≤ sinP x 11 + 2 * ((Nat.factorial 25 : ℝ))⁻¹ := by
  have hx1 : x ≤ 1 := h1.trans (by have := Real.pi_le_four; linarith : Real.pi / 4 ≤ 1)
  have hx25nn : (0 : ℝ) ≤ x ^ 25 := pow_nonneg h0 25
  have hx1pow : x ^ 26 ≤ x ^ 25 := pow_le_pow_of_le_one h0 hx1 (by norm_num)
  have hsin : |Real.sin x - sinP x 12| ≤ x ^ 26 / ((Nat.factorial 26 : ℝ)) := by
    have h := sin_bound x h0 12
    simpa using h
  have h12 : sinP x 12 = sinP x 11 + x ^ 25 / ((Nat.factorial 25 : ℝ)) := by
    have h := sinP_succ x 11
    have e1 : (2 * 11 + 3 : ℕ) = 25 := by norm_num
    have e2 : (-1 : ℝ) ^ (11 + 1) = 1 := by norm_num
    simp only [e1, e2] at h
    simpa using h
  have hfac : (Nat.factorial 25 : ℝ) ≤ (Nat.factorial 26 : ℝ) := by
    exact_mod_cast Nat.factorial_le (by norm_num : 25 ≤ 26)
  have hA : x ^ 26 / ((Nat.factorial 26 : ℝ)) ≤ x ^ 25 / ((Nat.factorial 25 : ℝ)) := by
    calc x ^ 26 / (Nat.factorial 26 : ℝ) ≤ x ^ 25 / (Nat.factorial 26 : ℝ) :=
          div_le_div_of_nonneg_right hx1pow (by positivity)
      _ ≤ x ^ 25 / (Nat.factorial 25 : ℝ) :=
          div_le_div_of_nonneg_left hx25nn (by positivity) hfac
  refine ⟨?_, ?_⟩
  · -- lower bound: `sinP x 11 = sinP x 12 - x^25/25! ≤ sin x`
    have h1' : -(x ^ 26 / (Nat.factorial 26 : ℝ)) ≤ Real.sin x - sinP x 12 :=
      le_trans (neg_le_neg hsin) (neg_abs_le _)
    have h1'' : sinP x 11 = sinP x 12 - x ^ 25 / ((Nat.factorial 25 : ℝ)) := by
      rw [h12]; ring
    rw [h1'']
    linarith [h1', hA]
  · -- upper bound: `sin x - sinP x 11 ≤ x^25/25! + x^26/26! ≤ 2/25!`
    have h2' : Real.sin x - sinP x 12 ≤ x ^ 26 / (Nat.factorial 26 : ℝ) :=
      le_trans (le_abs_self _) hsin
    have hX : x ^ 25 / ((Nat.factorial 25 : ℝ)) ≤ ((Nat.factorial 25 : ℝ))⁻¹ := by
      rw [inv_eq_one_div]
      gcongr
      exact pow_le_one₀ h0 hx1
    have key : Real.sin x - sinP x 11 =
        (Real.sin x - sinP x 12) + x ^ 25 / ((Nat.factorial 25 : ℝ)) := by
      rw [h12]; ring
    have hgoal : Real.sin x - sinP x 11 ≤ 2 * ((Nat.factorial 25 : ℝ))⁻¹ := by
      rw [key]; linarith [h2', hA, hX]
    linarith [hgoal]

end Work.CNum

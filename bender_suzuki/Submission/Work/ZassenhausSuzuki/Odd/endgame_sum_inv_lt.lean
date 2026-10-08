import Mathlib
import Submission.Work.ZassenhausSuzuki.Odd.endgame_card_le_three

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausSuzuki.Odd

/-- Endgame arithmetic bound: the sum of reciprocals `∑ 1/k a` over the set `V` of
admissible primes is strictly less than `5/4`.

Each `a ∈ V` satisfies `m a * a * k a = Q` with `Q = q^2 (q-1) (q^2+1)` and `k a ∈ {2,4}`.
Dividing by `a * k a`, the (rational) relation `Q = m a * a * k a` gives `1/k a = m a * a / Q`,
and since `a ≥ 5`, `4 (m a · a) ≤ 5 (m a · (a-1))`, i.e. `1/k a ≤ (5/(4Q)) · m a (a-1)`.
Summing and using `∑ m a (a-1) = Q - q^4 - B ≤ Q - q^4 < Q` with `Q > 0` yields
`∑ 1/k a ≤ (5/(4Q))(Q - q^4) < (5/(4Q))·Q = 5/4`. -/
lemma endgame_sum_inv_lt {q B : ℕ} {V : Finset ℕ} {m k : ℕ → ℕ}
    (hN : 0 < q ^ 2 * (q - 1) * (q ^ 2 + 1))
    (hV : ∀ a ∈ V, 5 ≤ a) (hk : ∀ a ∈ V, k a = 2 ∨ k a = 4)
    (hm : ∀ a ∈ V, m a * a * k a = q ^ 2 * (q - 1) * (q ^ 2 + 1))
    (hsum1 : ∑ a ∈ V, (m a : ℚ) * (a - 1)
        = (q ^ 2 * (q - 1) * (q ^ 2 + 1) : ℚ) - (q : ℚ) ^ 4 - (B : ℚ)) :
    ∑ a ∈ V, (1 : ℚ) / (k a : ℚ) < 5 / 4 := by
  have hq0 : q ≠ 0 := by rintro rfl; norm_num at hN
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr hq0
  have hq2 : 2 ≤ q := by
    by_contra h; push Not at h
    interval_cases q
    all_goals norm_num at hN
  set Q : ℚ := (q : ℚ) ^ 2 * ((q : ℚ) - 1) * ((q : ℚ) ^ 2 + 1) with hQ
  have hQpos : 0 < Q := by
    rw [hQ]
    have h2 : (0 : ℚ) < (q : ℚ) - 1 := by
      have : (1 : ℚ) < (q : ℚ) := by exact_mod_cast hq2
      linarith
    positivity
  have hcs : ((q ^ 2 * (q - 1) * (q ^ 2 + 1) : ℕ) : ℚ) = Q := by
    rw [hQ]; push_cast [Nat.cast_sub hq1]; ring
  -- `Q` is the common value `m a * a * k a` (cast to `ℚ`)
  have hQa : ∀ a ∈ V, Q = (m a : ℚ) * (a : ℚ) * (k a : ℚ) := by
    intro a ha
    have h := hm a ha
    have h2 : ((m a * a * k a : ℕ) : ℚ)
        = ((q ^ 2 * (q - 1) * (q ^ 2 + 1) : ℕ) : ℚ) := by
      exact_mod_cast h
    rw [hcs] at h2
    push_cast at h2
    exact h2.symm
  -- per-term bound
  have hterm : ∀ a ∈ V, (1 : ℚ) / (k a : ℚ) ≤ (5 / (4 * Q)) * ((m a : ℚ) * ((a : ℚ) - 1)) := by
    intro a ha
    have hka : (k a : ℚ) ≠ 0 := by rcases hk a ha with h | h <;> (rw [h]; norm_num)
    have hmain : (1 : ℚ) / (k a : ℚ) = (m a : ℚ) * (a : ℚ) / Q := by
      field_simp
      rw [hQa a ha]; ring
    rw [hmain]
    have hc := endgame_contrib_ge_rat (m a) a (hV a ha)
    have h4Q : (0 : ℚ) < 4 * Q := by linarith
    rw [div_mul_eq_mul_div]
    rw [div_le_div_iff₀ hQpos h4Q]
    nlinarith [hc, hQpos]
  calc ∑ a ∈ V, (1 : ℚ) / (k a : ℚ)
      ≤ (5 / (4 * Q)) * ∑ a ∈ V, (m a : ℚ) * ((a : ℚ) - 1) := by
        rw [Finset.mul_sum]; exact Finset.sum_le_sum (fun a ha => hterm a ha)
    _ = (5 / (4 * Q)) * (Q - (q : ℚ) ^ 4 - (B : ℚ)) := by rw [hsum1]
    _ ≤ (5 / (4 * Q)) * (Q - (q : ℚ) ^ 4) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith [show (0 : ℚ) ≤ (B : ℚ) by positivity]
    _ < (5 / (4 * Q)) * Q := by
        apply mul_lt_mul_of_pos_left _ (by positivity)
        have : (0 : ℚ) < (q : ℚ) ^ 4 := by positivity
        linarith
    _ = 5 / 4 := by field_simp

end Work.ZassenhausSuzuki.Odd

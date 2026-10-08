import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausSuzuki.Odd

lemma endgame_sum_T {q : ℕ} {V : Finset ℕ} {m k : ℕ → ℕ}
    (hN : 0 < q ^ 2 * (q - 1) * (q ^ 2 + 1))
    (hV : ∀ a ∈ V, 5 ≤ a) (hk : ∀ a ∈ V, k a = 2 ∨ k a = 4)
    (hm : ∀ a ∈ V, m a * a * k a = q ^ 2 * (q - 1) * (q ^ 2 + 1))
    (hsum2 : ∑ a ∈ V, (m a : ℚ) * a * (a - 1)
        = (q ^ 2 * (q - 1) * (q ^ 2 + 1) : ℚ) * (q - 1)) :
    ∑ a ∈ V, ((a : ℚ) - 1) / (k a : ℚ) = (q : ℚ) - 1 := by
  -- The whole product `q^2 * (q-1) * (q^2+1)` is positive, hence `q ≥ 1`.
  have hq1 : 1 ≤ q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · rw [h] at hN; norm_num at hN
    · exact h
  -- Its rational value is non-zero, so we may cancel it from the two sides.
  have hNnz : (q : ℚ) ^ 2 * ((q : ℚ) - 1) * ((q : ℚ) ^ 2 + 1) ≠ 0 := by
    have hpos : (0:ℚ) < (q:ℚ)^2 * ((q:ℚ) - 1) * ((q:ℚ)^2 + 1) := by
      have hcast : ((q ^ 2 * (q - 1) * (q ^ 2 + 1) : ℕ) : ℚ)
          = (q:ℚ)^2 * ((q:ℚ) - 1) * ((q:ℚ)^2 + 1) := by
        push_cast; rw [Nat.cast_sub hq1]; norm_num
      rw [← hcast]; exact_mod_cast hN
    exact ne_of_gt hpos
  -- For each `a ∈ V`, from `m a * a * k a = N` we get
  -- `(m a) * a = N / (k a)` and hence `(m a) * a * (a-1) = N * ((a-1)/(k a))`.
  have key : ∀ a ∈ V, (m a : ℚ) * (a : ℚ) * ((a : ℚ) - 1)
      = ((q:ℚ)^2 * ((q:ℚ) - 1) * ((q:ℚ)^2 + 1)) * (((a:ℚ) - 1) / (k a : ℚ)) := by
    intro a ha
    have hkq : (k a : ℚ) ≠ 0 := by rcases hk a ha with h | h <;> rw [h] <;> norm_num
    have hmcast : (m a : ℚ) * (a : ℚ) * (k a : ℚ)
        = (q:ℚ)^2 * ((q:ℚ)-1) * ((q:ℚ)^2+1) := by
      have h := hm a ha
      have h2 : ((m a * a * k a : ℕ) : ℚ) = ((q^2*(q-1)*(q^2+1) : ℕ) : ℚ) := by rw [h]
      push_cast at h2
      rw [Nat.cast_sub hq1] at h2
      exact h2
    have h1 : (m a : ℚ) * (a : ℚ)
        = ((q:ℚ)^2 * ((q:ℚ)-1) * ((q:ℚ)^2+1)) / (k a : ℚ) := by
      rw [eq_div_iff hkq]; exact hmcast
    rw [h1]; ring
  -- Sum the identity over `V`: this factors `N` out of the sum.
  have hsum_eq : (∑ a ∈ V, (m a : ℚ) * (a:ℚ) * ((a:ℚ)-1))
      = ((q:ℚ)^2 * ((q:ℚ)-1) * ((q:ℚ)^2+1)) * ∑ a ∈ V, (((a:ℚ)-1)/(k a:ℚ)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun a ha => key a ha)
  -- Compare with `hsum2` and cancel the non-zero factor `N`.
  have hmain : ((q:ℚ)^2 * ((q:ℚ)-1) * ((q:ℚ)^2+1)) * ∑ a ∈ V, (((a:ℚ)-1)/(k a:ℚ))
      = ((q:ℚ)^2 * ((q:ℚ)-1) * ((q:ℚ)^2+1)) * ((q:ℚ) - 1) := by
    rw [← hsum_eq]
    exact hsum2
  exact mul_left_cancel₀ hNnz hmain

end Work.ZassenhausSuzuki.Odd

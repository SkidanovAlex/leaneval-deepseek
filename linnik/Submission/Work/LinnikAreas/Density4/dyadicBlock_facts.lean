import Mathlib

namespace Work.LinnikAreas.Density4

/-!
# Elementary facts about the dyadic blocks `⌊V / 2^m⌋`

For a fixed natural number `V`, the quantity `b_m = ⌊(V : ℝ) / 2 ^ m⌋` is the
`m`-th dyadic block of `V` (roughly the number of multiples of `2^m` not
exceeding `V`).  We record the four facts used by the density argument:

* `b_0 = V`;
* `b_{V+1} = 0` (the blocks die out past the size of `V`);
* `b` is non-increasing in `m`;
* if `1 ≤ δ ≤ b_m`, then `2 ^ m ≤ V / δ` (a block of size at least `δ`
  certifies `δ * 2 ^ m ≤ V`).
-/

theorem dyadicBlock_facts (V : ℕ) :
    Nat.floor ((V : ℝ) / (2 : ℝ) ^ 0) = V ∧
    Nat.floor ((V : ℝ) / (2 : ℝ) ^ (V + 1)) = 0 ∧
    (∀ m : ℕ, Nat.floor ((V : ℝ) / (2 : ℝ) ^ (m + 1)) ≤ Nat.floor ((V : ℝ) / (2 : ℝ) ^ m)) ∧
    (∀ m δ : ℕ, 1 ≤ δ → δ ≤ Nat.floor ((V : ℝ) / (2 : ℝ) ^ m) →
      (2 : ℝ) ^ m ≤ (V : ℝ) / (δ : ℝ)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `b_0 = V`
    simp [Nat.floor_natCast]
  · -- `b_{V+1} = 0`, because `V < 2^(V+1)`
    rw [Nat.floor_eq_zero, div_lt_one (by positivity)]
    have h : V < 2 ^ (V + 1) :=
      lt_of_lt_of_le Nat.lt_two_pow_self
        (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ V))
    exact_mod_cast h
  · -- monotonicity in `m`
    intro m
    apply Nat.floor_mono
    have hc : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
    have hle : (2 : ℝ) ^ m ≤ (2 : ℝ) ^ (m + 1) := by
      exact_mod_cast (Nat.pow_le_pow_right (by norm_num : (1 : ℕ) ≤ 2) (Nat.le_succ m))
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg V) hc hle
  · -- a block of size `≥ δ` forces `2^m ≤ V / δ`
    intro m δ h1 h2
    have hδR : (δ : ℝ) ≤ (V : ℝ) / (2 : ℝ) ^ m := by
      have a : (δ : ℝ) ≤ (Nat.floor ((V : ℝ) / (2 : ℝ) ^ m) : ℝ) := by exact_mod_cast h2
      have b : (Nat.floor ((V : ℝ) / (2 : ℝ) ^ m) : ℝ) ≤ (V : ℝ) / (2 : ℝ) ^ m :=
        Nat.floor_le (by positivity)
      linarith
    have hδpos : (0 : ℝ) < δ := by exact_mod_cast h1
    have hpow : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
    have hmul : (δ : ℝ) * (2 : ℝ) ^ m ≤ (V : ℝ) := by
      have := mul_le_mul_of_nonneg_right hδR (le_of_lt hpow)
      rwa [div_mul_cancel₀ _ (ne_of_gt hpow)] at this
    rw [le_div_iff₀ hδpos]
    simpa [mul_comm] using hmul

end Work.LinnikAreas.Density4

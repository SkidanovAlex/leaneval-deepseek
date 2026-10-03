import Mathlib

namespace Work.FIArea2.Count

/-- For `H ≥ 1` and any real `a`, there is a dyadic level `n` that is large enough
to dominate `a` against the weight `2^n H`, yet small enough that the
(squared) dyadic weight `(1/4)^n` still dominates `(1 + a²/H²)⁻¹`. -/
lemma exists_dyadic_scale (H : ℝ) (hH : 1 ≤ H) (a : ℝ) :
    ∃ n : ℕ, a ≤ (2:ℝ)^n * H ∧ (1 + a^2/H^2)⁻¹ ≤ 4*(1/4:ℝ)^n := by
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hex : ∃ n : ℕ, a ≤ (2:ℝ)^n * H := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (a / H) (by norm_num : (1:ℝ) < 2)
    rw [div_lt_iff₀ hHpos] at hn
    exact ⟨n, le_of_lt hn⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  set n := Nat.find hex with hn
  have hspec : a ≤ (2:ℝ)^n * H := by rw [hn]; exact Nat.find_spec hex
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · rw [h0]
    have hle1 : (1 + a^2/H^2)⁻¹ ≤ 1 := by
      apply inv_le_one_of_one_le₀
      have : (0:ℝ) ≤ a^2/H^2 := div_nonneg (sq_nonneg a) (le_of_lt (by positivity))
      linarith
    calc (1 + a^2/H^2)⁻¹ ≤ 1 := hle1
      _ ≤ 4*(1/4:ℝ)^0 := by norm_num
  · have hmin : ¬ (a ≤ (2:ℝ)^(n-1) * H) := by
      have : n - 1 < Nat.find hex := by rw [← hn]; exact Nat.sub_one_lt (by omega)
      exact Nat.find_min hex this
    have hlt : (2:ℝ)^(n-1) * H < a := lt_of_not_ge hmin
    have hn_eq : n = (n-1) + 1 := (Nat.succ_pred_eq_of_pos hpos).symm
    have h2 : (2:ℝ)^n * H < 2*a := by
      have h1 : (2:ℝ)^n = (2:ℝ)^(n-1) * 2 := by
        nth_rewrite 1 [hn_eq]; rw [pow_succ]
      rw [h1]
      nlinarith [hlt]
    have h4n : (4:ℝ)^n * H^2 ≤ 4*a^2 := by
      have hsq : ((2:ℝ)^n * H)^2 < (2*a)^2 := by
        apply sq_lt_sq'
        · nlinarith [hlt, show (0:ℝ) < (2:ℝ)^(n-1) by positivity]
        · exact h2
      rw [mul_pow, show ((2:ℝ)^n)^2 = (4:ℝ)^n by
            rw [← pow_mul, show n * 2 = 2 * n by omega, pow_mul]; norm_num] at hsq
      nlinarith [hsq]
    rw [show (1 + a^2/H^2)⁻¹ = H^2/(H^2+a^2) by field_simp]
    rw [div_le_iff₀ (by positivity : (0:ℝ) < H^2 + a^2)]
    have huv : (4:ℝ)^n * (1/4:ℝ)^n = 1 := by rw [← mul_pow]; norm_num
    have h1 : (0:ℝ) ≤ (1/4)^n := by positivity
    nlinarith [h4n, huv, h1, sq_nonneg a, sq_nonneg H]

theorem dyadic_weight_pointwise
    (H : ℝ) (hH : 1 ≤ H) (X : ℕ → ℕ)
    (hX : ∀ j, (2:ℝ) ^ j * H ≤ (X j : ℝ)) :
    ∃ k : ℤ → ℕ,
      (∀ x : ℤ, |(x : ℝ)| ≤ (X (k x) : ℝ)) ∧
      (∀ x : ℤ, (1 + (x : ℝ) ^ 2 / H ^ 2)⁻¹ ≤ 4 * (1/4 : ℝ) ^ (k x)) := by
  choose k hk1 hk2 using fun x : ℤ => exists_dyadic_scale H hH |(x : ℝ)|
  exact ⟨k, fun x => le_trans (hk1 x) (hX (k x)), fun x => by
    have h := hk2 x
    rwa [sq_abs] at h⟩

end Work.FIArea2.Count

import Mathlib

set_option linter.unusedVariables false

namespace Work.NumberTheory.Chen.BTermCount

/-!
# A geometric-tail bound for the `B`-term dyadic sum

The estimate

```
∑_{k₀ ≤ k < K} (2^k)⁻¹ √((U + 4·2^{2k}) U) √((V + 4·2^{2k}) B₂)
  ≤ √(U B₂) (2 √(UV)/2^{k₀} + 2 √U · K + 2 √V · K + 4 · 2^K)
```

for `U, V, B₂ ≥ 0`.

The point is that `4 · 2^{2k} = (2 · 2^k)²`, so `√(U + 4·2^{2k}) ≤ √U + 2·2^k`; multiplying the two
square roots out produces the geometric series `∑ 2^{-k}` (bounded by `2·2^{-k₀}`) and
`∑ 2^k` (bounded by `2^K`).
-/

/-- `√(W + 4·2^{2k}) ≤ √W + 2·2^k`: the radicand is `(√W)² + (2·2^k)²`. -/
private lemma sqrt_add_four_pow_le (W : ℝ) (hW : 0 ≤ W) (k : ℕ) :
    Real.sqrt (W + 4 * (2:ℝ)^(2*k)) ≤ Real.sqrt W + 2*(2:ℝ)^k := by
  have hpow : (2:ℝ)^(2*k) = ((2:ℝ)^k)^2 := by rw [Nat.mul_comm 2 k, pow_mul]
  have hkey : W + 4 * (2:ℝ)^(2*k) = (Real.sqrt W)^2 + (2*(2:ℝ)^k)^2 := by
    rw [hpow, Real.sq_sqrt hW]; ring
  rw [hkey, Real.sqrt_le_left (by positivity)]
  nlinarith [Real.sqrt_nonneg W, pow_nonneg (show (0:ℝ) ≤ 2 by norm_num) k]

/-- Elementary product bound: `a⁻¹ s1 x s3 z ≤ x z (x y a⁻¹ + 2x + 2y + 4a)` for `s1 ≤ x + 2a`,
`s3 ≤ y + 2a`, all quantities nonnegative and `a > 0`. -/
private lemma key_prod {a x y z s1 s3 : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (ha : 0 < a)
    (hs1 : s1 ≤ x + 2*a) (hs3 : s3 ≤ y + 2*a) (hs3n : 0 ≤ s3) (hs1n : 0 ≤ s1) :
    a⁻¹ * s1 * x * s3 * z ≤ x * z * (x * y * a⁻¹ + 2*x + 2*y + 4*a) := by
  have h1 : s1 * s3 ≤ (x + 2*a) * (y + 2*a) := by
    apply mul_le_mul hs1 hs3
    · linarith
    · linarith
  have h2 : x * z * a⁻¹ * (s1 * s3) ≤ x * z * a⁻¹ * ((x + 2*a) * (y + 2*a)) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have e1 : a⁻¹ * s1 * x * s3 * z = x * z * a⁻¹ * (s1 * s3) := by ring
  have e2 : x * z * a⁻¹ * ((x + 2*a) * (y + 2*a)) = x * z * (x * y * a⁻¹ + 2*x + 2*y + 4*a) := by
    have ha' : a ≠ 0 := ne_of_gt ha
    field_simp
    ring
  rw [e1, ← e2]
  exact h2

/-- Termwise bound for the dyadic sum. -/
private lemma term_le (U V B : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hB : 0 ≤ B) (k : ℕ) :
    ((2:ℝ)^k)⁻¹ * Real.sqrt ((U + 4*(2:ℝ)^(2*k)) * U) * Real.sqrt ((V + 4*(2:ℝ)^(2*k)) * B)
      ≤ Real.sqrt (U*B) * (Real.sqrt (U*V) * ((2:ℝ)^k)⁻¹ + 2*Real.sqrt U + 2*Real.sqrt V + 4*(2:ℝ)^k) := by
  have hs1 : Real.sqrt (U + 4*(2:ℝ)^(2*k)) ≤ Real.sqrt U + 2*(2:ℝ)^k := sqrt_add_four_pow_le U hU k
  have hs3 : Real.sqrt (V + 4*(2:ℝ)^(2*k)) ≤ Real.sqrt V + 2*(2:ℝ)^k := sqrt_add_four_pow_le V hV k
  have hU4 : 0 ≤ U + 4 * (2:ℝ)^(2*k) := by
    have := pow_nonneg (show (0:ℝ) ≤ 2 by norm_num) (2*k); nlinarith
  have hV4 : 0 ≤ V + 4 * (2:ℝ)^(2*k) := by
    have := pow_nonneg (show (0:ℝ) ≤ 2 by norm_num) (2*k); nlinarith
  have e1 : Real.sqrt ((U + 4*(2:ℝ)^(2*k)) * U) = Real.sqrt (U + 4*(2:ℝ)^(2*k)) * Real.sqrt U :=
    Real.sqrt_mul hU4 U
  have e3 : Real.sqrt ((V + 4*(2:ℝ)^(2*k)) * B) = Real.sqrt (V + 4*(2:ℝ)^(2*k)) * Real.sqrt B :=
    Real.sqrt_mul hV4 B
  have eUB : Real.sqrt (U*B) = Real.sqrt U * Real.sqrt B := Real.sqrt_mul hU B
  have eUV : Real.sqrt (U*V) = Real.sqrt U * Real.sqrt V := Real.sqrt_mul hU V
  rw [e1, e3, eUB, eUV]
  exact le_of_eq_of_le (by ring)
    (key_prod (Real.sqrt_nonneg U) (Real.sqrt_nonneg V) (Real.sqrt_nonneg B)
      (by positivity) hs1 hs3 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

/-- The finite geometric sum `∑_{i<n} 2^{-i} ≤ 2`. -/
private lemma geom_inv_two_sum_le (n : ℕ) : (∑ i ∈ Finset.range n, ((2:ℝ)^i)⁻¹) ≤ 2 := by
  have h : ∀ i : ℕ, ((2:ℝ)^i)⁻¹ = ((1:ℝ)/2)^i := by
    intro i; rw [← inv_pow]; norm_num
  simp_rw [h]
  rw [geom_sum_eq (by norm_num : ((1:ℝ)/2) ≠ 1)]
  have h2 : (0:ℝ) < ((1:ℝ)/2)^n := by positivity
  have he : (((1:ℝ)/2)^n - 1)/((1:ℝ)/2 - 1) = 2 - 2*(((1:ℝ)/2)^n) := by
    field_simp; ring
  rw [he]; linarith

/-- `∑_{k₀ ≤ k < K} 2^{-k} ≤ 2·2^{-k₀}`. -/
private lemma sum_Ico_inv_two_le (k₀ K : ℕ) :
    (∑ k ∈ Finset.Ico k₀ K, ((2:ℝ)^k)⁻¹) ≤ 2 * ((2:ℝ)^k₀)⁻¹ := by
  have hg : (∑ i ∈ Finset.range (K - k₀), ((2:ℝ)^i)⁻¹) ≤ 2 := geom_inv_two_sum_le (K - k₀)
  rw [Finset.sum_Ico_eq_sum_range]
  have h : ∀ i : ℕ, ((2:ℝ)^(k₀+i))⁻¹ = ((2:ℝ)^k₀)⁻¹ * ((2:ℝ)^i)⁻¹ := by
    intro i; rw [pow_add, mul_inv_rev]; ring
  simp_rw [h]
  rw [← Finset.mul_sum]
  have hnn : 0 ≤ ((2:ℝ)^k₀)⁻¹ := by positivity
  calc ((2:ℝ)^k₀)⁻¹ * ∑ i ∈ Finset.range (K - k₀), ((2:ℝ)^i)⁻¹
      ≤ ((2:ℝ)^k₀)⁻¹ * 2 := mul_le_mul_of_nonneg_left hg hnn
    _ = 2 * ((2:ℝ)^k₀)⁻¹ := by ring

/-- `∑_{k₀ ≤ k < K} 2^k ≤ 2^K`. -/
private lemma sum_Ico_two_pow_le (k₀ K : ℕ) :
    (∑ k ∈ Finset.Ico k₀ K, (2:ℝ)^k) ≤ (2:ℝ)^K := by
  have hsub : Finset.Ico k₀ K ⊆ Finset.range K := by
    intro x hx; simp only [Finset.mem_Ico] at hx; simp only [Finset.mem_range]; omega
  calc ∑ k ∈ Finset.Ico k₀ K, (2:ℝ)^k ≤ ∑ k ∈ Finset.range K, (2:ℝ)^k :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (by intro x h1 h2; positivity)
    _ = (2:ℝ)^K - 1 := by rw [geom_sum_eq (by norm_num : (2:ℝ) ≠ 1)]; norm_num
    _ ≤ (2:ℝ)^K := by
        have h : (0:ℝ) < (2:ℝ)^K := by positivity
        linarith

/-- `#(Ico k₀ K) ≤ K`. -/
private lemma card_Ico_le (k₀ K : ℕ) : (Finset.Ico k₀ K).card ≤ K := by
  calc (Finset.Ico k₀ K).card ≤ (Finset.range K).card :=
        Finset.card_le_card (by intro x hx; simp only [Finset.mem_Ico] at hx
                                simp only [Finset.mem_range]; omega)
    _ = K := Finset.card_range K

theorem BLodGeomSum (U V B₂ : ℝ) (K k₀ : ℕ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hB : 0 ≤ B₂) :
    (∑ k ∈ Finset.Ico k₀ K, ((2:ℝ)^k)⁻¹ *
        Real.sqrt ((U + 4 * (2:ℝ)^(2*k)) * U) * Real.sqrt ((V + 4 * (2:ℝ)^(2*k)) * B₂))
      ≤ Real.sqrt (U * B₂) *
          (2 * Real.sqrt (U * V) / (2:ℝ)^k₀ + 2 * Real.sqrt U * K + 2 * Real.sqrt V * K
            + 4 * (2:ℝ)^K) := by
  have hterm : ∀ k ∈ Finset.Ico k₀ K,
      ((2:ℝ)^k)⁻¹ * Real.sqrt ((U + 4 * (2:ℝ)^(2*k)) * U) * Real.sqrt ((V + 4 * (2:ℝ)^(2*k)) * B₂)
        ≤ Real.sqrt (U * B₂) * (Real.sqrt (U*V) * ((2:ℝ)^k)⁻¹
            + (2*Real.sqrt U + 2*Real.sqrt V) + 4*(2:ℝ)^k) := by
    intro k hk
    have h := term_le U V B₂ hU hV hB k
    calc _ ≤ Real.sqrt (U * B₂) * (Real.sqrt (U*V) * ((2:ℝ)^k)⁻¹
              + 2*Real.sqrt U + 2*Real.sqrt V + 4*(2:ℝ)^k) := h
      _ = Real.sqrt (U * B₂) * (Real.sqrt (U*V) * ((2:ℝ)^k)⁻¹
              + (2*Real.sqrt U + 2*Real.sqrt V) + 4*(2:ℝ)^k) := by ring
  have hsum_le := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum] at hsum_le
  have hbracket : (∑ k ∈ Finset.Ico k₀ K, (Real.sqrt (U*V) * ((2:ℝ)^k)⁻¹
        + (2*Real.sqrt U + 2*Real.sqrt V) + 4*(2:ℝ)^k))
      ≤ 2 * Real.sqrt (U * V) / (2:ℝ)^k₀ + 2 * Real.sqrt U * K + 2 * Real.sqrt V * K
          + 4 * (2:ℝ)^K := by
    have hA : ∑ k ∈ Finset.Ico k₀ K, Real.sqrt (U*V) * ((2:ℝ)^k)⁻¹
        ≤ Real.sqrt (U*V) * (2 * ((2:ℝ)^k₀)⁻¹) := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (sum_Ico_inv_two_le k₀ K) (Real.sqrt_nonneg _)
    have hB : ∑ k ∈ Finset.Ico k₀ K, (2*Real.sqrt U + 2*Real.sqrt V)
        ≤ (K:ℝ) * (2*Real.sqrt U + 2*Real.sqrt V) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_Ico_le k₀ K) (by positivity)
    have hC : ∑ k ∈ Finset.Ico k₀ K, 4 * (2:ℝ)^k ≤ 4 * (2:ℝ)^K := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (sum_Ico_two_pow_le k₀ K) (by norm_num)
    have hdecomp : (∑ k ∈ Finset.Ico k₀ K, (Real.sqrt (U*V) * ((2:ℝ)^k)⁻¹
          + (2*Real.sqrt U + 2*Real.sqrt V) + 4*(2:ℝ)^k))
        = (∑ k ∈ Finset.Ico k₀ K, Real.sqrt (U*V) * ((2:ℝ)^k)⁻¹)
          + (∑ k ∈ Finset.Ico k₀ K, (2*Real.sqrt U + 2*Real.sqrt V))
          + (∑ k ∈ Finset.Ico k₀ K, 4*(2:ℝ)^k) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    rw [hdecomp]
    have hA' : Real.sqrt (U*V) * (2 * ((2:ℝ)^k₀)⁻¹) = 2 * Real.sqrt (U*V) / (2:ℝ)^k₀ := by
      rw [div_eq_mul_inv]; ring
    have hB' : (K:ℝ) * (2*Real.sqrt U + 2*Real.sqrt V) = 2*Real.sqrt U*K + 2*Real.sqrt V*K := by
      ring
    rw [hA'] at hA; rw [hB'] at hB
    linarith
  exact le_trans hsum_le (mul_le_mul_of_nonneg_left hbracket (Real.sqrt_nonneg _))

end Work.NumberTheory.Chen.BTermCount

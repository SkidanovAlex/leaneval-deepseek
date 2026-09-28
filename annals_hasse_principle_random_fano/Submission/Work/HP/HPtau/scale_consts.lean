import Mathlib

namespace Work.HP.HPtau

/-- Scaling constants for the box in the proof of the lower bound for the Archimedean factor:
`c₂/c₁ = 16(n+1)²` dominates the transverse/vertical ratio `2√n/(1/√(n+1))`, and `c₁` is small
enough that the quadratic Taylor remainder `T·(c₂²+n c₁²)` is beaten by the linear gain
`(1/√(n+1))·c₂/2 - 2√n c₁`.

Explicit witnesses: `c₁ = min (1/(64(n+1)²)) (6(n+1)/(T·(256(n+1)⁴+n+1)))`, `c₂ = 16(n+1)²·c₁`,
using `√(n+1) ≤ n+1` and `√n ≤ n`. -/
theorem scale_consts (n : ℕ) (hn : 3 ≤ n) (T : ℝ) (hT : 0 < T) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ c₂ = 16 * ((n : ℝ) + 1) ^ 2 * c₁ ∧
      c₂ ^ 2 + n * c₁ ^ 2 ≤ 1 / 4 ∧
      (1 / Real.sqrt (n + 1)) * c₂ / 2 > 2 * Real.sqrt n * c₁ + T * (c₂ ^ 2 + n * c₁ ^ 2) := by
  set k : ℝ := (n:ℝ) + 1 with hk
  have hnR : (3:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hk_ge : 4 ≤ k := by rw [hk]; linarith
  have hk_pos : 0 < k := by linarith
  have hk1 : (1:ℝ) ≤ k := by linarith
  have hkn : (n:ℝ) ≤ k := by rw [hk]; linarith
  set A : ℝ := 1/(64*k^2) with hA
  set B : ℝ := 6*k/(T*(256*k^4 + (n:ℝ) + 1)) with hB
  have hA_pos : 0 < A := by rw [hA]; positivity
  have hB_pos : 0 < B := by rw [hB]; positivity
  set c1 : ℝ := min A B with hc1
  have hc1_pos : 0 < c1 := by rw [hc1]; exact lt_min hA_pos hB_pos
  have hc1_le_A : c1 ≤ A := by rw [hc1]; exact min_le_left _ _
  have hc1_le_B : c1 ≤ B := by rw [hc1]; exact min_le_right _ _
  refine ⟨c1, 16*k^2*c1, hc1_pos, by positivity, ?_, ?_, ?_⟩
  · rw [hk]
  · -- middle bound: c₂² + n c₁² ≤ 1/4
    have hc1A : c1 ≤ 1/(64*k^2) := hc1_le_A
    have h64 : (0:ℝ) < 64*k^2 := by positivity
    have hstep : c1 * (64*k^2) ≤ 1 := (le_div_iff₀ h64).mp hc1A
    have hnn : 0 ≤ c1 * (64*k^2) := by positivity
    have hsq : (c1 * (64*k^2))^2 ≤ 1 := by
      have h := mul_self_le_mul_self hnn hstep
      nlinarith [h]
    have h1 : 4096*k^4*c1^2 ≤ 1 := by nlinarith [hsq]
    have hk4 : k ≤ k^4 := by
      have h3 : (1:ℝ) ≤ k^3 := one_le_pow₀ hk1
      have h := mul_le_mul_of_nonneg_left h3 (le_of_lt hk_pos)
      nlinarith [h]
    have h2 : (n:ℝ) ≤ 768*k^4 := by nlinarith [hkn, hk4]
    have h3 : (n:ℝ)*c1^2 ≤ 768*k^4*c1^2 := by
      have h := mul_le_mul_of_nonneg_right h2 (sq_nonneg c1)
      nlinarith [h]
    nlinarith [h1, h3]
  · -- main inequality
    have hs_pos : 0 < Real.sqrt k := Real.sqrt_pos.mpr hk_pos
    have hs_ne : Real.sqrt k ≠ 0 := ne_of_gt hs_pos
    have hk_sqrt_le : Real.sqrt k ≤ k := by
      rw [Real.sqrt_le_iff]
      exact ⟨by linarith, by nlinarith [hk1]⟩
    have hLHS_eq : 1 / Real.sqrt k * (16 * k ^ 2 * c1) / 2 = 8 * k^2 * c1 / Real.sqrt k := by
      field_simp
      ring
    have hLHS_ge : 8 * k * c1 ≤ 1 / Real.sqrt k * (16 * k ^ 2 * c1) / 2 := by
      rw [hLHS_eq, le_div_iff₀ hs_pos]
      have h := mul_le_mul_of_nonneg_left hk_sqrt_le (by positivity : (0:ℝ) ≤ 8*k*c1)
      nlinarith [h]
    have hsqrtn_le_n : Real.sqrt (n:ℝ) ≤ (n:ℝ) := by
      rw [Real.sqrt_le_iff]
      exact ⟨by positivity, by nlinarith [hnR]⟩
    have hsqrtn_le_k : Real.sqrt (n:ℝ) ≤ k := by linarith
    have hBnd : T * (256*k^4 + (n:ℝ)) * c1 < 6*k := by
      have hTP_nn : 0 ≤ T * (256*k^4 + (n:ℝ)) := by positivity
      have hle : T*(256*k^4+(n:ℝ))*c1 ≤ T*(256*k^4+(n:ℝ))*B :=
        mul_le_mul_of_nonneg_left hc1_le_B hTP_nn
      have hBeq : T*(256*k^4+(n:ℝ))*B = 6*k*(256*k^4+(n:ℝ))/(256*k^4+(n:ℝ)+1) := by
        rw [hB]; field_simp
      rw [hBeq] at hle
      have hlt : 6*k*(256*k^4+(n:ℝ))/(256*k^4+(n:ℝ)+1) < 6*k := by
        rw [div_lt_iff₀ (by positivity)]
        nlinarith
      linarith
    have hTterm_eq : T * ((16*k^2*c1)^2 + (n:ℝ)*c1^2) = c1 * (T*(256*k^4+(n:ℝ))*c1) := by ring
    have hTterm_lt : T * ((16*k^2*c1)^2 + (n:ℝ)*c1^2) < 6*k*c1 := by
      rw [hTterm_eq]
      have h := mul_lt_mul_of_pos_left hBnd hc1_pos
      nlinarith [h]
    have h2n : 2*Real.sqrt (n:ℝ)*c1 ≤ 2*k*c1 := by
      have h := mul_le_mul_of_nonneg_right hsqrtn_le_k (le_of_lt hc1_pos)
      nlinarith [h]
    nlinarith [hLHS_ge, hTterm_lt, h2n]

end Work.HP.HPtau

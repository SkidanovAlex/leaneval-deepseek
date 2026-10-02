/-
# ZeroFreeTables/P3/SideConditions — HB (9.9)–(9.12) from the side condition `cond913`

HB Lemma 9.1 assumes `K₀(a+λ₁)⁻³ + (a+λ₀)⁻³ ≥ a⁻³` with `K₀ = min(K+3/(4K), 4K)`.  The
§9 derivation needs, in its three cases, the four inequalities (9.9)–(9.12):

* (9.9)  `(K²+3/4)/(a+λ₁)³ + 2K/(a+λ₀)³ ≥ K/a³`        (case `ord χ₁ ∉ {2,3}`, `A ≥ 0`)
* (9.10) `K/(a+λ₁)³ + (1/2)/(a+λ₀)³ ≥ (1/4)/a³`         (case `χ₁³ = χ₀`, `B ≥ 0`)
* (9.11) `(K²+3/4)/(a+λ₁)³ + K/(a+λ₀)³ ≥ K/a³`          (case `χ₁² = χ₀`, `A' ≥ 0`)
* (9.12) `2K/(a+λ₁)³ + (1/2)/(a+λ₀)³ ≥ (1/2)/a³`        (case `χ₁² = χ₀`, `C, D ≥ 0`)

All four are consequences of `cond913` together with the elementary bounds
`K₀ ≤ K + 3/(4K)` and `K₀ ≤ 4K` (HB's remark that (9.11), (9.12) are the most stringent is
exactly this bookkeeping).  Proof: clearing the denominators of `cond913` gives
`K₀P + Q ≥ 1` with `P = a³/(a+λ₁)³`, `Q = a³/(a+λ₀)³ ≥ 0`; the four inequalities are then
`(K²+3/4)P + 2KQ ≥ K`, `KP + Q/2 ≥ 1/4`, `(K²+3/4)P + KQ ≥ K`, `2KP + Q/2 ≥ 1/2`, each
obtained by multiplying `K₀P + Q ≥ 1` by the coefficient of `P` on the left and comparing
using `K·K₀ ≤ K²+3/4`, resp. `K₀ ≤ 4K`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.Engine

noncomputable section
namespace Work.ZeroFreeTables

theorem side913 {a lam₁ lam₀ K : ℝ} (ha : 0 < a) (hK : 0 < K) (h₁ : 0 < a + lam₁)
    (h₀ : 0 < a + lam₀) (h : cond913 lam₁ lam₀ a K) :
    ((K ^ 2 + 3/4) / (a + lam₁) ^ 3 + 2 * K / (a + lam₀) ^ 3 ≥ K / a ^ 3) ∧
    (K / (a + lam₁) ^ 3 + (1/2) / (a + lam₀) ^ 3 ≥ (1/4) / a ^ 3) ∧
    ((K ^ 2 + 3/4) / (a + lam₁) ^ 3 + K / (a + lam₀) ^ 3 ≥ K / a ^ 3) ∧
    (2 * K / (a + lam₁) ^ 3 + (1/2) / (a + lam₀) ^ 3 ≥ (1/2) / a ^ 3) := by
  have ha3 : 0 < a ^ 3 := pow_pos ha 3
  have hA : 0 < (a + lam₁) ^ 3 := pow_pos h₁ 3
  have hB : 0 < (a + lam₀) ^ 3 := pow_pos h₀ 3
  have hAn : (a + lam₁) ^ 3 ≠ 0 := ne_of_gt hA
  have hBn : (a + lam₀) ^ 3 ≠ 0 := ne_of_gt hB
  have han : a ^ 3 ≠ 0 := ne_of_gt ha3
  set P : ℝ := a ^ 3 / (a + lam₁) ^ 3 with hPdef
  set Q : ℝ := a ^ 3 / (a + lam₀) ^ 3 with hQdef
  have hP : 0 ≤ P := by rw [hPdef]; positivity
  have hQ : 0 ≤ Q := by rw [hQdef]; positivity
  have hc : Kond K * P + Q ≥ 1 := by
    have h1 : 1 / a ^ 3 ≤ Kond K / (a + lam₁) ^ 3 + 1 / (a + lam₀) ^ 3 := h
    have h2 : 1 ≤ (Kond K / (a + lam₁) ^ 3 + 1 / (a + lam₀) ^ 3) * a ^ 3 :=
      (div_le_iff₀ ha3).mp h1
    have h3 : (Kond K / (a + lam₁) ^ 3 + 1 / (a + lam₀) ^ 3) * a ^ 3 = Kond K * P + Q := by
      rw [hPdef, hQdef]; field_simp; try ring
    linarith only [h2, h3]
  have hKadd : Kond K ≤ K + 3 / (4 * K) := min_le_left _ _
  have hK4 : Kond K ≤ 4 * K := min_le_right _ _
  have hKκ : K * Kond K ≤ K ^ 2 + 3/4 := by
    have h4 := mul_le_mul_of_nonneg_left hKadd (le_of_lt hK)
    have h5 : K * (K + 3 / (4 * K)) = K ^ 2 + 3/4 := by
      field_simp; try ring
    linarith only [h4, h5]
  have hKQ : K ≤ K * (Kond K * P + Q) := by
    simpa using mul_le_mul_of_nonneg_left hc (le_of_lt hK)
  have hKP : K * Kond K * P ≤ (K ^ 2 + 3/4) * P :=
    mul_le_mul_of_nonneg_right hKκ hP
  have hKQ2 : K * (Kond K * P + Q) = K * Kond K * P + K * Q := by ring
  have e1 : (K ^ 2 + 3/4) * P + 2 * K * Q ≥ K := by
    have h2 : K * Q ≥ 0 := mul_nonneg (le_of_lt hK) hQ
    linarith only [hKQ, hKQ2, hKP, h2]
  have e3 : (K ^ 2 + 3/4) * P + K * Q ≥ K := by linarith only [hKQ, hKQ2, hKP]
  have h24 : (1/4) * 1 ≤ (1/4) * (Kond K * P + Q) :=
    mul_le_mul_of_nonneg_left hc (by norm_num : (0:ℝ) ≤ 1/4)
  have hκP : (1/4) * (Kond K * P) ≤ K * P := by
    have h6 : (1/4) * Kond K ≤ K := by linarith only [hK4, hK]
    calc (1/4) * (Kond K * P) = ((1/4) * Kond K) * P := by ring
      _ ≤ K * P := mul_le_mul_of_nonneg_right h6 hP
  have e2 : K * P + (1/2) * Q ≥ 1/4 := by linarith only [h24, hκP, hQ, hc]
  have h12 : (1/2) * 1 ≤ (1/2) * (Kond K * P + Q) :=
    mul_le_mul_of_nonneg_left hc (by norm_num : (0:ℝ) ≤ 1/2)
  have hκP2 : (1/2) * (Kond K * P) ≤ 2 * K * P := by
    have h6 : (1/2) * Kond K ≤ 2 * K := by linarith only [hK4, hK]
    calc (1/2) * (Kond K * P) = ((1/2) * Kond K) * P := by ring
      _ ≤ (2 * K) * P := mul_le_mul_of_nonneg_right h6 hP
  have e4 : 2 * K * P + (1/2) * Q ≥ 1/2 := by linarith only [h12, hκP2, hQ, hc, hκP]
  have key1 : ((K ^ 2 + 3/4) * P + 2 * K * Q) / a ^ 3
      = (K ^ 2 + 3/4) / (a + lam₁) ^ 3 + 2 * K / (a + lam₀) ^ 3 := by
    rw [hPdef, hQdef]; field_simp; try ring
  have key2 : (K * P + (1/2) * Q) / a ^ 3
      = K / (a + lam₁) ^ 3 + (1/2) / (a + lam₀) ^ 3 := by
    rw [hPdef, hQdef]; field_simp; try ring
  have key3 : ((K ^ 2 + 3/4) * P + K * Q) / a ^ 3
      = (K ^ 2 + 3/4) / (a + lam₁) ^ 3 + K / (a + lam₀) ^ 3 := by
    rw [hPdef, hQdef]; field_simp; try ring
  have key4 : (2 * K * P + (1/2) * Q) / a ^ 3
      = 2 * K / (a + lam₁) ^ 3 + (1/2) / (a + lam₀) ^ 3 := by
    rw [hPdef, hQdef]; field_simp; try ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ge_iff_le, ← key1, div_le_div_iff_of_pos_right ha3]; linarith only [e1]
  · rw [ge_iff_le, ← key2, div_le_div_iff_of_pos_right ha3]; linarith only [e2, hQ, hc, hκP]
  · rw [ge_iff_le, ← key3, div_le_div_iff_of_pos_right ha3]; linarith only [e3, hKQ, hKP]
  · rw [ge_iff_le, ← key4, div_le_div_iff_of_pos_right ha3]; linarith only [e4, hc, hκP]

end Work.ZeroFreeTables

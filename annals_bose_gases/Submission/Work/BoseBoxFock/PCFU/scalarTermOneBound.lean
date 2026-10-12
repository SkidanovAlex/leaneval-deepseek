import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Submission.Work.BoseBoxFock.PCFU.scalarAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.PCFU

theorem scalarTermOneBound {M N K : ℕ} (hK : 2 * N ≤ K) (hNM : M + 3 ≤ 2 * N)
    {ℓ δ : ℝ} (hℓ : 0 < ℓ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    δ ^ K * ℓ ^ 3 * (125 * (1 + max 3 ℓ⁻¹) ^ 3 * ((1 + ℓ * δ) ^ (2 * N))⁻¹)
      ≤ 8000 * ((ℓ ^ M)⁻¹) := by
  have h3 : 3 ≤ 2 * N := by omega
  have hMle : M ≤ 2 * N - 3 := by omega
  rcases le_or_gt ℓ 1 with hℓ1 | hℓ1
  · -- small box: `ℓ ≤ 1`
    have hδk1 : δ ^ K ≤ 1 := pow_le_one₀ hδ0.le hδ1
    have hB1 : ((1 + ℓ * δ) ^ (2 * N))⁻¹ ≤ 1 :=
      inv_pow_le_one_of_one_le (by nlinarith [mul_pos hℓ hδ0]) (2 * N)
    have hLA : ℓ ^ 3 * (1 + max 3 ℓ⁻¹) ^ 3 ≤ 64 :=
      ell_cube_mul_one_add_max_cube_le hℓ hℓ1
    have hpos : (0 : ℝ) ≤ ℓ ^ 3 * (1 + max 3 ℓ⁻¹) ^ 3 := by
      have hmax : (0 : ℝ) < 1 + max 3 ℓ⁻¹ := by
        have : (3 : ℝ) ≤ max 3 ℓ⁻¹ := le_max_left 3 ℓ⁻¹
        linarith
      exact mul_nonneg (pow_nonneg hℓ.le 3) (pow_nonneg hmax.le 3)
    have h1 : δ ^ K * (ℓ ^ 3 * (1 + max 3 ℓ⁻¹) ^ 3) ≤ 1 * 64 :=
      mul_le_mul hδk1 hLA hpos (by norm_num)
    have h2 : δ ^ K * (ℓ ^ 3 * (1 + max 3 ℓ⁻¹) ^ 3) * ((1 + ℓ * δ) ^ (2 * N))⁻¹
        ≤ 64 := by
      have h := mul_le_mul h1 hB1 (by positivity) (by norm_num : (0 : ℝ) ≤ 1 * 64)
      linarith
    have hInv : (1 : ℝ) ≤ (ℓ ^ M)⁻¹ := one_le_inv_pow_of_le_one hℓ hℓ1 M
    calc δ ^ K * ℓ ^ 3 * (125 * (1 + max 3 ℓ⁻¹) ^ 3 * ((1 + ℓ * δ) ^ (2 * N))⁻¹)
        = 125 * (δ ^ K * (ℓ ^ 3 * (1 + max 3 ℓ⁻¹) ^ 3)
            * ((1 + ℓ * δ) ^ (2 * N))⁻¹) := by ring
      _ ≤ 125 * 64 := mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ = 8000 := by norm_num
      _ ≤ 8000 * (ℓ ^ M)⁻¹ := by
          have h := mul_le_mul_of_nonneg_left hInv (by norm_num : (0 : ℝ) ≤ 8000)
          simpa using h
  · -- large box: `1 < ℓ`
    have hℓge : 1 ≤ ℓ := le_of_lt hℓ1
    have hmax : max 3 ℓ⁻¹ = 3 := max_eq_three_of_one_le hℓge
    have hδB : δ ^ K * ((1 + ℓ * δ) ^ (2 * N))⁻¹ ≤ (ℓ ^ (2 * N))⁻¹ :=
      delta_pow_mul_inv_le hℓ hδ0 hδ1 hK
    have hpow : ℓ ^ 3 * (ℓ ^ (2 * N))⁻¹ = (ℓ ^ (2 * N - 3))⁻¹ :=
      pow3_mul_inv_pow_eq hℓ h3
    calc δ ^ K * ℓ ^ 3 * (125 * (1 + max 3 ℓ⁻¹) ^ 3 * ((1 + ℓ * δ) ^ (2 * N))⁻¹)
        = 8000 * (ℓ ^ 3 * (δ ^ K * ((1 + ℓ * δ) ^ (2 * N))⁻¹)) := by
          rw [hmax]; ring_nf
      _ ≤ 8000 * (ℓ ^ 3 * (ℓ ^ (2 * N))⁻¹) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hδB (by positivity : (0 : ℝ) ≤ ℓ ^ 3))
            (by norm_num : (0 : ℝ) ≤ 8000)
      _ = 8000 * ((ℓ ^ (2 * N - 3))⁻¹) := by rw [hpow]
      _ ≤ 8000 * ((ℓ ^ M)⁻¹) :=
          mul_le_mul_of_nonneg_left (inv_pow_le_inv_pow_of_le hℓge hMle) (by norm_num)

end Work.BoseBoxFock.PCFU

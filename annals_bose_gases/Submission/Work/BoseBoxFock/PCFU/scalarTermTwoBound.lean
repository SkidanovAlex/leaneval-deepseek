import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Submission.Work.BoseBoxFock.PCFU.scalarAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.PCFU

theorem scalarTermTwoBound {M N K : ℕ} (hK : 2 * N ≤ K) (hNM : M + 3 ≤ 2 * N)
    {ℓ δ CT : ℝ} (hℓ : 0 < ℓ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hCT : 0 ≤ CT) :
    δ ^ K * ℓ ^ 3 * ((2 : ℝ) ^ (2 * N) * ((ℓ ^ (2 * N))⁻¹)
        * (CT * (((max 3 ℓ⁻¹) ^ (2 * N - 3))⁻¹)))
      ≤ (2 : ℝ) ^ (2 * N) * CT * ((ℓ ^ M)⁻¹) := by
  -- The far-lattice row, with `R := max 3 ℓ⁻¹` and the common factor `2^{2N}` removed.
  have hKey : δ ^ K * ℓ ^ 3 * (ℓ ^ (2 * N))⁻¹ * ((max 3 ℓ⁻¹) ^ (2 * N - 3))⁻¹
      ≤ (ℓ ^ M)⁻¹ := by
    have hN3 : 3 ≤ 2 * N := by omega
    have hMle : M ≤ 2 * N - 3 := by omega
    -- `δ^K ≤ 1` (through `δ^K ≤ δ^{2N} ≤ 1`, which also consumes `hK`).
    have hδK : δ ^ K ≤ 1 :=
      le_trans (pow_le_pow_of_le_one hδ0.le hδ1 hK) (pow_le_one₀ hδ0.le hδ1)
    -- Combine the `ℓ`-powers with the `R`-power: `ℓ³ (ℓ^{2N})⁻¹ (R^{2N-3})⁻¹ = ((ℓR)^{2N-3})⁻¹`.
    have hA0 : ℓ ^ 3 * (ℓ ^ (2 * N))⁻¹ * ((max 3 ℓ⁻¹) ^ (2 * N - 3))⁻¹
        = ((ℓ * max 3 ℓ⁻¹) ^ (2 * N - 3))⁻¹ := by
      rw [pow3_mul_inv_pow_eq hℓ hN3, ← mul_inv, ← mul_pow]
    -- `ℓR = max (3ℓ) 1 ≥ max (ℓ, 1)`.
    have hb1 : 1 ≤ ℓ * max 3 ℓ⁻¹ := by rw [ell_mul_max_eq hℓ]; exact le_max_right _ _
    have hbℓ : ℓ ≤ ℓ * max 3 ℓ⁻¹ := by
      rw [ell_mul_max_eq hℓ]
      exact le_trans (by linarith) (le_max_left _ _)
    have hpowge : ℓ ^ M ≤ (ℓ * max 3 ℓ⁻¹) ^ (2 * N - 3) := by
      have hmax : ℓ ^ M ≤ max (ℓ ^ (2 * N - 3)) 1 := by
        rcases le_or_gt 1 ℓ with h | h
        · exact le_trans (pow_le_pow_right₀ h hMle) (le_max_left _ _)
        · exact le_trans (pow_le_one₀ hℓ.le h.le) (le_max_right _ _)
      exact le_trans hmax (max_le (pow_le_pow_left₀ hℓ.le hbℓ _) (one_le_pow₀ hb1))
    calc δ ^ K * ℓ ^ 3 * (ℓ ^ (2 * N))⁻¹ * ((max 3 ℓ⁻¹) ^ (2 * N - 3))⁻¹
        = δ ^ K * ((ℓ * max 3 ℓ⁻¹) ^ (2 * N - 3))⁻¹ := by rw [← hA0]; ring
      _ ≤ ((ℓ * max 3 ℓ⁻¹) ^ (2 * N - 3))⁻¹ := by
          have h := mul_le_mul_of_nonneg_right hδK
            (by positivity : (0:ℝ) ≤ ((ℓ * max 3 ℓ⁻¹) ^ (2 * N - 3))⁻¹)
          simpa using h
      _ ≤ (ℓ ^ M)⁻¹ := by
          rw [inv_le_inv₀ (by positivity) (by positivity)]
          exact hpowge
  -- Factor the common nonnegative constant `2^{2N} CT` out of both sides.
  have hc : (0:ℝ) ≤ (2:ℝ) ^ (2 * N) * CT := mul_nonneg (by positivity) hCT
  calc δ ^ K * ℓ ^ 3 * ((2 : ℝ) ^ (2 * N) * ((ℓ ^ (2 * N))⁻¹)
        * (CT * (((max 3 ℓ⁻¹) ^ (2 * N - 3))⁻¹)))
      = (2 ^ (2 * N) * CT)
          * (δ ^ K * ℓ ^ 3 * (ℓ ^ (2 * N))⁻¹ * ((max 3 ℓ⁻¹) ^ (2 * N - 3))⁻¹) := by ring
    _ ≤ (2 ^ (2 * N) * CT) * (ℓ ^ M)⁻¹ := mul_le_mul_of_nonneg_left hKey hc
    _ = (2 : ℝ) ^ (2 * N) * CT * ((ℓ ^ M)⁻¹) := by ring

end Work.BoseBoxFock.PCFU

import Mathlib

namespace Work.LinnikAreas.BGTZ.E

/-- From `δ⁻¹ ≤ q^{1/100}(log q)²` and `δ > 0`, any negative integral power of `δ` is bounded:
`δ^{-k} ≤ q^{k/100}(log q)^{2k}`. -/
theorem RpowNegNatLe {q δ : ℝ} (hq : 0 < q) (hδ : 0 < δ) (k : ℕ)
    (h : δ⁻¹ ≤ q ^ (1 / 100 : ℝ) * (Real.log q) ^ 2) :
    δ ^ (-(k : ℝ)) ≤ q ^ ((k : ℝ) / 100) * (Real.log q) ^ (2 * k) := by
  have hδinv : 0 ≤ δ⁻¹ := le_of_lt (inv_pos.mpr hδ)
  calc δ ^ (-(k : ℝ)) = (δ⁻¹) ^ k := by
        rw [Real.rpow_neg (le_of_lt hδ), Real.rpow_natCast]
        exact (inv_pow δ k).symm
    _ ≤ (q ^ (1 / 100 : ℝ) * (Real.log q) ^ 2) ^ k := pow_le_pow_left₀ hδinv h k
    _ = q ^ ((k : ℝ) / 100) * (Real.log q) ^ (2 * k) := by
        rw [mul_pow, ← Real.rpow_natCast (q ^ (1 / 100 : ℝ)) k,
            ← Real.rpow_mul (le_of_lt hq) (1 / 100) (k : ℝ),
            ← pow_mul (Real.log q) 2 k]
        ring_nf

end Work.LinnikAreas.BGTZ.E

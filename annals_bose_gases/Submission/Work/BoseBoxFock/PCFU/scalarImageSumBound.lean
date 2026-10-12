import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Submission.Work.BoseBoxFock.PCFU.scalarTermOneBound
import Submission.Work.BoseBoxFock.PCFU.scalarTermTwoBound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.PCFU

/-- The scalar arithmetic of the `Ksfr`-image bound: the two summands of the parenthesised
factor (`scalarTermOneBound`, `scalarTermTwoBound`, proved in the sibling modules) are each
bounded by `8000 (ℓ^M)⁻¹` and `2^{2N} CT (ℓ^M)⁻¹` respectively, and the nonnegative prefactors
`CK, Cdec` factor out. -/
theorem scalarImageSumBound {M N K : ℕ} (hK : 2 * N ≤ K) (hNM : M + 3 ≤ 2 * N)
    {δ ℓ CT CK Cdec : ℝ} (hℓ : 0 < ℓ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hCT : 0 ≤ CT) (hCK : 0 ≤ CK) (hCdec : 0 ≤ Cdec) :
    CK * δ ^ K * ℓ ^ 3 * Cdec
        * (125 * (1 + max 3 ℓ⁻¹) ^ 3 * ((1 + ℓ * δ) ^ (2 * N))⁻¹
            + (2 : ℝ) ^ (2 * N) * ((ℓ ^ (2 * N))⁻¹)
                * (CT * (((max 3 ℓ⁻¹) ^ (2 * N - 3))⁻¹)))
      ≤ CK * Cdec * (8000 + (2 : ℝ) ^ (2 * N) * CT) * ((ℓ ^ M)⁻¹) := by
  have h1 := scalarTermOneBound hK hNM hℓ hδ0 hδ1
  have h2 := scalarTermTwoBound hK hNM hℓ hδ0 hδ1 hCT
  set X1 : ℝ := 125 * (1 + max 3 ℓ⁻¹) ^ 3 * ((1 + ℓ * δ) ^ (2 * N))⁻¹ with hX1
  set X2 : ℝ := (2 : ℝ) ^ (2 * N) * ((ℓ ^ (2 * N))⁻¹)
                * (CT * (((max 3 ℓ⁻¹) ^ (2 * N - 3))⁻¹)) with hX2
  have hsum : δ ^ K * ℓ ^ 3 * (X1 + X2)
      ≤ 8000 * ((ℓ ^ M)⁻¹) + (2 : ℝ) ^ (2 * N) * CT * ((ℓ ^ M)⁻¹) := by
    rw [mul_add]
    exact add_le_add h1 h2
  calc CK * δ ^ K * ℓ ^ 3 * Cdec * (X1 + X2)
      = CK * Cdec * (δ ^ K * ℓ ^ 3 * (X1 + X2)) := by ring
    _ ≤ CK * Cdec * (8000 * ((ℓ ^ M)⁻¹) + (2 : ℝ) ^ (2 * N) * CT * ((ℓ ^ M)⁻¹)) :=
        mul_le_mul_of_nonneg_left hsum (mul_nonneg hCK hCdec)
    _ = CK * Cdec * (8000 + (2 : ℝ) ^ (2 * N) * CT) * ((ℓ ^ M)⁻¹) := by ring

end Work.BoseBoxFock.PCFU

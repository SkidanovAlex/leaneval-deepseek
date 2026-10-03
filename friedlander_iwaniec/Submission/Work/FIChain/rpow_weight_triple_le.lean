import Mathlib

namespace Work.FIChain

/-- Elementary real-analytic weight comparison used in the Friedman–Iwaniec
sieve bookkeeping.  If `1 ≤ D`, `1 ≤ P`, `1 ≤ Q`, `1 ≤ R` and `D ^ ε ≤ Q`,
then the "triple weight" `P ^ 2 * Q * R` is bounded by `D ^ (-ε)` times the
cube of `P * Q * R`.

The content is that, because `D ^ ε ≤ Q ≤ P * Q ^ 2 * R ^ 2`, the factor
`D ^ (-ε)` is at least `(P * Q ^ 2 * R ^ 2)⁻¹`, which is exactly the deficit
between `(P * Q * R) ^ 3` and `P ^ 2 * Q * R`. -/
theorem rpow_weight_triple_le {P Q R D ε : ℝ} (hD : 1 ≤ D) (hP : 1 ≤ P) (hQ : 1 ≤ Q)
    (hR : 1 ≤ R) (hQε : D ^ ε ≤ Q) :
    P ^ 2 * Q * R ≤ D ^ (-ε) * (P * Q * R) ^ 3 := by
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hDεpos : 0 < D ^ ε := Real.rpow_pos_of_pos hDpos ε
  -- `Q ≤ P * Q ^ 2 * R ^ 2`, using `1 ≤ P, Q, R`.
  have hstep : Q ≤ P * Q ^ 2 * R ^ 2 := by
    have hQle : Q ≤ Q ^ 2 := by nlinarith [hQ]
    have hR2 : 1 ≤ R ^ 2 := one_le_pow₀ hR
    have h1 : Q ≤ 1 * Q ^ 2 * R ^ 2 := by nlinarith [hQle, hR2]
    nlinarith [hP, h1]
  have hDε_le : D ^ ε ≤ P * Q ^ 2 * R ^ 2 := le_trans hQε hstep
  -- Hence `D ^ (-ε) * (P * Q ^ 2 * R ^ 2) ≥ 1`.
  have hkey : 1 ≤ D ^ (-ε) * (P * Q ^ 2 * R ^ 2) := by
    rw [Real.rpow_neg hDpos.le]
    calc (1 : ℝ) = (D ^ ε)⁻¹ * D ^ ε := (inv_mul_cancel₀ (ne_of_gt hDεpos)).symm
      _ ≤ (D ^ ε)⁻¹ * (P * Q ^ 2 * R ^ 2) :=
          mul_le_mul_of_nonneg_left hDε_le (inv_nonneg.mpr hDεpos.le)
  have hPQR : 0 ≤ P ^ 2 * Q * R := by positivity
  have h2 := mul_le_mul_of_nonneg_right hkey hPQR
  simp only [one_mul] at h2
  calc P ^ 2 * Q * R ≤ D ^ (-ε) * (P ^ 3 * Q ^ 3 * R ^ 3) := by nlinarith [h2]
    _ = D ^ (-ε) * (P * Q * R) ^ 3 := by ring

end Work.FIChain

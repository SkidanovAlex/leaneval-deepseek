import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Normed.Field.Basic

namespace Commons.Algebra.Matrix

/-- Core algebraic fact.  Given `a, c > 0` with `b^2 < a*c` and `u > 0`, `v ≥ 0`,
`w^2 ≤ u*v`, the bilinear pairing `a*u + c*v - 2*b*w` is strictly positive.
Geometrically: `[[a,b],[b,c]]` is positive definite, `[[u,w],[w,v]]` is negative
semidefinite with `u > 0`, and the pairing (a `tr(A·M)` with `M ⪯ 0`) is negative. -/
private lemma core_pos (a c b u v w : ℝ) (ha : 0 < a) (hc : 0 < c) (hac : b ^ 2 < a * c)
    (hu : 0 < u) (hv : 0 ≤ v) (huv : w ^ 2 ≤ u * v) :
    0 < a * u + c * v - 2 * b * w := by
  have hau : 0 < a * u := mul_pos ha hu
  have hcv : 0 ≤ c * v := mul_nonneg (le_of_lt hc) hv
  have hSpos : 0 < a * u + c * v := by linarith
  have huv_nonneg : 0 ≤ u * v := le_trans (sq_nonneg w) huv
  have hkey : (a * u + c * v) ^ 2 - (2 * b * w) ^ 2
      = (a * u - c * v) ^ 2 + 4 * b ^ 2 * (u * v - w ^ 2)
          + 4 * (a * c - b ^ 2) * (u * v) := by ring
  have hstrict : 0 < (a * u - c * v) ^ 2 + 4 * b ^ 2 * (u * v - w ^ 2)
      + 4 * (a * c - b ^ 2) * (u * v) := by
    by_cases huv0 : u * v = 0
    · have hw0 : w = 0 := by
        have hw2 : w ^ 2 ≤ 0 := by nlinarith [huv, huv0]
        nlinarith [sq_nonneg w]
      have hv0 : v = 0 := by
        rcases mul_eq_zero.mp huv0 with h | h
        · exact absurd h (ne_of_gt hu)
        · exact h
      have heq : (a * u - c * v) ^ 2 + 4 * b ^ 2 * (u * v - w ^ 2)
            + 4 * (a * c - b ^ 2) * (u * v) = (a * u) ^ 2 := by
        rw [hw0, hv0]; ring
      rw [heq]
      exact pow_pos hau 2
    · have huvpos : 0 < u * v := lt_of_le_of_ne huv_nonneg (Ne.symm huv0)
      have hacpos : 0 < a * c - b ^ 2 := by linarith
      have h3 : 0 < 4 * (a * c - b ^ 2) * (u * v) := by
        have : 0 < 4 * (a * c - b ^ 2) := by linarith
        exact mul_pos this huvpos
      have h1 : 0 ≤ (a * u - c * v) ^ 2 := sq_nonneg _
      have h2 : 0 ≤ 4 * b ^ 2 * (u * v - w ^ 2) := by
        have huw : 0 ≤ u * v - w ^ 2 := by linarith
        have hb2 : 0 ≤ 4 * b ^ 2 := by positivity
        exact mul_nonneg hb2 huw
      linarith
  have hsq : (2 * b * w) ^ 2 < (a * u + c * v) ^ 2 := by
    rw [← sub_pos, hkey]
    exact hstrict
  have habs : |2 * b * w| < a * u + c * v := by
    have h := sq_lt_sq.mp hsq
    rwa [abs_of_pos hSpos] at h
  have hle : 2 * b * w ≤ |2 * b * w| := le_abs_self _
  linarith

theorem twoByTwo_psd_of_gram_trace_det (E2 L2 EL M11 M12 M22 : ℝ)
    (hE2 : 0 < E2) (hG : 0 < E2 * L2 - EL ^ 2)
    (htr : 0 ≤ L2 * M11 - 2 * EL * M12 + E2 * M22)
    (hdet : 0 ≤ M11 * M22 - M12 ^ 2) :
    ∀ α β : ℝ, 0 ≤ M11 * α ^ 2 + 2 * M12 * α * β + M22 * β ^ 2 := by
  have hL2 : 0 < L2 := by
    have : 0 < E2 * L2 := by linarith [hG, sq_nonneg EL]
    exact pos_of_mul_pos_right this (le_of_lt hE2)
  -- Step 1: the upper-left entry is non-negative.
  have hM11 : 0 ≤ M11 := by
    by_contra hcon
    have hlt : M11 < 0 := lt_of_not_ge hcon
    -- determinant non-negativity forces M22 ≤ 0
    have hM22 : M22 ≤ 0 := by
      by_contra hM22c
      have hM22c' : 0 < M22 := not_le.mp hM22c
      have h1 : 0 ≤ M11 * M22 := le_trans (sq_nonneg M12) (by linarith [hdet])
      have h2 : M11 * M22 < 0 := mul_neg_of_neg_of_pos hlt hM22c'
      linarith
    have hac : (-EL) ^ 2 < L2 * E2 := by nlinarith [hG]
    have hcore := core_pos L2 E2 (-EL) (-M11) (-M22) M12 hL2 hE2 hac
        (by linarith) (by linarith) (by nlinarith [hdet])
    linarith [hcore, htr]
  intro α β
  by_cases hM11' : M11 = 0
  · -- vanishing upper-left entry: determinant forces the cross term to vanish,
    -- and the trace condition then gives M22 ≥ 0.
    have hM12 : M12 = 0 := by
      have h' := hdet
      rw [hM11'] at h'
      simp only [zero_mul, zero_sub] at h'
      have h2 : M12 ^ 2 = 0 := by nlinarith [sq_nonneg M12]
      exact sq_eq_zero_iff.mp h2
    have hM22 : 0 ≤ M22 := by
      have h' := htr
      rw [hM11', hM12] at h'
      have h2 : 0 ≤ E2 * M22 := by nlinarith [h']
      exact nonneg_of_mul_nonneg_right h2 hE2
    rw [hM11', hM12]
    nlinarith [mul_nonneg hM22 (sq_nonneg β)]
  · have hM11pos : 0 < M11 := lt_of_le_of_ne hM11 (Ne.symm hM11')
    have hid : M11 * (M11 * α ^ 2 + 2 * M12 * α * β + M22 * β ^ 2)
        = (M11 * α + M12 * β) ^ 2 + (M11 * M22 - M12 ^ 2) * β ^ 2 := by ring
    have hnonneg : 0 ≤ (M11 * α + M12 * β) ^ 2 + (M11 * M22 - M12 ^ 2) * β ^ 2 := by
      have h1 : 0 ≤ (M11 * α + M12 * β) ^ 2 := sq_nonneg _
      have h2 : 0 ≤ (M11 * M22 - M12 ^ 2) * β ^ 2 := mul_nonneg hdet (sq_nonneg β)
      linarith
    have hmul : 0 ≤ M11 * (M11 * α ^ 2 + 2 * M12 * α * β + M22 * β ^ 2) := by
      rw [hid]; exact hnonneg
    exact nonneg_of_mul_nonneg_right hmul hM11pos

end Commons.Algebra.Matrix
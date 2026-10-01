import Mathlib
import Submission.Work.LinnikAreas.FarBoundOfJutilaMontgomery

/-!
# Pointwise bound for one dyadic cell-layer term

For `A ≤ 1/2` and all `q R m k`,
`4^{-k} · cellLayer R m k · (q·2^k)^A ≤ q^A · (2^{-3/2})^k` when `R ≤ 2^k`, and the
left-hand side is `0` otherwise (because `cellLayer R m k = 0`).

The whole content is the exponent arithmetic: after factoring `(q·2^k)^A = q^A · 2^{kA}`
and dropping the indicator, one has to see
`4^{-k} · 2^{kA} = 2^{-2k+kA} ≤ 2^{-3k/2}`, which is `k·(A - 1/2) ≤ 0`.
-/

namespace Work.LinnikAreas.JMAux

private lemma quarter_pow_eq (k : ℕ) : (1/4:ℝ)^k = (2:ℝ)^(-(2*(k:ℝ))) := by
  have h2 : (0:ℝ) ≤ 2 := by norm_num
  have h14 : (1/4:ℝ) = (2:ℝ)^(-(2:ℝ)) := by
    rw [Real.rpow_neg (show (0:ℝ) ≤ 2 by norm_num), Real.rpow_ofNat]
    norm_num
  rw [h14, ← Real.rpow_natCast ((2:ℝ)^(-(2:ℝ))) k, ← Real.rpow_mul h2]
  rw [show (-(2:ℝ)) * (k:ℝ) = -(2*(k:ℝ)) by ring]

private lemma two_pow_neg_three_halves_pow (k : ℕ) :
    ((2:ℝ)^(-(3/2:ℝ)))^k = (2:ℝ)^((-(3/2:ℝ))*(k:ℝ)) := by
  rw [← Real.rpow_natCast ((2:ℝ)^(-(3/2:ℝ))) k,
    ← Real.rpow_mul (show (0:ℝ) ≤ 2 by norm_num)]

private lemma quarter_mul_two_rpow_le (k : ℕ) {A : ℝ} (hA : A ≤ 1/2) :
    (1/4:ℝ)^k * (2:ℝ)^((k:ℝ)*A) ≤ ((2:ℝ)^(-(3/2:ℝ)))^k := by
  rw [quarter_pow_eq k, two_pow_neg_three_halves_pow k,
    ← Real.rpow_add (show (0:ℝ) < 2 by norm_num)]
  apply Real.rpow_le_rpow_of_exponent_le (show (1:ℝ) ≤ 2 by norm_num)
  have hk : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
  nlinarith [mul_le_mul_of_nonneg_left hA hk]

lemma CellLayerTermLe (q R m k : ℕ) {A : ℝ} (hA : A ≤ 1/2) :
    (1/4:ℝ)^k * Work.LinnikAreas.cellLayer R m k * ((q:ℝ) * (2:ℝ)^k)^A
      ≤ (q:ℝ)^A * (if (R:ℝ) ≤ (2:ℝ)^k then ((2:ℝ) ^ (-(3/2:ℝ)))^k else 0) := by
  have hq0 : (0:ℝ) ≤ (q:ℝ) := Nat.cast_nonneg q
  have hqA : (0:ℝ) ≤ (q:ℝ)^A := Real.rpow_nonneg hq0 A
  have h4 : (0:ℝ) ≤ (1/4:ℝ)^k := by positivity
  have hX : (0:ℝ) ≤ ((q:ℝ) * (2:ℝ)^k)^A := Real.rpow_nonneg (by positivity) A
  have hcell : Work.LinnikAreas.cellLayer R m k ≤ 1 := by
    rw [Work.LinnikAreas.cellLayer]; split <;> norm_num
  have hmul : ((q:ℝ) * (2:ℝ)^k)^A = (q:ℝ)^A * (2:ℝ)^((k:ℝ)*A) := by
    rw [Real.mul_rpow hq0 (by positivity),
      ← Real.rpow_natCast_mul (show (0:ℝ) ≤ 2 by norm_num) k A]
  by_cases hR : (R:ℝ) ≤ (2:ℝ)^k
  · rw [if_pos hR]
    calc (1/4:ℝ)^k * Work.LinnikAreas.cellLayer R m k * ((q:ℝ) * (2:ℝ)^k)^A
        ≤ (1/4:ℝ)^k * 1 * ((q:ℝ) * (2:ℝ)^k)^A :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcell h4) hX
      _ = (q:ℝ)^A * ((1/4:ℝ)^k * (2:ℝ)^((k:ℝ)*A)) := by rw [hmul]; ring
      _ ≤ (q:ℝ)^A * ((2:ℝ)^(-(3/2:ℝ)))^k :=
          mul_le_mul_of_nonneg_left (quarter_mul_two_rpow_le k hA) hqA
  · rw [if_neg hR]
    have hc0 : Work.LinnikAreas.cellLayer R m k = 0 := by
      rw [Work.LinnikAreas.cellLayer, if_neg]
      intro h; exact hR h.1
    rw [hc0]
    simp

end Work.LinnikAreas.JMAux

import Mathlib

namespace Work.ZeroDensity.Jutila

/-- Key pointwise estimate: the reciprocal square root of `n + 1` is dominated by twice the
increment of `√·` over the interval `[n, n + 1]`. -/
private lemma sqrtSuccBoundAux (n : ℕ) :
    (1 : ℝ) / Real.sqrt ((n + 1 : ℕ) : ℝ) ≤
      2 * (Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt (n : ℝ)) := by
  push_cast
  rw [div_le_iff₀ (Real.sqrt_pos.2 (by positivity : (0 : ℝ) < (n : ℝ) + 1))]
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (n : ℝ) + 1 by positivity),
    Real.sq_sqrt (show (0 : ℝ) ≤ (n : ℝ) by positivity),
    sq_nonneg (Real.sqrt ((n : ℝ) + 1) - Real.sqrt (n : ℝ)),
    Real.sqrt_nonneg (n : ℝ), Real.sqrt_nonneg ((n : ℝ) + 1)]

/-- `∑_{b ≤ m} 1/√b ≤ 2√m`, the standard integral-comparison bound for the harmonic-type sum
over square roots. -/
theorem sumInvSqrtBound (m : ℕ) :
    ∑ b ∈ Finset.Ioc 0 m, (1 : ℝ) / Real.sqrt (b : ℝ) ≤ 2 * Real.sqrt (m : ℝ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le m)]
    have hh := sqrtSuccBoundAux m
    push_cast at hh ⊢
    linarith

end Work.ZeroDensity.Jutila

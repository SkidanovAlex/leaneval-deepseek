import Mathlib.Algebra.Order.Star.Real

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux

/-- Arithmetic bookkeeping for the `(N, L)` row pair: with `b ≤ 5`, `k ≤ 6` and the bounds
`L m ≤ M² (m ≤ 4)`, `L m ≤ S (m ≤ 6)`, `N m ≤ M² (m ≤ 3)`, `N m ≤ S (m ≤ 6)`, every term of
`∑_{b₁ = 0}^{b} √(L (b₁+1)) · √(N (k-b₁) · L k)` is at most `(1+M)²(1+S)`.

Reason: `L (b₁+1) ≤ S` and `L k ≤ S` always, and at least one of `b₁+1 ≤ 4`,
`k - b₁ ≤ 3` must hold (otherwise `k ≥ b₁ + 4 ≥ 8 > 6`), so the corresponding square root is
`≤ M`.  Hence the term is `≤ max(M²√S, M·S) ≤ (1+M)²(1+S)`; summing the at most six terms and
using `6 ≤ 1000` gives the claim. -/
theorem fkArith (M S : ℝ) (hM : 0 ≤ M) (hS : 0 ≤ S) (L N : ℕ → ℝ)
    (hLnn : ∀ m, 0 ≤ L m) (hNnn : ∀ m, 0 ≤ N m)
    (hL4 : ∀ m, m ≤ 4 → L m ≤ M ^ 2) (hL6 : ∀ m, m ≤ 6 → L m ≤ S)
    (hN3 : ∀ m, m ≤ 3 → N m ≤ M ^ 2) (hN6 : ∀ m, m ≤ 6 → N m ≤ S)
    (b k : ℕ) (hb : b ≤ 5) (hk : k ≤ 6) :
    ∑ b₁ ∈ Finset.range (b + 1),
        Real.sqrt (L (b₁ + 1)) * Real.sqrt (N (k - b₁) * L k) ≤ 1000 * (1 + M) ^ 2 * (1 + S) := by
  have hsqSnn : 0 ≤ Real.sqrt S := Real.sqrt_nonneg S
  have hsqSsq : Real.sqrt S * Real.sqrt S = S := Real.mul_self_sqrt hS
  have hsqSle : Real.sqrt S ≤ 1 + S := by
    nlinarith [Real.sq_sqrt hS, hS, Real.sqrt_nonneg S]
  have hMMs : 0 ≤ M * M * Real.sqrt S := mul_nonneg (mul_nonneg hM hM) hsqSnn
  -- every summand is bounded by `(1+M)^2 * (1+S)`
  have hterm : ∀ b₁ ∈ Finset.range (b + 1),
      Real.sqrt (L (b₁ + 1)) * Real.sqrt (N (k - b₁) * L k) ≤ (1 + M) ^ 2 * (1 + S) := by
    intro b₁ hb₁
    rw [Finset.mem_range] at hb₁
    have hLknnM : Real.sqrt (L k) ≤ Real.sqrt S := Real.sqrt_le_sqrt (hL6 k hk)
    have hLknn : 0 ≤ Real.sqrt (L k) := Real.sqrt_nonneg _
    have hBnn : 0 ≤ Real.sqrt (N (k - b₁)) := Real.sqrt_nonneg _
    rw [Real.sqrt_mul (hNnn (k - b₁)) (L k)]
    have hmid : Real.sqrt (L (b₁ + 1)) * (Real.sqrt (N (k - b₁)) * Real.sqrt (L k))
        ≤ M * ((M + Real.sqrt S) * Real.sqrt S) := by
      rcases le_or_gt b₁ 3 with h3 | h3
      · -- `b₁ + 1 ≤ 4`, so `√(L (b₁+1)) ≤ M`
        have hA : Real.sqrt (L (b₁ + 1)) ≤ M := by
          have h := Real.sqrt_le_sqrt (hL4 (b₁ + 1) (by omega))
          rwa [Real.sqrt_sq hM] at h
        have hBC : Real.sqrt (N (k - b₁)) * Real.sqrt (L k) ≤ (M + Real.sqrt S) * Real.sqrt S := by
          rcases le_or_gt (k - b₁) 3 with hk3 | hk3
          · have hB : Real.sqrt (N (k - b₁)) ≤ M := by
              have h := Real.sqrt_le_sqrt (hN3 (k - b₁) hk3)
              rwa [Real.sqrt_sq hM] at h
            have h1 : Real.sqrt (N (k - b₁)) * Real.sqrt (L k) ≤ M * Real.sqrt S :=
              mul_le_mul hB hLknnM hLknn hM
            nlinarith [h1, hsqSsq, hsqSnn, hM, hS]
          · have hB : Real.sqrt (N (k - b₁)) ≤ Real.sqrt S :=
              Real.sqrt_le_sqrt (hN6 (k - b₁) (by omega))
            have h1 : Real.sqrt (N (k - b₁)) * Real.sqrt (L k) ≤ Real.sqrt S * Real.sqrt S :=
              mul_le_mul hB hLknnM hLknn hsqSnn
            nlinarith [h1, hsqSsq, hsqSnn, hM, hS]
        exact le_trans (mul_le_mul hA hBC (mul_nonneg hBnn hLknn) hM) le_rfl
      · -- `b₁ ≥ 4`, so `b₁ + 1 ≥ 5` and necessarily `k - b₁ ≤ 3`
        have hA : Real.sqrt (L (b₁ + 1)) ≤ Real.sqrt S :=
          Real.sqrt_le_sqrt (hL6 (b₁ + 1) (by omega))
        have hk3 : k - b₁ ≤ 3 := by omega
        have hB : Real.sqrt (N (k - b₁)) ≤ M := by
          have h := Real.sqrt_le_sqrt (hN3 (k - b₁) hk3)
          rwa [Real.sqrt_sq hM] at h
        have h1 : Real.sqrt (L (b₁ + 1)) * (Real.sqrt (N (k - b₁)) * Real.sqrt (L k))
            ≤ Real.sqrt S * (M * Real.sqrt S) :=
          mul_le_mul hA (mul_le_mul hB hLknnM hLknn hM) (mul_nonneg hBnn hLknn) hsqSnn
        nlinarith [h1, hsqSsq, hsqSnn, hM, hS, hMMs]
    have hfin : M * ((M + Real.sqrt S) * Real.sqrt S) ≤ (1 + M) ^ 2 * (1 + S) := by
      have h2 : M * M * Real.sqrt S ≤ M * M * (1 + S) :=
        mul_le_mul_of_nonneg_left hsqSle (mul_nonneg hM hM)
      have h3 : M * S ≤ (1 + M) * (1 + S) := by nlinarith [hM, hS]
      nlinarith [h2, h3, hsqSsq, hM, hS]
    linarith [hmid, hfin]
  calc ∑ b₁ ∈ Finset.range (b + 1), Real.sqrt (L (b₁ + 1)) * Real.sqrt (N (k - b₁) * L k)
      ≤ ∑ b₁ ∈ Finset.range (b + 1), (1 + M) ^ 2 * (1 + S) := Finset.sum_le_sum hterm
    _ = ((b + 1 : ℕ) : ℝ) * ((1 + M) ^ 2 * (1 + S)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ 6 * ((1 + M) ^ 2 * (1 + S)) := by
        have hb6 : ((b + 1 : ℕ) : ℝ) ≤ 6 := by
          have : b + 1 ≤ 6 := by omega
          exact_mod_cast this
        have hX : 0 ≤ (1 + M) ^ 2 * (1 + S) := by positivity
        nlinarith
    _ ≤ 1000 * (1 + M) ^ 2 * (1 + S) := by
        have hX : 0 ≤ (1 + M) ^ 2 * (1 + S) := by positivity
        nlinarith

end Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux

import Mathlib
import Submission.Work.Diff.STE.Torus

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `wt m ^ k` is dominated by the "word sum" `Σ_{l : Fin k → ι} ∏ᵢ (2π m_{lᵢ})²`

`wt m = 1 + Σᵢ mᵢ² = ⟨m⟩²` is the weight of `∂^0` in the torus Fourier calculus, and
`2π mᵢ` is the Fourier multiplier of `∂ᵢ`.  A single derivative `∂ᵢ` distributed over a
product of `k + 1` factors picks one factor, and the Fourier-side weight it contributes to
that factor is `2π` times the corresponding Fourier index.  Summing over all the ways of
choosing a direction for each of `k` derivatives therefore gives the *word sum*

`wordSum k m = Σ_{l : Fin k → ι} ∏_{i : Fin k} (2π m_{l i})²`,

which is the weight appearing in the `k`-fold Leibniz rule.  The present lemma is the
elementary comparison that makes the Leibniz rule usable in the energy method: the `k`-th
power of the weight of the *undifferentiated* coefficient is dominated by a constant
(`2 ^ k`) times a *single* word-sum weight, uniformly in `k` and `m`.

The mathematics is two lines.  By the multinomial expansion
(`Fintype.sum_pow`, here in the form `(Σᵢ fᵢ)^k = Σ_{l : Fin k → ι} ∏ᵢ f_{l i}`)

`wordSum k m = (Σᵢ (2π mᵢ)²)^k = ((2π)² S)^k`,  where  `S = Σᵢ mᵢ²`,

and `wt m ^ k = (1 + S)^k`; so it suffices to know the elementary
`(1 + S)^k ≤ 2^k (1 + ((2π)² S)^k)` for `S ≥ 0`.  That last inequality is
`add_pow_le` (giving `(1+S)^k ≤ 2^{k-1} (1 + S^k)`, i.e. the concavity of `t ↦ t^k`)
combined with `S^k ≤ ((2π)² S)^k`, which holds because `(2π)² ≥ 1 ≥ 0` and `S ≥ 0`.
No hypothesis on `ι` beyond finiteness is needed, and `k = 0` is covered
(the empty word sum is `1`) since both extremes of `add_pow_le` degenerate correctly.
-/

namespace Work.Diff.STE

open Finset

/-- The elementary numerical core: for `S ≥ 0` and any `k`, the `k`-th power of `1 + S` is
dominated by `2 ^ k` times the two extreme terms `1` and `((2π)² S)^k`; the factor `(2π)²`
only makes the second term larger. -/
lemma one_add_pow_le_two_pow (k : ℕ) {S : ℝ} (hS : 0 ≤ S) :
    (1 + S) ^ k ≤ 2 ^ k * (1 + ((2 * Real.pi) ^ 2 * S) ^ k) := by
  -- concavity of `t ↦ t ^ k` on `ℝ≥0`, in the form `(1 + S)^k ≤ 2^{k-1} (1 + S^k)`
  have h1 : (1 + S) ^ k ≤ 2 ^ (k - 1) * (1 + S ^ k) := by
    simpa using add_pow_le (show (0:ℝ) ≤ 1 by norm_num) hS k
  -- `(2π)² ≥ 1`, hence `S ≤ (2π)² S` for `S ≥ 0`
  have hcp : 1 ≤ (2 * Real.pi) ^ 2 := by
    have := Real.pi_gt_three
    nlinarith
  have hSk : S ^ k ≤ ((2 * Real.pi) ^ 2 * S) ^ k :=
    pow_le_pow_left₀ hS (by nlinarith [mul_le_mul_of_nonneg_right hcp hS]) k
  calc (1 + S) ^ k ≤ 2 ^ (k - 1) * (1 + S ^ k) := h1
    _ ≤ 2 ^ k * (1 + ((2 * Real.pi) ^ 2 * S) ^ k) := by
        exact mul_le_mul (pow_le_pow_right₀ (by norm_num) (Nat.sub_le k 1))
          (by linarith) (by positivity) (by positivity)

/-- The word sum of the `k`-fold Leibniz rule is `(2π)^{2k} (Σᵢ mᵢ²)^k`: summing the
products `∏ᵢ (2π m_{l i})²` over all words `l : Fin k → ι` is the `k`-fold product of the
weight `Σᵢ (2π mᵢ)²` (multinomial expansion). -/
lemma wordSum_eq {ι : Type*} [Fintype ι] (k : ℕ) (m : ι → ℤ) :
    (∑ l : Fin k → ι, ∏ i, (2 * Real.pi * ((m (l i) : ℤ) : ℝ)) ^ 2)
      = ((2 * Real.pi) ^ 2 * ∑ i, ((m i : ℤ) : ℝ) ^ 2) ^ k := by
  rw [← Fintype.sum_pow (fun i => (2 * Real.pi * ((m i : ℤ) : ℝ)) ^ 2) k]
  congr 1
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [mul_pow]

theorem wt_pow_le_wordSum {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ) (m : ι → ℤ) :
    (Work.Diff.STE.wt m) ^ k
      ≤ 2 ^ k * (1 + ∑ l : Fin k → ι, ∏ i, (2 * Real.pi * ((m (l i) : ℤ) : ℝ)) ^ 2) := by
  have hS : 0 ≤ ∑ i, ((m i : ℤ) : ℝ) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  rw [Work.Diff.STE.wt, wordSum_eq k m]
  exact one_add_pow_le_two_pow k hS

end Work.Diff.STE

import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-- Splitting off the top term of a sum over `Icc 1 M`: for `M ≥ 1`,
`∑_{n=1}^{M} a n (b (n+1) - b n) = ∑_{n=1}^{M-1} a n (b (n+1) - b n) + a M (b (M+1) - b M)`. -/
private lemma sum_Icc_one_mul_diff_succ_top (a b : ℕ → ℝ) (M : ℕ) (hM : 1 ≤ M) :
    ∑ n ∈ Finset.Icc 1 M, a n * (b (n + 1) - b n)
      = ∑ n ∈ Finset.Icc 1 (M - 1), a n * (b (n + 1) - b n) + a M * (b (M + 1) - b M) := by
  conv_lhs => rw [← Nat.sub_add_cancel hM]
  rw [Finset.sum_Icc_succ_top (show 1 ≤ M - 1 + 1 by omega)
    (f := fun n => a n * (b (n + 1) - b n))]
  congr 1
  rw [Nat.sub_add_cancel hM]

/-- Discrete integration by parts (Abel summation) on `n ∈ [1, M]`: for any `a b : ℕ → ℝ` and
`M ≥ 1`,
`∑_{n=1}^{M} (a n - a (n-1)) b n = a M b M - a 0 b 1 - ∑_{n=1}^{M-1} a n (b (n+1) - b n)`.

Induction on `M ≥ 1`. Base `M = 1`: both sides are `(a 1 - a 0) b 1 = a 1 b 1 - a 0 b 1`.
Step `M → M+1`: the left side gains the term `(a (M+1) - a M) b (M+1)`, while the right side
gains `a (M+1) b (M+1) - a M b (M+1)` once the top term `a M (b (M+1) - b M)` of the inner
sum over `Icc 1 M` is split off; these are equal term by term. -/
lemma sum_Icc_diff_mul_eq (a b : ℕ → ℝ) {M : ℕ} (hM : 1 ≤ M) :
    ∑ n ∈ Finset.Icc 1 M, (a n - a (n - 1)) * b n
      = a M * b M - a 0 * b 1 - ∑ n ∈ Finset.Icc 1 (M - 1), a n * (b (n + 1) - b n) := by
  induction M, hM using Nat.le_induction with
  | base => simp; ring
  | succ M hM ih =>
    rw [Finset.sum_Icc_succ_top (show 1 ≤ M + 1 by omega)
      (f := fun n => (a n - a (n - 1)) * b n)]
    rw [ih]
    rw [show M + 1 - 1 = M from by omega]
    rw [sum_Icc_one_mul_diff_succ_top a b M hM]
    ring

end Work.BMF

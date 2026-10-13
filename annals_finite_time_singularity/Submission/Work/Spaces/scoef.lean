/-
Copyright: work module for the Elgindi finite-time singularity project.

# The Stirling coefficients of the iterated operator `D_z = z ∂_z`

The operators `D_z = z ∂_z` and `∂_z` satisfy the commutation relation
`∂_z ∘ D_z = D_z ∘ ∂_z + ∂_z`, so that the powers of `D_z` expand in terms of the
powers of `∂_z` with the **Stirling numbers of the second kind** `S(n,k)`:

`D_z^n f = ∑_{k=0}^{n} S(n,k) z^k ∂_z^k f`.

This file only sets up the coefficients (`scoef n k = S(n,k)`, defined by the
Pascal-type recursion `S(n+1,k+1) = (k+1) S(n,k+1) + S(n,k)`) and their elementary
properties, together with the reindexing identity (`scoef_sum_shift`) used by one
step of the induction in `Submission.Work.Spaces.DzIter_le_of_pzIter`.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Tactic.IntervalCases

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

namespace Work.Spaces

set_option autoImplicit false

/-- `scoef n k` is the Stirling number of the second kind `S(n,k)`, defined by the
recursion `S(0,0) = 1`, `S(n+1,0) = 0` and `S(n+1,k+1) = (k+1) S(n,k+1) + S(n,k)`.
These are the coefficients of the expansion `D_z^n = ∑_k S(n,k) z^k ∂_z^k`. -/
def scoef : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => (k + 1) * scoef n (k + 1) + scoef n k

/-- The `n`-th Bell number, i.e. the sum of the Stirling numbers of the second kind
in row `n`: `bell n = ∑_{k≤n} S(n,k)`.  This is exactly the total size of the
coefficients of the expansion `D_z^n = ∑_k S(n,k) z^k ∂_z^k`
(and `bell n = ∑_{k≤n} |S(n,k)|`, since the coefficients are nonnegative). -/
def bell (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), scoef n k

/-- `S(n,k) = 0` for `k > n`: the expansion of `D_z^n` only involves the derivatives
`∂_z^k` with `k ≤ n`. -/
theorem scoef_eq_zero_of_lt : ∀ {n k : ℕ}, n < k → scoef n k = 0 := by
  intro n
  induction n with
  | zero => intro k hk; cases k with
    | zero => omega
    | succ m => simp [scoef]
  | succ n ih => intro k hk; cases k with
    | zero => omega
    | succ m =>
      have h1 : n < m + 1 := by omega
      have h2 : n < m := by omega
      simp [scoef, ih h1, ih h2]

/-- `scoef n (n+1) = 0`, the case of `scoef_eq_zero_of_lt` used by the reindexing. -/
theorem scoef_succ_self_eq_zero (n : ℕ) : scoef n (n + 1) = 0 :=
  scoef_eq_zero_of_lt (Nat.lt_succ_self n)

/-- The Bell numbers of the rows `0 ≤ n ≤ 4` are `1, 1, 2, 5, 15`, all of them
well below `100`. -/
theorem bell_le (n : ℕ) (hn : n ≤ 4) : bell n ≤ 100 := by
  interval_cases n <;> decide

end Work.Spaces

import Mathlib

/-!
# The antidiagonal → range sum bridge

`∑_{b ∈ antidiagonal n} f b.1 b.2 = ∑_{k < n+1} f k (n - k)`.

Mathlib has this for `Finset.Nat.antidiagonal` (`Finset.Nat.sum_antidiagonal_eq_sum_range_succ`) but the
workspace's coefficient lemmas (`coeffNu_mul`, `coeffNu_zero_mul`, `coeffNu_coeff_mul_of_ambF`) are all
phrased with `Finset.HasAntidiagonal.antidiagonal`, and the two namespaces were the single most likely
place to lose a compile cycle in the `coeffNu_mul_two_terms` proof.  Stating the bridge once, here,
removes that hazard permanently.

⚠ Also removes a *second* hazard: `rcases` cannot case-split a `Finset`-literal membership
(`Decidable.rec … instDecidableEqBool … at case List.Mem.head`), so proofs that would want
`rcases h with h | h` on `Finset.HasAntidiagonal`-indexed hypotheses must convert to `range` form
first, where `simp only [Finset.mem_insert, Finset.mem_singleton] at h` then `rcases` does work
(`Submission/PLAN.md` §«SESSION 354» §«continued 36», PROBES A and B).
-/

theorem sum_hasAntidiagonal_eq_sum_range {M : Type*} [AddCommMonoid M] (n : ℕ)
    (f : ℕ → ℕ → M) :
    (∑ b ∈ Finset.HasAntidiagonal.antidiagonal n, f b.1 b.2)
      = ∑ k ∈ Finset.range (n + 1), f k (n - k) := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ]

import Mathlib

/-!
# The coprimality instance `IsCoprime (X ^ n) (X ^ (n - 1) - 1)`

Used twice in the `k = q-1` two-term endgame (`Submission/PLAN.md` §«SESSION 354»):
* via `Commons.Algebra.Coprime.pow_dvd_of_mul_eq` with `x = X`, `n = q-1`, `p = X^(q-1) - 1`;
* for the `X ^ q ∣ g` step of the elimination `(E0′) = (E1′)`.

Stated over a general `CommRing` — the coefficient comparison needs nothing more.  Proof: `X` and
`X^(n-1) - 1` are coprime since `X^(n-2) * X + (-1) * (X^(n-1) - 1) = 1`, then `IsCoprime.pow_left`.
-/

theorem isCoprime_X_pow_X_pow_sub_one {R : Type*} [CommRing R] {n : ℕ} (hn : 2 ≤ n) :
    IsCoprime ((Polynomial.X : Polynomial R) ^ n) (Polynomial.X ^ (n - 1) - 1) := by
  have h1 : IsCoprime (Polynomial.X : Polynomial R) (Polynomial.X ^ (n - 1) - 1) := by
    refine ⟨Polynomial.X ^ (n - 2), -1, ?_⟩
    rw [← pow_succ, show n - 2 + 1 = n - 1 from by omega]
    ring
  exact h1.pow_left

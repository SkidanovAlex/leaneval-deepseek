import Submission.Work.DSM2p.Basic

/-!
# The `p`-th root closure of a polynomial algebra

This module introduces the *root-system ring* `rootClosure A p ι`, the algebraic model of the
ring `A[T_i^{1/p^n} | i ∈ ι, n ≥ 0]` of the Česnavičius–Scholze construction
(arXiv:1912.10932, proof of `Andre-lem`), in which the `n`-th "root" of the variable `i` is a
genuine variable subject to the relations `X_{i,n+1} ^ p = X_i`.

## Main definitions

* `rootClosureIdeal A p ι` — the ideal `(X_{i,n+1} ^ p - X_{i,n})` of `MvPolynomial (ι × ℕ) A`.
* `rootClosure A p ι` — the quotient, i.e. the root-system ring.

## Main results

* `rootClosure_X_pow` — the defining relation `x_{i,n+1} ^ p = x_{i,n}` in the quotient.

The ring is the filtered colimit of the free `A`-algebras `MvPolynomial ι A` along the
substitution `X_i ↦ X_i ^ p`; this description gives flatness and `p`-torsion-freeness (the
lemmas `rootClosure_flat` and `rootClosure_isSMulRegular`, delegated, live in sibling files).
-/

open scoped Classical

namespace Work.DSM2p

universe u

/-- The ideal of relations `X_{i,n+1} ^ p = X_{i,n}` in the polynomial ring on the variables
`ι × ℕ` (the variable `(i,n)` is the `p^n`-th root of the variable `i`). -/
noncomputable def rootClosureIdeal (A : Type u) [CommRing A] (p : ℕ) (ι : Type u) :
    Ideal (MvPolynomial (ι × ℕ) A) :=
  Ideal.span (Set.range fun q : ι × ℕ => MvPolynomial.X (q.1, q.2 + 1) ^ p - MvPolynomial.X q)

/-- The root-system ring `A[X_i^{1/p^n} | i ∈ ι, n ≥ 0]` with `(X_i^{1/p^{n+1}})^p = X_i^{1/p^n}`. -/
abbrev rootClosure (A : Type u) [CommRing A] (p : ℕ) (ι : Type u) : Type u :=
  MvPolynomial (ι × ℕ) A ⧸ rootClosureIdeal A p ι

namespace rootClosure

variable (A : Type u) [CommRing A] (p : ℕ) (ι : Type u)

/-- **The defining relation of the root-system ring.** -/
theorem X_pow (i : ι) (n : ℕ) :
    (Ideal.Quotient.mk (rootClosureIdeal A p ι) (MvPolynomial.X (i, n + 1))) ^ p
      = Ideal.Quotient.mk (rootClosureIdeal A p ι) (MvPolynomial.X (i, n)) := by
  rw [← map_pow, ← sub_eq_zero]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨(i, n), rfl⟩)

end rootClosure

end Work.DSM2p

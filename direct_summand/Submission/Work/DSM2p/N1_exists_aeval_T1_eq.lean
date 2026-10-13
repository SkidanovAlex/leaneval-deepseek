import Mathlib
import Submission.Work.DSM2p.LamOne
import Submission.Work.DSM2p.N1_defs

/-!
# `Work.DSM2p.N1_exists_aeval_T1_eq`

Every element of `Λ = Lam1 A p = A[T^{1/p^n} | n ∈ ℕ]` is a polynomial in a single,
sufficiently high, root `T1 A p k`: for every `z : Λ` and every `n` there are `k ≥ n` and
`u : Polynomial A` with `z = u(T^{1/p^k})`.  Equivalently, `Λ` is the union of the polynomial
subalgebras `A[T^{1/p^k}]`.

The proof: `Λ` is the quotient of the polynomial ring on the variables `X_{(⋆,j)}`,
`j ∈ ℕ`, by the relations `X_{(⋆,j+1)}^p = X_{(⋆,j)}`; the class of `X_{(⋆,j)}` is `T1 A p j`.
An element `z` is the class of a polynomial `g`, and `g` involves only finitely many variables,
so by `MvPolynomial.induction_on` it suffices to track constants, sums and products by a
variable, keeping the height `k` (the index of the root in which one writes everything) large
enough.  The two ingredients are

* `T1_eq_aeval_X_pow` — for `j ≤ k`, `T1 A p j = (T1 A p k) ^ (p ^ (k - j))` is a polynomial in
  `T1 A p k`;
* `T1_aeval_eq_of_le` — the images of `Polynomial.aeval (T1 A p ·)` are nested: a polynomial in
  a lower root is a polynomial in a higher root.
-/

open scoped Classical

namespace Work.DSM2p

universe u

/-- **A lower root is a polynomial in a higher one.**  For `j ≤ k` the root `T1 A p j` equals
`(T1 A p k) ^ (p ^ (k - j))`, hence lies in the range of `Polynomial.aeval (T1 A p k)`. -/
theorem T1_eq_aeval_X_pow (A : Type*) [CommRing A] (p : ℕ) {j k : ℕ} (h : j ≤ k) :
    T1 A p j = Polynomial.aeval (T1 A p k) (Polynomial.X ^ (p ^ (k - j)) : Polynomial A) := by
  have hjk : j + (k - j) = k := Nat.add_sub_cancel' h
  have hkey : (Polynomial.aeval (T1 A p k)) (Polynomial.X ^ (p ^ (k - j)) : Polynomial A)
      = T1 A p k ^ (p ^ (k - j)) := by
    rw [map_pow, Polynomial.aeval_X]
  rw [hkey, show T1 A p k = T1 A p (j + (k - j)) from by rw [hjk], T1_pow_iter]

/-- **The polynomial subalgebras `A[T^{1/p^k}]` are nested.**  For `k ≤ k'` every polynomial in
`T1 A p k` is a polynomial in `T1 A p k'`, namely the same polynomial composed with
`X ^ (p ^ (k' - k))`. -/
theorem T1_aeval_eq_of_le (A : Type*) [CommRing A] (p : ℕ) (k k' : ℕ) (h : k ≤ k')
    (u : Polynomial A) :
    ∃ u' : Polynomial A, Polynomial.aeval (T1 A p k') u' = Polynomial.aeval (T1 A p k) u := by
  refine ⟨u.comp (Polynomial.X ^ (p ^ (k' - k))), ?_⟩
  have hkd : k + (k' - k) = k' := Nat.add_sub_cancel' h
  have hT1 : T1 A p k' ^ (p ^ (k' - k)) = T1 A p k := by
    nth_rewrite 1 [← hkd]
    exact T1_pow_iter A p k (k' - k)
  rw [Polynomial.aeval_comp, map_pow, Polynomial.aeval_X, hT1]

/-- **`Λ` is the union of its polynomial subalgebras `A[T^{1/p^k}]`.**  Every `z : Lam1 A p` is a
polynomial in a single root `T1 A p k` with `k` arbitrary large. -/
theorem N1_exists_aeval_T1_eq (A : Type*) [CommRing A] (p : ℕ) (hp : 1 < p) (n : ℕ)
    (z : Lam1 A p) :
    ∃ k : ℕ, n ≤ k ∧ ∃ u : Polynomial A, z = Polynomial.aeval (T1 A p k) u := by
  classical
  have _hp : 1 < p := hp
  -- `z` is the class of a polynomial `g` in the variables `X_{(⋆,j)}`.
  obtain ⟨g, hg⟩ := Ideal.Quotient.mkₐ_surjective A (rootClosureIdeal A p PUnit) z
  rw [← hg]
  -- Induction on `g`, carrying a bound `k ≥ n` on the height of the root used.
  refine MvPolynomial.induction_on (motive := fun g => ∃ k : ℕ, n ≤ k ∧ ∃ u : Polynomial A,
    Ideal.Quotient.mkₐ A (rootClosureIdeal A p PUnit) g = Polynomial.aeval (T1 A p k) u)
    g ?hC ?hadd ?hmul
  case hC =>
    -- constants are polynomials in any root
    intro a
    exact ⟨n, le_refl n, Polynomial.C a, by simp⟩
  case hadd =>
    -- sums: take the larger of the two heights
    intro x y hx hy
    obtain ⟨k1, hk1, u1, hu1⟩ := hx
    obtain ⟨k2, hk2, u2, hu2⟩ := hy
    obtain ⟨u1', hu1'⟩ := T1_aeval_eq_of_le A p k1 (max k1 k2) (le_max_left _ _) u1
    obtain ⟨u2', hu2'⟩ := T1_aeval_eq_of_le A p k2 (max k1 k2) (le_max_right _ _) u2
    refine ⟨max k1 k2, le_trans hk1 (le_max_left _ _), u1' + u2', ?_⟩
    rw [map_add, map_add, hu1, hu2, ← hu1', ← hu2']
  case hmul =>
    -- multiplication by a variable `X_{(⋆,j)}`, i.e. by `T1 A p j`: take the larger height
    intro x q hx
    obtain ⟨k1, hk1, u1, hu1⟩ := hx
    obtain ⟨u1', hu1'⟩ := T1_aeval_eq_of_le A p k1 (max k1 q.2) (le_max_left _ _) u1
    refine ⟨max k1 q.2, le_trans hk1 (le_max_left _ _),
      u1' * Polynomial.X ^ (p ^ (max k1 q.2 - q.2)), ?_⟩
    have hXq : Ideal.Quotient.mkₐ A (rootClosureIdeal A p PUnit) (MvPolynomial.X q)
        = T1 A p q.2 := rfl
    rw [map_mul, hXq, hu1, ← hu1', T1_eq_aeval_X_pow A p (le_max_right k1 q.2), map_mul]

end Work.DSM2p

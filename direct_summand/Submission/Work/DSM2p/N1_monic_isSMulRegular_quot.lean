import Mathlib
import Submission.Work.DSM2p.LamOne
import Submission.Work.DSM2p.N1_defs
import Submission.Work.DSM2p.N1_exists_aeval_T1_eq
import Submission.Work.DSM2p.N1_quot_algEquiv_rootClosure
import Submission.Work.DSM2p.N1_T1_aeval_injective

/-!
# `Work.DSM2p.N1_monic_isSMulRegular_quot` (node `N1` of the M2p design)

Let `Λ = Lam1 A p = rootClosure A p PUnit = A[T^{1/p^n} | n ∈ ℕ]/((T^{1/p^{n+1}})^p - T^{1/p^n})`
and let `T1 A p n` be the class of the variable `T^{1/p^n}`.  The node says:

> for every ideal `I ⊆ A` and every *monic* `g ∈ A[X]`, the class of `g(T^{1/p^n})` is a
> non-zero-divisor of `Λ ⧸ I Λ`.

The proof has three ingredients.

1. `N1_T1_aeval_injective`: `T^{1/p^n}` is transcendental over `A`, i.e. `Polynomial.aeval
   (T1 A p n) : A[X] → Λ` is injective.  (The relation `T^{1/p^{n+1}} = (T^{1/p^n})^p` is not a
   polynomial relation of `T^{1/p^n}` with coefficients in `A`, and indeed the map is injective
   for every coefficient ring `A`.)

2. `N1_exists_aeval_T1_eq`: every element of `Λ` is a polynomial in a single, sufficiently high,
   root: for every `z` there are `k ≥ n` and `u ∈ A[X]` with `z = u(T^{1/p^k})`.  This is the
   statement that `Λ` is the union of the polynomial rings `A[T^{1/p^k}]`.

3. `N1_quot_algEquiv_rootClosure`: base change, `Λ ⧸ I Λ ≅ Λ_{A ⧸ I}`, compatibly with
   `T1 ↦ T1` and with coefficients.

Given these, the argument is: replacing `T^{1/p^n}` by `T^{1/p^k}` for `k ≥ n` the monic
polynomial `g` becomes the monic polynomial `g(X^{p^(k-n)}) = expand A (p^(k-n)) g`, so on the
"tower level" `A[X]` the element acts as a monic polynomial, hence regularly; and injectivity of
`aeval (T1 A p k)` transports regularity from `A[X]` up to `Λ`.  Since every element of `Λ` is
already a polynomial in `T^{1/p^k}` (as soon as `k` is large enough), this proves regularity on
all of `Λ`.  Finally, base change transports the statement from `A` to `A ⧸ I`.
-/

open scoped Classical

namespace Work.DSM2p

universe u

/-- **The coefficient-ring form of the node.**  For an arbitrary commutative ring `B` and a monic
`g ∈ B[X]`, the element `g(T^{1/p^n})` is a non-zero-divisor of `Λ = Lam1 B p`. -/
theorem N1_zero (B : Type u) [CommRing B] (p : ℕ) (hp : 1 < p) (n : ℕ) (g : Polynomial B)
    (hg : g.Monic) :
    IsSMulRegular (Lam1 B p) (Polynomial.aeval (T1 B p n) g) := by
  classical
  refine isLeftRegular_iff.mpr ?_
  intro x y hxy
  -- it suffices to test against annihilators, and every element of `Λ` is a polynomial in
  -- `T^{1/p^k}` for `k` large
  have key : ∀ z : Lam1 B p, Polynomial.aeval (T1 B p n) g * z = 0 → z = 0 := by
    intro z hz
    obtain ⟨k, hk, u, hu⟩ := N1_exists_aeval_T1_eq B p hp n z
    have hT1 : T1 B p k ^ (p ^ (k - n)) = T1 B p n := by
      have hT1' : T1 B p (n + (k - n)) ^ (p ^ (k - n)) = T1 B p n :=
        T1_pow_iter B p n (k - n)
      rwa [Nat.add_sub_cancel' hk] at hT1'
    have haeval : Polynomial.aeval (T1 B p k) (Polynomial.expand B (p ^ (k - n)) g)
        = Polynomial.aeval (T1 B p n) g := by
      rw [Polynomial.expand_eq_comp_X_pow, Polynomial.aeval_comp, map_pow, Polynomial.aeval_X,
        hT1]
    have hmonic : (Polynomial.expand B (p ^ (k - n)) g).Monic :=
      hg.expand (pow_pos (by omega) _)
    have hreg : IsLeftRegular (Polynomial.expand B (p ^ (k - n)) g) := hmonic.isRegular.left
    have h0 : Polynomial.aeval (T1 B p k) (u * Polynomial.expand B (p ^ (k - n)) g) = 0 := by
      rw [map_mul, ← hu, haeval, mul_comm]
      exact hz
    have hz0 : u * Polynomial.expand B (p ^ (k - n)) g = 0 := by
      refine N1_T1_aeval_injective B p hp k ?_
      rw [h0, map_zero]
    have hu0 : u = 0 := by
      have h2 : Polynomial.expand B (p ^ (k - n)) g * u = 0 := by rwa [mul_comm] at hz0
      exact (IsLeftRegular.mul_left_eq_zero_iff hreg).mp h2
    rw [hu0, map_zero] at hu
    exact hu
  have hsub : Polynomial.aeval (T1 B p n) g * (x - y) = 0 := by
    have hxy' : Polynomial.aeval (T1 B p n) g * x = Polynomial.aeval (T1 B p n) g * y := hxy
    rw [mul_sub, hxy', sub_self]
  exact sub_eq_zero.mp (key (x - y) hsub)

theorem N1_monic_isSMulRegular_quot (A : Type*) [CommRing A] (p : ℕ) [Fact p.Prime]
    (I : Ideal A) (n : ℕ) (g : Polynomial A) (hg : g.Monic) :
    IsSMulRegular (Lam1 A p ⧸ I.map (algebraMap A (Lam1 A p)))
      (Ideal.Quotient.mk (I.map (algebraMap A (Lam1 A p)))
        (Polynomial.aeval (T1 A p n) g)) := by
  classical
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  obtain ⟨e, he⟩ := N1_quot_algEquiv_rootClosure A p I
  have hmonic : (g.map (Ideal.Quotient.mk I)).Monic := hg.map _
  have hcore : IsSMulRegular (Lam1 (A ⧸ I) p)
      (Polynomial.aeval (T1 (A ⧸ I) p n) (g.map (Ideal.Quotient.mk I))) :=
    N1_zero (A ⧸ I) p hp n _ hmonic
  refine (Equiv.isSMulRegular_congr (e := e) ?_).mpr hcore
  intro x
  show e (Ideal.Quotient.mk (I.map (algebraMap A (Lam1 A p))) (Polynomial.aeval (T1 A p n) g)
        * x)
      = Polynomial.aeval (T1 (A ⧸ I) p n) (g.map (Ideal.Quotient.mk I)) * e x
  rw [map_mul, he n g]

end Work.DSM2p

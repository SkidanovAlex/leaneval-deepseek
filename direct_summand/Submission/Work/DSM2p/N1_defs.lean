import Mathlib
import Submission.Work.DSM2p.LamOne

/-!
# `Work.DSM2p.N1_defs`

Elementary vocabulary for the node `N1_monic_isSMulRegular_quot`.

The root-system ring `Λ = Lam1 A p = rootClosure A p PUnit` is `A[T^{1/p^n} | n ∈ ℕ]` with
`(T^{1/p^{n+1}})^p = T^{1/p^n}`; the class of the variable `X_{(⋆,n)}` is `T1 A p n`.  The
iterated form of the defining relation is recorded here; it is what turns an arbitrary element
of `Λ` into a polynomial in a single, sufficiently high, root `T1 A p k`.

## Main result

* `T1_pow_iter` — `(T1 A p (m + d)) ^ (p ^ d) = T1 A p m`.
-/

open scoped Classical

namespace Work.DSM2p

universe u

/-- **Iterated defining relation of the root-system ring.**  The `p^d`-th power of the variable
`T^{1/p^{m+d}}` is the variable `T^{1/p^m}`. -/
theorem T1_pow_iter (A : Type u) [CommRing A] (p : ℕ) (m d : ℕ) :
    T1 A p (m + d) ^ (p ^ d) = T1 A p m := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hpow : p ^ (d + 1) = p * p ^ d := by rw [pow_succ']
    have hidx : m + (d + 1) = (m + d) + 1 := by omega
    rw [hpow, hidx, pow_mul, T1_pow, ih]

end Work.DSM2p

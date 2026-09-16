import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.Hom.Defs

namespace Commons.Algebra.Polynomial

/-- **The product of a periodic orbit under a ring endomorphism is fixed.**

If `σ : R →+* R` and `(σ^[M]) p = p`, then the product `∏ m ∈ range M, (σ^[m]) p` is `σ`-fixed.

Proof: `σ` of the product is `∏ m ∈ range M, (σ^[m+1]) p = ∏ m ∈ range M, (σ^[m]) p` after reindexing
`range M → Icc 1 M` and using `(σ^[M]) p = p` to move the last factor to the front.

Motivation: a Frobenius orbit that closes up to an associate gives `σ^M(r) = c·r`; rescaling `r` by a
constant makes it literally `σ^M`-periodic, and then this product is fixed by `σ`, hence (for
`σ = polyTwist 1`) has coefficients in `F_q` — an `F_q[X]`-denominator for `r`. -/
theorem map_prod_range_iterate_eq_self {R : Type*} [CommSemiring R] (σ : R →+* R) (p : R) (M : ℕ)
    (hM : (σ^[M]) p = p) :
    σ (∏ m ∈ Finset.range M, (σ^[m]) p) = ∏ m ∈ Finset.range M, (σ^[m]) p := by
  have key : ∏ m ∈ Finset.range M, (σ^[m + 1]) p = ∏ m ∈ Finset.range M, (σ^[m]) p := by
    cases M with
    | zero => simp
    | succ n =>
      calc ∏ m ∈ Finset.range (n + 1), (σ^[m + 1]) p
          = (∏ m ∈ Finset.range n, (σ^[m + 1]) p) * (σ^[n + 1]) p :=
              Finset.prod_range_succ (fun m => (σ^[m + 1]) p) n
        _ = (∏ m ∈ Finset.range n, (σ^[m + 1]) p) * (σ^[0]) p := by
              rw [hM, Function.iterate_zero_apply]
        _ = ∏ m ∈ Finset.range (n + 1), (σ^[m]) p :=
              (Finset.prod_range_succ' (fun m => (σ^[m]) p) n).symm
  calc σ (∏ m ∈ Finset.range M, (σ^[m]) p)
      = ∏ m ∈ Finset.range M, σ ((σ^[m]) p) := map_prod σ (fun m => (σ^[m]) p) (Finset.range M)
    _ = ∏ m ∈ Finset.range M, (σ^[m + 1]) p := by
          simp_rw [← Function.iterate_succ_apply']
    _ = ∏ m ∈ Finset.range M, (σ^[m]) p := key

end Commons.Algebra.Polynomial
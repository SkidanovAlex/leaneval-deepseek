import Mathlib
import Submission.Work.ORLyndon.Fox

/-!
# The Fox derivative of a power

For the Fox calculus on a free group `F(X)` with coefficients in a ring `K`, the
derivative of a power satisfies the geometric series identity

`∂(g ^ n)/∂x = (1 + g + g² + ⋯ + g ^ (n-1)) * ∂g/∂x`,

where `g` denotes the image of `g` in `K[F(X)]` and the sum is empty for `n = 0`.
This is the Leibniz rule `∂(gh)/∂x = ∂g/∂x + g · ∂h/∂x` iterated, using
`of (g ^ i) = (of g) ^ i`.

This is the standard input for Lyndon's identity theorem: for a relator `r = u ^ l`
the identity turns `(u - 1) · ∂(u ^ l)/∂x = (u ^ l - 1) · ∂u/∂x` into `0`.
-/

set_option autoImplicit false

namespace Work.ORLyndon

open MonoidAlgebra

theorem foxD_pow {X : Type*} [DecidableEq X] {K : Type*} [Ring K] (x : X) (g : FreeGroup X)
    (n : ℕ) :
    Work.ORLyndon.foxD (K := K) x (g ^ n) =
      (∑ i ∈ Finset.range n, ((MonoidAlgebra.of K (FreeGroup X)) g) ^ i) *
        Work.ORLyndon.foxD (K := K) x g := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, foxD_mul, ih, Finset.sum_range_succ, add_mul]
    simp only [map_pow]

end Work.ORLyndon

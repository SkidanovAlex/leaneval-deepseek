import Mathlib
import Submission.Commons.Analysis.Asymptotics.abel_tail_bound_finite

set_option autoImplicit false

namespace Commons.Analysis.Sums

/-- Finite Abel (partial summation) tail bound: if contiguous sums of `a : ℕ → ℂ`
over `Icc x y` are bounded by `B`, then for `0 < s.re` and `1 ≤ N ≤ M`,
`‖∑_{k=N}^{M} a k · k^(-s)‖ ≤ B · N^(-s.re) · (1 + ‖s‖ / s.re)`. -/
theorem tail_pow_abel_bound {a : ℕ → ℂ} (B : ℝ) (hB : ∀ x y : ℕ, x ≤ y →
    ‖∑ n ∈ Finset.Icc x y, a n‖ ≤ B) (s : ℂ) (hs : 0 < s.re)
    {N M : ℕ} (hNM : N ≤ M) (hN1 : 1 ≤ N) :
    ‖∑ k ∈ Finset.Icc N M, a k * (k : ℂ) ^ (-s)‖
      ≤ B * (N : ℝ) ^ (-s.re) * (1 + ‖s‖ / s.re) :=
  Commons.Analysis.Asymptotics.abel_tail_bound_finite B hB s hs hNM hN1

end Commons.Analysis.Sums

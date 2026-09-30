import Mathlib
import Submission.Work.BMF.halasz_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Auxiliary objects for `Work.BMF.halasz_plancherel`

The Mellin–Plancherel identity for `Kf f t = Σ_{n ≤ t} f n log n` is proved by truncating the
sum at `n ≤ N`, computing both sides exactly for the truncation, and passing to the limit.
The objects below are the truncated summatory function `KfN`, the truncated Dirichlet series
`dirSum`, and the quadratic form `UN` that both truncated sides evaluate to.
-/

namespace Work.BMF

/-- Truncated summatory function `KfN f N t = Σ_{n ≤ min N ⌊t⌋} f n · log n`. -/
noncomputable def KfN (f : ℕ → ℂ) (N : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 (min N ⌊t⌋₊), f n * (Real.log n : ℂ)

/-- Truncated Dirichlet series `dirSum f α N τ = Σ_{n ≤ N} f n · log n · n^{-(1+α+iτ)}`. -/
noncomputable def dirSum (f : ℕ → ℂ) (α : ℝ) (N : ℕ) (τ : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, (f n * (Real.log n : ℂ)) *
    (n : ℂ) ^ (-(((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I))

/-- The real quadratic form
`UN f α N = Σ_{m,n ≤ N} Re (f m log m · conj (f n log n)) · max m n ^ (-(2+2α))`. -/
noncomputable def UN (f : ℕ → ℂ) (α : ℝ) (N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
    ((f m * (Real.log m : ℂ)) * starRingEnd ℂ (f n * (Real.log n : ℂ))).re *
      (((max m n : ℕ) : ℝ) ^ (-(2 + 2 * α)))

end Work.BMF

/-
# The raw dyadic families and the identification with the dyadic telescope

`rawH a m k = a (2 ^ m * k) - a (2 ^ m * (k - k % 2))` is the increment of `a` over the aligned
block `(2 ^ m * (k - k % 2), 2 ^ m * k]` (which is empty, i.e. `0`, when `k` is even).  The
identification `rawH a m (N / 2 ^ m) = a (rnd N m) - a (rnd N (m+1))` is what makes the dyadic
telescoping of `Work.Analysis.Variation.Dyadic` into a "per-scale" statement: for each `m`, the
sequence `N ↦ a (rnd N m) - a (rnd N (m+1))` is the raw family at scale `2 ^ m` evaluated at the
*monotone* index `N / 2 ^ m`, which is exactly the situation handled by
`Work.Analysis.Variation.lp_variation_le_of_monotone_index`.
-/
import Submission.Work.Analysis.Variation.Dyadic

set_option autoImplicit false

open scoped BigOperators ENNReal
open Finset

namespace Work.Analysis.Variation

/-- The dyadic telescope is the raw family at the monotone index `N / 2 ^ m`. -/
theorem rawH_eq_rnd (a : ℕ → ℂ) (m N : ℕ) :
    rawH a m (N / 2 ^ m) = a (rnd N m) - a (rnd N (m + 1)) := by
  have h : rnd N (m + 1) = 2 ^ m * (N / 2 ^ m - N / 2 ^ m % 2) := rnd_succ_eq N m
  rw [rawH, rnd, h]

/-- The two-dimensional dyadic telescope is the raw two-dimensional family at the monotone
pair of indices `(N / 2 ^ m₁, N / 2 ^ m₂)`. -/
theorem rawH2_eq_rnd (a : ℕ → ℕ → ℂ) (m₁ m₂ N : ℕ) :
    rawH2 a m₁ m₂ (N / 2 ^ m₁) (N / 2 ^ m₂)
      = a (rnd N m₁) (rnd N m₂) - a (rnd N (m₁ + 1)) (rnd N m₂)
        - a (rnd N m₁) (rnd N (m₂ + 1)) + a (rnd N (m₁ + 1)) (rnd N (m₂ + 1)) := by
  have h1 : rnd N (m₁ + 1) = 2 ^ m₁ * (N / 2 ^ m₁ - N / 2 ^ m₁ % 2) := rnd_succ_eq N m₁
  have h2 : rnd N (m₂ + 1) = 2 ^ m₂ * (N / 2 ^ m₂ - N / 2 ^ m₂ % 2) := rnd_succ_eq N m₂
  rw [rawH2, rnd, h1, h2]
  simp only [rnd]

end Work.Analysis.Variation

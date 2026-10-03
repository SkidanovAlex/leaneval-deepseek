import Mathlib
import Submission.Commons.Analysis.ExponentialSums.second_derivative_test

namespace Commons.Analysis.ExponentialSums

open Finset
open scoped BigOperators

/-- The distance-to-nearest-integer `intDist x = min (fract x) (1 - fract x)` is 1-Lipschitz:
`|intDist x - intDist y| ≤ |x - y|`.  Equivalently `intDist` is the distance from `x` to `ℤ`,
and distance to a set is Lipschitz. -/
theorem intDist_abs_sub_le (x y : ℝ) :
    |Submission.VanDerCorput.intDist x - Submission.VanDerCorput.intDist y| ≤ |x - y| := by
  -- Core one-sided bound: `intDist u ≤ |u - v| + intDist v`.
  have key : ∀ u v : ℝ,
      Submission.VanDerCorput.intDist u ≤ |u - v| + Submission.VanDerCorput.intDist v := by
    intro u v
    -- `intDist u ≤ |u - ⌊v⌋| ≤ |u - v| + frac v`
    have h1 : Submission.VanDerCorput.intDist u ≤ |u - v| + Int.fract v := by
      have h := Submission.IntDistRegion.intDist_le_abs_sub u ⌊v⌋
      have htri : |u - (⌊v⌋ : ℝ)| ≤ |u - v| + |v - (⌊v⌋ : ℝ)| := by
        have heq : u - (⌊v⌋ : ℝ) = (u - v) + (v - (⌊v⌋ : ℝ)) := by ring
        rw [heq]
        exact abs_add_le _ _
      rw [Submission.IntDistRegion.abs_sub_floor_eq_fract v] at htri
      exact le_trans h htri
    -- `intDist u ≤ |u - (⌊v⌋+1)| ≤ |u - v| + (1 - frac v)`
    have h2 : Submission.VanDerCorput.intDist u ≤ |u - v| + (1 - Int.fract v) := by
      have h := Submission.IntDistRegion.intDist_le_abs_sub u (⌊v⌋ + 1)
      have htri : |u - ((⌊v⌋ + 1 : ℤ) : ℝ)| ≤
          |u - v| + |v - ((⌊v⌋ + 1 : ℤ) : ℝ)| := by
        have heq : u - ((⌊v⌋ + 1 : ℤ) : ℝ) =
            (u - v) + (v - ((⌊v⌋ + 1 : ℤ) : ℝ)) := by ring
        rw [heq]
        exact abs_add_le _ _
      rw [Submission.IntDistRegion.abs_sub_floor_add_one v] at htri
      exact le_trans h htri
    -- combine with `min (frac v) (1 - frac v) = intDist v`
    show Submission.VanDerCorput.intDist u ≤
      |u - v| + min (Int.fract v) (1 - Int.fract v)
    rw [← min_add_add_left]
    exact le_min h1 h2
  have h1 := key x y
  have h2 := key y x
  rw [abs_sub_comm] at h2
  rw [abs_sub_le_iff]
  exact ⟨by linarith, by linarith⟩

end Commons.Analysis.ExponentialSums

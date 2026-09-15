import Mathlib
import Submission.Commons.Combinatorics.Additive.Gowers.gowers_cube_nonneg

namespace Commons.Combinatorics.Additive.Gowers

/-- **Positivity of the Gowers cube sum.**  For `d ≥ 1` the `d`-dimensional cube sum of a
constant family is nonnegative, so that `‖f‖_{U^d} := (cube sum)^{1/2^d}` is well defined.
This is the positivity property of Green–Tao (2008), §5 (see also Gowers 1998). -/
theorem gowers_cube_sum_const_nonneg {G : Type*} [AddCommGroup G] [Fintype G]
    (f : G → ℝ) (d : ℕ) (hd : 0 < d) :
    0 ≤ ∑ h : Fin d → G, ∑ x : G, ∏ ω : Fin d → Bool,
        f (x + ∑ i : Fin d, (if ω i then h i else 0)) := by
  obtain ⟨d', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hd)
  exact gowers_cube_nonneg f d'

end Commons.Combinatorics.Additive.Gowers

import Mathlib
import Submission.Commons.Combinatorics.Transference.Unorm_pow
import Submission.Commons.Combinatorics.Transference.cubeSum_nonneg

namespace Commons.Combinatorics.Transference

open Finset
open scoped BigOperators

/-- The Gowers `U^d` norm is nonnegative. -/
theorem Unorm_nonneg {G : Type*} [AddCommGroup G] [Fintype G] (d : ℕ) (hd : 1 ≤ d) (g : G → ℝ) :
    0 ≤ Unorm d g := by
  rw [Unorm]
  exact Real.rpow_nonneg
    (div_nonneg (cubeSum_nonneg d hd g) (pow_nonneg (Nat.cast_nonneg _) _)) _

end Commons.Combinatorics.Transference

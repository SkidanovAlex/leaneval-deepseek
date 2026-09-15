import Mathlib
import Submission.Commons.Combinatorics.Transference.Unorm_pow

namespace Commons.Combinatorics.Transference

open Finset
open scoped BigOperators

/-- The cube sum is homogeneous of degree `2^d`: `cubeSum d (c·f) = c^{2^d}·cubeSum d f`. -/
theorem cubeSum_smul {p : ℕ} [Fact p.Prime] {d : ℕ} (c : ℝ) (f : ZMod p → ℝ) :
    cubeSum d (fun x => c * f x) = c ^ (2 ^ d) * cubeSum d f := by
  unfold cubeSum
  -- In each product `∏ ω, c * f (x + ω·h)` there are `2^d` factors `c` (since
  -- `Fintype.card (Fin d → Bool) = 2 ^ d`), which can be pulled out of the sums.
  simp only [Finset.mul_sum, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]

end Commons.Combinatorics.Transference

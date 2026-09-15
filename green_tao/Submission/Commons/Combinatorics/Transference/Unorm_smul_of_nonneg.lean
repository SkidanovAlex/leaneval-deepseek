import Mathlib
import Submission.Commons.Combinatorics.Transference.Unorm_pow
import Submission.Commons.Combinatorics.Transference.Unorm_nonneg
import Submission.Commons.Combinatorics.Transference.cubeSum_smul

namespace Commons.Combinatorics.Transference

open Finset
open scoped BigOperators

/-- Scaling a nonnegative real `x` by the `2^d`-th power of a nonnegative `c` only to take the
`2^d`-th root again recovers `c` times the `2^d`-th root of `x`: for `c, x ≥ 0`,
`(c^{2^d}·x)^{1/2^d} = c·x^{1/2^d}`. -/
private lemma pow_mul_rpow_inv_pow_two {d : ℕ} {x m : ℝ} (hx : 0 ≤ x) (hm : 0 ≤ m) :
    (x ^ (2 ^ d) * m) ^ (((2 ^ d : ℕ) : ℝ)⁻¹) = x * m ^ (((2 ^ d : ℕ) : ℝ)⁻¹) := by
  have hn : ((2 ^ d : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (pow_ne_zero d (by norm_num : (2 : ℕ) ≠ 0))
  rw [Real.mul_rpow (pow_nonneg hx (2 ^ d)) hm, ← Real.rpow_natCast x (2 ^ d),
    ← Real.rpow_mul hx, mul_inv_cancel₀ hn, Real.rpow_one]

/-- The Gowers `U^d` norm is homogeneous of degree one for nonnegative scalars:
`‖c·f‖_{U^d} = c·‖f‖_{U^d}` for `c ≥ 0`.  (Useful for replacing `(ν+1)/2` by `ν` in the
transference arguments: `‖(ν-1)/2‖ = ‖ν-1‖/2`.) -/
theorem Unorm_smul_of_nonneg {p : ℕ} [Fact p.Prime] {d : ℕ} (hd : 1 ≤ d) {c : ℝ} (hc : 0 ≤ c)
    (f : ZMod p → ℝ) :
    Unorm d (fun x => c * f x) = c * Unorm d f := by
  have hA0 : 0 ≤ cubeSum d f / ((Fintype.card (ZMod p) : ℝ) ^ (d + 1)) :=
    cubeSum_div_card_nonneg d hd f
  rw [Unorm, Unorm, cubeSum_smul]
  rw [show c ^ (2 ^ d) * cubeSum d f / ((Fintype.card (ZMod p) : ℝ) ^ (d + 1))
        = c ^ (2 ^ d) * (cubeSum d f / ((Fintype.card (ZMod p) : ℝ) ^ (d + 1))) by ring]
  exact pow_mul_rpow_inv_pow_two hc hA0

end Commons.Combinatorics.Transference

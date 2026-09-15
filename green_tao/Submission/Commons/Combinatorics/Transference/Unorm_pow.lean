import Mathlib
import Submission.Commons.Combinatorics.Transference.cubeSum_nonneg

namespace Commons.Combinatorics.Transference

open Finset
open scoped BigOperators

/-- The Green–Tao `d`-cube sum `∑_h ∑_x ∏_{ω : Fin d → Bool} g (x + ω·h)`, where
`ω·h = ∑_i (if ω i then h i else 0)`.  This is `|G|^{d+1} · ‖g‖_{U^d}^{2^d}`. -/
noncomputable def cubeSum {G : Type*} [AddCommGroup G] [Fintype G] (d : ℕ) (g : G → ℝ) : ℝ :=
  ∑ h : Fin d → G, ∑ x : G, ∏ ω : Fin d → Bool, g (x + ∑ i, (if ω i then h i else 0))

/-- The Gowers `U^d` norm of `g`, as an explicit real number
`(cubeSum d g / |G|^{d+1})^{1/2^d}`. -/
noncomputable def Unorm {G : Type*} [AddCommGroup G] [Fintype G] (d : ℕ) (g : G → ℝ) : ℝ :=
  (cubeSum d g / ((Fintype.card G : ℝ) ^ (d + 1))) ^ (((2 ^ d : ℕ) : ℝ)⁻¹)

/-- The normalising factor `cubeSum d g / |G|^{d+1}` is nonnegative, because it is a
nonnegative cube sum divided by a nonnegative power of the (real) group order. -/
lemma cubeSum_div_card_nonneg {G : Type*} [AddCommGroup G] [Fintype G]
    (d : ℕ) (hd : 1 ≤ d) (g : G → ℝ) :
    0 ≤ cubeSum d g / ((Fintype.card G : ℝ) ^ (d + 1)) :=
  div_nonneg (cubeSum_nonneg d hd g) (pow_nonneg (Nat.cast_nonneg _) _)

/-- `Unorm d g` raised to the `2^d`-th power recovers the normalised cube sum. -/
theorem Unorm_pow {G : Type*} [AddCommGroup G] [Fintype G] (d : ℕ) (hd : 1 ≤ d) (g : G → ℝ) :
    Unorm d g ^ (2 ^ d) = cubeSum d g / ((Fintype.card G : ℝ) ^ (d + 1)) := by
  rw [Unorm]
  exact Real.rpow_inv_natCast_pow (cubeSum_div_card_nonneg d hd g) (by positivity)

end Commons.Combinatorics.Transference

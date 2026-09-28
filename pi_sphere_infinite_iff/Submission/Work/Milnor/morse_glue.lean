import Mathlib
import Submission.Work.Milnor.MorseFun

set_option synthInstance.maxHeartbeats 400000

/-!
# The two chart expressions of Milnor's Morse function agree across the gluing

The function `F` of `Submission.Work.Milnor.MorseFun` is given in the first chart by

`morseChart1 (x, y) = Re(ẋ * y) / √(1 + ‖x‖²)`,   `ẋ = Quaternion.linearIsometryEquivTuple.symm x`,

and in the second chart by `morseChart2 (x', y') = Re(y') / √(1 + ‖x'‖²)`.

The two charts of `Mk (-2)` are glued along `{x ≠ 0} × S³` by
`clutchMap (-2) (x, y) = (x/‖x‖², u² y u⁻¹)`, `u = x/‖x‖`, so the compatibility of the two
expressions is the identity

`Re(ẋ y) / √(1 + ‖x‖²) = Re(u² y u⁻¹) / √(1 + ‖x/‖x‖²‖²)`.

The two ingredients are

* `Re(u² y u⁻¹) = Re(u y) = ‖x‖⁻¹ Re(ẋ y)` (cyclic invariance of `Re` of a triple product, and
  `u = ẋ/‖x‖`), and
* `√(1 + ‖x/‖x‖²‖²) = √(1 + ‖x‖²) / ‖x‖`.

Both are proved below; `morse_glue` is then immediate.
-/

namespace Work.Milnor

open scoped Manifold ContDiff Topology
open TopologicalSpace Set
open Submission.Milnor

noncomputable section

/-- `Re` of a product of three quaternions is invariant under cyclic permutations. -/
lemma re_mul_mul_comm (a b c : Quaternion ℝ) : (a * b * c).re = (c * a * b).re := by
  calc (a * b * c).re = (c * (a * b)).re := Submission.Milnor.re_mul_comm (a * b) c
    _ = (c * a * b).re := by rw [mul_assoc]

/-- The real part of the twist `clutch 2 (unitDir x, y) = u ^ 2 * y * u⁻¹`, `u = unitDir x`:
cyclicity of `Re` together with `u⁻¹ u² = u` and `u = ẋ / ‖x‖` give `‖x‖⁻¹ Re(ẋ y)`. -/
lemma re_clutch_two (x : EuclideanSpace ℝ (Fin 4)) (hx : x ≠ 0) (y : QS3) :
    ((clutch 2 (unitDir x, y) : QS3) : Quaternion ℝ).re
      = (Quaternion.linearIsometryEquivTuple.symm x * (y : Quaternion ℝ)).re / ‖x‖ := by
  have hu : ((unitDir x : QS3) : Quaternion ℝ) = dirVal x := unitDir_coe x hx
  have hne : ((unitDir x : QS3) : Quaternion ℝ) ≠ 0 :=
    norm_ne_zero_iff.mp (by rw [Submission.Milnor.norm_coe]; exact one_ne_zero)
  rw [show ((clutch 2 (unitDir x, y) : QS3) : Quaternion ℝ)
        = ((unitDir x : QS3) : Quaternion ℝ) ^ (2 : ℤ) * (y : Quaternion ℝ)
          * ((unitDir x : QS3) : Quaternion ℝ)⁻¹
      from by simp only [clutch, clutchVal, Subtype.coe_mk]]
  rw [zpow_two, re_mul_mul_comm]
  have hu2 : ((unitDir x : QS3) : Quaternion ℝ)⁻¹
      * (((unitDir x : QS3) : Quaternion ℝ) * ((unitDir x : QS3) : Quaternion ℝ))
      = ((unitDir x : QS3) : Quaternion ℝ) := by
    rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  rw [hu2, hu, dirVal, Algebra.smul_mul_assoc, Quaternion.re_smul, smul_eq_mul,
    div_eq_mul_inv, mul_comm]

/-- `√(1 + ‖x/‖x‖²‖²) = √(1 + ‖x‖²)/‖x‖` for `x ≠ 0`. -/
lemma sqrt_one_add_invBase_sq (x : EuclideanSpace ℝ (Fin 4)) (hx : x ≠ 0) :
    Real.sqrt (1 + ‖invBase x‖ ^ 2) = Real.sqrt (1 + ‖x‖ ^ 2) / ‖x‖ := by
  have hxn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  rw [norm_invBase]
  have hsq : (1 + ‖x‖ ^ 2) * (‖x‖⁻¹) ^ 2 = 1 + (‖x‖⁻¹) ^ 2 := by
    rw [add_mul, one_mul, inv_pow, mul_inv_cancel₀ (pow_ne_zero 2 hxn)]
    ring
  rw [← hsq, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity : (0 : ℝ) ≤ ‖x‖⁻¹),
    div_eq_mul_inv]

/-- The two chart expressions of the Morse function on `Mk (-2)` agree on the overlap of the two
charts. -/
theorem morse_glue (p : MSpace) (hp : p.1 ≠ 0) :
    morseChart1 p = morseChart2 (clutchMap (-2) p) := by
  simp only [morseChart1, morseChart2, clutchMap, neg_neg]
  rw [re_clutch_two p.1 hp p.2, sqrt_one_add_invBase_sq p.1 hp,
    div_div_div_cancel_right₀ (norm_ne_zero_iff.mpr hp) _ _]

end

end Work.Milnor

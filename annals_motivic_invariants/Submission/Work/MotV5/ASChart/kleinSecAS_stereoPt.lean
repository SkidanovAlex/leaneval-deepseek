import Mathlib
import Submission.Work.MotAS.ASLink
import Submission.Work.MotV5.ASChart.Stereo
import Submission.Work.Reflect.PolyId

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The twisted secant quintic at the stereographic point

The AS stereographic point is the constant vector `stereoPt w = 288 • e₀` (`MotAS.stereoPt_eq`),
so `w` drops out of the evaluation and the statement reduces to a characteristic-`5` polynomial
identity in `(a,b,g)`:

* the secant quintic `kleinSecAS a b g` is homogeneous of degree `5` in the coordinates, and at
  `288 • e₀` it evaluates (in *any* commutative ring, by an integer identity) to
  `-288⁵ · (a¹⁰ − a⁵b⁵ − b¹⁰)`;
* in a ring with `5 = 0`, `288⁵ ≡ 3` and `−3 ≡ 2`, while the Frobenius is additive:
  `(a² − ab − b²)⁵ = a¹⁰ − a⁵b⁵ − b¹⁰`.

Hence `kleinSecAS a b g (stereoPt w) = 2 (a² − ab − b²)⁵`, which is the non-vanishing input
`S^AS(stereoPt) ≠ 0` of the AS link (under `a² − ab − b² ≠ 0`).

The evaluation is a large certificate: unfolding `kleinSecAS` needs very generous
`maxRecDepth`/`maxHeartbeats` (as in `Stereo.lean`).
-/

set_option maxRecDepth 4000000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Work.MotV5.ASChart

/-- In a commutative ring with `5 = 0`, the fifth-power map is additive (Frobenius). -/
theorem pow_add_five {R : Type*} [CommRing R] (h5 : (5 : R) = 0) (x y : R) :
    (x + y) ^ 5 = x ^ 5 + y ^ 5 := by
  linear_combination (norm := first | refl_ring1 | ring1) (x ^ 4 * y + 2 * x ^ 3 * y ^ 2 + 2 * x ^ 2 * y ^ 3 + x * y ^ 4) * h5

/-- **The twisted secant quintic at the stereographic point:**
`s^AS(stereoPt w) = 2 (a² − ab − b²)⁵`. -/
theorem kleinSecAS_stereoPt {R : Type*} [CommRing R] (a b g w : R) (h5 : (5 : R) = 0)
    (hw : w ^ 5 = w + g) :
    Work.MotAS.kleinSecAS a b g (Work.MotAS.stereoPt w)
      = 2 * (a ^ 2 - a * b - b ^ 2) ^ 5 := by
  rw [Work.MotAS.stereoPt_eq (R := R) w]
  -- The evaluation at the constant vector `288 • e₀` is an integer polynomial identity.
  have hkey : Work.MotAS.kleinSecAS a b g (fun i : Fin 5 => if i = 0 then (288 : R) else 0)
      = -1981355655168 * (a ^ 10 - a ^ 5 * b ^ 5 - b ^ 10) := by
    simp only [Work.MotAS.kleinSecAS]
    norm_num
    first | refl_ring1 | ring
  rw [hkey]
  -- `(a² − ab − b²)⁵ = a¹⁰ − a⁵b⁵ − b¹⁰` in characteristic `5`.
  have hpow : (a ^ 2 - a * b - b ^ 2) ^ 5 = a ^ 10 - a ^ 5 * b ^ 5 - b ^ 10 := by
    have h1 : a ^ 2 - a * b - b ^ 2 = a ^ 2 + (-(a * b) + -(b ^ 2)) := by ring
    rw [h1, pow_add_five h5 (a ^ 2) (-(a * b) + -(b ^ 2)),
      pow_add_five h5 (-(a * b)) (-(b ^ 2))]
    first | refl_ring1 | ring
  rw [hpow]
  -- `−19981355655168 = −288⁵ = 2` in characteristic `5`.
  have hconst : (-1981355655168 : R) = 2 := by
    linear_combination (norm := first | refl_ring1 | ring1) ((-396271131034 : R)) * h5
  rw [hconst]

end Work.MotV5.ASChart

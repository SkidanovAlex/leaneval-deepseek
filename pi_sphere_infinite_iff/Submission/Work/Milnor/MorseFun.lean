import Mathlib
import Submission.Work.Milnor.Clutch

/-!
# The two-critical-point Morse function on `Mk (-2)`

Milnor's exotic sphere `M_1` is, in this workspace, `Mk (-2)`: the quotient of two copies of
`ℝ⁴ × S³` glued along `{x ≠ 0}` by `(x, y) ↦ (x/‖x‖², û² y û⁻¹)`, `û = x/‖x‖`
(the twisting parameter `k = -2` is the one for which the clutching function has Euler number
`1`, i.e. the total space is a homotopy `7`-sphere).

This file sets up the explicit smooth function `F` on `Mk (-2)` which has exactly two
nondegenerate critical points (of indices `0` and `7`), so that Reeb's theorem
(`Work.Morse.reeb`) shows `Mk (-2) ≃ₜ S⁷`.

Its expressions in the two charts are

* chart 1: `F₁(x, y) = ⟨q, y⟩ / √(1 + ‖x‖²)`  with `q = x` viewed as a quaternion, and where
  `⟨a, b⟩ = Re (a * b)` is the real inner product of quaternions;
* chart 2: `F₂(x', y') = Re(y') / √(1 + ‖x'‖²)`.

The function is well defined because the gluing sends `(x, y)` to `(x/‖x‖², û²yû⁻¹)` and
`Re(û²yû⁻¹) = Re(ûy)`, while `√(1 + ‖x/‖x‖²‖²) = √(1 + ‖x‖²)/‖x‖`.  Both expressions are
smooth (they are smooth functions of `(x, y)`), and the only critical points of `F` are the two
points `x' = 0`, `y' = ±1` of the second chart: `F` restricted to chart 1 has no critical points
at all, and on the pole `x' = 0` the gradient vanishes exactly when `y' = ±1`.
-/

open scoped Manifold ContDiff Topology
open TopologicalSpace Set

namespace Submission.Milnor

noncomputable section

/-- The real part of a product of quaternions is invariant under cyclic permutation. -/
theorem re_mul_comm (a b : Quaternion ℝ) : (a * b).re = (b * a).re := by
  rw [Quaternion.re_mul, Quaternion.re_mul]; ring

/-- The chart-1 expression of the Morse function on `Mk (-2)`:
`(x, y) ↦ Re(x * y) / √(1 + ‖x‖²)`. -/
def morseChart1 (p : MSpace) : ℝ :=
  ((Quaternion.linearIsometryEquivTuple.symm p.1 * (p.2 : Quaternion ℝ)).re) /
    Real.sqrt (1 + ‖p.1‖ ^ 2)

/-- The chart-2 expression of the Morse function on `Mk (-2)`:
`(x', y') ↦ Re(y') / √(1 + ‖x'‖²)`. -/
def morseChart2 (p : MSpace) : ℝ :=
  ((p.2 : Quaternion ℝ).re) / Real.sqrt (1 + ‖p.1‖ ^ 2)

end

end Submission.Milnor

import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Coercivity.Defs
import Submission.Work.Coercivity.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Coercivity

/-- The radial weight `w(z) = (1+z)²/z²` has derivative `-2(1+z)/z³` away from `z = 0`.
This is the `z`-derivative appearing in the identity `𝓛(g)·w = g·w + z∂_z(g·w)`. -/
theorem hasDerivAt_w {z : ℝ} (hz : z ≠ 0) :
    HasDerivAt Spaces.w (-2 * (1 + z) / z ^ 3) z := by
  have hnum : HasDerivAt (fun z : ℝ => (1 + z) ^ 2) (2 * (1 + z)) z := by
    convert ((hasDerivAt_id z).const_add 1).pow 2 using 1 <;> (first | rfl | simp)
  have hden : HasDerivAt (fun z : ℝ => z ^ 2) (2 * z) z := by
    convert (hasDerivAt_id z).pow 2 using 1 <;> (first | rfl | simp)
  have hne : z ^ 2 ≠ 0 := pow_ne_zero 2 hz
  have h := hnum.div hden hne
  convert h using 1
  · rfl
  · field_simp
    ring

/-- **Leibniz rule for `∂_z` against the radial weight `w`**: the `z`-derivative of
`f(z,θ)·w(z)` is `∂_z f · w - f · 2(1+z)/z³`. -/
theorem pz_mul_w {f : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : z ≠ 0)
    (hf : HasDerivAt (fun z' => f z' θ) (Spaces.pz f z θ) z) :
    Spaces.pz (fun z θ => f z θ * Spaces.w z) z θ
      = Spaces.pz f z θ * Spaces.w z - f z θ * (2 * (1 + z) / z ^ 3) := by
  have hw := hasDerivAt_w hz
  have hmul := hf.mul hw
  simp only [Spaces.pz]
  have h2 : deriv (fun z' => f z' θ * Spaces.w z') z
      = Spaces.pz f z θ * Spaces.w z + f z θ * (-2 * (1 + z) / z ^ 3) := by
    convert hmul.deriv using 1
  rw [h2, hf.deriv]
  ring

end Work.Coercivity

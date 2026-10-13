import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Coercivity.zAux
import Submission.Work.Coercivity.l_self_w_sq_eq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Coercivity

/-- Pointwise (radial) form of the self-adjointness of `𝓛` against the angular weight
`Weta z θ = w(z)² sin(2θ)^{-η}`: for `g` smooth on a neighbourhood of the closed quadrant
and `z > 0`, `θ ∈ Iθ`,

  `𝓛g · g · Weta(z,θ) = ½ g² · Weta(z,θ) + ½ ∂_z(z (g w)²) · sin(2θ)^{-η}`.

This is the identity `𝓛g·w = g·w + z∂_z(g·w)` (`L_mul_w_deriv`) multiplied by `g·w` and
the angular factor `sin(2θ)^{-η}`, together with the Leibniz rule applied to
`z ↦ z (g(z,θ) w(z))²`.  Only smoothness of the `z`-slice (from `Spaces.SmoothNbhd`) is
needed — no boundary/decay hypotheses. -/
theorem L_mul_self_Weta (g : ℝ → ℝ → ℝ) (hg : Spaces.SmoothNbhd g) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Spaces.Iθ) :
    L g z θ * g z θ * Weta z θ
      = (1 / 2) * (g z θ) ^ 2 * Weta z θ
        + (1 / 2) * deriv (fun z' => z' * (g z' θ * Spaces.w z') ^ 2) z
            * (Real.sin (2 * θ)) ^ (-Spaces.eta) := by
  have hzmem : z ∈ Set.Ioi (-1) := by simp only [Set.mem_Ioi]; linarith
  -- the `θ`-slice of `g` is differentiable at `z`, with derivative `pz g z θ`
  have hf : HasDerivAt (fun z' => g z' θ) (Spaces.pz g z θ) z :=
    Spaces.hardyZ_hasDerivAt_slice g hg hθ hzmem
  -- `𝓛g · w = g·w + z ∂_z(g·w)`
  have hLw : L g z θ * Spaces.w z
      = g z θ * Spaces.w z + z * Spaces.pz (fun z θ => g z θ * Spaces.w z) z θ :=
    L_mul_w_deriv hz hf
  have hgw : DifferentiableAt ℝ (fun z' => g z' θ * Spaces.w z') z :=
    (hf.mul (hasDerivAt_w (ne_of_gt hz))).differentiableAt
  have hsq : DifferentiableAt ℝ (fun z' => (g z' θ * Spaces.w z') ^ 2) z := hgw.pow 2
  -- Leibniz rule for `z ↦ z (g w)²`
  have hD1 : deriv (fun z' => z' * (g z' θ * Spaces.w z') ^ 2) z
      = (g z θ * Spaces.w z) ^ 2 + z * deriv (fun z' => (g z' θ * Spaces.w z') ^ 2) z := by
    have h : HasDerivAt (fun z' => z' * (g z' θ * Spaces.w z') ^ 2)
        (1 * (g z θ * Spaces.w z) ^ 2
          + z * deriv (fun z' => (g z' θ * Spaces.w z') ^ 2) z) z :=
      (hasDerivAt_id z).mul hsq.hasDerivAt
    rw [h.deriv]; ring
  -- chain rule for the square
  have hD2 : deriv (fun z' => (g z' θ * Spaces.w z') ^ 2) z
      = 2 * (g z θ * Spaces.w z) * Spaces.pz (fun z θ => g z θ * Spaces.w z) z θ := by
    have h1 := (hgw.hasDerivAt).pow 2
    have h2 : deriv (fun z' => (g z' θ * Spaces.w z') ^ 2) z
        = 2 * (g z θ * Spaces.w z) ^ (2 - 1) * deriv (fun z' => g z' θ * Spaces.w z') z :=
      h1.deriv
    rw [h2]
    simp only [Nat.reduceSub, pow_one, Spaces.pz]
  rw [Weta, hD1, hD2]
  -- assemble
  have harith : L g z θ * g z θ * (Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta))
      = ((g z θ * Spaces.w z + z * Spaces.pz (fun z θ => g z θ * Spaces.w z) z θ)
          * (g z θ * Spaces.w z)) * (Real.sin (2 * θ)) ^ (-Spaces.eta) := by
    rw [← hLw]; ring
  rw [harith]
  ring

end Work.Coercivity

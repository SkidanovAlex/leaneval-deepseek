import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Coercivity.Defs
import Submission.Work.Coercivity.Basic
import Submission.Work.Coercivity.pz_mul_w
import Submission.Work.Coercivity.L_mul_w_deriv
import Submission.Work.Spaces.CurrySmooth
import Submission.Work.Spaces.HardyZ

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Coercivity

theorem l_self_w_sq_eq {u : ℝ → ℝ → ℝ} (hu : Work.Coercivity.IBP u) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Coercivity.L u z θ * u z θ * Work.Spaces.w z ^ 2
      = (u z θ * Work.Spaces.w z) ^ 2
        + (1 / 2) * (z * deriv (fun z' => (u z' θ * Work.Spaces.w z') ^ 2) z) := by
  -- Differentiability of the `z`-slice of `u` at the interior point `(z,θ)`.
  have hU : (z, θ) ∈ Work.Spaces.U :=
    Work.Spaces.mem_U_of_dom (le_of_lt hz) hθ
  have hd : DifferentiableAt ℝ (Function.uncurry u) (z, θ) :=
    (hu.smooth.differentiableOn (n := ⊤) (by simp)).differentiableAt
      (Work.Spaces.isOpen_U.mem_nhds hU)
  have hslice : DifferentiableAt ℝ (fun z' => u z' θ) z :=
    Work.Spaces.differentiableAt_curry_left hd
  have hf : HasDerivAt (fun z' => u z' θ) (Work.Spaces.pz u z θ) z := hslice.hasDerivAt
  -- `L u · w = u · w + z ∂_z (u · w)`.
  have hLw : Work.Coercivity.L u z θ * Work.Spaces.w z
      = u z θ * Work.Spaces.w z
        + z * Work.Spaces.pz (fun z θ => u z θ * Work.Spaces.w z) z θ :=
    Work.Coercivity.L_mul_w_deriv hz hf
  -- Differentiability of `z' ↦ u z' θ · w z'`.
  have hgw : DifferentiableAt ℝ (fun z' => u z' θ * Work.Spaces.w z') z :=
    (hf.mul (Work.Coercivity.hasDerivAt_w (ne_of_gt hz))).differentiableAt
  -- `∂_z (u w)² = 2 (u w) ∂_z(u w)`.
  have hgsq : deriv (fun z' => (u z' θ * Work.Spaces.w z') ^ 2) z
      = 2 * (u z θ * Work.Spaces.w z)
          * Work.Spaces.pz (fun z θ => u z θ * Work.Spaces.w z) z θ := by
    have h1 := (hgw.hasDerivAt).pow 2
    have h2 : deriv (fun z' => (u z' θ * Work.Spaces.w z') ^ 2) z
        = 2 * (u z θ * Work.Spaces.w z) ^ (2 - 1)
            * deriv (fun z' => u z' θ * Work.Spaces.w z') z := h1.deriv
    rw [h2]
    simp only [Nat.reduceSub, pow_one]
    rfl
  -- Assemble.
  have hkey : Work.Coercivity.L u z θ * u z θ * Work.Spaces.w z ^ 2
      = (Work.Coercivity.L u z θ * Work.Spaces.w z) * (u z θ * Work.Spaces.w z) := by
    ring
  rw [hkey, hLw, hgsq]
  ring

end Work.Coercivity

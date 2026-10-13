import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.CurrySmooth
import Submission.Work.Spaces.SmoothCompact_Aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5Aux.slotIdents

theorem pz_pz_eq {u : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : ContDiffAt ℝ 2 (Function.uncurry u) (z, θ)) (hz : z ≠ 0) :
    Work.Spaces.pz (Work.Spaces.pz u) z θ
      = (Work.Spaces.DzIter 2 u z θ - Work.Spaces.DzIter 1 u z θ) / z ^ 2 := by
  -- The `z`-slice of `u` at `θ` and its plain derivatives.
  have hφ : ContDiffAt ℝ 2 (fun t : ℝ => u t θ) z := by
    have hlin : ContDiffAt ℝ 2 (fun z' : ℝ => (z', θ)) z := by fun_prop
    exact h.comp z hlin
  -- A `C²` function has a differentiable first derivative.
  have hd : DifferentiableAt ℝ (deriv (fun t : ℝ => u t θ)) z := by
    have h1 : DifferentiableWithinAt ℝ
        (iteratedDerivWithin 1 (fun t : ℝ => u t θ) Set.univ) Set.univ z :=
      hφ.differentiableWithinAt_iteratedDerivWithin (by norm_num) (by simp)
    simpa only [iteratedDerivWithin_univ, iteratedDeriv_one, differentiableWithinAt_univ] using h1
  -- Leibniz for `∂_z (z ∂_z u)`.
  have hderiv2 : deriv (fun t : ℝ => t * deriv (fun s : ℝ => u s θ) t) z
      = deriv (fun s : ℝ => u s θ) z
        + z * deriv (deriv (fun s : ℝ => u s θ)) z := by
    rw [deriv_fun_mul (c := fun y : ℝ => y)
      (d := fun t : ℝ => deriv (fun s : ℝ => u s θ) t) (x := z) (by fun_prop) hd]
    simp
  -- `D_z` is `z ∂_z`, by definition.
  have hD1 : Work.Spaces.DzIter 1 u z θ = z * deriv (fun s : ℝ => u s θ) z := rfl
  have hD2 : Work.Spaces.DzIter 2 u z θ
      = z * deriv (fun t : ℝ => t * deriv (fun s : ℝ => u s θ) t) z := rfl
  have hpz2 : Work.Spaces.pz (Work.Spaces.pz u) z θ
      = deriv (deriv (fun s : ℝ => u s θ)) z := rfl
  -- `D_z²u - D_zu = z² ∂_zz u`.
  have hmain : Work.Spaces.DzIter 2 u z θ - Work.Spaces.DzIter 1 u z θ
      = z ^ 2 * Work.Spaces.pz (Work.Spaces.pz u) z θ := by
    rw [hD1, hD2, hderiv2, hpz2]; ring
  rw [hmain, mul_div_cancel_left₀ _ (pow_ne_zero 2 hz)]

end Work.FTS.StrongEps.E5Aux.slotIdents

import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

theorem hasDerivAt_inv_mul_comp2 {F : ℝ → ℝ} {lam : ℝ → ℝ} {c t : ℝ}
    (hlam : HasDerivAt lam (deriv lam t) t)
    (hlam2 : HasDerivAt (deriv lam) (deriv (deriv lam) t) t)
    (hne : lam t ≠ 0)
    (hF : HasDerivAt F (deriv F (c / lam t)) (c / lam t))
    (hF2 : HasDerivAt (deriv F) (deriv (deriv F) (c / lam t)) (c / lam t)) :
    HasDerivAt
      (fun s => -(deriv lam s * (F (c / lam s) + c / lam s * deriv F (c / lam s)) / (lam s) ^ 2))
      (-(deriv (deriv lam) t * (F (c / lam t) + c / lam t * deriv F (c / lam t)) / (lam t) ^ 2
        + deriv lam t * (-(deriv lam t / lam t)
            * (c / lam t * (2 * deriv F (c / lam t) + c / lam t * deriv (deriv F) (c / lam t))))
            / (lam t) ^ 2
        - 2 * deriv lam t ^ 2 * (F (c / lam t) + c / lam t * deriv F (c / lam t))
            / (lam t) ^ 3)) t := by
  have hne2 : lam t ^ 2 ≠ 0 := pow_ne_zero 2 hne
  -- Derivative of the shift `s ↦ c / lam s`.
  have hu : HasDerivAt (fun s => c / lam s) (-(c * deriv lam t) / (lam t) ^ 2) t := by
    have h : HasDerivAt (fun s => c / lam s) ((0 * lam t - c * deriv lam t) / (lam t) ^ 2) t :=
      (hasDerivAt_const t c).div hlam hne
    convert h using 1
    ring
  -- Derivative of the composition with `F` and with `deriv F`.
  have h1 : HasDerivAt (fun s => F (c / lam s))
      (deriv F (c / lam t) * (-(c * deriv lam t) / (lam t) ^ 2)) t := by
    simpa only [Function.comp_def] using hF.comp t hu
  have h2 : HasDerivAt (fun s => deriv F (c / lam s))
      (deriv (deriv F) (c / lam t) * (-(c * deriv lam t) / (lam t) ^ 2)) t := by
    simpa only [Function.comp_def] using hF2.comp t hu
  -- Assemble the derivative of the whole expression by the combinators.
  have h3 := hu.mul h2
  have h4 := h1.add h3
  have h5 := hlam2.mul h4
  have h6 : HasDerivAt (fun s => (lam s) ^ 2) (2 * lam t * deriv lam t) t := by
    have h := hlam.pow 2
    convert h using 1
    ring
  have h7 := h5.div h6 hne2
  have h8 := h7.neg
  -- Identify the combinator-produced value with the stated one by pure algebra.
  convert h8 using 1
  simp only [Pi.mul_apply, Pi.add_apply]
  field_simp
  ring

end Work.ConstructionInstance

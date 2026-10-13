import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

/-- **Chain rule for the self-similar rescaling.**  If `lam` and `F` are differentiable at `t` and
at `c/lam t` respectively, then `s ↦ (lam s)⁻¹ * F (c / lam s)` is differentiable at `t` with
derivative `-(l·(F(c/λ) + (c/λ)·d)/λ²)` where `λ = lam t`, `l = deriv lam t` and `d = deriv F (c/λ)`.

(The algebraic form of the value is chosen so that multiplying by `(lam t)^2` gives exactly
`-(l * (F (c/lam t) + (c/lam t) * d))`: the chain rule with `s ↦ c/lam s` has derivative
`-(c/λ²)·l`, so the product with the `λ⁻¹` factor produces the combination
`F + (c/λ)∂_zF` with the overall `λ⁻²` weight.) -/
theorem hasDerivAt_inv_mul_comp {F : ℝ → ℝ} {lam : ℝ → ℝ} {c d l : ℝ} {t : ℝ}
    (hlam : HasDerivAt lam l t) (hlt : lam t ≠ 0) (hF : HasDerivAt F d (c / lam t)) :
    HasDerivAt (fun s => (lam s)⁻¹ * F (c / lam s))
      (-(l * (F (c / lam t) + (c / lam t) * d) / (lam t) ^ 2)) t := by
  -- derivative of `s ↦ (lam s)⁻¹`
  have h1 : HasDerivAt (fun s => (lam s)⁻¹) (-l / (lam t) ^ 2) t := hlam.inv hlt
  -- derivative of the inner map `s ↦ c / lam s`, namely `-(c·l)/λ²`
  have hdiv : HasDerivAt (fun s => c / lam s) (-(c * l) / (lam t) ^ 2) t := by
    have h := (hasDerivAt_const (x := t) c).div hlam hlt
    convert h using 1
    ring
  -- chain rule for the outer map `F`
  have h3 : HasDerivAt (fun s => F (c / lam s)) (d * (-(c * l) / (lam t) ^ 2)) t := by
    have h := hF.comp t hdiv
    convert h using 1
    ext s; rfl
  -- product rule
  have h4 := h1.mul h3
  convert h4 using 1
  field_simp
  ring

end Work.ConstructionInstance

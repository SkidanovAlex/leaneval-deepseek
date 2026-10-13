import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Cyl.pdZ_comp_polar

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Cyl

/-- The axial derivative of `z' ↦ ρ(r,z')^α / c`, obtained from
`hasDerivAt_rhoP_rpow_polar` (which gives the derivative `α ρ^{α-1} · (z/ρ)` of
`z' ↦ ρ(r,z')^α`) after dividing by the constant `c` and rewriting
`ρ^{α-1} · (z/ρ) = ρ^α · (z/ρ^2)`. -/
theorem hasDerivAt_rhoP_rpow_div_snd (r α z c : ℝ) (hr : 0 < r) :
    HasDerivAt (fun z' : ℝ => Work.Cyl.rhoP r z' ^ α / c)
      (α * (Work.Cyl.rhoP r z ^ α / c) * (z / Work.Cyl.rhoP r z ^ 2)) z := by
  have h := (Work.Cyl.hasDerivAt_rhoP_rpow_polar r α z hr).div_const c
  have hne : rhoP r z ≠ 0 := rhoP_ne_zero hr z
  convert h using 1
  rw [Real.rpow_sub_one hne, div_eq_mul_inv, div_eq_mul_inv]
  field_simp

end Work.Cyl

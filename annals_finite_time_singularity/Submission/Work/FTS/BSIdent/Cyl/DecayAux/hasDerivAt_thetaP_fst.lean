import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Cyl.Coords
import Submission.Work.Cyl.Frame

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSIdent.Cyl.DecayAux

theorem hasDerivAt_thetaP_fst (r z : ℝ) (hr : 0 < r) :
    HasDerivAt (fun r' : ℝ => Work.Cyl.thetaP r' z) (-z / Work.Cyl.rhoP r z ^ 2) r := by
  -- `θ = arctan (z/r)`, so `∂_r θ = (1 + (z/r)²)⁻¹ · (-z/r²) = -z/(r²+z²) = -z/ρ²`.
  have hdiv : HasDerivAt (fun r' : ℝ => z / r') (-z / r ^ 2) r := by
    have h := (hasDerivAt_const (x := r) z).div (hasDerivAt_id r) (ne_of_gt hr)
    have hfun : ((fun _ : ℝ => z) / id : ℝ → ℝ) = fun r' => z / r' := by
      funext x; simp [Pi.div_apply]
    rw [hfun] at h
    convert h using 1
    simp
  have h := hdiv.arctan
  have hfun : (fun r' : ℝ => Work.Cyl.thetaP r' z) = fun r' => Real.arctan (z / r') := by
    funext r'; rw [Work.Cyl.thetaP]
  rw [hfun]
  convert h using 1
  rw [Work.Cyl.rhoP]
  field_simp
  rw [Real.sq_sqrt (by positivity)]

end Work.FTS.BSIdent.Cyl.DecayAux

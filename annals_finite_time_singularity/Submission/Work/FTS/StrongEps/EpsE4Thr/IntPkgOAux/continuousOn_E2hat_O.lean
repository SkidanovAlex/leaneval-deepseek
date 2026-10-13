import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.CoercivityFix.Coer1.IntFacts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.IntPkgOAux

open MeasureTheory Set Filter

/-- The rational factor `z ↦ z/(1+z)²` is continuous on the open quadrant. -/
theorem continuousOn_zdiv_sq_Qd :
    ContinuousOn (fun p : ℝ × ℝ => p.1 / (1 + p.1) ^ 2) Work.FTS.CoercivityFix.Coer1.Qd :=
  continuousOn_fst.div ((continuousOn_const.add continuousOn_fst).pow 2)
    (fun p hp => pow_ne_zero 2 (by
      have h1 : (0 : ℝ) < p.1 := hp.1
      linarith))

/-- The defect `Ê₂f = (2zf + 3z·D_θf)/(1+z)²` is continuous on the open quadrant, for `f`
smooth there. -/
theorem continuousOn_E2hat_Qd {f : Work.FTS.Galerkin.Fn} (hs : Work.FTS.EllipticEst.SmoothOpen f) :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.CoercivityFix.E2hat f p.1 p.2)
      Work.FTS.CoercivityFix.Coer1.Qd := by
  have hfun : (fun p : ℝ × ℝ => Work.FTS.CoercivityFix.E2hat f p.1 p.2)
      = fun p : ℝ × ℝ => (p.1 / (1 + p.1) ^ 2)
          * (2 * f p.1 p.2 + 3 * Work.Spaces.Dth f p.1 p.2) := by
    funext p
    obtain ⟨z, θ⟩ := p
    rw [Work.FTS.CoercivityFix.E2hat_eq]
    ring
  rw [hfun]
  exact continuousOn_zdiv_sq_Qd.mul
    ((hs.continuousOn.const_mul 2).add (hs.Dth.continuousOn.const_mul 3))

theorem continuousOn_E2hat_O {f : Work.FTS.Galerkin.Fn} (hs : Work.FTS.EllipticEst.SmoothOpen f)
    {ρ : Work.FTS.Galerkin.Fn}
    (hρc : ContinuousOn (fun p : ℝ × ℝ => ρ p.1 p.2) Work.FTS.CoercivityFix.Coer1.Qd) :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.CoercivityFix.E2hat f p.1 p.2
      * Work.Spaces.Dz f p.1 p.2 * ρ p.1 p.2) Work.FTS.CoercivityFix.Coer1.Qd := by
  exact ((continuousOn_E2hat_Qd hs).mul hs.Dz.continuousOn).mul hρc

end Work.FTS.StrongEps.EpsE4Thr.IntPkgOAux

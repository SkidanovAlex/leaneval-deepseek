import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Series.Deleg

theorem hasDerivAt_pairGreen {K sn sp : ℝ} {A B F1 F2 : ℝ → ℝ} {z : ℝ}
    (hA : HasDerivAt A (F1 z) z) (hB : HasDerivAt B (-(F2 z)) z) (hz : z ≠ 0) :
    HasDerivAt (fun y => K * ((sn * y ^ (sn - 1)) * A y + (sp * y ^ (sp - 1)) * B y))
      (K * (((sn * ((sn - 1) * z ^ (sn - 2))) * A z + (sn * z ^ (sn - 1)) * F1 z)
          + ((sp * ((sp - 1) * z ^ (sp - 2))) * B z + (sp * z ^ (sp - 1)) * (-(F2 z))))) z := by
  -- product rule: differentiate `y ↦ K * ((sn * y^(sn-1)) * A y + (sp * y^(sp-1)) * B y)`
  have hp1 : HasDerivAt (fun t : ℝ => sn * t ^ (sn - 1))
      (sn * ((sn - 1) * z ^ (sn - 2))) z := by
    have h := (Real.hasDerivAt_rpow_const (x := z) (p := sn - 1) (Or.inl hz)).const_mul sn
    rwa [show (sn - 1) - 1 = sn - 2 from by ring] at h
  have hp2 : HasDerivAt (fun t : ℝ => sp * t ^ (sp - 1))
      (sp * ((sp - 1) * z ^ (sp - 2))) z := by
    have h := (Real.hasDerivAt_rpow_const (x := z) (p := sp - 1) (Or.inl hz)).const_mul sp
    rwa [show (sp - 1) - 1 = sp - 2 from by ring] at h
  exact ((hp1.mul hA).add (hp2.mul hB)).const_mul K

end Work.FTS.PhiStar.Series.Deleg

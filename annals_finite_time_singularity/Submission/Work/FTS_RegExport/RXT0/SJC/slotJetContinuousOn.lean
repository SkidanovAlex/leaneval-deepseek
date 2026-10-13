import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS_RegExport.RXT.Slots.v2_SlotJetsTendsto
import Submission.Work.FTS_RegExport.RXT.SysAux.PieceCalc
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.FinCalc
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT0.SJC

open scoped Real Topology
open Set Filter
set_option autoImplicit false
variable {α : ℝ}

theorem slotJetContinuousOn {X : ℝ → ℝ → ℝ} {α : ℝ}
    (hX : ContDiffOn ℝ 3 (Function.uncurry X) Work.FTS.EllipticEst.Q0)
    (j i : ℕ) (hji : j + i ≤ 2) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed j i
        (fun z θ => Work.Construction.Vop X z θ) p.1 p.2) Work.FTS.EllipticEst.Q0 ∧
      ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed j i
        (fun z θ => Work.Construction.Rop α X z θ) p.1 p.2) Work.FTS.EllipticEst.Q0 ∧
      ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed j i
        (fun z θ => Work.Construction.Uop α X z θ / Real.sin (2 * θ)) p.1 p.2)
        Work.FTS.EllipticEst.Q0 := by
  -- `j + i ≤ 2` in the order matching `continuousOn_mixed_of_contDiffOn`
  have hji' : i + j ≤ 2 := by omega
  -- the three slot functions are `C²` on the open quadrant `Q0`: `Q0` is open, so the
  -- plain derivative lowers the order by one, `tan` and `1/cos`, `1/sin(2·)` are smooth
  -- there, and the coefficients `Uop, Vop, Rop` are *linear* in `Ψ, ∂_zΨ, ∂_θΨ`.
  have hV := Work.FTS_RegExport.RXT.contDiffOn_uncurry_Vop hX
  have hR := Work.FTS_RegExport.RXT.contDiffOn_uncurry_Rop (α := α) hX
  have hU := Work.FTS_RegExport.RXT.contDiffOn_uncurry_div_sin_two
    (Work.FTS_RegExport.RXT.contDiffOn_uncurry_Uop (α := α) hX)
  -- a mixed slot `D_z^jD_θ^i` of a `C²` function on the open quadrant is continuous there
  exact ⟨Work.FTS.StrongEps.continuousOn_mixed_of_contDiffOn hV hji',
    Work.FTS.StrongEps.continuousOn_mixed_of_contDiffOn hR hji',
    Work.FTS.StrongEps.continuousOn_mixed_of_contDiffOn hU hji'⟩

end Work.FTS_RegExport.RXT0.SJC

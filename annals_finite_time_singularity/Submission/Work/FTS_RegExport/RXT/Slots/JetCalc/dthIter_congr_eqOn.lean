import Mathlib.Analysis.Complex.Trigonometric
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.DzDthIterCommOn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT.Slots.JetCalc

/-- `D_θ` is a local operator: if `F` and `G` agree on the open quadrant `Q0`, then so do all
their iterated `D_θ`-derivatives.  The induction step needs the θ-slice congruence of `pth` on
an open set (`Work.Spaces.pth_congr_of_isOpen`), which applies because `Q0` is open (so `F` and
`G` agree in a neighbourhood of every point of `Q0` in the `θ`-direction). -/
theorem dthIter_congr_eqOn {F G : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry F) (Function.uncurry G) Work.FTS.EllipticEst.Q0) (i : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DthIter i F))
      (Function.uncurry (Work.Spaces.DthIter i G)) Work.FTS.EllipticEst.Q0 := by
  induction i with
  | zero => simpa using h
  | succ i ih =>
      rintro ⟨z, θ⟩ hz
      show Work.Spaces.Dth (Work.Spaces.DthIter i F) z θ
        = Work.Spaces.Dth (Work.Spaces.DthIter i G) z θ
      simp only [Work.Spaces.Dth]
      rw [Work.Spaces.pth_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 ih hz]

end Work.FTS_RegExport.RXT.Slots.JetCalc

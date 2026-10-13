import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.DzDthIterCommOn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT.Slots.JetCalc

/-- The operator `D_z^j` is local: two functions which agree on an open set `V` have the
same iterated `D_z`-jets on `V`.

`D_z f = z ∂_z f` and `∂_z` acts on the `z`-slice `z' ↦ f z' θ`, so this is the
`z`-variable counterpart of `pth_congr_of_isOpen` (`Work.Spaces.pz_congr_of_isOpen`),
iterated; the openness of `V` is used to make the agreeing set a *neighbourhood* of the
`z`-coordinate. -/
theorem dzIter_congr_of_isOpen {F G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : Set.EqOn (Function.uncurry F) (Function.uncurry G) V) (j : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DzIter j F))
      (Function.uncurry (Work.Spaces.DzIter j G)) V := by
  induction j with
  | zero => exact h
  | succ j ih =>
    intro p hp
    simp only [Function.uncurry, Work.Spaces.DzIter_succ, Work.Spaces.Dz]
    rw [Work.Spaces.pz_congr_of_isOpen hV ih hp]

theorem dzIter_congr_eqOn {F G : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry F) (Function.uncurry G) Work.FTS.EllipticEst.Q0) (j : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DzIter j F))
      (Function.uncurry (Work.Spaces.DzIter j G)) Work.FTS.EllipticEst.Q0 :=
  dzIter_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 h j

end Work.FTS_RegExport.RXT.Slots.JetCalc

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.LWP.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

theorem bkm_congr_of_eqOn_Ico
    {u v : Work.LWP.R3 → ℝ → Work.LWP.R3} {T : ℝ}
    (h : ∀ x t, t ∈ Set.Ico 0 T → u x t = v x t) :
    ∀ t ∈ Set.Ico 0 T, Work.LWP.bkm u t = Work.LWP.bkm v t := by
  intro t ht
  simp only [Work.LWP.bkm]
  apply intervalIntegral.integral_congr
  intro s hs
  have hsT : s ∈ Set.Ico 0 T := by
    rw [Set.uIcc_of_le ht.1] at hs
    exact ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩
  have hfun : (u · s) = (v · s) := funext (fun x => h x s hsT)
  show (⨆ x, ‖FiniteTimeSingularity.vorticity (u · s) x‖)
      = ⨆ x, ‖FiniteTimeSingularity.vorticity (v · s) x‖
  rw [hfun]

end Work.ConstructionInstance

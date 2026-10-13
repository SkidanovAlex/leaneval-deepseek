/-
# The derivative of `q = potOn ω` at the boundary time

`hasFDerivWithinAt_potOn_uncurry_boundary`: at every boundary point `(y₀,0)` of the half open box
`bbox x₀ T = B(x₀,1) × [0,T/2)` the uncurried potential `(x,t) ↦ potOn ω x t` has the within
derivative `potFDerivExt ω T (y₀,0)`.

This is the concrete instance of the abstract `ε`-estimate `hasFDerivWithinAt_of_boundary_data`
(`BoundaryTime/BdryAbstract.lean`), with the spatial partial derivative `potGradExt ω T` and the
time partial derivative `potTDerivExt ω T`.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Submission.Work.FTS.PressureOn.Defs
import Submission.Work.FTS.PressureOn.EulerAssembly
import Submission.Work.FTS.PressureOn.Connect.Deriv
import Submission.Work.FTS.PressureOn.Connect.ctu_aux.Basic
import Submission.Work.FTS.PressureOn.Connect.ctu_aux.Grad
import Submission.Work.FTS.PressureOn.Connect.ctu_aux.PotOnTime
import Submission.Work.FTS.PressureOn.Connect.BoundaryTime
import Submission.Work.FTS.PressureOn.Connect.BoundaryTime.ExtData
import Submission.Work.FTS.PressureOn.Connect.BoundaryTime.ExtDeriv
import Submission.Work.FTS.PressureOn.Connect.BoundaryTime.BdryAbstract

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set MeasureTheory Filter
open Work.FTS.Physical (physVel)
open scoped Topology NNReal ENNReal

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FTS.PressureOn.Connect

noncomputable section

variable {α : NNReal} {ω : R3 → ℝ → R3} {T : ℝ}

theorem hasFDerivWithinAt_potOn_uncurry_boundary (hT : 0 < T)
    (hstrips : ∀ S ∈ Set.Ioo 0 T, IsContDiffHolderOn ℝ α
      (physVel ω).uncurry (Set.univ ×ˢ Set.Icc 0 S))
    (hcurl : ∀ t ∈ Set.Ico 0 T, ∀ x, vorticity (fun z => physVel ω z t) x = ω x t)
    (hsupp : ∀ S ∈ Set.Ioo 0 T, ∃ R, ∀ t ∈ Set.Icc 0 S, ∀ x, ω x t ≠ 0 → ‖x‖ ≤ R)
    (hcontDt : ContinuousOn (fun q : R3 × ℝ => timeDeriv ω q.1 q.2) (Set.univ ×ˢ Set.Ico 0 T))
    (hderiv : ∀ x, ∀ t ∈ Set.Ico 0 T,
      HasDerivWithinAt (ω x) (timeDeriv ω x t) (Set.Ici t) t)
    (hgq : ∀ t ∈ Set.Ioo 0 T, ∀ x, HasFDerivAt (potOn ω · t) (potGradCLM ω x t) x) :
    ∀ x₀ : R3, ∀ y₀ ∈ Metric.ball x₀ 1,
      HasFDerivWithinAt (fun p : R3 × ℝ => potOn ω p.1 p.2)
        (potFDerivExt ω T (y₀, 0)) (bbox x₀ T) (y₀, 0) := by
  have hT2T : T / 2 ≤ T := by linarith
  intro x₀ y₀ hy₀
  have hmain := hasFDerivWithinAt_of_boundary_data
    (F := fun p : R3 × ℝ => potOn ω p.1 p.2)
    (A := potGradExt ω T) (c := fun p : R3 × ℝ => potTDerivExt ω T p.1 p.2)
    hT hy₀
    (potOn_uncurry_continuousOn_strip (α := α) hT hstrips hcurl hsupp)
    (potGradExt_continuousOn_strip (α := α) hT hstrips hcurl)
    (potTDerivExt_continuousOn_strip (α := α) hT hstrips hcurl hsupp hcontDt hderiv)
    (fun σ hσ z => by
      have hpg : potGradExt ω T (z, σ) = timeDeriv (physVel ω) z σ
          - crossVec (physVel ω z σ) (ω z σ) := by
        simp only [potGradExt, if_neg (ne_of_gt hσ.1)]
      rw [hpg]
      simpa only [potGradCLM] using hgq σ ⟨hσ.1, lt_of_lt_of_le hσ.2 hT2T⟩ z)
    (fun σ hσ => by
      rw [potTDerivExt_eq_potTDeriv ω T y₀ hσ.1]
      exact hasDerivAt_potOn_time_aux hstrips hcurl hsupp hcontDt hderiv y₀
        ⟨hσ.1, lt_of_lt_of_le hσ.2 hT2T⟩)
  simpa only [bbox, potFDerivExt] using hmain

end

end Work.FTS.PressureOn.Connect

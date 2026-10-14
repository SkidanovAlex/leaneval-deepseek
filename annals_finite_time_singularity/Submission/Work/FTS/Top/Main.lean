import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.SolutionDelivery.Assembly
import Submission.Work.Spaces.bt_f_bound
import Submission.Work.Stability.CutFactorFderivZero
-- ===== merged: Submission.Work.FTS.LocData.HkMem_zfar_Fstar =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocData

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## The far part `zfar L F_*` is `C^∞` on the quadrant -/


/-! ## Integrability of the angular majorant times the radial weight -/


/-! ## The target -/


end Work.FTS.LocData
end
end
-- ===== merged: Submission.Work.FTS.Top.Main =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

set_option autoImplicit false

namespace Work.FTS.Top

/-- **The challenge statement from a blow-up at time `1`.**

The conclusion is the challenge's existential, verbatim: some `β > 0`, a divergence-free odd
`C^{1,β}` datum with `‖ω₀(x)‖ ≤ C/(‖x‖^β + 1)`, and a local solution `(p,u)` on `[0,1)`, odd at
every time, jointly `C^{1,β}` on every strip `ℝ³ × [0,T]` with `T < 1`, whose BKM integral diverges
at `1`. -/
theorem theorem_1_of_blowupAt {α : ℝ≥0} (hα : 0 < (α : ℝ)) (B : BlowupAt α 1) :
    ∃ β > 0, ∃ u₀ : R3 → R3, div u₀ = 0 ∧ IsOdd u₀ ∧ IsContDiffHolder ℝ β u₀ ∧
      (∃ C : ℝ, 0 < C ∧ ∀ x : R3, ‖vorticity u₀ x‖ ≤ C / (‖x‖ ^ (β : ℝ) + 1)) ∧
        ∃ p : R3 → ℝ → ℝ, ∃ u : R3 → ℝ → R3,
            (∀ t ∈ Set.Ico 0 1, IsOdd (u · t)) ∧
            IsLocalEulerEquationSolution p u₀ 1 u ∧
              (∀ T ∈ Set.Ioo 0 1,
                IsContDiffHolderOn ℝ β u.uncurry (Set.univ ×ˢ Set.Icc 0 T)) ∧
                Filter.Tendsto (fun t => ∫ s in 0..t, ⨆ x, ‖vorticity (fun y => u y s) x‖)
                  (𝓝[<] 1) Filter.atTop := by
  have hα' : (0 : ℝ≥0) < α := NNReal.coe_pos.mp hα
  exact ⟨α, hα', (B.u · 0), B.div0, B.odd 0 ⟨le_rfl, B.hT⟩, B.cdh0, B.decay0,
    B.p, B.u, B.odd, B.sol, B.strip, B.bkm_divergence_one⟩


end Work.FTS.Top
end

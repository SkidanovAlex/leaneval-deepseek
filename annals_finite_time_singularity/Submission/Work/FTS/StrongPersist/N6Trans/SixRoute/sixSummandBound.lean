import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.N6Trans.L6Core
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.fluxFamSix
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.fluxFamSixTop
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.pureGamFamSix
import Submission.Work.FTS.StrongPersist.SP6.RadialSlot6
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.T2Sup.PairBnd
import Submission.Work.FTS.TransportS.T3SlotAux.Pointwise
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.Spaces.sq_mul_div_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.N6Trans.SixRoute

open MeasureTheory Set Filter
open scoped Real Topology

set_option maxHeartbeats 3200000
set_option autoImplicit false

set_option quotPrecheck false in
/-- The product of the two restricted Lebesgue measures, as in the statement. -/
local notation "IPM" => ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
  (MeasureTheory.volume.restrict Work.Spaces.Iθ))

noncomputable section

/-! ## Elementary bookkeeping -/



/-- Every leaf weight is nonnegative on the closed angular interval. -/
theorem leafW_nonneg {α : ℝ} {a : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hρ : Work.FTS.TransportS.IsLeafW α a ρ) {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ ρ z θ := by
  rcases hρ with h | h | ⟨_, h⟩
  · rw [h]
    exact Work.FTS.TransportS.leafEta_nonneg
      (Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθ)
  · rw [h]; exact Work.FTS.TransportS.leafOne_nonneg z θ
  · rw [h]
    exact Work.FTS.TransportS.leafGam_nonneg α
      (Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθ)



/-! ## The two pointwise case lemmas -/







end

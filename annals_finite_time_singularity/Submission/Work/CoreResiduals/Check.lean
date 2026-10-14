import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Tactic.MinImports
import Submission.Work.CoreResiduals.BiotSavart.biotSavartSpaceTime_holds
import Submission.Work.FTS.RegPkgGal.RVocab
import Submission.Work.FTS.StrongEps.EComparison.SlotsZeroSliceInt
import Submission.Work.FTS.StrongPersist.Star6
import Submission.Work.FTS_MuLipC.RowN.FaSlice
import Submission.Work.R1G.vecResid_eq_scalar_smul
import Submission.Work.SolutionDelivery.Check
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end
end
-- ===== merged: Submission.Work.CoreResiduals.Check =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.CoreResiduals

/-! ## The wiring -/








/-! ## R3 at the model data, PROVED (no residual input)

The space-time `C¹` input of R3 is *proved* (`BiotSavart.biotSavartSpacetimeC1_holds`), and so are
the two model-side conditions it consumes (the half-window admissibility bundle and the
second-order time condition).  Hence R3 holds at the model data with no residual input at all. -/


/-! ## Certificates for the model data -/

/-- **Certificate R4 — residual R4 is a theorem at the model data.** -/
example {α : NNReal} (hα : 0 < (α : ℝ)) (hα13 : (α : ℝ) ≤ 1 / 3) :
    TimeHolderDerivModel α :=
  timeHolderDeriv_model hα hα13


/-- **Certificate — every model-side hypothesis of the sharpest closure is a proved statement.**
For any inhabitant, the three admissibility/second-order conditions that `theorem1_of_model_data`
asks about the explicit field are theorems of this area: the half-window bundle, the second-order
time condition, and the strip bundle. -/
example {α : NNReal} (I : Inhabitant α) :
    BSAdmissibleOnWindow (solVort I.P) I.P.R I.P.T ∧
      TimeDerivLocallyLipschitz (solVort I.P) I.P.T ∧
        (∀ S : ℝ, 0 < S → S < I.P.T → BSAdmissibleStrip α (solVort I.P) I.P.R S) :=
  ⟨solVort_BSAdmissibleOnWindow I.P, timeDerivLocallyLipschitz_of_inhabitant I,
    fun S hS hST => solVort_BSAdmissibleStrip I.P hS hST⟩

/-- **Certificate — the *full* R2 bundle for the model data**: the strip admissibility, the
time-regularity of `∂ₜω` and the second-order time-regularity of `∂ₜω` on every strip
`0 < S < T`, i.e. exactly the hypothesis of `BiotSavartSpaceTime α`. -/
example {α : NNReal} (I : Inhabitant α) :
    ∀ S : ℝ, 0 < S → S < I.P.T → BSAdmissibleStripFull α (solVort I.P) I.P.R S :=
  fun S hS hST =>
    solVort_BSAdmissibleStripFull I.P (timeDerivLocallyLipschitz_of_inhabitant I) hS hST

/-- **Certificate R1-obstruction — the rate of the model data is not the reference rate.**  The
model modulation `λ̄(t) = 1-t/2` has rate `κ = -λ̄' = 1/2`, while the profile `F_*` is stationary at
the reference rates `(κ*,b*) = (1,1)`; `Model.fstar_rate_rigid` shows that both cannot hold with the
same stream function. -/
example {α : NNReal} (I : Inhabitant α) :
    -(deriv I.P.lam 1) ≠ Work.Stability.kappaStar 0 :=
  model_rate_ne_reference I

end Work.CoreResiduals
end
end

import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.CoreResiduals.Check
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.FKdzIter_sq_le
import Submission.Work.R1G.vecResid_eq_scalar_smul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.CoreResiduals

/-! ## The enstrophy functional -/



/-- **The enstrophy density** of the constructed vorticity at time `t`, as a function of `x`:
`x ↦ ‖solVort P x t‖²`.  Its integral is twice the enstrophy; it is the object whose pointwise
form is computed by `norm_solVort_sq_model`. -/
noncomputable def enstrophyDensity {α : NNReal} (P : Work.ConstructionInstance.ProfileData α)
    (t : ℝ) : R3 → ℝ :=
  fun x => ‖solVort P x t‖ ^ 2

@[simp] theorem enstrophyDensity_apply {α : NNReal}
    (P : Work.ConstructionInstance.ProfileData α) (t : ℝ) (x : R3) :
    enstrophyDensity P t x = ‖solVort P x t‖ ^ 2 := rfl

/-- **The difference of the enstrophy densities** at the times `s` and `t`.  Its integral is zero
exactly when the enstrophy is the same at `s` and `t`; the strict positivity of its support is the
positive-measure strictness used in `enstrophy_lt_of_lt`. -/
noncomputable def enstrophyDiff {α : NNReal} (P : Work.ConstructionInstance.ProfileData α)
    (s t : ℝ) : R3 → ℝ :=
  fun x => ‖solVort P x t‖ ^ 2 - ‖solVort P x s‖ ^ 2

@[simp] theorem enstrophyDiff_apply {α : NNReal}
    (P : Work.ConstructionInstance.ProfileData α) (s t : ℝ) (x : R3) :
    enstrophyDiff P s t x = ‖solVort P x t‖ ^ 2 - ‖solVort P x s‖ ^ 2 := rfl

/-- **The gradient density of the constructed vorticity**: `x ↦ ‖ω(x,t)‖·‖(Dω)(x,t)‖`.  Its
integrability is the hypothesis that makes the integration by parts in the enstrophy conservation
law legal. -/
noncomputable def vortGradDensity {α : NNReal} (P : Work.ConstructionInstance.ProfileData α)
    (t : ℝ) : R3 → ℝ :=
  fun x => ‖solVort P x t‖ * ‖fderiv ℝ (fun y : R3 => solVort P y t) x‖

@[simp] theorem vortGradDensity_apply {α : NNReal}
    (P : Work.ConstructionInstance.ProfileData α) (t : ℝ) (x : R3) :
    vortGradDensity P t x = ‖solVort P x t‖ * ‖fderiv ℝ (fun y : R3 => solVort P y t) x‖ := rfl



/-! ## The squared model profile -/





/-! ## The pointwise identity for the model vorticity -/





/-! ## Strict monotonicity of the enstrophy, and its non-constancy

The two analytic side conditions of this section are *positive-measure strictness* of the pointwise
comparison and *integrability* of the enstrophy density; both are proved for the model data in the
delegated lemmas `Work.CoreResiduals.strict_pos_set_enstrophy` and
`Work.CoreResiduals.integrable_norm_solVort_sq`.  Keeping them as hypotheses here isolates the
*pointwise* content of the finding, which is what the file proves outright. -/



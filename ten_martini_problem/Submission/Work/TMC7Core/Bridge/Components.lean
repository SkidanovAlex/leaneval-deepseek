import Submission.Work.TMC7Core.Bridge.P_BJ_transfer
import Submission.Work.TMContract.Components

/-!
# Bridge: the TMPlan components between the frozen contract and `TMC7Core`

`Work.TMC7Core.Defs` is a verbatim copy of the frozen `Work.TMContract.Defs`, so the
component `Prop`s transfer.  Only `iterC` (compiled by structural recursion, hence not
definitionally equal across the two copies) and `lyap` (defined through it) need work; the
required bridges are in `Bridge/P_BJ_transfer.lean`.
-/

open MeasureTheory Filter Topology Set
open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMC7Core.Bridge

/-- `P_OpBasics` is definitionally the same in both vocabularies. -/
theorem P_OpBasics_transfer (h : Work.TMContract.P_OpBasics) : Work.TMC7Core.P_OpBasics := h

/-- `P_UniqErg` is definitionally the same in both vocabularies. -/
theorem P_UniqErg_transfer (h : Work.TMContract.P_UniqErg) : Work.TMC7Core.P_UniqErg := h

/-- `P_Schnol` is definitionally the same in both vocabularies. -/
theorem P_Schnol_transfer (h : Work.TMContract.P_Schnol) : Work.TMC7Core.P_Schnol := h

/-- The two copies of the Frobenius norm agree. -/
theorem frob_eq (A : Matrix (Fin 2) (Fin 2) ℂ) :
    Work.TMC7Core.frob A = Work.TMContract.frob A := rfl

/-- `P_LEBasics` transfers (its statement mentions `iterC`, `frob` and `lyap`). -/
theorem P_LEBasics_transfer (h : Work.TMContract.P_LEBasics) : Work.TMC7Core.P_LEBasics := by
  constructor
  · intro α lam E
    rw [lyap_eq]
    exact h.1 α lam E
  · intro α lam hα E₀ ε hε
    obtain ⟨r, hr, n₀, hn⟩ := h.2 α lam hα E₀ ε hε
    refine ⟨r, hr, n₀, fun n hn' E hE x => ?_⟩
    have := hn n hn' E hE x
    simpa only [iterC_eq, lyap_eq, frob_eq] using this

end Work.TMC7Core.Bridge

end

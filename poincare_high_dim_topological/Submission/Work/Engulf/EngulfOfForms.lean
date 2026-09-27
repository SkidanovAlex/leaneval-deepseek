import Submission.Work.Engulf.All
import Submission.Work.Engulf.ToolsInstance
import Submission.Work.EngulfForms.All

/-!
# A9: `EngulfForm` from the remaining forms of the other areas

`Work.Engulf.All` proves `Work.Engulf.engulf : ToolsAll n → EngulfForm n`, and
`Submission/Work/Engulf/ToolsInstance.lean` assembles `ToolsAll n` from the *proved* results of
A1/A2/A3/A7 and the concrete barycentric subdivision of A2, leaving exactly three inputs:

* `SubdivShellForm N` — A4's shelling (`G4`) for `Work.PL.Subdiv.sdIter`;
* `PlApproxFrozenForm` — A5's frozen PL approximation (`G5`);
* `JoinPrismForm N` — A1's `G2`.

This file performs the substitution, so that once those three inputs exist as terms, Newman's
engulfing theorem is available in the form `Work.Cells.Connell.EngulfForm n` that the
Campbell–Connell area (A8) consumes.
-/

open Set Metric PL

namespace Work.Engulf

universe u

/-- Newman's Theorem 5 (`EngulfForm`) from the three remaining forms of A1, A4 and A5. -/
theorem engulf_of_forms {n : ℕ}
    (shell : ∀ N, SubdivShellForm N)
    (plApprox : ∀ N, PlApproxFrozenForm (subdivTools (shell N)) n)
    (full : ∀ N, SdFullForm (subdivTools (shell N)))
    (joinPrism : ∀ N, JoinPrismForm N) :
    Work.Cells.Connell.EngulfForm.{u} n :=
  engulf n (toolsAll shell plApprox full joinPrism)

/-- Newman's Theorem 6 from the same three forms. -/
theorem newman6_of_forms {n : ℕ}
    (shell : ∀ N, SubdivShellForm N)
    (plApprox : ∀ N, PlApproxFrozenForm (subdivTools (shell N)) n)
    (full : ∀ N, SdFullForm (subdivTools (shell N)))
    (joinPrism : ∀ N, JoinPrismForm N) :
    ∀ (p : ℕ) (M : Type u) [MetricSpace M] (V X : Set M) (N : ℕ) (Γ : Cx N)
      (H L : Set (E N)) (f : E N → M), Amb n p M V → Cfg n p V X Γ H L f →
      ∀ ε > 0, Engulfs V X Γ H L f ε :=
  fun p M _ V X N Γ H L f A c ε hε =>
    newman6 (toolsAll shell plApprox full joinPrism) A c ε hε

/-- **Newman's engulfing theorem, unconditional**: `Work.Cells.Connell.EngulfForm n`, obtained from
`Work.Engulf.engulf` and the unconditional bundle `Work.EngulfForms.toolsAll n` (which supplies,
from the delivered areas A1/A2/A4/A5/A7, every field of `Tools`).  The only mathematical input that
is still not on this workspace is the `E4` repair (`Work.Engulf.E4alt.E4alt`), on which
`Work.Engulf.engulf` depends through `B_all`. -/
theorem engulf_unconditional (n : ℕ) : Work.Cells.Connell.EngulfForm.{u} n :=
  engulf n (Work.EngulfForms.toolsAll n)

/-- The same, phrased through `engulf_of_forms` and the four labelled instances of the
`EngulfForms` area. -/
theorem engulf_unconditional' (n : ℕ) : Work.Cells.Connell.EngulfForm.{u} n :=
  engulf_of_forms Work.EngulfForms.shellForm_all (Work.EngulfForms.plApproxFrozenForm_all n)
    Work.EngulfForms.sdFullForm_all Work.EngulfForms.joinPrismForm_all

end Work.Engulf

import Submission.Work.Engulf.Chain.B_zero
import Submission.Work.Engulf.Chain.E1
import Submission.Work.Engulf.Chain.E2
import Submission.Work.Engulf.Chain.E3
import Submission.Work.Engulf.E4alt.E4alt
import Submission.Work.Engulf.Chain.E5
import Submission.Work.Engulf.Chain.engulf_of_newman6

/-!
# Area A9 (`Work.Engulf`): the assembly of the chain

This file assembles the lemmas of the chain into the final theorems of the area:

* `Work.Engulf.B_all`     : `B n p k` for all `k ≤ p + 1` (induction on `k` from `B_zero`,
  `E2`, and `E3 ∘ E5 ∘ E4`);
* `Work.Engulf.newman6`   : Newman's Theorem 6 (`E1` applied to `B_all`);
* `Work.Engulf.engulf`    : Newman's Theorem 5 = `Work.Cells.Connell.EngulfForm n` (`E0`), the
  form in which the Campbell–Connell area (A8) consumes the engulfing theorem.

All three take the bundle `Work.Engulf.ToolsAll n` of the other areas' results as a hypothesis;
`Submission/Work/Engulf/ToolsInstance.lean` discharges the fields that the other areas have
already delivered, and the remaining ones (`subdiv`, `carrier`, `plApprox`, `vertexPerturb`,
`joinPrism`) are delivered by A2/A4, A5 and A1.
-/

open Set Metric PL

namespace Work.Engulf

universe u

variable {n : ℕ} {M : Type*} [MetricSpace M] {N : ℕ}

/-- The `B`-induction: `B n p k` for every `k ≤ p + 1`. -/
theorem B_all (n p : ℕ) (T : ToolsAll.{u} n) : ∀ k ≤ p + 1, B.{u} n p k := by
  intro k hk
  induction k with
  | zero => exact Chain.B_zero n p
  | succ k ih =>
      have hB : B.{u} n p k := ih (by omega)
      exact Chain.E2 n p k T hB
        (Chain.E3 n p k T (Chain.E5 n p k T (E4alt.E4alt n p k T (by omega) hB)))

/-- Newman's Theorem 6 (contract `E6`): the engulfing theorem for an arbitrary configuration. -/
theorem newman6 {n p : ℕ} (T : ToolsAll.{u} n) {M : Type u} [MetricSpace M] {V X : Set M}
    {N : ℕ} {Γ : Cx N} {H L : Set (E N)} {f : E N → M} (A : Amb n p M V)
    (c : Cfg n p V X Γ H L f) (ε : ℝ) (hε : 0 < ε) : Engulfs V X Γ H L f ε :=
  Chain.E1 n p T (B_all n p T (p + 1) le_rfl) A c ε hε

/-- **Newman's engulfing theorem** (contract `E0`), in the exact form `EngulfForm` in which the
Connell area (A8) consumes it. -/
theorem engulf (n : ℕ) (T : ToolsAll.{u} n) : Work.Cells.Connell.EngulfForm.{u} n :=
  Chain.engulf_of_newman6 (fun p M _ V X N Γ H L f A c ε hε => newman6 T A c ε hε)

end Work.Engulf

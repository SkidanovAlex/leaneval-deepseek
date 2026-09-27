import Mathlib
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLNonExc.Defs
import Submission.Work.EKLNonExc.Assembly
import Submission.Work.EKLNonExc.VFacts
import Submission.Work.EKLNonExc.DinjFacts
import Submission.Work.EKLNonExc.BadNull
import Submission.Work.EKLNonExc.NoDiag

/-! Guidance from the project lead (the requester):

CONTEXT (project lead). This is one component of the FROZEN EKL contract (Submission/Work/EKLContract/Defs.lean; the composition
ekl_of_components and the glue are PROVED, so proving all components closes the problem). Read first:
* Submission/Work/EKLPlan/ROUTE_LEAD.md: your component section, with its source (EKL / Pisa notes / Venkatesh), proof sketch and hardest step;
* EKLContract/NOTES.md (statement changes) and REPORT.md;
* REFS/ (EKL TeX, the Pisa notes, the feasibility audit).
Other components are available as hypotheses only where your Prop takes them. Do not assume anything else. Reuse
EKLContract/Lemmas/* and Mathlib. Parallelise: request independent pieces at once.

YOUR COMPONENT: C9 no exceptional returns for SL3(Z) (EKL §5).

The proof is assembled from `Work.EKLNonExc.*`:

* `Defs` — the shared vocabulary (`Dinj`, `clBox`, `fmax`, `bconj`, `Bad`);
* `MatrixFacts` — the centraliser `Lset hab` and the contraction by `bconj`;
* `Endgame` — EKL L9.4: an `Lset`-return with `fmax = 0` produces a nontrivial diagonal
  `diag(λ,λ,λ⁻²)` fixing a point, contradicting L9.3 (`NoDiag`);
* `CloseReturn` — the finite-cover + Poincaré recurrence "close return";
* `VFacts` — compactness of `clBox`, the `V`-neighbourhood basis, the `V`-arithmetic and openness
  of the orbit images;
* `DinjFacts` — EKL L9.1: `Dinj` is closed and every compact set lies in some `Dinj δ`;
* `BadNull` — EKL Lemma 4.2 / L9.2: the "bad `Lset`-returns" are null;
* `NoDiag` — EKL L9.3: no `diag(λ,λ,λ⁻²)` with `λ > 0`, `λ ≠ 1` fixes a point of `X₃`;
* `Assembly` — the final `NonExceptional` assembly.
-/

namespace Work.EKLComp

open MeasureTheory Filter Topology
open Work.EKLContract

set_option maxHeartbeats 800000 in
theorem prove_NonExc : Work.EKLContract.P_NonExc := by
  intro μ hμ hA a b c hab hac hcb
  haveI := hμ
  exact Work.EKLNonExc.nonExceptional_of (a := a) (b := b) (c := c) hab hac hcb μ hA
    (Work.EKLNonExc.DinjFacts.2.2)
    (fun ℓ ℓu n ε hℓu hℓ hε =>
      (Work.EKLNonExc.BadNull a b c hab hac hcb μ hA
        (fun δ => Work.EKLNonExc.DinjFacts.1 δ)
        (fun δ => Work.EKLNonExc.VFacts.1 δ)).2 ℓ ℓu n ε hℓu hℓ hε)
    (Work.EKLNonExc.VFacts.2.2.1)
    (fun lam hlam hlam1 x h hmat =>
      Work.EKLNonExc.NoDiag a b c hab hac hcb lam hlam hlam1 x h hmat)

end Work.EKLComp

import Mathlib
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLContract.Lemmas.SL3Topology
import Submission.Work.EKLContract.Lemmas.Gamma3Facts
import Submission.Work.EKLComp.LeafDefs
import Submission.Work.EKLComp.X3Background
import Submission.Work.EKLComp.exists_isCompact_image
import Submission.Work.EKLComp.locallyFree_compacta
import Submission.Work.EKLComp.condExpKernel_atom
import Submission.Work.EKLRelCross.LeafBasic
import Submission.Work.EKLComp.prove_X3
import Submission.Work.EKLComp.AeFreeness
import Submission.Work.EKLComp.LeafExistence
import Submission.Work.EKLComp.leaf_unique
import Submission.Work.EKLComp.leaf_invariant
import Submission.Work.EKLComp.leaf_propor
import Submission.Work.EKLComp.leaf_ergodic
import Submission.Work.EKLComp.leaf_acovariant
import Submission.Work.EKLComp.leaf_entropy_cs
import Submission.Work.EKLRelCross.leafwise_crossSection
import Submission.Work.EKLRelCross.leafwise_luzin

/-! Guidance from the project lead (the requester):

CONTEXT (project lead). This is one component of the FROZEN EKL contract (Submission/Work/EKLContract/Defs.lean; the composition
ekl_of_components and the glue are PROVED, so proving all components closes the problem). Read first:
* Submission/Work/EKLPlan/ROUTE_LEAD.md: your component section, with its source (EKL / Pisa notes / Venkatesh), proof sketch and hardest step;
* EKLContract/NOTES.md (statement changes) and REPORT.md;
* REFS/ (EKL TeX, the Pisa notes, the feasibility audit).
Other components are available as hypotheses only where your Prop takes them. Do not assume anything else. Reuse
EKLContract/Lemmas/* and Mathlib. Parallelise: request independent pieces at once.

YOUR COMPONENT: C5 leafwise measures (Pisa §§5–6).

# Assembly of `P_Leafwise`

The frozen contract asks, for a probability `μ` on `X₃ = SL₃(ℝ)/SL₃(ℤ)`, a horospherical
`U ≤ SL₃(ℝ)` and **one** measure-preserving contracting `α^{t₀}`:

* **existence** (Pisa Thm 6.3) of a system of leafwise measures `ν` on a conull set `X'`
  (`Work.EKLC7.FlowerFam.nu`, built from the flower family `Work.EKLC7.FlowerFamExists`, the
  measurable leaf coordinate `Work.EKLC7.OrbitCoord`, the conditional measures
  `condExpKernel` and their patching — see `Submission/Work/EKLC7/LeafNu*.lean`), and
* the nine derived properties (U1)–(U9) for any such system.

The construction needs the a.e. freeness of the `U`-orbits (Pisa 7.12) and the
`A`-invariance of `μ` only through it; the frozen hypotheses supply it as
`Work.EKLComp.ae_freeness`.  `Work.EKLComp.leafwise_exists_of_free`
(`Submission/Work/EKLComp/LeafExistence.lean`) rebuilds the flower family and the conull good set
of `Work.EKLC7.LeafwiseHoro` with a.e. freeness as the input instead of `A`-invariance, giving the
existence clause under exactly the frozen hypotheses.

The derived clauses are `Work.EKLComp.leaf_unique` (U1), `Work.EKLComp.ae_freeness` (U2),
`Work.EKLRelCross.leafwise_crossSection` (U3), `Work.EKLComp.leaf_invariant` (U4),
`Work.EKLComp.leaf_propor` (U5), `Work.EKLRelCross.leafwise_luzin` (U6),
`Work.EKLComp.leaf_acovariant` (U7), `Work.EKLComp.leaf_ergodic` (U8) and
`Work.EKLComp.leaf_entropy_cs` (U9); the two `Work.EKLRelCross` clauses are proved from the
background component `P_X3`, which is unconditional here (`Work.EKLComp.prove_X3`).

See `Submission/Work/EKLComp/LeafPLAN.md` for the architecture and the status log.
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open LeanEval.Dynamics.EinsiedlerKatokLindenstrauss

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLComp

open Work.EKLContract

/-- **C5 (frozen)**: existence, uniqueness and the derived properties of the system of leafwise
measures of a horospherical subgroup `U ≤ SL₃(ℝ)` (Pisa §§5–6, EKL §2.1 (1)–(9)). -/
theorem prove_Leafwise : Work.EKLContract.P_Leafwise := by
  intro μ hμ U hU t0 hmp hcontr
  have hfree : ∀ᵐ x ∂μ, ∀ u ∈ U, u • x = x → u = 1 :=
    ae_freeness U hU μ t0 hmp hcontr
  refine ⟨leafwise_exists_of_free U hU μ hfree, ?_⟩
  intro ν X' hL
  exact ⟨leaf_unique μ U hU t0 hmp hcontr ν X' hL,
    hfree,
    Work.EKLRelCross.leafwise_crossSection prove_X3 μ U hU t0 hmp hcontr ν X' hL,
    leaf_invariant μ U hU t0 hmp hcontr ν X' hL,
    leaf_propor μ U hU t0 hmp hcontr ν X' hL,
    Work.EKLRelCross.leafwise_luzin prove_X3 μ U hU t0 hmp hcontr ν X' hL,
    leaf_acovariant μ U hU t0 hmp hcontr ν X' hL,
    leaf_ergodic μ U hU t0 hmp hcontr ν X' hL,
    leaf_entropy_cs μ U hU t0 hmp hcontr ν X' hL⟩

end Work.EKLComp

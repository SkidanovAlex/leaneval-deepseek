/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `Submission/Work/IndecomposedDeep/` — block (i) of the Neukirch–Uchida endgame, instantiated

Umbrella module: `import Submission.NK.IndecomposedDeep.All` (namespace `NK.IndecomposedDeep`).

The sibling chapter `Submission/Work/Indecomposed/` *assembles* Neukirch's local characterisation of
decomposition groups from two structures,

```
NK.Indecomposed.RankData          p K K' κ κ'   =  (hp, card_global, card_local, surj)
NK.Indecomposed.LocalReconstruction p K K' κ κ'  =  (korollar1, finishingStep)
```

This chapter *instantiates* them from a named classical input catalogue, proves every step in
between, and composes the result with the Neukirch–Uchida endgame.

## Main results

| theorem | statement |
|---|---|
| **`NK.IndecomposedDeep.rankData_of_inputs`** | `NK.Indecomposed.RankData p K K' κ κ'` from `LocalFieldBrauerCyclic` (local CFT, on disk), `GlobalBrauerTransport`, `LocalGroupBrauer` and `NeukirchH2modifiedsurj` (on disk) |
| `NK.IndecomposedDeep.rankData_of_deepInputs` | the same from the bundled catalogue `DeepInputs` |
| **`NK.IndecomposedDeep.localReconstruction_of_inputs`** | `NK.Indecomposed.LocalReconstruction p K K' κ κ'` from `LocalSubgroupClosed`, `LocalInjectionFiniteIndex` (on disk) and `IndexOneOfSelfNormalizing` (on disk) |
| `NK.IndecomposedDeep.localReconstruction_of_deepInputs` | the same from `DeepInputs` |
| **`NK.IndecomposedDeep.preservesDecompositionGroups_of_classical`** | `Submission.NeukirchUchida.PreservesDecompositionGroups ϕ` — the endgame input (a) — from the per-prime Hasse input and the catalogue |
| **`NK.IndecomposedDeep.perPrime_residuals`** | the per-prime residual form `∀ 𝔭, ∃ p, Sha2Input p · ∧ RankData p · ∧ LocalReconstruction p ·` consumed verbatim by `NK.Mine.neukirch_uchida_of_localStructureData_residuals` |
| **`NK.IndecomposedDeep.neukirch_uchida_of_classical`** | the `∃!` form of CoNF XII Thm 12.2.1 with block (i) supplied by this chapter |

Supporting statements:

* `NK.IndecomposedDeep.natCard_H2Twist_top_of_localFieldBrauerCyclic` — `|H²(G_κ, μ_p)| = p` from
  the on-disk local Brauer input (proved);
* `NK.IndecomposedDeep.natCard_H2Twist_of_transport` — the same at the labelled closed subgroups;
* `NK.IndecomposedDeep.neukirchH2modifiedsurjAt_of_input` — Neukirch's surjectivity in the guarded
  form from the on-disk unconditional form (proved);
* `NK.IndecomposedDeep.relIndex_pos_of_isClosed` and
  `NK.IndecomposedDeep.localKorollar1_of_inputs` — Neukirch's Korollar 1 (proved);
* `NK.IndecomposedDeep.localFinishingStep_of_indexOne` — the finishing step from the on-disk
  index-one input;
* `NK.IndecomposedDeep.localFinishingStep_local` — the *corrected* local form of the finishing
  step, proved from `LocalNUExistence` and `LocalDegreeRigidity`;
* `NK.IndecomposedDeep.globalBrauerTransport_of_rankData`,
  `NK.IndecomposedDeep.localGroupBrauer_of_rankData`,
  `NK.IndecomposedDeep.indexOne_of_localDecompositionCriterion` — the satisfiability/non-vacuity
  audit of the catalogue;
* **the corrected maximality** — `NK.IndecomposedDeep.indexOne_of_localGaloisField`
  (`indexOne_of_localGaloisField.lean`), its `LocalFinishingStep`-shaped form
  `…localFinishingStepAtLocalField_of_inputs`, and the corrected reconstruction
  `NK.IndecomposedDeep.LocalReconstructionAtLocalField`
  (`localReconstructionAtLocalField_of_inputs`, `CorrectedForm.lean`);
* **the degree rigidity of `p`-adic fields** — `NK.IndecomposedDeep.localDegreeRigidity`
  (`localDegreeRigidity.lean`) and `…localDegreeRigidity_holds`, with the corrected statements in
  the form that consumes it (`Rigidity.lean`);
* **the `p = 2` route** — the comparison of the twisted and trivial coefficient theories
  `NK.IndecomposedDeep.twistTwoComparison` (`twistTwoComparison.lean`), and the unconditional
  `rankDataTrivial_two_of_deepInputs` / `indecomposedPrime_two_of_deepInputs`
  (`TrivialTwoFinal.lean`).

See `README.md` for the catalogue with references, the audit (including the §7 finding on the
hypotheses of the finishing step and §13 for the `p = 2` route), and the honest list of what is
assumed.
-/

import Submission.NK.IndecomposedDeep.Defs
import Submission.NK.IndecomposedDeep.RankData
import Submission.NK.IndecomposedDeep.Korollar1
import Submission.NK.IndecomposedDeep.Reconstruction
import Submission.NK.IndecomposedDeep.Corrected
import Submission.NK.IndecomposedDeep.indexOne_of_localGaloisField
import Submission.NK.IndecomposedDeep.CorrectedForm
import Submission.NK.IndecomposedDeep.Rigidity
import Submission.NK.IndecomposedDeep.Endgame
import Submission.NK.IndecomposedDeep.TrivialTwo
import Submission.NK.IndecomposedDeep.twistTwoComparison
import Submission.NK.IndecomposedDeep.TrivialTwoFinal
import Submission.NK.IndecomposedDeep.Audit

/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `Submission/Work/Indecomposed/` — Neukirch's local characterisation of decomposition groups,
assembled

Umbrella module: `import Submission.NK.Indecomposed.All` (namespace `NK.Indecomposed`).

This chapter assembles Neukirch's local characterisation of decomposition groups — Theorem 1 of
J. Neukirch, *Kennzeichnung der `p`-adischen und der endlich algebraischen Zahlkörper*, Invent.
Math. **6** (1969); Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, (12.1.9) "if" — in its
coefficient-correct (`μ_p`-twisted) form `NK.BrauerTwist.LocalDecompositionCriterion p K K' κ κ'`,
from the rank-count input of `Submission/Work/HasseTwist/` and Neukirch's local reconstruction, with
every intermediate step proved here.

## Main results

| theorem | statement |
|---|---|
| **`NK.Indecomposed.le_stabSubgroup_of_rankData`** | Neukirch's "the prime is indecomposed" step from the rank data: a non-zero local component forces `H ≤ D_{A'}` (the group-theoretic content of `NK.LocalDecomposition.IndecomposedPrime`, proved, not assumed) |
| **`NK.Indecomposed.localDecompositionCriterion_of_rankData`** | the criterion from `RankData` and `LocalReconstruction` |
| **`NK.Indecomposed.localDecompositionCriterion_of_twistedHasse`** | the requested shape: `Sha2Input`, `NeukirchH2modifiedsurjAt`, the twisted cardinalities, the local reconstruction ⟹ the criterion |
| `NK.Indecomposed.localDecompositionCriterion_of_twistedHasse_allLocals` | the same with the local cardinality hypothesis imposed on *all* local groups |
| `NK.Indecomposed.exists_decompositionGroup_of_twistedHasse` | the Hasse-discharged (existential) form: every labelled closed self-normalising subgroup is a decomposition group |
| `NK.Indecomposed.localH2Input_of_rankData` | the local Brauer non-vanishing from the rank data |
| **`NK.Indecomposed.indecomposedPrime_of_rankDataTrivial`** | the trivial-coefficient form: `NK.LocalDecomposition.IndecomposedPrime p K K' κ κ'` from `RankDataTrivial` and `LocalReconstruction` |
| **`NK.Indecomposed.indecomposedPrime_two_of_rankData`** | the same at `p = 2` |
| **`NK.Indecomposed.preservesDecompositionGroups_of_localData_two_of_rankData`** | the `p = 2` `(a)`-chain of `Submission/Work/LocalDecomposition/` with the "indecomposed prime" and index-one inputs discharged |
| **`NK.Indecomposed.exists_localData_of_rankData`** | the per-finite-prime data consumed by `NK.BrauerTwist.preservesDecompositionGroups_of_localGalois` |
| **`NK.Indecomposed.preservesDecompositionGroups_of_hasseAt`** | the `(a)`-chain from the per-prime Hasse input, rank data and local reconstruction |

## Supporting lemmas

| theorem | statement |
|---|---|
| `NK.Indecomposed.subsingleton_h2Twist_bot` | `H²(⊥, μ_p)` is a point |
| `NK.Indecomposed.subsingleton_localH2Twist_of_inf_eq_bot` | the local cohomology at a place is a point when the local group is trivial |
| `NK.Indecomposed.inf_stabSubgroup_ne_bot_of_loc_ne_zero` | a non-zero local component forces a non-trivial local group |
| `NK.Indecomposed.subsingleton_h2Profinite_of_subsingleton`, `NK.Indecomposed.inf_stabSubgroup_ne_bot_of_loc_ne_zero_trivial` | the same in the trivial-coefficient vocabulary |
| `NK.Indecomposed.subsingleton_of_ne_bot_of_surjective` (+ `_trivial`) | the rank count: at most one non-trivial local group |
| `NK.Indecomposed.le_stabSubgroup_of_unique_localGroup` | the FKS step: the unique non-trivial local group lies in `H ∩ D_A`, so `H ≤ D_A` |
| `NK.Indecomposed.relIndex_pos_of_localKorollar1` | Neukirch's Korollar 1: `0 < H.relIndex D_A` |
| `NK.Indecomposed.mem_localGroupSubgroupsOver_stabSubgroup` | the local groups of a decomposition group over a prime are `D_A` and `⊥` |
| `NK.Indecomposed.not_forall_card_local_of_bot_mem` | the unrestricted local cardinality hypothesis is refutable as soon as `⊥` occurs as a local group |
| `NK.Indecomposed.not_localInjectionFiniteIndexSubgroup` | the general (`κ₀`-indexed) form of Korollar 1 of the sibling chapter is unsatisfiable; the `κ`-indexed form `NK.Indecomposed.LocalKorollar1` is the correct one |

See `README.md` for the account of the argument, the satisfiability audit of the hypotheses, the
precise relation to the siblings' inputs, and the honest list of what is assumed.
-/

import Submission.NK.Indecomposed.Defs
import Submission.NK.Indecomposed.subsingleton_h2Twist_bot
import Submission.NK.Indecomposed.subsingleton_localH2Twist_of_inf_eq_bot
import Submission.NK.Indecomposed.inf_stabSubgroup_ne_bot_of_loc_ne_zero
import Submission.NK.Indecomposed.subsingleton_h2Profinite_of_subsingleton
import Submission.NK.Indecomposed.inf_stabSubgroup_ne_bot_of_loc_ne_zero_trivial
import Submission.NK.Indecomposed.not_localInjectionFiniteIndexSubgroup
import Submission.NK.Indecomposed.mem_localGroupSubgroupsOver_stabSubgroup
import Submission.NK.Indecomposed.not_forall_card_local_of_bot_mem
import Submission.NK.Indecomposed.subsingleton_of_ne_bot_of_surjective
import Submission.NK.Indecomposed.subsingleton_of_ne_bot_of_surjective_trivial
import Submission.NK.Indecomposed.le_stabSubgroup_of_unique_localGroup
import Submission.NK.Indecomposed.relIndex_pos_of_localKorollar1
import Submission.NK.Indecomposed.Main
import Submission.NK.Indecomposed.TrivialCoeff
import Submission.NK.Indecomposed.Preserves

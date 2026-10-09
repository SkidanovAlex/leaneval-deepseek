/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The cyclotomic-twist chapter in one import

Everything under `Submission/Work/BrauerTwist/` in a single import: the coefficient module `μ_p`
(the `p`-th roots of unity, with the Galois action), the level-wise twisted cohomology
`H²(U, μ_p(L))`, the generic filtered-colimit machinery, the twisted profinite cohomology
`H²(U, μ_p)` with its localisation maps, the three corrected classical inputs, and Neukirch's
criterion in its coefficient-correct form.

## The main entry points

* `NK.BrauerTwist.exists_decompositionGroup_of_localGalois`
  (`Submission/Work/BrauerTwist/Main.lean`): Neukirch's characterisation of the decomposition
  groups of `G_K`, with `μ_p`-coefficients — a closed, self-normalising subgroup isomorphic to the
  absolute Galois group of a `p`-adic field is the decomposition group of a place of `K̄` over a
  finite prime of `K`.
* `NK.BrauerTwist.preservesDecompositionGroups_of_localGalois`
  (`Submission/Work/BrauerTwist/Preserves.lean`): per-prime twisted local data implies
  `Submission.NeukirchUchida.PreservesDecompositionGroups ϕ`, the input (a) of the endgame.

## The inputs (named classical theorems, never axioms)

* `NK.BrauerTwist.LocalH2Input`, `NK.BrauerTwist.LocalFieldBrauerCyclic` — Kummer + Hilbert 90
  (`H²(G_κ, μ_p) = Br(κ)[p] ≅ Z/p` for every `p`-adic `κ`);
* `NK.BrauerTwist.Sha2Vanishing` — Hasse–Brauer–Noether with `μ_p`-coefficients and its limit
  form;
* `NK.BrauerTwist.LocalDecompositionCriterion` — Neukirch's local finishing step.

See `README.md` in this directory for the full list of what is proved and what is assumed.
-/

import Submission.NK.BrauerTwist.Basic
import Submission.NK.BrauerTwist.System
import Submission.NK.BrauerTwist.levelMap_comp
import Submission.NK.BrauerTwist.levelMap_refl
import Submission.NK.BrauerTwist.localLevelMap_comp
import Submission.NK.BrauerTwist.localLevelMap_refl
import Submission.NK.BrauerTwist.levelMap_locLevel_apply
import Submission.NK.BrauerTwist.muLevel_eq_top_of_isPrimitiveRoot
import Submission.NK.BrauerTwist.muRep_isTrivial_of_isPrimitiveRoot
import Submission.NK.BrauerTwist.Profinite
import Submission.NK.BrauerTwist.Hasse
import Submission.NK.BrauerTwist.Main
import Submission.NK.BrauerTwist.Preserves
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

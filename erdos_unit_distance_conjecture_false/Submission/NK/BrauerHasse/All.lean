/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Brauer / local-global chapter in one import

Everything under `Submission/Work/BrauerHasse/` in a single import.  The main entry point is

* `NK.BrauerHasse.exists_decompositionGroup_of_localGalois`
  (`Submission/Work/BrauerHasse/Main.lean`): Neukirch's characterisation of the decomposition
  groups of `G_K` — a closed, self-normalising subgroup isomorphic to the absolute Galois group of
  a `p`-adic field is the decomposition group of a place of `K̄` over a finite prime of `K`.

The inputs are `NK.BrauerHasse.LocalFieldBrauerCyclic`, `NK.BrauerHasse.LocalH2Input`,
`NK.BrauerHasse.Sha2Vanishing` and `NK.BrauerHasse.LocalDecompositionCriterion`
(`Submission/Work/BrauerHasse/Hasse.lean`); see `README.md` in this directory.
-/

import Submission.NK.BrauerHasse.Basic
import Submission.NK.BrauerHasse.Commons
import Submission.NK.BrauerHasse.Profinite
import Submission.NK.BrauerHasse.ofLevel_eq_iff
import Submission.NK.BrauerHasse.ofLevel_zero
import Submission.NK.BrauerHasse.local_ofLevel_eq_iff
import Submission.NK.BrauerHasse.local_ofLevel_zero
import Submission.NK.BrauerHasse.localLevelMap_comp
import Submission.NK.BrauerHasse.exists_restriction_map
import Submission.NK.BrauerHasse.exists_add
import Submission.NK.BrauerHasse.exists_heightOneSpectrum_eq_comap
import Submission.NK.BrauerHasse.Hasse
import Submission.NK.BrauerHasse.Main

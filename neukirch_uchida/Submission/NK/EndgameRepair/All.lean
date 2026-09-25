import Submission.NK.EndgameRepair.LevelPairData
import Submission.NK.EndgameRepair.LevelIsoInputComplexPrime
import Submission.NK.EndgameRepair.LevelIsoInputGeneral
import Submission.NK.EndgameRepair.ExistsSigma
import Submission.NK.EndgameRepair.Endgame
import Submission.NK.EndgameRepair.Wall
import Submission.NK.EndgameRepair.not_classicalChaptersDeep
import Submission.NK.EndgameRepair.neukirch_uchida_of_reconstructLeaves_corrected
import Submission.NK.EndgameRepair.neukirch_uchida_of_brauerTwistLeaves_corrected
import Submission.NK.EndgameRepair.neukirch_uchida_of_decompositionGroups_corrected

/-!
# `Submission/Work/EndgameRepair/` — the repaired Shimizu endgame of Neukirch–Uchida

Umbrella module (namespace `NK.EndgameRepair`).  **Import this module to get the whole chapter:**

```lean
import Submission.NK.EndgameRepair.All
```

## Why the chapter exists

`Submission/Work/RankTheoryDeep/` proves, for the workspace's definitions, that

* `NK.ShimizuRank.GammaTFRankFinite Ω ℓ` is **false** for every prime `ℓ`
  (`NK.RankTheoryDeep.not_gammaTFRankFinite_prime`),
* hence `NK.ShimizuRank.Residuals Ω ℓ` is unsatisfiable (`not_residuals_prime`),
* hence `NK.Mine.ResidualsDerived K K' ℓ` is false (`not_residualsDerived`),
* and `NK.Reconstruct.HausRankInput Ω 2` is **false** (`not_hausRankInput`).

The cause is a formalisation defect: the workspace's `NK.Reconstruct.Gamma K K' ℓ` has
torsion-free part of *infinite* `ℤ_ℓ`-rank, whereas the classical invariant `r_ℓ(K)` is the rank of
the **Hausdorff** quotient `Γ_K ⧸ invisible`.  Consequently every theorem of the Shimizu route that
is conditioned on those three inputs is **vacuous**; the repaired replacement is
`NK.RankTheoryDeep.CorrectedResidualsDeep Ω ℓ` (equivalently
`NK.RankTheoryDeep.CorrectedResidualsDerived K K' ℓ`), whose fields are named classical theorems
and which *implies* `NK.Reconstruct.Fourf5InputGen Ω ℓ`.

## What the chapter delivers

* **the repaired σ-producing step** — `NK.EndgameRepair.exists_sigma_of_localCorrespondence_corrected`,
  its `∃!` forms, and the versions whose rank hypothesis is the corrected residual
  (`exists_sigma_of_correctedResiduals`, `exists_sigma_of_correctedResidualsDeep`), in
  `ExistsSigma.lean`;
* **the repaired endgame chapters** — the `PreservesDecompositionGroups` and `LocalStructureData`
  forms, and the `NK.Mine`-shaped capstone on the corrected residual, in `Endgame.lean`;
* **the repaired classical-input wall and capstone** —
  `NK.EndgameRepair.ClassicalChaptersRepaired`,
  `NK.EndgameRepair.neukirch_uchida_of_repairedChapters`,
  `NK.EndgameRepair.challenge_of_repairedChapters` (the verbatim challenge statement), in
  `Wall.lean`;
* the level-pair bridges on which the above rest — `LevelPairData.lean`,
  `LevelIsoInputComplexPrime.lean`, `LevelIsoInputGeneral.lean`.

See `README.md` (audit of the refuted on-disk theorems, description of the repair, satisfiability of
every structure, universes, and what remains for the final assembly) and `Axioms.lean`
(`#print axioms` of every public declaration of the chapter; not imported here).
-/

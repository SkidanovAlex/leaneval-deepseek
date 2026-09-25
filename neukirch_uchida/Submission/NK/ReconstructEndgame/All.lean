import Submission.NK.ReconstructEndgame.Basic
import Submission.NK.ReconstructEndgame.rankStrictMonoLevelInputGen_congr
import Submission.NK.ReconstructEndgame.resRankInputGen_congr
import Submission.NK.ReconstructEndgame.chebotarevInput_congr
import Submission.NK.ReconstructEndgame.Main
import Submission.NK.ReconstructEndgame.FrobeniusInput

/-!
# `Submission/Work/ReconstructEndgame/` — the Shimizu endgame of Neukirch–Uchida

Umbrella module (namespace `NK.ReconstructEndgame`).  See the module docstrings of `Basic.lean`
and `Main.lean`; the headline theorems are

* `NK.ReconstructEndgame.neukirch_uchida_of_reconstructLeaves` — CoNF XII Thm 12.2.1 (`∃!`) from
  block (i), block (ii) and the Shimizu inputs, with the `ℚ`-algebra structure on `K₁'` derived;
* `NK.ReconstructEndgame.exists_sigma_of_reconstructLeaves` — its existence half;
* `NK.ReconstructEndgame.neukirch_uchida_of_shimizu` — block (ii) already reduced to
  `NK.PTorsionTop.LocalGaloisInputsTop`;
* `NK.ReconstructEndgame.neukirch_uchida_of_preserves_shimizu` — the same with
  `Submission.NeukirchUchida.PreservesDecompositionGroups ϕ` taken directly;
* `NK.ReconstructEndgame.neukirch_uchida_of_brauerTwistLeaves` — block (i) in the
  `NK.BrauerTwist` form;
* the `_inst` variants of all of these, in which the `ℚ`-algebra data on `K₁'` is a hypothesis;
* `NK.ReconstructEndgame.neukirch_uchida_of_localStructureData` — with the Frobenius
  correspondence discharged by `NK.ResidueFrob.LocalStructureData` at every place.
-/


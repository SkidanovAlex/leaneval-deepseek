/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.PointlessTwist
-/
import Submission.Work.PointlessTwist.Defs
import Submission.Work.PointlessTwist.Place
import Submission.Work.PointlessTwist.FunctionField
import Submission.Work.PointlessTwist.Constants
import Submission.Work.PointlessTwist.Assembly
import Submission.Work.PointlessTwist.Data
import Submission.Work.PointlessTwist.GaloisFixed.galMap_eq_self_iff
import Submission.Work.PointlessTwist.Kummer.not_exists_pow_five_eq_X
import Submission.Work.PointlessTwist.Constants.nonempty_constantTateData
import Submission.Work.PointlessTwist.Constants.hasGoodAut_of_j_ne
import Submission.Work.PointlessTwist.bridge.trivialGaloisAction_of_constantsOnly

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.PointlessTwist` — the pointless-twist arithmetic

`import Submission.Work.PointlessTwist.All` is the single entry point of the area; read `NOTES.md`
for the full account, including the exact gap in each field class.

## What the caller gets

* `Work.PointlessTwist.PointlessOf C₅ L` — the arithmetic residual at the paper's data
  (`Work.Twist.PointlessOf`): the twist of `C₅` by `L` has no `𝕜`-point, equivalently
  `¬ ∃ R : E(L), σ R - R = P` (`pointlessOf_iff_not_exists_shift`).
* `Work.PointlessTwist.HasPointlessTwist 𝕜` — some quintic twist over `𝕜` is pointless, i.e. the
  arithmetic half of `Work.Twist.PointlessTwistData 𝕜`.
* the criteria `pointlessOf_of_localObstruction`, `pointlessOf_of_galTrivial`,
  `pointlessOf_of_invariantObstruction`, `pointlessOf_of_forall_galMap_eq`,
  `pointlessOf_of_hasReductionPlace` (`Defs`, `Place`);
* `hasInvariantObstruction_iff_pointless` — the invariant-obstruction form is equivalent to the
  residual, so a place-based proof loses nothing;
* the per-class residuals and their reductions to `HasPointlessTwist`:
  `Assembly.NumberFieldResidual`, `Assembly.KummerResidual`,
  `Assembly.hasPointlessTwist_of_numberFieldResidual`,
  `Assembly.hasPointlessTwist_of_kummerResidual`, and the four concrete `Residual_*` props;
* the constant-curve dictionary: `FunctionField.ConstantsOnly` (`E(𝔽(s)) = E(𝔽)`),
  `FunctionField.map_eq_self_of_constantsOnly`, `FunctionField.TrivialGaloisAction`,
  `Constants.ConstantTateData` (the concrete constant Tate model over a tower) with
  `Constants.nonempty_constantTateData`, and the bridge
  `bridge.trivialGaloisAction_of_constantsOnly`;
* the `H⁰` descent lemma `GaloisFixed.galMap_eq_self_iff` (`E(L)^σ = E(𝕜)`);
* the Kummer input `Kummer.not_exists_pow_five_eq_X` (`t ∉ 𝔽(t)^5`).
-/

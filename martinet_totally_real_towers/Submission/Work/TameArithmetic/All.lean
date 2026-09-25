import Submission.Work.TameArithmetic.Defs
import Submission.Work.TameArithmetic.VSDefs
import Submission.Work.TameArithmetic.exists_maximalTamePro2
import Submission.Work.TameArithmetic.exists_surjective_presentedGroup_zmodTwo
import Submission.Work.TameArithmetic.residuallyFiniteTwoGroup_galoisGroup_tame
import Submission.Work.TameArithmetic.infinite_galoisGroup_of_presentation
import Submission.Work.TameArithmetic.MartinetWall
import Submission.Work.TameArithmetic.card_le_of_generating_presentedGroup
import Submission.Work.TameArithmetic.residuallyFinite_presentedGroup
import Submission.Work.TameArithmetic.isPGroup_two_quotient_of_model
import Submission.Work.TameArithmetic.realization_of_model
import Submission.Work.TameArithmetic.isProTwoModel_of_realization
import Submission.Work.TameArithmetic.exists_pm_square_of_isIdealSquare
import Submission.Work.TameArithmetic.isSquare_neg_one_padic
import Submission.Work.TameArithmetic.neg_one_mem_VS
import Submission.Work.TameArithmetic.neg_one_not_square
import Submission.Work.TameArithmetic.VS_eq_pm_squares
import Submission.Work.TameArithmetic.VS_mod_squares_two
import Submission.Work.TameArithmetic.exists_sqrt_of_finrank_two
import Submission.Work.TameArithmetic.quadratic_tame_classification
import Submission.Work.TameArithmetic.Assembly

/-!
# `Work.TameArithmetic.All` -- the whole chapter in one import

The arithmetic of the tame Golod--Shafarevich route (see `README.md` in this directory).

## Main results

* `Work.TameArithmetic.tameGolodShafarevichInput_of_arithmeticInput` (`Assembly.lean`):

  ```lean
  theorem tameGolodShafarevichInput_of_arithmeticInput (h : TameArithmeticInput) :
      Submission.NumberField.TameGolodShafarevichInput
  ```

  i.e. the single arithmetic input of `Submission.lean` follows from `TameArithmeticInput`
  (`Defs.lean`), which is the Shafarevich--Koch relation bound (`TameRelationBound`, five
  generators and at most six relators) together with the abstract-model condition
  (`IsProTwoModel K (presentedGroup P)`).
* `Work.TameArithmetic.exists_totallyReal_discr_le_of_arithmeticInput`: the benchmark statement
  itself, from that input and the proved reduction of the seed plus Chapter B.
* `Work.TameArithmetic.martinetTameWall_of_relationBound` (`MartinetWall.lean`):

  ```lean
  theorem martinetTameWall_of_relationBound (h : TameRelationBound) :
      Submission.NumberField.MartinetTameWall
  ```

  **the `MartinetTameWall` exit, which needs ONLY the Shafarevich--Koch relation bound** -- the
  abstract-model condition `IsProTwoModel` is not used here (Golod--Shafarevich is applied to the
  *presented* group, which is a finitely generated subgroup of the Galois group, not to a group
  whose quotients must be realized arithmetically).  Together with the seed's proved
  `Submission.NumberField.exists_totallyReal_discr_le_of_martinetTameWall` this gives the benchmark
  statement from `TameRelationBound` alone
  (`exists_totallyReal_discr_le_of_relationBound`).
* the elementary pieces, all proved: `exists_maximalTamePro2`;
  `exists_surjective_presentedGroup_zmodTwo`, `card_le_of_generating_presentedGroup` (the generator
  rank `d ≥ 5` and the minimality of the five-element generating set);
  `quadratic_tame_classification`, `exists_sqrt_of_finrank_two` (the elementary classification,
  `d ≤ 5`); `VS_eq_pm_squares`, `neg_one_mem_VS`, `neg_one_not_square`,
  `VS_mod_squares_two`, `exists_pm_square_of_isIdealSquare`, `isSquare_neg_one_padic` (the
  `𝔽₂`-rank computation `dim V_S/ℚ^{×2} = 1`, giving `r ≤ 6`);
  `four_mul_le_sq_of_rel_card_le_six` (the counting `4r ≤ d²`);
  `residuallyFinite_presentedGroup`, `isPGroup_two_quotient_of_model`, `realization_of_model`
  (the three clauses of `TameGolodShafarevichInput` about the presented abstract group).
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area BSW, `Work.BSW`)

# Area BSW: the character-theoretic setup of Bender §2

Nothing in this file: it is the import that puts the area's counting vocabulary
(`Submission/Work/BSW/Vocab.lean`) together with the character theory of the odd-order import
closure that Bender's §2 uses:

* `OddOrder.RepresentationTheory.ClassFunction` and `ClassFunction.inner`, `ClassFunction.induce`
  (`GroupTheory/RepresentationTheory/ClassFunction.lean`, `InducedCharacter.lean`);
* `OddOrder.RepresentationTheory.IrreducibleCharacter` (`IrrIndexing.lean`) and the linear
  characters `OddOrder.RepresentationTheory.linearIrreducibleCharacter` (`LinearCharacter.lean`);
* the class-multiplication formula `classSum_mul_apply` (`ClassSumSections.lean`) and
  `classSumCoeff_mul_centralizer_card_eq_sum_irreducibleCharacter` (`ClassSumCoefficientFormula.lean`);
* the Brauer–Suzuki TI isometry `ClassFunction.inner_induce_eq_of_isTISubset`
  (`InducedCharacter.lean`) and `OddOrder.GroupTheory.IsTISubset` (`GroupTheory/TISubset.lean`).

The contracts `Submission/Work/BSW/Char/*.lean` are stated over this vocabulary.
-/
import Submission.Work.BSW.Vocab
import Submission.OddOrder.FeitThompson

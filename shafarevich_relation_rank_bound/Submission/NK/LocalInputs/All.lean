/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `NK.LocalInputs`: instantiation of the local inputs for genuine `p`-adic fields

This is the umbrella module of the `Submission/Work/LocalInputs/` subproject.  Its purpose is to
*instantiate* the conditional local-invariance chapter `Submission/Work/LocalAnabelian/` (which
proves everything it proves relative to the structure
`NK.LocalAnabelian.PadicGaloisInputs p d δ κ K'`) for genuine `p`-adic fields, namely for the
completions `κ = 𝔭.adicCompletion K` of a number field at a finite prime.

Main entry points:

* `NK.LocalInputs.padicGaloisInputs_of_localInputs` (in `Instantiation`): the instantiation
  `NK.LocalAnabelian.PadicGaloisInputs p (localDegree K 𝔭) (zetaIndicator p κ) κ K'`;
* `NK.LocalInputs.residueChar_and_localDegree_eq_of_decompositionGroup` (in `Global`): the
  *global* corollary — corresponding places have the same residue characteristic and the same
  absolute local degree `[K_𝔭 : ℚ_p]`;
* `NK.LocalInputs.Degree.sum_localDegree_eq_finrank` and
  `NK.LocalInputs.finrank_eq_of_localDegree_eq`: `∑_{𝔮 | p} [K_𝔮 : ℚ_p] = [K : ℚ]`, and the
  consequence that a bijection of the primes above `p` which matches the local degrees gives
  `[K₁ : ℚ] = [K₂ : ℚ]`;
* `NK.LocalInputs.LocalFieldInputs` and `NK.LocalInputs.LocalGaloisInputs` (in `Inputs`): the
  named classical inputs which remain (see the README for the exact list and the references);
* `NK.LocalInputs.Zeta.localFieldInputs_rat`: the arithmetic input discharged for `K = ℚ` from
  the commons' `p`-power class counts.

See `Submission/Work/LocalInputs/README.md` for the full description.
-/
import Submission.NK.LocalInputs.Defs
import Submission.NK.LocalInputs.Hints
import Submission.NK.LocalInputs.Inputs
import Submission.NK.LocalInputs.PowerQuotient.natCard_residueUnits_quot_pow_eq_one
import Submission.NK.LocalInputs.PowerQuotient.natCard_KummerGroup_eq_pow_of_principalUnits
import Submission.NK.LocalInputs.PowerQuotient.natCard_KummerGroup_rat_adic_eq_sq
import Submission.NK.LocalInputs.PowerQuotient.hasFrattiniRank_units_adicCompletion
import Submission.NK.LocalInputs.ResidueChar.primesEquiv_primeBelow
import Submission.NK.LocalInputs.ResidueChar.primeBelow_eq_of_liesOver
import Submission.NK.LocalInputs.ResidueChar.residueCard_eq_primesEquiv
import Submission.NK.LocalInputs.Degree.localDegree_eq_ramificationIdx_mul_inertiaDeg
import Submission.NK.LocalInputs.Degree.sum_localDegree_eq_finrank
import Submission.NK.LocalInputs.Degree.finrank_eq_of_localDegree_eq
import Submission.NK.LocalInputs.Degree.localDegree_rat
import Submission.NK.LocalInputs.AbelianRank.Hints
import Submission.NK.LocalInputs.AbelianRank.fixingSubgroup_fixedField_eq_topologicalClosure
import Submission.NK.LocalInputs.AbelianRank.hasAbelianFrattiniRank_of_maxAbelian_of_isOpen
import Submission.NK.LocalInputs.AbelianRank.of_lubinTate
import Submission.NK.LocalInputs.CommGroupRank.hasFrattiniRank_of_natCard_quot_powSubgroup
import Submission.NK.LocalInputs.CommGroupRank.numIndexSubgroups_profiniteCompletion
import Submission.NK.LocalInputs.CommGroupRank.infinite_indexP_subgroups_of_infinite_exp_p
import Submission.NK.LocalInputs.Zeta.not_exists_isPrimitiveRoot_rat_adic
import Submission.NK.LocalInputs.Zeta.localFieldInputs_rat
import Submission.NK.LocalInputs.Global.nonempty_mulEquiv_sepClosure_of_decompositionGroup_map
import Submission.NK.LocalInputs.Instantiation
import Submission.NK.LocalInputs.InputsOfUnits
import Submission.NK.LocalInputs.Global

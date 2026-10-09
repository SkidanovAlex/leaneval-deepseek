/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `Work.HilbertSymbol` : the Hilbert symbol over `ℚ`, local computations, and reciprocity

Umbrella module importing the whole chapter.  The entry points are

* definitions : `Work.HilbertSymbol.hilbertSymbol`, `Work.HilbertSymbol.hilbertSymbolAtPrime`,
  `Work.HilbertSymbol.hilbertSymbolReal`, `Work.HilbertSymbol.Place`;
* basic algebraic properties : `Work.HilbertSymbol.hilbertSymbol_mul_left`,
  `Work.HilbertSymbol.hilbertSymbol_mul_right`, `Work.HilbertSymbol.hilbertSymbol_comm`,
  `Work.HilbertSymbol.hilbertSymbol_sq_left`, `Work.HilbertSymbol.hilbertSymbol_sq_right`,
  `Work.HilbertSymbol.hilbertSymbolOdd_neg_self`, `Work.HilbertSymbol.hilbertSymbolTwo_neg_self`,
  `Work.HilbertSymbol.hilbertSymbolOdd_add_eq_one`, `Work.HilbertSymbol.hilbertSymbolTwo_add_eq_one`,
  `Work.HilbertSymbol.hilbertSymbolReal_isotropic_iff`;
* places and finiteness : `Work.HilbertSymbol.contributingPrimes`,
  `Work.HilbertSymbol.hilbertSymbol_some_eq_one_of_not_mem`,
  `Work.HilbertSymbol.placeProduct`, `Work.HilbertSymbol.placeProduct_mul_left`,
  `Work.HilbertSymbol.placeProduct_mul_right`;
* reciprocity : `Work.HilbertSymbol.hilbertReciprocity`,
  `Work.HilbertSymbol.hilbertReciprocity_prod`, `Work.HilbertSymbol.hilbertReciprocity_places`;
* the norm-form criterion : `Work.HilbertSymbol.normForm`, `Work.HilbertSymbol.Isotropic`,
  `Work.HilbertSymbol.HilbertSymbolCriterionAtPrime`,
  `Work.HilbertSymbol.HilbertSymbolCriterionReal`;
* documented global inputs : `Work.HilbertSymbol.HasseBrauerNoether`,
  `Work.HilbertSymbol.HasseNormTheorem`, `Work.HilbertSymbol.GrunwaldWang`.
-/



import Submission.Work.HilbertSymbol.Basic
import Submission.Work.HilbertSymbol.Criterion
import Submission.Work.HilbertSymbol.GlobalInputs
import Submission.Work.HilbertSymbol.Places
import Submission.Work.HilbertSymbol.SmallLemmas
import Submission.Work.HilbertSymbol.Symbol
import Submission.Work.HilbertSymbol.contributingPrimes_mul_subset
import Submission.Work.HilbertSymbol.contributingPrimes_primeUnit
import Submission.Work.HilbertSymbol.dvd_num_den_add_of_padicValRat_add_pos
import Submission.Work.HilbertSymbol.epsZ_mul
import Submission.Work.HilbertSymbol.epsZ_primeUnit
import Submission.Work.HilbertSymbol.exists_intUnit_mul_sq
import Submission.Work.HilbertSymbol.hilbertReciprocity
import Submission.Work.HilbertSymbol.hilbertReciprocity_prod
import Submission.Work.HilbertSymbol.hilbertSymbolAtPrime_eq_one_of_not_dvd
import Submission.Work.HilbertSymbol.hilbertSymbolOdd_add_eq_one
import Submission.Work.HilbertSymbol.hilbertSymbolOdd_eq_one_of_padicVal_eq_zero
import Submission.Work.HilbertSymbol.hilbertSymbolOdd_mul_left
import Submission.Work.HilbertSymbol.hilbertSymbolOdd_mul_right
import Submission.Work.HilbertSymbol.hilbertSymbolOdd_neg_one_neg_one
import Submission.Work.HilbertSymbol.hilbertSymbolOdd_neg_one_primeUnit
import Submission.Work.HilbertSymbol.hilbertSymbolOdd_neg_self
import Submission.Work.HilbertSymbol.hilbertSymbolOdd_primeUnit
import Submission.Work.HilbertSymbol.hilbertSymbolOdd_primeUnit_of_ne
import Submission.Work.HilbertSymbol.hilbertSymbolOdd_primeUnit_self
import Submission.Work.HilbertSymbol.hilbertSymbolOdd_primeUnit_self_odd
import Submission.Work.HilbertSymbol.hilbertSymbolOdd_primeUnit_two_odd
import Submission.Work.HilbertSymbol.hilbertSymbolOdd_sq_left
import Submission.Work.HilbertSymbol.hilbertSymbolOdd_sq_right
import Submission.Work.HilbertSymbol.hilbertSymbolReal_add_eq_one
import Submission.Work.HilbertSymbol.hilbertSymbolReal_isotropic_iff
import Submission.Work.HilbertSymbol.hilbertSymbolReal_mul_left
import Submission.Work.HilbertSymbol.hilbertSymbolReal_neg_one_neg_one
import Submission.Work.HilbertSymbol.hilbertSymbolReal_neg_one_primeUnit
import Submission.Work.HilbertSymbol.hilbertSymbolReal_primeUnit
import Submission.Work.HilbertSymbol.hilbertSymbolReal_sq_left
import Submission.Work.HilbertSymbol.hilbertSymbolTwo_add_eq_one
import Submission.Work.HilbertSymbol.hilbertSymbolTwo_mul_left
import Submission.Work.HilbertSymbol.hilbertSymbolTwo_mul_right
import Submission.Work.HilbertSymbol.hilbertSymbolTwo_neg_one_neg_one
import Submission.Work.HilbertSymbol.hilbertSymbolTwo_neg_one_primeUnit_odd
import Submission.Work.HilbertSymbol.hilbertSymbolTwo_neg_one_two
import Submission.Work.HilbertSymbol.hilbertSymbolTwo_neg_self
import Submission.Work.HilbertSymbol.hilbertSymbolTwo_primeUnit_primeUnit_odd
import Submission.Work.HilbertSymbol.hilbertSymbolTwo_primeUnit_two_odd
import Submission.Work.HilbertSymbol.hilbertSymbolTwo_sq_left
import Submission.Work.HilbertSymbol.hilbertSymbolTwo_sq_right
import Submission.Work.HilbertSymbol.hilbertSymbolTwo_two_two
import Submission.Work.HilbertSymbol.intUnit_num_den_mul_sq
import Submission.Work.HilbertSymbol.legendreOf_eq_one_of_padicVal_eq_zero_of_sub_one_pos
import Submission.Work.HilbertSymbol.legendreOf_intUnit
import Submission.Work.HilbertSymbol.legendreOf_mul_eq_legendreOf_neg_one_of_add_eq_one
import Submission.Work.HilbertSymbol.legendreOf_neg
import Submission.Work.HilbertSymbol.legendreSym_mul_eq_legendreSym_neg_one_of_dvd_add
import Submission.Work.HilbertSymbol.numDenNat_dvd_mul
import Submission.Work.HilbertSymbol.omegaZ_mul
import Submission.Work.HilbertSymbol.omegaZ_primeUnit
import Submission.Work.HilbertSymbol.padicVal_eq_zero_iff
import Submission.Work.HilbertSymbol.placeProduct_comm
import Submission.Work.HilbertSymbol.placeProduct_intUnit
import Submission.Work.HilbertSymbol.placeProduct_mul_left
import Submission.Work.HilbertSymbol.placeProduct_mul_right
import Submission.Work.HilbertSymbol.placeProduct_neg_one_neg_one
import Submission.Work.HilbertSymbol.placeProduct_neg_one_primeUnit_odd
import Submission.Work.HilbertSymbol.placeProduct_neg_one_two
import Submission.Work.HilbertSymbol.placeProduct_primeUnit_neg_one
import Submission.Work.HilbertSymbol.placeProduct_primeUnit_primeUnit
import Submission.Work.HilbertSymbol.placeProduct_primeUnit_primeUnit_distinct_odd
import Submission.Work.HilbertSymbol.placeProduct_primeUnit_self_odd
import Submission.Work.HilbertSymbol.placeProduct_primeUnit_two_odd
import Submission.Work.HilbertSymbol.placeProduct_sq_left
import Submission.Work.HilbertSymbol.placeProduct_sq_right
import Submission.Work.HilbertSymbol.placeProduct_two_two
import Submission.Work.HilbertSymbol.primeUnit_eq_intUnit
import Submission.Work.HilbertSymbol.signOf_epsZ_primeUnit
import Submission.Work.HilbertSymbol.signOf_intCast
import Submission.Work.HilbertSymbol.signOf_omegaZ_primeUnit
import Submission.Work.HilbertSymbol.unitPart_neg
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

import Mathlib
import Submission.NK.CFTLib.Existence.isUnramified_of_normClassSubgroup_le_integralIdeles_two
import Submission.NK.NUV2.LC.hilbertSymbolNormCriterion
import Submission.NK.NUV2.LC.hilbertSymbolAt_independent
import Submission.Work.HilbertSymbol.All
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Vocabulary wrapper for the general-number-field Hilbert symbol chapter

This module only re-exports the vocabulary needed to *state* the general-number-field Hilbert
symbol and its properties, so that delegated statements about them can declare their `depends_on`
entirely inside `Submission/Work`:

* `NK.NUV2.LC.hilbertSymbol`, `NK.NUV2.LC.hilbertSymbolAt` — the canonical `2`-torsion local
  Hilbert symbol over an arbitrary field `F` with a local reciprocity datum `R`, together with its
  norm criterion `NK.NUV2.LC.hilbertSymbol_eq_one_iff_normGroup`, multiplicativity in the first
  variable (`NK.NUV2.LC.hilbertSymbolAt_mul`) and independence of the chosen square root
  (`NK.NUV2.LC.hilbertSymbolAt_independent`);
* `NK.NUV2.LC.IsLocalNorm`, `NK.GlobalCFT.Place`, `NK.GlobalCFT.Idele` — the global local-norm
  condition at a place of a number field;
* `NK.CFTLib.IdeleHasse.badSet_not_singleton` — the proved Hilbert reciprocity
  ("Hasse's norm theorem with one place omitted") for cyclic extensions of number fields;
* `NK.CFTLib.IdeleHasse.mem_normImage_iff_localNorm` — the local–global principle for idèle norms;
* `NK.CFTLib.IdeleHasse.badSet_not_singleton`'s bridges
  `NK.CFTLib.Existence.isLocalNorm_iff_exists_idele` and
  `NK.CFTLib.Existence.isLocalNorm_of_exists_idele_ofFinite`;
* `NK.NUV2.LC.HilbertReciprocityTwo` — the global product formula for quadratic extensions
  ("the set of places at which `x` fails to be a local norm is finite of even cardinality"),
  together with its corollary `NK.NUV2.LC.HilbertReciprocityTwo.eq_empty_of_subset_singleton`;
* `Work.HilbertSymbol.hilbertReciprocity_prod` — the proved Hilbert reciprocity over `ℚ`, i.e.
  step 4 of the road to `HilbertReciprocityTwo`.
-/

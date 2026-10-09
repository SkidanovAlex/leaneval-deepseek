import Mathlib
import Submission.NK.GlobalCFT.Place
import Submission.Commons.RingTheory.Henselian.adicCompletionMap_liesOver
import Submission.Commons.NumberTheory.NumberField.Completion.val_adicCompletionMap_eq_pow
import Submission.Commons.NumberTheory.NumberField.Completion.isIntegralClosure_adicCompletionIntegers_extension
import Submission.Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion
import Submission.Commons.NumberTheory.NumberField.Completion.exists_uniformizer_val_eq_exp_neg_one
import Submission.NK.CFTLib.Arl.val_norm_one_add_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Import bundle: the local level-matching lemma for the idèlic norm

Nothing is proved here; this module only collects, for the convenience of the lemma
`Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.localNormFinite_sub_one_le_of_val`,
the imports that its statement and (suggested) proof need:

* `NK.GlobalCFT.Place.localNormFinite` — the local norm `N_{L_q/K_Q}` on unit groups;
* `Commons.RingTheory.Henselian.adicCompletionMap` — the underlying ring map `K_Q →+* L_q`;
* `Commons.NumberTheory.NumberField.Completion.val_adicCompletionMap_eq_pow` —
  `v (adicCompletionMap z) = (v z) ^ e` (`e` the ramification index);
* `...module_finite_adicCompletion`, `...isIntegralClosure_adicCompletionIntegers_extension` —
  the finiteness/integral-closure inputs of the proof of `NK.CFTLib.Arl.val_norm_one_add_le`,
  whose argument generalises verbatim from a rational integer `m` to an element `y` of the ring of
  integers `Q.adicCompletionIntegers K` of the `Q`-adic completion;
* `...exists_uniformizer_val_eq_exp_neg_one` — the uniformizer `π` with `v π = exp (-1)`.
-/

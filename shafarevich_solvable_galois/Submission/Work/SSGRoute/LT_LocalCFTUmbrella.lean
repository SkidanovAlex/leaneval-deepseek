import Mathlib
import Submission.NK.LocalCFT.Basic
import Submission.NK.LocalReciprocity.le_maxAbelianSubext_of_commutative
import Submission.NK.LocalReciprocity.commutator_gal_maxAbelianSubext
import Submission.NK.LocalReciprocityLubinTate.Target
import Submission.NK.NUV2.kernelCondition_all
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Umbrella re-export of the local class field theory vocabulary used by the `LT` local pairing lane

This module only re-exports, for the use of the delegated lemmas in
`Submission/Work/SSGRoute/LT_*`, the local class field theory API of `Submission.NK`:

* `NK.LocalCFT.ArtinReciprocity` (`artin : Fˣ →* AbGal F F'`, `isLevelIso` at every finite abelian
  level, `cofinal`), together with `NK.LocalCFT.AbGal` and the restriction
  `NK.LocalCFT.levelRestrict`;
* the maximal abelian subextension `NK.LocalReciprocity.maxAbelianSubext` with its two structural
  lemmas (`commutator_gal_maxAbelianSubext`, `le_maxAbelianSubext_of_commutative`);
* the existence of the reciprocity datum at every completion of a number field
  (`NK.LocalReciprocityLubinTate.artinReciprocity_adicCompletion` from
  `NK.NUV2.kernelCondition_all`).

Nothing is proved here.
-/

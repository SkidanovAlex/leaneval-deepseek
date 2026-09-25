import Submission.NK.LocalReciprocity.Prelude
import Submission.NK.LocalReciprocity.NormGroup
import Submission.NK.LocalReciprocity.NormGroupTower
import Submission.NK.LocalReciprocity.LocalSetup
import Submission.NK.LocalReciprocity.exists_isFrobeniusLocal
import Submission.NK.LocalReciprocity.isFrobeniusLocal_unique
import Submission.NK.LocalReciprocity.isFrobeniusLocal_pow_val
import Submission.NK.LocalReciprocity.orderOf_eq_inertiaDeg_of_isFrobeniusLocal
import Submission.NK.LocalReciprocity.Frobenius
import Submission.NK.LocalReciprocity.ArtinUnramified
import Submission.NK.LocalReciprocity.index_normGroup_eq_finrank
import Submission.NK.LocalReciprocity.NormGroupIndexUnramified
import Submission.NK.LocalReciprocity.localRestrict_frobeniusLocal
import Submission.NK.LocalReciprocity.localRestrict_artinUnramified
import Submission.NK.LocalReciprocity.Reciprocity
import Submission.NK.LocalReciprocity.commutator_gal_maxAbelianSubext
import Submission.NK.LocalReciprocity.normGroup_sup_eq_inf
import Submission.NK.LocalReciprocity.le_maxAbelianSubext_of_commutative
import Submission.NK.LocalReciprocity.MaxAbelianSetup
import Submission.NK.LocalReciprocity.artinHom_surjective
import Submission.NK.LocalReciprocity.exists_levelMap_normGroup_le
import Submission.NK.LocalReciprocity.exists_mulEquiv_completion_maxAbelian
import Submission.NK.LocalReciprocity.Invariants
import Submission.NK.LocalReciprocity.LubinTate

/-!
# The local reciprocity chapter

Everything under `Submission/Work/LocalReciprocity/` in one import.  The main entry points are

* `NK.LocalReciprocity.normGroup` — the norm group `N_{E/F} Eˣ`, with its transitivity
  (`normGroup_trans`, the first class-formation axiom) and the local-field instance
  `normGroup_adicCompletion_tower`;
* `NK.LocalReciprocity.frobeniusLocal` / `NK.LocalReciprocity.artinUnramified` /
  `NK.LocalReciprocity.artinUnramifiedEquiv` — the canonical (Frobenius-normalised) Artin map of
  an *unramified* local extension, its surjectivity, kernel, index formula and canonicity
  (`eq_artinUnramified_of`);
* `NK.LocalReciprocity.localRestrict_frobeniusLocal` /
  `NK.LocalReciprocity.localRestrict_artinUnramified` — functoriality of those Artin maps with
  respect to restriction along a tower `K ⊆ L ⊆ M`;
* `NK.LocalReciprocity.index_normGroup_eq_finrank` /
  `NK.LocalReciprocity.index_normGroup_eq_finrank_of_ramificationIdx_eq_one` — the norm index;
* `NK.LocalReciprocity.LocalReciprocityDatum` — the reciprocity datum (the canonical family of
  reciprocity isomorphisms: the Lubin–Tate/existence input), with
  `NK.LocalReciprocity.LocalReciprocityDatum.artinLevelMulEquiv` (the canonical finite-level
  reciprocity isomorphism) and `NK.LocalReciprocity.normGroup_sup_eq_inf` (the second
  class-formation axiom);
* `NK.LocalReciprocity.exists_mulEquiv_completion_maxAbelian` — the infinite-level reciprocity
  `κˣ^{∧} ≅ G_κ^{ab}` conditional on the datum;
* `NK.LocalReciprocity.Invariants` — transfer of the group-theoretic invariants of
  `Submission.NK.LocalAnabelian` along that isomorphism (residue-characteristic detection and the
  `p`-adic rank), conditional on the arithmetic of `κˣ`;
* `NK.LocalReciprocity.LubinTateInput` — the explicit statement of the remaining input.
-/

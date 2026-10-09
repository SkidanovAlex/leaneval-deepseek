import Submission.NK.LocalCFT.Basic
import Submission.NK.LocalCFT.Functoriality.levelMulEquiv_restrict
import Submission.NK.LocalCFT.Functoriality.artin_eq_of_comp_levelRestrict_eq
import Submission.NK.LocalCFT.NormGroup.normGroup_le_iff
import Submission.NK.LocalCFT.NormGroup.normGroup_eq_iff
import Submission.NK.LocalCFT.NormGroup.normGroup_sup_eq_inf
import Submission.NK.LocalCFT.Completion.exists_mulEquiv_unitsCompletion
import Submission.NK.LocalCFT.NilpotentObstruction.commutator_eq_commutator_commutator
import Submission.NK.LocalCFT.NilpotentObstruction.isMulCommutative_of_abelian_sup_commutator_eq_top
import Submission.NK.LocalCFT.NilpotentObstruction.not_nonempty_localReciprocityDatum_of_galoisQuotient
import Submission.NK.LocalCFT.Reduction.Defs
import Submission.NK.LocalCFT.Reduction.nonempty_artinReciprocity_of_reciprocityLaw
import Submission.NK.LocalCFT.Reduction.reciprocityLaw_of_artinReciprocity
import Submission.NK.LocalCFT.Reduction.existenceTheorem_of_abstract
import Submission.NK.LocalCFT.Reduction.Classical
import Submission.NK.LocalCFT.Units.numIndexSubgroups_le_of_commutative
import Submission.NK.LocalCFT.Units.not_hasUnboundedTowerRank_of_commutative
import Submission.NK.LocalCFT.Units.Invariants
import Submission.NK.LocalCFT.Units.Structure
import Submission.NK.LocalCFT.Instance.artinReciprocity_complex
import Submission.NK.LocalCFT.Instance.completionUnits_complex
import Submission.NK.LocalCFT.Brauer.Basic
import Submission.NK.LocalCFT.Brauer.localH2Nonvanishing_iff_surviving
import Submission.NK.LocalCFT.Brauer.exists_ne_zero_H2Profinite_of_mulEquiv
import Submission.NK.LocalCFT.Brauer.localH2Input_of_nonvanishing
import Submission.NK.LocalCFT.Brauer.exists_ne_zero_H2_of_finite_cyclic
import Submission.NK.LocalCFT.Brauer.localH2Nonvanishing_iff_finite
import Submission.NK.LocalCFT.Brauer.localH2Nonvanishing_of_finite_cyclic
import Submission.NK.LocalCFT.Brauer.localFieldBrauerCyclic_complex
import Submission.NK.LocalCFT.Brauer.Twist
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `NK.LocalCFT` chapter: local class field theory for `p`-adic fields

Everything under `Submission/Work/LocalCFT/` in one import.  The main entry points are

* `NK.LocalCFT.ArtinReciprocity F F'` (`Basic.lean`) — **the corrected canonical reciprocity
  datum** of local class field theory: `artin : Fˣ →* Gal(F^{ab}/F)` inducing the reciprocity
  isomorphisms `Fˣ ⧸ N_{L/F} Lˣ ≃* Gal(L/F)` at all finite abelian levels, with the existence
  theorem (cofinality of the norm groups).  This is the *satisfiable* form of
  `NK.LocalReciprocity.LocalReciprocityDatum`; see the module docstring of `Basic.lean` and the
  `README.md`;
* `NK.LocalCFT.Completion.exists_mulEquiv_unitsCompletion` — the infinite-level reciprocity
  `Fˣ^{∧} ≃* G_F^{ab}`, the interface the downstream developments consume;
* `NK.LocalCFT.Reduction.nonempty_artinReciprocity_of_reciprocityLaw` — the reduction of the
  datum to the two classical inputs `NK.LocalCFT.ReciprocityLaw` (the reciprocity law at each
  finite abelian level, compatibly) and `NK.LocalCFT.ExistenceTheorem`;
* `NK.LocalCFT.NormGroup.normGroup_le_iff`, `normGroup_eq_iff`, `normGroup_sup_eq_inf`, and
  `NK.LocalCFT.Functoriality.levelMulEquiv_restrict`,
  `NK.LocalCFT.Functoriality.artin_eq_of_comp_levelRestrict_eq` — functoriality and the
  norm-group description of the Artin map;
* `NK.LocalCFT.NilpotentObstruction.not_nonempty_localReciprocityDatum_of_galoisQuotient` — the
  formal refutation of the sibling's `LocalReciprocityDatum` (hence of
  `NK.LocalReciprocity.LubinTateInput`) as soon as `G_F` has a nonabelian nilpotent Galois
  quotient, which is the case for every `p`-adic field;
* `NK.LocalCFT.Brauer.Basic` — the local Brauer input `H²(G_κ, ℤ/p) ≅ ℤ/p`
  (`NK.BrauerHasse.LocalFieldBrauerCyclic`) and its reductions;
* `NK.LocalCFT.Units.Invariants` — the unit-group invariants of `G_κ^{ab}`, and the proof that
  the tower-rank invariant vanishes on `G_κ^{ab}` (so the residue characteristic cannot be read off
  from the abelianised Galois group).

See `README.md` for the full account, the conventions, and the honest list of what is *not* proved.
-/

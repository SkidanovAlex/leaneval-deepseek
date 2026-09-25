import Submission.Work.RelatorRank.Consequences
import Submission.Work.RelatorRank.ElementaryQuotient
import Submission.Work.RelatorRank.ProP
import Submission.Work.RelatorRank.Transfer.hasProP2Presentation_pad_generators
import Submission.Work.RelatorRank.Transfer.ker_lift_comp_mulEquiv
import Submission.Work.RelatorRank.Transfer.hasAbstractPresentation_of_mulEquiv
import Submission.Work.RelatorRank.GeneratorRank.hasDenseGeneratingFamily_of_continuous_surjective
import Submission.Work.RelatorRank.GeneratorRank.le_generatorRank_of_surjective_elementaryAbelian
import Submission.Work.RelatorRank.GeneratorRank.exists_card_frattiniQuotient_eq_two_pow
import Submission.Work.RelatorRank.GeneratorRank.generatorRank_eq_log_card_frattiniQuotient
import Submission.Work.RelatorRank.DenseGenerating.denseGenerating_iff_forall_openNormalSubgroup
import Submission.Work.RelatorRank.ProPFrattini.pFrattini_normal
import Submission.Work.RelatorRank.ProPFrattini.eq_top_of_sup_pFrattini_eq_top
import Submission.Work.RelatorRank.ProPFrattini.denseGenerating_of_sup_pFrattini
import Submission.Work.RelatorRank.API.hasProP2Presentation_zero_iff
import Submission.Work.RelatorRank.API.hasDenseGeneratingFamily_zero_iff
import Submission.Work.RelatorRank.Abstract.genRank_eq_dGens
import Submission.Work.RelatorRank.Abstract.hasAbstractPresentation_iff_exists_hasPresentation
import Submission.Work.RelatorRank.Cohomology.card_continuousHom_eq_two_pow_generatorRank
import Submission.Work.RelatorRank.Counterexample.aut_not_transitive_on_generating_pairs
import Submission.Work.RelatorRank.Instance.abstractRelatorHalfOf_elementaryAbelian
import Submission.Work.RelatorRank.Instance.abstractRelatorHalfOf_commutative
import Submission.Work.RelatorRank.Discrete
import Submission.Work.RelatorRank.Gaschutz.frattini_nongenerating_of_fg
import Submission.Work.RelatorRank.Gaschutz.eq_of_normalClosure_sup_frattini_eq_top
import Submission.Work.RelatorRank.Gaschutz.NormalGeneration
import Submission.Work.RelatorRank.CohomologyH2
import Submission.Work.Gaschutz.schanuel_corrected
import Submission.Work.RelatorRank.Dictionary
-- NOTE (session 6, operator): the module
-- `Submission.Work.RelatorRank.Gaschutz.kernel_eq_of_align` was DELETED from the source tree by a
-- concurrent refactor (only its build artefacts remain), which broke the library build for every
-- importer of this file.  Nothing in the workspace referenced the deleted theorem (checked), so the
-- import is dropped here to restore the build.  If the module is restored, re-add the import.
import Submission.Work.RelatorRank.Gaschutz.exists_aut_align_two

/-!
# `Work.RelatorRank` -- the relation-rank chapter, all at once

**Namespace** `Work.RelatorRank`; module `Submission.Work.RelatorRank.All`.

One import for the whole chapter.  See `README.md` in this directory for the map and, in
particular, for the precise statement of the single group-theoretic input that is *not* proved here
(the invariance of the minimal number of relators, i.e. `r(Γ) = dim_{𝔽₂} H²(Γ, 𝔽₂)` for finitely
generated pro-`2` groups).
-/

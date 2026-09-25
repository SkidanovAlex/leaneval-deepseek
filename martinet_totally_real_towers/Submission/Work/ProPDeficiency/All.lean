import Submission.Work.ProPDeficiency.Basic
import Submission.Work.ProPDeficiency.HomRank
import Submission.Work.ProPDeficiency.GolodShafarevich
import Submission.Work.ProPDeficiency.Deficiency
import Submission.Work.ProPDeficiency.Quotients
import Submission.Work.ProPDeficiency.Arithmetic
import Submission.Work.ProPDeficiency.Specialisations
import Submission.Work.ProPDeficiency.FrattiniGenerators
import Submission.Work.ProPDeficiency.FiniteDeficiency
import Submission.Work.ProPDeficiency.pHomDim_le_dGens
import Submission.Work.ProPDeficiency.card_homFp_eq_pow_pHomDim
import Submission.Work.ProPDeficiency.dGens_eq_log_card_frattini
import Submission.Work.ProPDeficiency.dGens_eq_pHomDim_of_isPGroup
import Submission.Work.ProPDeficiency.dGens_eq_pHomDim_of_maximal_finiteIndex
import Submission.Work.ProPDeficiency.dGens_freeGroup
import Submission.Work.ProPDeficiency.dGens_zmod_pow
import Submission.Work.ProPDeficiency.dGens_quotient_frattini
import Submission.Work.ProPDeficiency.le_dGens_of_surjective_zmod_pow
import Submission.Work.ProPDeficiency.hasPresentation_of_isPresentation
import Submission.Work.ProPDeficiency.isPresentation_of_groupPresentation
import Submission.Work.ProPDeficiency.nonempty_equiv_frattini_zmod_pow
import Submission.Work.ProPDeficiency.card_le_rel_card_of_finite

/-!
# The pro-`p` deficiency chapter: everything at once

**Namespace** `Work.ProPDeficiency`; module `Submission.Work.ProPDeficiency.All`.

Imports the whole chapter (see `README.md` in this directory for the map).  A caller who wants
everything imports this module; a caller who wants a minimal dependency set imports
`Submission.Work.ProPDeficiency.Arithmetic` (the packaged conclusion) or
`Submission.Work.ProPDeficiency.GolodShafarevich` (the criterion) instead.

Every module of the chapter is imported here, including
`dGens_eq_pHomDim_of_maximal_finiteIndex` (the `d = dim H¹` equality under the extra hypothesis
that every maximal subgroup has finite index).
-/

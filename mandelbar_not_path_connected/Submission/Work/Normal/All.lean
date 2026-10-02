import Submission.Work.Normal.Basic
import Submission.Work.Normal.FilledJulia
import Submission.Work.Normal.Frontier
import Submission.Work.Normal.Invariance
import Submission.Work.Normal.JuliaBasics
import Submission.Work.Normal.JuliaIterate
import Submission.Work.Normal.Perfect
import Submission.Work.Normal.Preimages
import Submission.Work.Normal.Tricorn
import Submission.Work.Normal.TricornDynamics
import Submission.Work.Normal.TricornJulia
import Submission.Work.Normal.compl_filledJuliaSet_subset_fatouSet
import Submission.Work.Normal.escapeRadius
import Submission.Work.Normal.filledJuliaSet_interior_subset_fatouSet
import Submission.Work.Normal.isCompact_juliaSet
import Submission.Work.Normal.isCoerciveContinuous_of_isPolynomialMapOfDegree
import Submission.Work.Normal.juliaSet_comp_self
import Submission.Work.Normal.juliaSet_infinite
import Submission.Work.Normal.juliaSet_subset_filledJuliaSet
import Submission.Work.Normal.mandelbar_iff_criticalOrbitBounded
import Submission.Work.Normal.montel_locallyBounded
import Submission.Work.Normal.montel_omits_three
import Submission.Work.Normal.poly_eval_surjective
import Submission.Work.Normal.poly_unique_root_factorization
import Submission.Work.Normal.tendstoLocallyUniformlyAtTop_comp_of_isCoerciveContinuous
import Submission.Work.Normal.tendstoLocallyUniformlyOn_comp_continuous
import Submission.Work.Normal.unique_preimage_mem_fatou

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Entry point for the `Work.Normal` area

Importing this module gives the whole chapter: normal families and Montel's theorems, the escape
radius and the filled Julia set, `JuliaSet f = frontier (FilledJuliaSet f)`, the complete invariance
of the Fatou and Julia sets, density of iterated preimages, perfectness of the Julia set, and the
tricorn specialisation `TantibarSq c`.  See `Submission/Work/Normal/NOTES.md`.
-/

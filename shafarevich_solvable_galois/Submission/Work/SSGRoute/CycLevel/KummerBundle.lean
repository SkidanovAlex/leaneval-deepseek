import Mathlib
import Submission.Work.SSGRoute.CycLevel.GrunwaldImports
import Submission.NK.UchidaKummer.Kummer.localDeg_kummerField_eq_one_iff
import Submission.NK.UchidaKummer.Kummer.isKummerLocalDichotomy_of_exists_isPrimitiveRoot
import Submission.NK.LocalAnabelian.Kummer.isGalois_kummerField_and_finrank
import Submission.NK.LocalAnabelian.Kummer.Defs
import Submission.Commons.NumberTheory.NumberField.Set.hasDirichletDensity_primes_splitsCompletely
import Submission.Commons.NumberTheory.NumberField.Set.hasDirichletDensity_zero_of_finite
import Submission.Commons.NumberTheory.NumberField.Set.hasDirichletDensity_union_of_density_zero
import Submission.Commons.NumberTheory.NumberField.Set.hasDirichletDensity_compl
import Submission.Commons.NumberTheory.NumberField.ncard_primesOver_eq_finrank_iff_splitCompletely
import Submission.NK.Mine.Generation
import Submission.Work.SSGRoute.PTW.mem_pthPower_of_all_open_index_p_subgroups
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Import bundle for the per-place Grünwald development

Bundles the Kummer/locality vocabulary (`NK.LocalAnabelian.kummerField`,
`NK.UchidaKummer.Kummer.localDeg_kummerField_eq_one_iff`), the Čebotarev split-density input
(`Commons.NumberTheory.NumberField.Set.hasDirichletDensity_primes_splitsCompletely`) and the
`p`-power criterion in the idèle class group
(`Work.SSGRoute.PTW.mem_pthPower_of_all_open_index_p_subgroups`), so that the pieces of
`Work.SSGRoute.CycLevel.grunwald_odd_single_place` can be requested with a `depends_on`.
-/

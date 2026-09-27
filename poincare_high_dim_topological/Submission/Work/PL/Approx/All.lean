/-
# Area A5 (`Work.PL.Approx`): PL approximation in a cube

Single import for the whole area: G5 `pl_approx` and its frozen variants, together with the
cutoff API, the vertex interpolant, the mesh/compactness helpers, the barycentric bridge
`sdSubdiv`, the frozen-face machinery `Sd/exists_frozen_faces`, and the counterexample
`Ex/not_restrictsTo` for the `RestrictsTo` hypothesis.

See `NOTES_APPROX.md` in this directory for the interface and the usage recipe.
-/

import Submission.Work.PL.Approx.Clamp.clamp_eq_of_mem
import Submission.Work.PL.Approx.Clamp.clamp_eq_right
import Submission.Work.PL.Approx.Clamp.clamp_mem
import Submission.Work.PL.Approx.Clamp.continuous_clamp
import Submission.Work.PL.Approx.Continuous.continuousOn_g
import Submission.Work.PL.Approx.Continuous.dist_add_smul_sub_le
import Submission.Work.PL.Approx.Cutoff.continuous_cubeCut
import Submission.Work.PL.Approx.Cutoff.cubeCut_eq_one
import Submission.Work.PL.Approx.Cutoff.cubeCut_eq_one_of_mem
import Submission.Work.PL.Approx.Cutoff.cubeCut_eq_zero
import Submission.Work.PL.Approx.Cutoff.cubeCut_mem
import Submission.Work.PL.Approx.Cutoff.cubeCut_ne_zero
import Submission.Work.PL.Approx.Defs
import Submission.Work.PL.Approx.Ex.Defs
import Submission.Work.PL.Approx.Ex.not_restrictsTo
import Submission.Work.PL.Approx.Finite.abs_apply_le_dist_zero
import Submission.Work.PL.Approx.Finite.dist_lt_of_mesh
import Submission.Work.PL.Approx.Finite.exists_delta_of_continuousOn
import Submission.Work.PL.Approx.Finite.isCompact_space_of_finite
import Submission.Work.PL.Approx.Frozen.eq_of_mem_frozen
import Submission.Work.PL.Approx.Frozen.pl_approx_frozen_at
import Submission.Work.PL.Approx.Frozen.pl_approx_frozen_faces
import Submission.Work.PL.Approx.Frozen.pl_approx_frozen_fine
import Submission.Work.PL.Approx.Frozen.pl_approx_frozen_sub
import Submission.Work.PL.Approx.Interp.eqOn_simp_of_eqOn
import Submission.Work.PL.Approx.Interp.exists_affineMap_eqOn
import Submission.Work.PL.Approx.Interp.exists_glue
import Submission.Work.PL.Approx.Interp.exists_interp
import Submission.Work.PL.Approx.Near.dist_lt_of_linOn
import Submission.Work.PL.Approx.Near.oscillation_of_mesh
import Submission.Work.PL.Approx.Sd.exists_frozen_faces
import Submission.Work.PL.Approx.Sd.simp_subset_face_of_union
import Submission.Work.PL.Approx.SdMain
import Submission.Work.PL.Approx.SdSubdiv
import Submission.Work.PL.Approx.Seg.continuous_seg
import Submission.Work.PL.Approx.Seg.seg_eq_one
import Submission.Work.PL.Approx.Seg.seg_eq_zero
import Submission.Work.PL.Approx.Seg.seg_mem
import Submission.Work.PL.Approx.Seg.seg_ne_zero
import Submission.Work.PL.Approx.pl_approx
import Submission.Work.PL.Approx.pl_approx_frozen
import Submission.Work.PL.Approx.pl_approx_frozen_of_osc
import Submission.Work.PL.Approx.pl_approx_of_osc

/-! ## Axiom audit of the headline results -/

#print axioms Work.PL.Approx.pl_approx
#print axioms Work.PL.Approx.pl_approx_of_osc
#print axioms Work.PL.Approx.pl_approx_frozen
#print axioms Work.PL.Approx.pl_approx_frozen_of_osc
#print axioms Work.PL.Approx.Frozen.pl_approx_frozen_faces
#print axioms Work.PL.Approx.Frozen.pl_approx_frozen_sub
#print axioms Work.PL.Approx.Frozen.pl_approx_frozen_at
#print axioms Work.PL.Approx.Frozen.pl_approx_frozen_fine
#print axioms Work.PL.Approx.Sd.exists_frozen_faces
#print axioms Work.PL.Approx.pl_approx_sd
#print axioms Work.PL.Approx.pl_approx_of_osc_of_mesh
#print axioms Work.PL.Approx.pl_approx_LinOn
#print axioms Work.PL.Approx.pl_approx_frozen_LinOn
#print axioms Work.PL.Approx.Ex.not_restrictsTo

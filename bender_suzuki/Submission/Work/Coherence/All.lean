import Submission.Work.Coherence.Inner
import Submission.Work.Coherence.Defs
import Submission.Work.Coherence.Basic
import Submission.Work.Coherence.Isometry
import Submission.Work.Coherence.Coherent
import Submission.Work.Coherence.Bridge
import Submission.Work.Coherence.sum_sq_eq_two
import Submission.Work.Coherence.norm_one_of_mem_zSpan
import Submission.Work.Coherence.norm_two_of_mem_zSpan
import Submission.Work.Coherence.norm_zero_of_mem_zSpan
import Submission.Work.Coherence.norm_two_diff_of_mem_zSpan
import Submission.Work.Coherence.inv_eq_conj_of_pow_eq_one
import Submission.Work.Coherence.char_inv_eq_conj
import Submission.Work.Coherence.irr_degree_pos
import Submission.Work.Coherence.irr_cfInner
import Submission.Work.Coherence.irr_conj
import Submission.Work.Coherence.irr_inv
import Submission.Work.Coherence.isVChar_conj
import Submission.Work.Coherence.NormIrr
import Submission.Work.Coherence.cfInner_span_eq
import Submission.Work.Coherence.orthonormal_phi
import Submission.Work.Coherence.isometryOnAll_extend
import Submission.Work.Coherence.coherent_of_isometry_extension
import Submission.Work.Coherence.exists_common_of_pairwise_inner_one
import Submission.Work.Coherence.exists_common_of_pairwise_inner_one_nonempty
import Submission.Work.Coherence.coherent_of_norm_two_lift

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Coherence`: the coherence area of the Feit–Thompson drive

Single entry point: `import Submission.Work.Coherence.All` gives the whole area (all definitions and
results listed in `Submission/Work/Coherence/NOTES.md`).
-/

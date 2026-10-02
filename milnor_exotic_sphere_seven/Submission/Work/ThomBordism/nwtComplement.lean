import Mathlib
import Submission.Work.ThomBordism.nwtDefs
import Submission.Work.ThomBordism.nwtKerComplP
import Submission.Work.ThomBordism.nwtComplI_complP

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

open scoped Manifold ContDiff Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-!
# The orthonormal complement data of the normal bundle

`Work.ThomBordism.complP`/`complI` (`nwtDefs.lean`) are the projection and the insertion of the
orthonormal normal bundle of the embedding `E`, in the coordinate spaces.  This file assembles them
into a `ComplementData` over the cover `CoverIdx V k`: the only facts needed are
`Work.ThomBordism.nwtKerComplP` (the kernel is the plane of the frame) and the chart-independence of
the plane (`range_coeffMap_frame_agree`); the remaining fields are the immediate identities
`complP_comp_complI` and the continuity lemmas of `nwtDefs.lean`.
-/

namespace Work.ThomBordism

open Work.ThomBordism.PontryaginThom Work.TangentClasses Work.Thom
open Work.ThomBordism.Grassmann

noncomputable section

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-- **The orthonormal complement data of the normal bundle** of `E` with normal data `ND`. -/
noncomputable def orthComplementData (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e) :
    ComplementData V.pt k (CoverIdx V k) where
  baseSet := ND.D.baseSet
  isOpen_baseSet := ND.D.isOpen_baseSet
  indexAt := ND.D.indexAt
  mem_baseSet_at := ND.D.mem_baseSet_at
  P := complP E ND
  I := complI E ND
  continuousOn_P := continuousOn_complP E ND
  continuousOn_I := continuousOn_complI E ND
  P_comp_I := complP_comp_complI E ND
  ker_agree := by
    have hf : ContMDiff (𝓡 8) (𝓡 (8 + k)) 1 E.e := E.smooth.of_le (by simp)
    intro i j x hi hj
    rw [nwtKerComplP E ND i hi, nwtKerComplP E ND j hj]
    exact range_coeffMap_frame_agree E.e hf (coverChart i) (coverChart j)
      (ND.baseSet_sub i.1 i.2 x hi) (ND.baseSet_sub j.1 j.2 x hj)

@[simp] theorem orthComplementData_baseSet (E : EmbeddingData V (8 + k))
    (ND : NormalData V k E.e) (i : CoverIdx V k) :
    (orthComplementData E ND).baseSet i = ND.D.baseSet i := rfl

@[simp] theorem orthComplementData_P (E : EmbeddingData V (8 + k))
    (ND : NormalData V k E.e) (i : CoverIdx V k) (x : V.pt) :
    (orthComplementData E ND).P i x = complP E ND i x := rfl

@[simp] theorem orthComplementData_I (E : EmbeddingData V (8 + k))
    (ND : NormalData V k E.e) (i : CoverIdx V k) (x : V.pt) :
    (orthComplementData E ND).I i x = complI E ND i x := rfl

end

end Work.ThomBordism

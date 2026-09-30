import Mathlib
import Submission.Work.BW.sieg2KernelDefs
import Submission.Work.BW.sieg2_PhiE_aux
import Submission.Work.BW.psiAssemble_mulVec
import Submission.Work.BW.Phi_surjective
import Submission.Work.BW.PhiE_ofLp_mulVec

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Surjectivity of `PhiE`

`PhiE a` is the matrix/coordinate model of the mixed-space map `Phi a`,
`y ↦ (∑_j mulK (a i j) (y j))_i`, in the orthonormal basis `stdOrthonormalBasis F` of the
Euclidean mixed space.  If the rows of `a` are `F`-linearly independent then `a` defines a
surjective `F`-linear map `F^N → F^M`; base-changing along `ℚ → ℝ` (equivalently, applying the
same matrix with `mulK`-entries) keeps it surjective, so `PhiE a` is surjective.
-/

open scoped Classical
open NumberField

namespace Work.BW

theorem sieg2_PhiE_surjective {F : Type*} [Field F] [NumberField F] {M N : ℕ}
    (a : Fin M → Fin N → F) (hli : LinearIndependent F a) :
    Function.Surjective (PhiE a) := by
  have hPhi : Function.Surjective (Phi a) := Phi_surjective a hli
  intro x
  obtain ⟨v, hv⟩ := hPhi (psiAssemble (F := F) M x.ofLp)
  refine ⟨WithLp.toLp 2 (psiAssembleInv (F := F) N v), ?_⟩
  -- The coordinate model of `Phi a` is `(PhiMat a).mulVec`.
  have h1 : (PhiE a (WithLp.toLp 2 (psiAssembleInv (F := F) N v))).ofLp
      = (PhiMat a).mulVec (psiAssembleInv (F := F) N v) := by
    rw [PhiE_ofLp_mulVec, WithLp.ofLp_toLp]
  -- `psiAssemble` conjugates `(PhiMat a).mulVec` to `Phi a`.
  have h2 : psiAssemble (F := F) M ((PhiMat a).mulVec (psiAssembleInv (F := F) N v))
      = psiAssemble (F := F) M x.ofLp := by
    rw [psiAssemble_mulVec, psiAssemble_psiAssembleInv]
    exact hv
  have h3 : (PhiMat a).mulVec (psiAssembleInv (F := F) N v) = x.ofLp :=
    psiAssemble_injective M h2
  exact (WithLp.equiv 2 (Fin M × NumberField.mixedEmbedding.index F → ℝ)).injective
    (h1.trans h3)

end Work.BW

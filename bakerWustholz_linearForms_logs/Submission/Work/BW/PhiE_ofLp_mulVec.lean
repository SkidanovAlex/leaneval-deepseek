import Mathlib
import Submission.Work.BW.sieg2_PhiE_aux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `PhiE a` is `PhiMat a` on coordinates

`PhiE a` is defined as `Matrix.toEuclideanLin (PhiMat a)`; unfolding `toEuclideanLin = toLpLin 2 2`
and the two `rfl`-lemmas `Matrix.ofLp_toLpLin` and `Matrix.toLpLin_apply` shows that on the
underlying coordinate spaces `PhiE a` is exactly multiplication by the matrix `PhiMat a`.
-/

namespace Work.BW

theorem PhiE_ofLp_mulVec {F : Type*} [Field F] [NumberField F] {M N : ℕ}
    (a : Fin M → Fin N → F)
    (x : EuclideanSpace ℝ (Fin N × NumberField.mixedEmbedding.index F)) :
    (PhiE a x).ofLp = (PhiMat a).mulVec x.ofLp := by
  rfl

end Work.BW

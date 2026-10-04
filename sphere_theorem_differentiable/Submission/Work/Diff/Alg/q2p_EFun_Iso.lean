import Mathlib
import Submission.Work.Diff.Alg.q2p_defs
import Submission.Work.Diff.Alg.q2p_secK_Iso

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The isotropic-curvature form `EFun` of the round sphere on orthogonal quadruples

`EFun (Iso n) x y z w = R(ζ, η, ζ̄, η̄)` with `ζ = x + iy`, `η = z + iw`, for the curvature tensor
`Iso n = δᵢₖ δⱼₗ - δᵢₗ δⱼₖ` of the unit round sphere.  Using the component identity
`R4 (Iso n) a b c d = ⟪a, c⟫ ⟪b, d⟫ - ⟪a, d⟫ ⟪b, c⟫` (`Work.Diff.Alg.R4_Iso`), for a quadruple
of mutually orthogonal vectors all cross terms vanish and

`EFun (Iso n) x y z w = (|x|² + |y|²) (|z|² + |w|²)`,

the value that makes `Iso n` lie in the interior of the `PIC2` cone exactly when `x` and `y`
(or `z` and `w`) are non-vanishing.  This is the normalization used by the quarter-pinching
algebra (`Work.Diff.Alg.quarter_to_pic2`).
-/

namespace Work.Diff.Alg

open Submission.Diff.Alg Finset
open Work.Diff.Alg.Q2P

/-- For four pairwise orthogonal vectors, the isotropic curvature of the round sphere `Iso n`
(equivalently `EFun`) is the product of the two squared lengths: all the cross terms in
`R4 (Iso n) a b c d = ⟪a, c⟫ ⟪b, d⟫ - ⟪a, d⟫ ⟪b, c⟫` vanish. -/
theorem q2p_EFun_Iso {n : ℕ} {x y z w : Fin n → ℝ} (h : Work.Diff.Alg.Q2P.PairwiseOrth x y z w) :
    Work.Diff.Alg.Q2P.EFun (Submission.Diff.Alg.Iso n) x y z w
      = (Submission.Diff.Alg.dot x x + Submission.Diff.Alg.dot y y) *
        (Submission.Diff.Alg.dot z z + Submission.Diff.Alg.dot w w) := by
  obtain ⟨hxy, hxz, hxw, hyz, hyw, hzw⟩ := h
  -- the reversed cross-orthogonality conditions
  have hzx : dot z x = 0 := by rw [dot_comm'' z x]; exact hxz
  have hwx : dot w x = 0 := by rw [dot_comm'' w x]; exact hxw
  have hzy : dot z y = 0 := by rw [dot_comm'' z y]; exact hyz
  have hwy : dot w y = 0 := by rw [dot_comm'' w y]; exact hyw
  simp only [EFun, R4_Iso]
  rw [hxz, hxw, hyz, hyw, hzx, hwx, hzy, hwy]
  ring

end Work.Diff.Alg

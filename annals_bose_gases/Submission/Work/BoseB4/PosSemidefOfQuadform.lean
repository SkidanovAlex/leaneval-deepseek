import Mathlib.LinearAlgebra.Matrix.PosDef
import Submission.Work.BoseB4.ModeFock
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB4

theorem PosSemidefOfQuadform {Mode : Type*} [Fintype Mode] [DecidableEq Mode]
    (K : Mode → Mode → ℝ)
    (hsym : ∀ i j, K i j = K j i)
    (hquad : ∀ v : Mode → ℝ, 0 ≤ ∑ i : Mode, ∑ j : Mode, v i * K i j * v j) :
    (Matrix.of K).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact Matrix.IsHermitian.ext (fun i j => by simpa using hsym j i)
  · intro x
    simpa [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc] using hquad x

end Work.BoseB4

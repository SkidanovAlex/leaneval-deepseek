import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseB4.BoxChi
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB4

/-- **Symmetry of FS's box kernel.**  `χ̂²` is even (`hatChiSq_neg`, since `χ̂²` is
the cosine transform of `χ²`), so its argument `ℓ(k−k')` may be replaced by
`ℓ(k'−k)`; the condensate term is symmetric by commutativity of multiplication. -/
theorem boxKernel_symm (B : Work.BoseB4.BoxData) (ℓ : ℝ) (k k' : EuclideanSpace ℝ (Fin 3)) :
    B.boxKernel ℓ k k' = B.boxKernel ℓ k' k := by
  have h : B.hatChiSq (ℓ • (k - k')) = B.hatChiSq (ℓ • (k' - k)) := by
    rw [← B.hatChiSq_neg (ℓ • (k - k')), ← smul_neg, neg_sub]
  rw [BoxData.boxKernel, BoxData.boxKernel, h]
  ring

end Work.BoseB4

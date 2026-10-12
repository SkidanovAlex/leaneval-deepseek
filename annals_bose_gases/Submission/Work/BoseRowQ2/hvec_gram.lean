import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseRowQ2.Tail_eq_gram_h
import Submission.Work.BoseRowQ2.maskSharpCore
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowQ2.hvec_gram`

The Gram product of the two deviation vectors `hvec HM μ k` (the orthogonal complement of
`(HM μ).f k` in the excited `θ`-span) is the lattice tail matrix `Tail (HM μ).N k j`.

This is the definitional unfolding of `hvec` composed with the proved identity
`Work.BoseRowQ2.Tail_eq_gram_h`, which states

    `Tail N k j = ∑_l (f k l − ∑_{i∈excited} Chat N k i · g i l) · (f j l − ∑_{i∈excited} Chat N j i · g i l)`

and the right-hand side is exactly `gram (hvec HM μ k) (hvec HM μ j)` by definition of
`Work.BoseB4.gram` and of `Work.BoseRowQ2.hvec`.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseRowQ2

/-- **`⟨h_k, h_j⟩ = Tail_{kj}`**: the Gram product of the deviations is the lattice tail
matrix. -/
theorem hvec_gram {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v} {fc fu : Work.BoseBoxFix.LowCut}
    (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ) (μ : ℝ)
    (k j : Work.BoseBoxFock.Lab (HM μ).N) :
    Work.BoseB4.gram (Work.BoseRowQ2.hvec HM μ k) (Work.BoseRowQ2.hvec HM μ j)
      = Work.BoseRowQ2.Tail (HM μ).N k j := by
  simpa only [Work.BoseB4.gram, hvec]
    using (Tail_eq_gram_h (h := h) (fc := fc) (fu := fu) HM μ k j).symm

end Work.BoseRowQ2

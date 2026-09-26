import Mathlib
import Submission.Work.Asymptotics.funnel_tauAtom_second_order
import Submission.Work.Kernels.TildeFacts.KPlus_z_tildeA
import Submission.Work.Asymptotics.KhatE1.Bracket24ClearedDefs

/-!
# Third-order expansion of `E₂ˢ` at the cusp

`E₂ˢ = E₂|₂S`, and the workspace proves `TildeFacts.E2S_eq : E₂ˢ(z) = E₂(z) - 6i/(πz)`.  Since
`S0z z = 1 - 6i/(πz)` (`KhatE1.S0z`), the `-6i/(πz)` terms cancel and

  `E₂ˢ(z) - (S0z z - 24 q - 72 q²) = E₂(z) - 1 + 24 q + 72 q²`,

which is exactly the remainder of the proved `Work.Asymptotics.E2Fun_second_order`.  This gives
the third-order cusp expansion of `E₂ˢ` used by the `K₊`-half of the `E(z)`-expansion of the
`Sh`-cleared `d = 24` bracket.
-/

namespace Work.Asymptotics.KhatE1Core

open UpperHalfPlane

noncomputable section

/-- **Third-order expansion of `E₂ˢ` on `{1 ≤ Im z}`**, in the form
`E₂ˢ = S0z - 24q - 72q² + O(q³)`. -/
theorem E2SThirdOrder :
    ∃ C : ℝ, 0 < C ∧ ∀ z : UpperHalfPlane, 1 ≤ z.im →
      ‖Work.Kernels.E2S z - (Work.Asymptotics.KhatE1.S0z z
          - 24 * Work.Kernels.qParamFun z
          - 72 * (Work.Kernels.qParamFun z) ^ 2)‖
        ≤ C * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
  obtain ⟨C, hC, h⟩ := Work.Asymptotics.E2Fun_second_order
  refine ⟨C, hC, fun z hz => ?_⟩
  have key : Work.Kernels.E2S z - (Work.Asymptotics.KhatE1.S0z z
        - 24 * Work.Kernels.qParamFun z - 72 * (Work.Kernels.qParamFun z) ^ 2)
      = Work.Kernels.E2Fun z - 1 + 24 * Work.Kernels.qParamFun z
        + 72 * (Work.Kernels.qParamFun z) ^ 2 := by
    simp only [Work.Kernels.TildeFacts.E2S_eq, Work.Asymptotics.KhatE1.S0z]
    ring
  rw [key]
  exact h z hz

end

end Work.Asymptotics.KhatE1Core

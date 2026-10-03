/-
# Area `A7` from the two scale regimes of Theorem `varp`

This file assembles the frozen contract's area `A7`

  `AreaA7 = ∀ P p₁ p₂, 2 ≤ P.natDegree → 1 < p₁,p₂ < ⊤ → p₁⁻¹+p₂⁻¹ ≤ 1 → (p₁,p₂) ≠ (2,2) →
              AreaA1 → VarpLossKMT P p₁ p₂`

from the two halves of the paper's §7/§8 analysis proved in `A7/SmallLoss.lean` and
`A7/LargeLoss.lean`, glued by the (proved) assembly `A7/varpLossKMT_of_small_large` of
`A7/Split.lean`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.SmallLoss
import Submission.Work.KMTAreas.A7.LargeLoss

set_option autoImplicit false

namespace Work.KMTAreas.A7

open scoped ENNReal NNReal

/-- **Area `A7`**: Theorem `varp` at every exponent pair `(p₁,p₂) ≠ (2,2)` with the controlled
loss `2^{Aρ·max(max l₁ l₂)(max s₁ s₂)}`, from area `A1` alone. -/
theorem areaA7_proof : Work.KMTContract.AreaA7 :=
  areaA7_of_halves SmallLoss LargeLoss

end Work.KMTAreas.A7

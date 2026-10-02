import Mathlib
import Submission.Work.StemsB.collarDelta_collarSPart
import Submission.Work.StemsB.collarSplit

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The splitting of the collar cohomology along the suspension class

For the collar pair `(Q, C) = (↥(sphLoopBig b) × Y, sphLoopCollarProd b Y)`, a Thom class `τ`, a
class `s` with `δ s = τ` (`Work.StemsB.CollarTransgresses`) and the transgression coefficient map
`Σ = collarSigma` (`π^*(Σ x) ⌣ τ = δ x`), this file records the **splitting**

  `x - π^*(Σ x) ⌣ s ∈ im i^*`   (`collarSplit`),

i.e. every class of `H^{m+b}(C)` is the sum of a class coming from `Q` and a multiple
`π^*(Σ x) ⌣ s` of the suspension class.  It is `Work.StemsB.collarSplit_of_delta` applied to the
`δ`-computation `Work.StemsB.collarDelta_collarSPart`.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.StemsB

noncomputable section

/-- **The splitting of the collar cohomology.**  For every `x : H^{m+b}(C)` there is `a : H^{m+b}(Q)`
with `x - π^*(Σ x) ⌣ s = i^* a`. -/
theorem collarSplit (b : ℕ) (hb : 1 ≤ b) (Y : Type) [TopologicalSpace Y]
    (τ : Work.Thom.RelCoh ℤ b (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y))
    (hτ : CollarThom (Y := Y) b τ)
    (s : (Work.Cohomology.singularCochainComplex ℤ
          (TopCat.of ↥(sphLoopCollarProd b Y))).homology (b - 1))
    (hs : CollarTransgresses b hb (Y := Y) s τ)
    (m : ℕ)
    (x : (Work.Cohomology.singularCochainComplex ℤ
          (TopCat.of ↥(sphLoopCollarProd b Y))).homology (m + b)) :
    ∃ a : (Work.Cohomology.singularCochainComplex ℤ
        (TopCat.of (↥(sphLoopBig b) × Y))).homology (m + b),
      x - collarSPart b hb (Y := Y) τ hτ s m x = collarRestr (Y := Y) b (m + b) a :=
  collarSplit_of_delta b hb Y τ hτ s m x
    (collarDelta_collarSPart b hb Y τ hτ s hs m x)

end

end Work.StemsB

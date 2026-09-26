import Submission.Work.CoreTopology.IntersectionNumberStandard
import Submission.Work.CoreTopology.Transport
import Submission.Work.CoreTopology.pardonsI_mapHomeomorph

/-!
# `I(F, β) = min p q` for a torus that is the image of the standard one

Pardon's theorem is applied not to the standard torus of revolution but to its image under an
ambient isotopy (a homeomorphism of `ℝ³`).  `Work.CoreTopology.pardonsI_mapHomeomorph` shows
that Pardon's invariant is unchanged by an ambient homeomorphism; combining it with
`Work.CoreTopology.pardonsI_standard` gives the computation `I(F, β) = min p q` for
`F = ψ(F_standard)` and `β = ψ((p,q)\text{-curve})`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.CoreTopology

noncomputable section

/-- **Deliverable 1, for a torus that is the image of the standard one under a homeomorphism of
`ℝ³`.**  Let `ψ` be a homeomorphism of `ℝ³`, let `F = ψ(F_standard)` be the image of the
standard torus of revolution, and let `β = ψ(β_standard)` be the image of the standard
`(p,q)`-curve, where `p, q > 0` are coprime.  Then `I(F, β) = min p q`. -/
theorem pardonsI_standard_mapHomeomorph (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hc : Nat.Coprime p q) (ψ : R3 ≃ₜ R3) :
    pardonsI (ParamTorus.mapHomeomorph ψ)
        (ClosedCurve.mapHomeomorph ψ (standardCurve p q)) = (Nat.min p q : ℕ∞) := by
  rw [pardonsI_mapHomeomorph]
  exact pardonsI_standard p q hp hq hc

end

end Work.CoreTopology

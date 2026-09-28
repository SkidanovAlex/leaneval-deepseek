import Mathlib
import Submission.Work.Kunneth.kronH_unconditional
import Submission.Work.Kunneth.cp2Cross

/-!
# The fundamental class of `ℂP² × ℂP²` and the Kronecker rule for it

The fundamental class of the oriented `8`-manifold `ℂP² × ℂP²` is the homology cross product
`[ℂP²] × [ℂP²] = homCrossLin _ _ 4 4 ([ℂP²] ⊗ [ℂP²])`, and the Kronecker pairing of a cross
product with it is the product of the pairings of the factors
(`Work.Kunneth.kronH_crossH_homCrossLin`).

This file is part of the *convention A* half of the chapter (the generic
`AddCommGroup.toIntModule` instance is removed, see `README.md` §5): it is where the tensor
product `[ℂP²] ⊗ [ℂP²]` is formed, matching the instance used by `Work.Kunneth.homCrossLin`.

## Main results

* `Work.Kunneth.cpFund` — the fundamental class `[ℂP²] × [ℂP²] ∈ H₈(ℂP² × ℂP²;ℤ)`;
* `Work.Kunneth.cpFund_pairing` — `⟨u × v, cpFund⟩ = ⟨u,[ℂP²]⟩·⟨v,[ℂP²]⟩`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct Simplicial

namespace Work.Kunneth

noncomputable section

open Work.Cohomology

attribute [-instance] AddCommGroup.toIntModule

/-- `ℂP²`, as a simplicial set. -/
abbrev cpX : SSet := Work.Projective.cp2SSet

/-- `ℂP² × ℂP²`, as a simplicial set. -/
abbrev cpZ : SSet := sProd cpX cpX

/-- The first projection `ℂP² × ℂP² ⟶ ℂP²`. -/
abbrev cpFst : cpZ ⟶ cpX := CategoryTheory.SemiCartesianMonoidalCategory.fst cpX cpX

/-- The second projection `ℂP² × ℂP² ⟶ ℂP²`. -/
abbrev cpSnd : cpZ ⟶ cpX := CategoryTheory.SemiCartesianMonoidalCategory.snd cpX cpX

/-- The fundamental class `[ℂP²] ∈ H₄(ℂP²;ℤ)`. -/
abbrev cpFund0 : ↥((sChain cpX).homology 4) := Work.Projective.cp2C

/-- **The fundamental class of `ℂP² × ℂP²`** as the homology cross product `[ℂP²] × [ℂP²]`. -/
abbrev cpFund : ↥((sChain cpZ).homology 8) :=
  homCrossLin cpX cpX 4 4 cp2_homology_projective cp2_homology_projective
    (cpFund0 ⊗ₜ[ℤ] cpFund0)

/-- **The Kronecker rule for the fundamental class of `ℂP² × ℂP²`**:
`⟨a × b, [ℂP²] × [ℂP²]⟩ = ⟨a, [ℂP²]⟩ · ⟨b, [ℂP²]⟩`. -/
theorem cpFund_pairing (u v : ↥((cochainC ℤ cpX).homology 4)) :
    kronH ℤ cpZ 8 (crossH cpX cpX 4 4 u v) cpFund
      = kronH ℤ cpX 4 u cpFund0 * kronH ℤ cpX 4 v cpFund0 :=
  kronH_crossH_homCrossLin cpX cpX 4 4 cp2_homology_projective cp2_homology_projective
    u v cpFund0 cpFund0

end

end Work.Kunneth

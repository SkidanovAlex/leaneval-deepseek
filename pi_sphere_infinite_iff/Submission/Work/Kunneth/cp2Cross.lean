import Mathlib
import Submission.Work.Kunneth.HomCross
import Submission.Work.Kunneth.cpn_kunneth_hypotheses
import Submission.Work.Kunneth.kunneth_h4_cp2cp2

/-!
# The cross products for `ℂP² × ℂP²`

Specialisation of the homology cross product and of the Kronecker rule to the case at hand for the
applications (the `ℂP² × ℂP²` Pontryagin numbers and the fundamental class): the homology of
`ℂP²` is free in every degree, so all the hypotheses of `Work.Kunneth.homCrossLin` and
`Work.Kunneth.kronH_homCrossLin` are discharged here, and the cross product
`H_p(ℂP²) ⊗ H_q(ℂP²) → H_{p+q}(ℂP² × ℂP²)` and its Kronecker rule are available with no
side conditions on the factors.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct Simplicial

namespace Work.Kunneth

noncomputable section

open Work.Cohomology

attribute [-instance] AddCommGroup.toIntModule

/-- The homology of `ℂP²` is free, hence projective, in every degree. -/
theorem cp2_homology_projective (n : ℕ) :
    Module.Projective ℤ ↥((sChain Work.Projective.cp2SSet).homology n) := by
  haveI : Module.Free ℤ ↥((sChain Work.Projective.cp2SSet).homology n) :=
    cpnHomology_free 2 n
  exact Module.Projective.of_free

/-- **The homology cross product for `ℂP² × ℂP²`**, with no side conditions. -/
noncomputable def cp2Cross (p q : ℕ) :
    ↥((sChain Work.Projective.cp2SSet).homology p
        ⊗ (sChain Work.Projective.cp2SSet).homology q) →ₗ[ℤ]
      ↥((sChain (sProd Work.Projective.cp2SSet Work.Projective.cp2SSet)).homology (p + q)) :=
  homCrossLin Work.Projective.cp2SSet Work.Projective.cp2SSet p q
    cp2_homology_projective cp2_homology_projective

/-- **The Kronecker rule for `ℂP² × ℂP²`**: `⟨α × β, x × y⟩ = ⟨α,x⟩·⟨β,y⟩`, for a normalized
`q`-cocycle `β` of `ℂP²` (representatives with this property exist for every class, see
`README.md` §6.1). -/
theorem kronH_cp2Cross (p q : ℕ)
    (x : ↥((sChain Work.Projective.cp2SSet).homology p))
    (y : ↥((sChain Work.Projective.cp2SSet).homology q))
    (α : Cochain ℤ Work.Projective.cp2SSet p) (β : Cochain ℤ Work.Projective.cp2SSet q)
    (hα : cochainDiff ℤ Work.Projective.cp2SSet α = 0)
    (hβ : cochainDiff ℤ Work.Projective.cp2SSet β = 0)
    (hn : ∀ z ∈ Work.Projective.cp2SSet.degenerate q, genEval ℤ Work.Projective.cp2SSet β z = 0)
    (hc : cochainDiff ℤ (sProd Work.Projective.cp2SSet Work.Projective.cp2SSet)
      (crossCochain Work.Projective.cp2SSet Work.Projective.cp2SSet p q α β) = 0) :
    kronH ℤ (sProd Work.Projective.cp2SSet Work.Projective.cp2SSet) (p + q)
        (cohomologyClassOf ℤ (sProd Work.Projective.cp2SSet Work.Projective.cp2SSet)
          (crossCochain Work.Projective.cp2SSet Work.Projective.cp2SSet p q α β) hc)
        (cp2Cross p q (x ⊗ₜ[ℤ] y))
      = kronH ℤ Work.Projective.cp2SSet p
          (cohomologyClassOf ℤ Work.Projective.cp2SSet α hα) x
        * kronH ℤ Work.Projective.cp2SSet q
          (cohomologyClassOf ℤ Work.Projective.cp2SSet β hβ) y :=
  kronH_homCrossLin Work.Projective.cp2SSet Work.Projective.cp2SSet p q
    cp2_homology_projective cp2_homology_projective x y α β hα hβ hn hc

end

end Work.Kunneth

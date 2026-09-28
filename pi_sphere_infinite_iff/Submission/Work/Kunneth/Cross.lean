import Mathlib
import Submission.Work.Kunneth.Basic
import Submission.Work.Cohomology.CupRing

/-!
# The cross product of cochains

For simplicial sets `X`, `Y`, `Work.Kunneth.crossCochain X Y p q α β` is the **cross product**
of a `p`-cochain `α` of `X` and a `q`-cochain `β` of `Y`:

  `(α × β)(σ, τ) = α(σ) · β(τ)`,

a cochain of degree `p+q` on `X ⊗ Y`.  It is the transpose of the Alexander–Whitney map
`Work.Kunneth.awGen`, and it is a cochain map
`C^p(X) ⊗ C^q(Y) ⟶ C^{p+q}(X ⊗ Y)`, i.e. `δ(α × β) = δα × β + (-1)^p α × δβ`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct Simplicial

namespace Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

/-- **The cross product of cochains** `C^p(X) × C^q(Y) → C^{p+q}(X ⊗ Y)`,
`(α × β)(σ,τ) = α(σ)·β(τ)`. -/
def crossCochain (X Y : SSet) (p q : ℕ)
    (α : Work.Cohomology.Cochain ℤ X p) (β : Work.Cohomology.Cochain ℤ Y q) :
    Work.Cohomology.Cochain ℤ (sProd X Y) (p + q) :=
  ModuleCat.Hom.hom (((sProd X Y).isColimitChainComplexXCofan zz (p + q)).desc
    (Cofan.mk zz (fun z => ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ ℤ
      (Work.Cohomology.genEval ℤ X α
          (Work.Cohomology.frontFace X p (p + q) (Nat.le_add_right p q) z.1) *
        Work.Cohomology.genEval ℤ Y β (backFaceLE Y q (p + q) (by omega) z.2))))))

end

end Work.Kunneth

import Mathlib
import Submission.Work.Kunneth.Cross
import Submission.Work.Cohomology.CupRing

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The computation rule for the cross product of cochains

`Work.Kunneth.crossCochain_apply` evaluates the cross product `α × β` of a `p`-cochain `α` of `X`
and a `q`-cochain `β` of `Y` on a `(p+q)`-simplex `z = (σ, τ)` of `X ⊗ Y`:

  `(α × β)(σ, τ) = α(σ_front) · β(τ_back)`.

The cross product is *defined* as the transpose of the Alexander–Whitney map, built through the
coproduct universal property of the singular chains `C_{p+q}(X ⊗ Y)`
(`Cofan.IsColimit.desc`), so the proof is a single application of `Cofan.IsColimit.fac`
(`genEval_desc_apply` below).
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct Simplicial

namespace Work.Kunneth

noncomputable section

/-- Computation rule for a morphism out of the coproduct of copies of `zz` that is the singular
`n`-chains of a simplicial set, built with `Cofan.IsColimit.desc`: evaluating it on the generator
attached to a simplex `z` gives the value of the corresponding component at `1`. -/
lemma genEval_desc_apply (X : SSet) (n : ℕ) (g : (z : X _⦋n⦌) → zz ⟶ zz) (z : X _⦋n⦌) :
    (IsColimit.desc (X.isColimitChainComplexXCofan zz n) (Cofan.mk zz g)).hom
        ((X.ιChainComplex (R := zz) z).hom 1) = (g z).hom 1 := by
  have h := Cofan.IsColimit.fac (X.isColimitChainComplexXCofan zz n) g z
  have h2 := congrArg (fun (m : zz ⟶ zz) => m.hom (1 : ℤ)) h
  rw [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  exact h2

theorem crossCochain_apply (X Y : SSet) (p q : ℕ)
    (α : Work.Cohomology.Cochain ℤ X p) (β : Work.Cohomology.Cochain ℤ Y q)
    (z : (Work.Kunneth.sProd X Y).obj (Opposite.op (SimplexCategory.mk (p + q)))) :
    Work.Cohomology.genEval ℤ (Work.Kunneth.sProd X Y) (Work.Kunneth.crossCochain X Y p q α β) z
      = Work.Cohomology.genEval ℤ X α
          (Work.Cohomology.frontFace X p (p + q) (Nat.le_add_right p q) z.1) *
        Work.Cohomology.genEval ℤ Y β (Work.Kunneth.backFaceLE Y q (p + q) (Nat.le_add_left q p) z.2) := by
  have h := genEval_desc_apply (sProd X Y) (p + q)
      (fun w => ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ ℤ
        (Work.Cohomology.genEval ℤ X α
            (Work.Cohomology.frontFace X p (p + q) (Nat.le_add_right p q) w.1) *
          Work.Cohomology.genEval ℤ Y β
            (Work.Kunneth.backFaceLE Y q (p + q) (Nat.le_add_left q p) w.2)))) z
  exact h.trans (by simp [LinearMap.toSpanSingleton_apply])

end

end Work.Kunneth

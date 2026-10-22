import Mathlib
import Submission.Work.TOOLKIT.Sigma.Defs

/-!
# Coproducts of kernels and cokernels

For an abelian category `C` in which coproducts of shape `J` are exact (AB4), the coproduct
of a family of kernels is canonically the kernel of the coproduct, and dually for cokernels.

This file contains the definitions of the canonical comparison maps; the statements that
they are isomorphisms are proved in the companion files
`Submission.Work.TOOLKIT.Sigma.sigmaKernel` and `Submission.Work.TOOLKIT.Sigma.sigmaCokernel`.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid
open scoped CategoryTheory.Pretriangulated.Opposite

namespace Work.TOOLKIT

noncomputable section

/-! ## The comparison maps -/

/-- The canonical comparison map `∐ j, kernel (g j) ⟶ kernel (Sigma.map g)` for a family of
morphisms `g j : A j ⟶ B j` in an abelian category. -/
noncomputable def sigmaKernelHom {C : Type*} [Category* C] [Abelian C] {J : Type}
    (A B : J → C) (φ : ∀ j, A j ⟶ B j)
    [HasCoproduct A] [HasCoproduct B] [HasCoproduct (fun j => kernel (φ j))] :
    (∐ fun j => kernel (φ j)) ⟶ kernel (Limits.Sigma.map φ) :=
  kernel.lift (Limits.Sigma.map φ)
    (Sigma.desc (fun j => kernel.ι (φ j) ≫ Sigma.ι A j)) (by
    apply Sigma.hom_ext
    intro j
    rw [Sigma.ι_comp_desc_assoc, Category.assoc, Sigma.ι_map]
    simp)

/-- The canonical comparison map `∐ j, cokernel (g j) ⟶ cokernel (Sigma.map g)` for a family of
morphisms `g j : A j ⟶ B j` in an abelian category. -/
noncomputable def sigmaCokernelHom {C : Type*} [Category* C] [Abelian C] {J : Type}
    (A B : J → C) (φ : ∀ j, A j ⟶ B j)
    [HasCoproduct A] [HasCoproduct B] [HasCoproduct (fun j => cokernel (φ j))] :
    (∐ fun j => cokernel (φ j)) ⟶ cokernel (Limits.Sigma.map φ) :=
  Sigma.desc (fun j =>
    cokernel.desc (φ j) (Sigma.ι B j ≫ cokernel.π (Limits.Sigma.map φ)) (by
      rw [← Category.assoc, ← Sigma.ι_map φ, Category.assoc,
        cokernel.condition, comp_zero]))

end

end Work.TOOLKIT

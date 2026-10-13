import Mathlib
import Submission.Work.DSEQ0.AugDefs

/-!
# The sections functor preserves kernels

For an open `V` of a scheme `X`, the sections functor
`Work.DSEQ0.sectionsV X V : X.Modules ⥤ AddCommGrpCat` is the composite

`X.Modules --toPresheaf--> (X.Opens)ᵒᵖ ⥤ AddCommGrpCat --ev (op V)--> AddCommGrpCat`.

Both factors preserve limits: the forgetful functor `toPresheaf` from sheaves of `𝒪_X`-modules
to presheaves of abelian groups creates limits (it is a right adjoint), and evaluation at a
point of a functor category preserves limits because limits in a functor category are computed
pointwise.  Hence `sectionsV X V` preserves limits, in particular kernels.

Consequently, for `g : A ⟶ B` in `X.Modules` there is a canonical isomorphism
`Γ(kernel g, V) ≅ kernel (Γ(g, V))`, compatible with the kernel inclusions; this is
`PreservesKernel.iso`, whose compatibility with `kernel.ι` is `PreservesKernel.iso_inv_ι`
(the direction stated in `PreservesKernel.iso_hom_ι` below).

This file provides the instance for the limit shape `WalkingParallelPair` and the resulting
kernel iso `Work.DSF1.Sheaf.sectionsV_kernel_iso`.
-/

namespace Work.DSF1.Sheaf

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

universe u

set_option linter.style.haveILetI false

/-- The sections functor `sectionsV X V : X.Modules ⥤ AddCommGrpCat` preserves limits of the
shape of the kernel (equalizer) diagram, since it is the composite of the limit-preserving
functors `toPresheaf` and `evaluation (op V)`. -/
instance sectionsV_preservesLimitsOfShape_walkingParallelPair
    (X : AlgebraicGeometry.Scheme.{u}) (V : X.Opens) :
    PreservesLimitsOfShape WalkingParallelPair (Work.DSEQ0.sectionsV X V) := by
  haveI : PreservesLimitsOfShape WalkingParallelPair
      ((CategoryTheory.evaluation (X.Opens)ᵒᵖ AddCommGrpCat.{u}).obj (Opposite.op V)) :=
    CategoryTheory.Limits.evaluation_preservesLimitsOfShape _
  exact (Limits.comp_preservesLimitsOfShape (AlgebraicGeometry.Scheme.Modules.toPresheaf X)
    ((CategoryTheory.evaluation (X.Opens)ᵒᵖ AddCommGrpCat.{u}).obj (Opposite.op V)))

/-- The canonical comparison `Γ(kernel g, V) ⟶ kernel (Γ(g, V))` is compatible with the kernel
inclusions. -/
lemma sectionsV_preservesKernel_iso_hom_ι {X : AlgebraicGeometry.Scheme.{u}} (V : X.Opens)
    {A B : X.Modules} (g : A ⟶ B) :
    (PreservesKernel.iso (Work.DSEQ0.sectionsV X V) g).hom ≫
        kernel.ι ((Work.DSEQ0.sectionsV X V).map g) =
      (Work.DSEQ0.sectionsV X V).map (kernel.ι g) := by
  haveI : PreservesLimit (parallelPair g 0) (Work.DSEQ0.sectionsV X V) :=
    PreservesLimitsOfShape.preservesLimit
  rw [← PreservesKernel.iso_inv_ι]
  simp

/-- The sections functor over `V` commutes with kernels: the kernel of the induced map on
sections is canonically isomorphic to the sections of the kernel sheaf, compatibly with the
kernel inclusions. -/
theorem sectionsV_kernel_iso {X : AlgebraicGeometry.Scheme.{u}} (V : X.Opens)
    {A B : X.Modules} (g : A ⟶ B) :
    ∃ e : (Work.DSEQ0.sectionsV X V).obj (CategoryTheory.Limits.kernel g) ≅
      CategoryTheory.Limits.kernel ((Work.DSEQ0.sectionsV X V).map g),
      CategoryTheory.CategoryStruct.comp e.hom
        (CategoryTheory.Limits.kernel.ι ((Work.DSEQ0.sectionsV X V).map g)) =
        (Work.DSEQ0.sectionsV X V).map (CategoryTheory.Limits.kernel.ι g) :=
  ⟨PreservesKernel.iso (Work.DSEQ0.sectionsV X V) g,
    sectionsV_preservesKernel_iso_hom_ι V g⟩

end Work.DSF1.Sheaf

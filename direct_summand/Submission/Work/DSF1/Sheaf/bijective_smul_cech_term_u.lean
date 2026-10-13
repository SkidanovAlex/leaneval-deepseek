import Mathlib
import Submission.Work.DSF1.Sheaf.CechStruct
import Submission.Work.DSF1.Sheaf.isUnit_res_of_le_basicOpen
import Submission.Work.DSF1.Sheaf.isAffineOpen_Eobj_of
import Submission.Work.DSF1.Sheaf.bijective_smul_cech_term

/-!
# Multiplication by a global section on a Čech term: the universe-polymorphic form

This is the universe-polymorphic version of `Work.DSF1.Sheaf.bijective_smul_cech_term`
(which is pinned to schemes in universe `0`).  Let `X` be an affine scheme, `f` a finite
family of global sections and `g` a global section whose basic open contains all the
`D (f i)`.  Multiplication by `g` is then a bijection on the `m`-th term of the Čech
complex of the structure sheaf along the family `D (f i)`.

The argument is that of `bijective_smul_cech_term`: the `m`-th term is the product over
the `m`-simplices `x` of the Čech nerve of the section modules `Γ(X, Eobj m x)`, where
`Eobj m x = ⨅ a, D (f (x a)) ≤ D g`.  Since intersections of basic opens of an affine
scheme are affine, `isUnit_res_of_le_basicOpen` shows that the restriction of `g` to
`Eobj m x` is a unit of `Γ(X, Eobj m x)`, so multiplication by `g` is bijective on each
factor; a product of bijections is a bijection.  All the ingredients are already
universe-polymorphic in the scheme, so the same proof goes through verbatim.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory AlgebraicGeometry Opposite Limits
open scoped Simplicial BigOperators

universe u

namespace Work.DSF1.Sheaf

theorem bijective_smul_cech_term_u {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsAffine X]
    {ι : Type u} [Fintype ι] (f : ι → ↥(X.presheaf.obj (Opposite.op ⊤)))
    (g : ↥(X.presheaf.obj (Opposite.op ⊤)))
    (hmem : ∀ i, X.basicOpen (f i) ≤ X.basicOpen g) (m : ℕ) :
    Function.Bijective (fun x : (Work.DSF1.Sheaf.cechBasicOpen X f).X m => g • x) := by
  let U : ι → X.Opens := basicOpenFamily X f
  let C := (Work.DSF1.Cech.E U).obj (Opposite.op (SimplexCategory.mk m))
  let M : C.I → ModuleCat ↥(X.presheaf.obj (Opposite.op ⊤)) :=
    fun i => (structPresheaf X).obj (Opposite.op (C.obj i))
  have hU : ∀ j, IsAffineOpen (U j) := fun j => (isAffineOpen_top X).basicOpen (f j)
  have hcomp : ∀ i, IsIso (smulEndHom (M i) g) := by
    intro i
    have hAff : IsAffineOpen (C.obj i) := Work.DSF1.Cech.isAffineOpen_Eobj_of U hU m i
    have hle : C.obj i ≤ X.basicOpen g := by
      calc C.obj i = ∏ᶜ (U ∘ i) := rfl
        _ = ⨅ a, (U ∘ i) a := Work.DSF1.Cech.piObj_eq_iInf (U ∘ i)
        _ ≤ (U ∘ i) 0 := iInf_le _ 0
        _ ≤ X.basicOpen g := hmem (i 0)
    exact isIso_smulEndHom_of_bijective (M i) g (bijective_smul_structPresheaf_obj hAff g hle)
  have hprod : IsIso (smulEndHom (∏ᶜ M) g) := isIso_smulEndHom_piObj M g hcomp
  have hT : IsIso (smulEndHom ((cechBasicOpen X f).X m) g) := hprod
  exact bijective_of_isIso_smulEndHom ((cechBasicOpen X f).X m) g hT

end Work.DSF1.Sheaf

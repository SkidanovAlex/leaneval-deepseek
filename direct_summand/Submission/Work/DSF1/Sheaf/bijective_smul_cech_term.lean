import Mathlib
import Submission.Work.DSF1.Sheaf.CechStruct
import Submission.Work.DSF1.Sheaf.isUnit_res_of_le_basicOpen
import Submission.Work.DSF1.Sheaf.isAffineOpen_Eobj_of

/-!
# Multiplication by a global section on a Čech term of the structure sheaf

Let `X` be an affine scheme, `f : ι → Γ(X, ⊤)` a finite family of global sections and
`g : Γ(X, ⊤)` a section whose basic open contains all the `D (f i)`.  Then scalar
multiplication by `g` is a bijection of the `m`-th term of the Čech complex of the
structure sheaf along the family of basic opens `D (f i)`.

The term of the Čech complex in degree `m` is the product, over the simplices
`x : Fin (m+1) → ι` of the Čech nerve, of the section modules `Γ(X, Eobj m x)` where
`Eobj m x = ⨅ a, D (f (x a))`.  Since `Eobj m x ≤ D (f (x 0)) ≤ D g`, the restriction of
`g` to `Eobj m x` is a unit of the ring `Γ(X, Eobj m x)` (`isUnit_res_of_le_basicOpen`,
using that intersections of basic opens of an affine scheme are affine), and the scalar
action of `Γ(X, ⊤)` on `Γ(X, Eobj m x)` is multiplication by the restriction; hence
multiplication by `g` is bijective on each factor.  Products of bijections are bijections,
which is the statement.

The formalisation works throughout with the categorical product `∏ᶜ` of modules: the
endomorphism "multiply by `g`" is realised as a morphism of `ModuleCat` (`smulEndHom`),
which shows that it is an isomorphism because `Pi.map` of isomorphisms is an isomorphism,
and an isomorphism of modules is a bijective map.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicGeometry Opposite Limits
open scoped Simplicial BigOperators

namespace Work.DSF1.Sheaf

universe u

/-- Scalar multiplication by `g` as an endomorphism of the module `M`. -/
noncomputable def smulEndHom {R : Type u} [CommRing R] (M : ModuleCat.{u} R) (g : R) : M ⟶ M :=
  ModuleCat.ofHom (algebraMap R (Module.End R M) g)

lemma smulEndHom_apply {R : Type u} [CommRing R] (M : ModuleCat.{u} R) (g : R) (x : M) :
    smulEndHom M g x = g • x := by
  show (algebraMap R (Module.End R M) g) x = g • x
  rw [Module.algebraMap_end_eq_smul_id]
  rfl

lemma smulEndHom_fun {R : Type u} [CommRing R] (M : ModuleCat.{u} R) (g : R) :
    ⇑(smulEndHom M g) = (fun x : M => g • x) :=
  funext (fun x => smulEndHom_apply M g x)

/-- Scalar multiplication by `g` is an isomorphism of modules as soon as it is a bijection
of the underlying sets. -/
lemma isIso_smulEndHom_of_bijective {R : Type u} [CommRing R] (M : ModuleCat.{u} R) (g : R)
    (h : Function.Bijective (fun x : M => g • x)) : IsIso (smulEndHom M g) := by
  rw [ConcreteCategory.isIso_iff_bijective, smulEndHom_fun]
  exact h

/-- Conversely, an isomorphism given by scalar multiplication is a bijection. -/
lemma bijective_of_isIso_smulEndHom {R : Type u} [CommRing R] (M : ModuleCat.{u} R) (g : R)
    (h : IsIso (smulEndHom M g)) : Function.Bijective (fun x : M => g • x) := by
  rw [← smulEndHom_fun]
  exact (ConcreteCategory.isIso_iff_bijective _).mp h

/-- Scalar multiplication is natural with respect to linear maps. -/
lemma smulEndHom_natural {R : Type u} [CommRing R] {A B : ModuleCat.{u} R} (f : A ⟶ B) (g : R) :
    f ≫ smulEndHom B g = smulEndHom A g ≫ f := by
  ext x
  simp only [ModuleCat.comp_apply, smulEndHom_apply, map_smul]

/-- Scalar multiplication by `g` on a product of modules is an isomorphism as soon as it is on
every factor. -/
lemma isIso_smulEndHom_piObj {R : Type u} [CommRing R] {ι : Type u} (M : ι → ModuleCat.{u} R)
    (g : R) (h : ∀ i, IsIso (smulEndHom (M i) g)) : IsIso (smulEndHom (∏ᶜ M) g) := by
  haveI : IsIso (Limits.Pi.map (fun i => smulEndHom (M i) g)) := inferInstance
  have heq : Limits.Pi.map (fun i => smulEndHom (M i) g) = smulEndHom (∏ᶜ M) g := by
    refine Limits.Pi.hom_ext _ _ (fun i => ?_)
    rw [Limits.Pi.map_π]
    exact smulEndHom_natural (Limits.Pi.π M i) g
  rwa [← heq]

/-- Multiplication by `g` on the sections of the structure sheaf over an affine open `W`
contained in `D g` is a bijection.  The module structure of `Γ(X, W)` over `Γ(X, ⊤)` is
that induced by the restriction ring homomorphism, so multiplication by `g` is
multiplication by the unit `g|_W` of the ring `Γ(X, W)`. -/
lemma bijective_smul_structPresheaf_obj {X : Scheme.{u}} {W : X.Opens} (hW : IsAffineOpen W)
    (g : ↥(X.presheaf.obj (op ⊤))) (hg : W ≤ X.basicOpen g) :
    Function.Bijective (fun x : (structPresheaf X).obj (op W) => g • x) := by
  let resHom : ↥(X.presheaf.obj (op ⊤)) →+* ↥(X.presheaf.obj (op W)) :=
    (X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom
  letI : Algebra ↥(X.presheaf.obj (op ⊤)) ↥(X.presheaf.obj (op W)) := resHom.toAlgebra
  letI : Module ↥(X.presheaf.obj (op ⊤)) ↥(X.presheaf.obj (op W)) := Algebra.toModule
  have hu : IsUnit (resHom g) := isUnit_res_of_le_basicOpen hW g hg
  have hb : Function.Bijective (fun x : ↥(X.presheaf.obj (op W)) => g • x) := by
    have h1 : (fun x : ↥(X.presheaf.obj (op W)) => g • x) = fun x => resHom g * x := by
      funext x
      rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
    rw [h1]
    exact (IsUnit.isUnit_iff_mulLeft_bijective).mp hu
  exact hb

theorem bijective_smul_cech_term {X : AlgebraicGeometry.Scheme} [AlgebraicGeometry.IsAffine X]
    {ι : Type} [Fintype ι] (f : ι → ↥(X.presheaf.obj (Opposite.op ⊤)))
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

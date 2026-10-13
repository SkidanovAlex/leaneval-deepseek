import Mathlib
import Submission.Work.DSF1.Sheaf.AcycDefs
import Submission.Work.DSF1.Sheaf.CechSheafTerm

/-!
# Flasqueness of the sheaf-level Čech terms

For a scheme `X`, a family of opens `U : ι → X.Opens` and a presheaf of abelian groups `P` on
`X.Opens`, the degree-`n` term of the sheaf-level Čech complex is the presheaf

`W ↦ ∏ x : Fin (n+1) → ι, P (⋂ a, U (x a) ⊓ W)`

(`cechSheafTerm U P n`, see `CechSheafTerm.lean`).

Here we show that each such term is flasque as soon as `P` is.  Two facts are used:

* the structure maps of `cechSheafTerm U P n` are products of restriction maps of `P`
  (`Pi.map` of the maps `(restrNat P h).app ·`, by `cochainComplexFunctor_map_f`);
* in `AddCommGrpCat` a product of epimorphisms is an epimorphism (`pi_map_epi_of_epi`); the
  index type `Fin (n+1) → ι` is infinite in general, so the finiteness hypothesis of
  `Limits.Pi.map_epi` does not apply and the statement is proved directly from the description
  of products in `AddCommGrpCat` as `Pi`-types.
-/

namespace Work.DSF1.Sheaf

open CategoryTheory AlgebraicGeometry Opposite Limits TopologicalSpace

open scoped Simplicial

universe u

set_option linter.style.haveILetI false

/-- In `AddCommGrpCat`, a product of epimorphisms is an epimorphism.  This is the classical
fact that the epimorphisms of abelian groups are the surjective maps, and that the product of a
family of surjective maps is surjective: an element of the target is obtained by choosing, for
each index, a preimage of its `j`-th component.  Note that the index type is arbitrary: the
finiteness assumption of `Limits.Pi.map_epi` is not available here. -/
theorem pi_map_epi_of_epi {J : Type u} {f g : J → AddCommGrpCat.{u}} (p : ∀ j, f j ⟶ g j)
    [∀ j, Epi (p j)] : Epi (Limits.Pi.map p) := by
  rw [AddCommGrpCat.epi_iff_surjective]
  intro y
  have hsurj : ∀ j, Function.Surjective (ConcreteCategory.hom (p j)) := fun j =>
    (AddCommGrpCat.epi_iff_surjective (p j)).mp inferInstance
  choose z hz using fun j => hsurj j ((ConcreteCategory.hom (Limits.Pi.π g j)) y)
  refine ⟨(Concrete.productEquiv f).symm z, ?_⟩
  apply (Concrete.productEquiv g).injective
  funext j
  rw [Concrete.productEquiv_apply_apply, Limits.Pi.map_π_apply,
    Concrete.productEquiv_symm_apply_π, hz j, Concrete.productEquiv_apply_apply]

/-- The degree-`n` component of the map of Čech complexes induced by the restriction
`restrNat P h : restrP P A.unop ⟶ restrP P B.unop` (`h : B.unop ≤ A.unop`) is the product of
the corresponding restriction maps of `P`. -/
lemma cechComplexP_map_f {X : AlgebraicGeometry.Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    (P : (X.Opens)ᵒᵖ ⥤ AddCommGrpCat.{u}) (n : ℕ)
    {A B : (X.Opens)ᵒᵖ} (h : B.unop ≤ A.unop) :
    ((cechComplexP U P).map (homOfLE h).op).f n =
      Limits.Pi.map (fun x : ((FormalCoproduct.mk ι U).cech.obj (op ⦋n⦌)).I =>
        P.map (homOfLE (inf_le_inf_left (((FormalCoproduct.mk ι U).cech.obj (op ⦋n⦌)).obj x) h)).op) := by
  dsimp only [cechComplexP, CategoryTheory.cechComplexFunctor, Functor.comp_map]
  rw [FormalCoproduct.cochainComplexFunctor_map_f]
  congr 1

/-- The same computation for the sheaf-level Čech terms: the map of `cechSheafTerm U P n`
induced by an inclusion of opens is a product of restriction maps of `P`. -/
lemma cechSheafTerm_map {X : AlgebraicGeometry.Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    (P : (X.Opens)ᵒᵖ ⥤ AddCommGrpCat.{u}) (n : ℕ)
    {A B : (X.Opens)ᵒᵖ} (h : B.unop ≤ A.unop) :
    (cechSheafTerm U P n).map (homOfLE h).op =
      Limits.Pi.map (fun x : ((FormalCoproduct.mk ι U).cech.obj (op ⦋n⦌)).I =>
        P.map (homOfLE (inf_le_inf_left (((FormalCoproduct.mk ι U).cech.obj (op ⦋n⦌)).obj x) h)).op) := by
  dsimp only [cechSheafTerm, cechComplexP, CategoryTheory.cechComplexFunctor, Functor.comp_map]
  rw [HomologicalComplex.eval_map]
  rw [FormalCoproduct.cochainComplexFunctor_map_f]
  congr 1

theorem isFlasque_cechSheafTerm {X : AlgebraicGeometry.Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    (P : CategoryTheory.Functor (Opposite (X.Opens)) (AddCommGrpCat.{u}))
    (hP : TopCat.Presheaf.IsFlasque P) (n : ℕ) :
    TopCat.Presheaf.IsFlasque (Work.DSF1.Sheaf.cechSheafTerm U P n) := by
  refine ⟨fun {A B} i => ?_⟩
  -- every morphism of `(X.Opens)ᵒᵖ` is the `op` of a `homOfLE`
  rw [show i = (homOfLE (leOfHom i.unop)).op from Subsingleton.elim _ _]
  rw [cechSheafTerm_map U P n (leOfHom i.unop)]
  -- each factor is a restriction map of `P`, hence an epimorphism
  haveI : ∀ x : ((FormalCoproduct.mk ι U).cech.obj (op ⦋n⦌)).I,
      Epi (P.map (homOfLE (inf_le_inf_left (((FormalCoproduct.mk ι U).cech.obj (op ⦋n⦌)).obj x)
        (leOfHom i.unop))).op) := fun x => hP.epi _
  exact pi_map_epi_of_epi _

end Work.DSF1.Sheaf

import Mathlib

/-!
# General categorical / set-theoretic auxiliaries for `Work.ANALYTIC`

Two elementary lemmas used throughout the ANALYTIC area:

* `bijective_of_conj` — a function-level conjugation of bijectivity statements;
* `bijective_precomp_congr` — precomposition maps on hom-sets with conjugate morphisms have
  conjugate bijectivity: if `e : A ≅ A'` and `f ≫ e.hom = e.hom ≫ f'` then
  `(· ≫ f) : (A ⟶ M) → (A ⟶ M)` is bijective iff `(· ≫ f') : (A' ⟶ M) → (A' ⟶ M)` is.
-/

open CategoryTheory MonoidalCategory MonoidalClosed

namespace Work.ANALYTIC.CatAux

universe u v

/-- Conjugation of a bijectivity statement along a bijection: if `e` is a bijection and
`∀ a, e (f a) = g (e a)` then `f` is bijective iff `g` is. -/
lemma bijective_of_conj {α : Type*} {β : Type*} (e : α → β) (he : Function.Bijective e)
    {f : α → α} {g : β → β} (h : ∀ a, e (f a) = g (e a)) :
    Function.Bijective f ↔ Function.Bijective g := by
  have hcomp : e ∘ f = g ∘ e := funext h
  rw [← Function.Bijective.of_comp_iff' he f, hcomp, Function.Bijective.of_comp_iff g he]

/-- Precomposition maps with conjugate morphisms have conjugate bijectivity. -/
lemma bijective_precomp_congr {C : Type u} [Category.{v, u} C] {A A' M : C} (e : A ≅ A')
    {f : A ⟶ A} {f' : A' ⟶ A'} (h : f ≫ e.hom = e.hom ≫ f') :
    Function.Bijective (fun u : A ⟶ M => f ≫ u) ↔
      Function.Bijective (fun u' : A' ⟶ M => f' ≫ u') := by
  have he' : Function.Bijective (fun u' : A' ⟶ M => e.hom ≫ u') := by
    refine ⟨fun a b hab => ?_, fun a => ⟨e.inv ≫ a, ?_⟩⟩
    · have h2 : e.inv ≫ (e.hom ≫ a) = e.inv ≫ (e.hom ≫ b) :=
        congrArg (fun t => e.inv ≫ t) hab
      simpa only [← Category.assoc, e.inv_hom_id, Category.id_comp] using h2
    · show e.hom ≫ (e.inv ≫ a) = a
      rw [← Category.assoc, e.hom_inv_id, Category.id_comp]
  refine (bijective_of_conj (fun u' : A' ⟶ M => e.hom ≫ u') he' ?_).symm
  intro u'
  show e.hom ≫ (f' ≫ u') = f ≫ (e.hom ≫ u')
  calc e.hom ≫ (f' ≫ u') = (e.hom ≫ f') ≫ u' := (Category.assoc _ _ _).symm
    _ = (f ≫ e.hom) ≫ u' := by rw [h]
    _ = f ≫ (e.hom ≫ u') := Category.assoc _ _ _

section PropDefs

variable {C : Type u} [Category.{v, u} C] [MonoidalCategory C]

/-- The tensor-side precomposition statement: precomposition by `S ▷ (X ⊗ Z)` is bijective on
`Hom(P ⊗ (X ⊗ Z), M)`.  Stated as a plain `Prop` so that it can be used in the statement of a lemma
in a file that does not `open MonoidalCategory`. -/
def TensorPrecompBij (P X M Z : C) (S : P ⟶ P) : Prop :=
  Function.Bijective (fun (t : P ⊗ (X ⊗ Z) ⟶ M) => (S ▷ (X ⊗ Z)) ≫ t)

/-- The curried-side precomposition statement: precomposition by `S ▷ Z` is bijective on
`Hom(P ⊗ Z, X ⟹ M)`. -/
def CurryPrecompBij [MonoidalClosed C] (P X M Z : C) (S : P ⟶ P) : Prop :=
  Function.Bijective (fun (y : P ⊗ Z ⟶ (ihom X).obj M) => (S ▷ Z) ≫ y)

end PropDefs

end Work.ANALYTIC.CatAux

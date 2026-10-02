import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The abstract Mayer–Vietoris short complex attached to a pullback square of index sets

Let `A`, `B`, `C`, `S` be types and `γ : C → A`, `δ : C → B`, `α : A → S`, `β : B → S` maps
satisfying `α ∘ γ = β ∘ δ`.  Forming coproducts of copies of a ring `R` (viewed as a module over
itself) we obtain the induced morphisms

`γ_* : ∐_C R ⟶ ∐_A R`, `δ_* : ∐_C R ⟶ ∐_B R`, `α_* : ∐_A R ⟶ ∐_S R`, `β_* : ∐_B R ⟶ ∐_S R`

and the short complex

`0 ⟶ ∐_C R --(γ_*,δ_*)--> ∐_A R ⊞ ∐_B R --α_* - β_*--> ∐_S R ⟶ 0`.

This file collects the definitions (`coprodMap`, `coprodShortComplex`) and the two basic
computation lemmas (`ι_coprodMap`, `coprodMap_comp`).  The main theorem saying that this short
complex is short exact, when the square of index maps is a pullback and the images of `α` and `β`
cover `S`, is `Work.Cohomology.coprod_shortExact` in `Submission/Work/Cohomology/CoprodMV.lean`.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits

namespace Work.Cohomology

noncomputable section

variable {R : Type} [Ring R]

/-- The morphism `∐_{a : A} R ⟶ ∐_{s : S} R` induced by a map `f : A → S` of index types. -/
def coprodMap {A S : Type} (f : A → S) :
    (∐ (fun _ : A => ModuleCat.of R R)) ⟶ (∐ (fun _ : S => ModuleCat.of R R)) :=
  Sigma.map' f (fun _ => 𝟙 _)

/-- On the generator indexed by `a : A`, `coprodMap f` is the generator indexed by `f a`. -/
lemma ι_coprodMap {A S : Type} (f : A → S) (a : A) :
    Sigma.ι (fun _ : A => ModuleCat.of R R) a ≫ coprodMap (R:=R) f
      = Sigma.ι (fun _ : S => ModuleCat.of R R) (f a) := by
  simp only [coprodMap]
  rw [Sigma.ι_comp_map']
  simp

/-- `coprodMap` is functorial in the map of index types. -/
lemma coprodMap_comp {A B S : Type} (f : A → B) (g : B → S) :
    coprodMap (R:=R) f ≫ coprodMap (R:=R) g = coprodMap (R:=R) (g ∘ f) := by
  simp only [coprodMap]
  rw [Sigma.map'_comp_map']
  simp

/-- The Mayer–Vietoris short complex attached to a commutative square of index types. -/
def coprodShortComplex {A B C S : Type} (γ : C → A) (δ : C → B) (α : A → S) (β : B → S)
    (hcomm : α ∘ γ = β ∘ δ) : ShortComplex (ModuleCat R) :=
  ShortComplex.mk (biprod.lift (coprodMap (R:=R) γ) (coprodMap (R:=R) δ))
    (biprod.desc (coprodMap (R:=R) α) (-(coprodMap (R:=R) β)))
    (by
      rw [biprod.lift_desc]
      have h : coprodMap (R:=R) γ ≫ coprodMap (R:=R) α
          = coprodMap (R:=R) δ ≫ coprodMap (R:=R) β := by
        rw [coprodMap_comp, coprodMap_comp, hcomm]
      rw [h]
      simp)

end

end Work.Cohomology

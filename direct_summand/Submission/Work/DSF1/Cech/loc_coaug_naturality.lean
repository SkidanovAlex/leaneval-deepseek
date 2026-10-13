import Mathlib
import Submission.Work.DSF1.Cech.CechDefs

/-!
# Naturality of the coaugmentation with respect to the localisation `locᵢ`

For a family `f : ι → R` of elements of a commutative ring and an index `i`, the
coaugmentation `coaugQ f : 𝒪(⊤) ⟶ 𝒞⁰` of the Čech complex of `Spec R` along the
principal opens `D (f j)`, and the comparison map `loc f i : 𝒞 ⟶ 𝒞ᵢ` onto the Čech
complex of the localised presheaf `W ↦ 𝒪(W ⊓ D(f i))`, satisfy

`coaugQ f ≫ (loc f i).f 0 = etaITop f i ≫ coaugQi f i`

in degree `0`.  In degree `0` both sides are products over the `0`-simplices of the
Čech nerve, and the identity is exactly the naturality of the restriction
`ηᵢ : P ⟶ Qi P U i` at the maps `D(f j) ≤ ⊤`.

The proof is a componentwise computation: `Pi.lift` against `Pi.map` reduces to the
pointwise composites (`pi_lift_comp_map`, `pi_comp_lift`), and each component is an
instance of the naturality square of `etaI`.
-/

open CategoryTheory AlgebraicGeometry Opposite Limits
open scoped Simplicial BigOperators

universe u

namespace Work.DSF1.Cech

/- In degree `0`, the chain map `loc f i` is the product, over the `0`-simplices `x`
of the Čech nerve, of the restrictions `ηᵢ.app (op (Eobj f 0 x))`. -/
set_option backward.isDefEq.respectTransparency false in
lemma loc_f_zero {R : Type u} [CommRing R] {ι : Type u} (f : ι → R) (i : ι) :
    (loc f i).f 0 =
      Limits.Pi.map (fun x =>
        (etaI (basicOpens f) (specPresheaf R) i).app (op (Eobj (basicOpens f) 0 x))) := by
  rw [loc]
  simp only [CategoryTheory.cechComplexFunctor,
    FormalCoproduct.cochainComplexFunctor_map_f]

/-- `Pi.lift` versus `Pi.map`: both ways of composing a cone with a natural family of
maps between the factors give the same morphism. -/
lemma pi_lift_comp_map {β : Type*} {C : Type*} [Category C] {f g : β → C}
    [HasProduct f] [HasProduct g] {X : C} (p : ∀ b, X ⟶ f b) (q : ∀ b, f b ⟶ g b) :
    Limits.Pi.lift p ≫ Limits.Pi.map q = Limits.Pi.lift (fun b => p b ≫ q b) := by
  refine Limits.Pi.hom_ext _ _ (fun b => ?_)
  rw [Category.assoc, Limits.Pi.map_π, ← Category.assoc, Limits.Pi.lift_comp_π,
    Limits.Pi.lift_comp_π]

/-- `Pi.lift` is natural in the source object. -/
lemma pi_comp_lift {β : Type*} {C : Type*} [Category C] {f : β → C} [HasProduct f]
    {X Y : C} (h : X ⟶ Y) (p : ∀ b, Y ⟶ f b) :
    h ≫ Limits.Pi.lift p = Limits.Pi.lift (fun b => h ≫ p b) := by
  refine Limits.Pi.hom_ext _ _ (fun b => ?_)
  rw [Category.assoc, Limits.Pi.lift_comp_π, Limits.Pi.lift_comp_π]

theorem loc_coaug_naturality {R : Type u} [CommRing R] {ι : Type u} (f : ι → R) (i : ι) : CategoryTheory.CategoryStruct.comp (Work.DSF1.Cech.coaugQ f) ((Work.DSF1.Cech.loc f i).f 0) = CategoryTheory.CategoryStruct.comp (Work.DSF1.Cech.etaITop f i) (Work.DSF1.Cech.coaugQi f i) := by
  have h1 := loc_f_zero f i
  have hmain :
      Limits.Pi.lift (fun x : (E (basicOpens f)).obj (op ⦋0⦌) |>.I =>
          (specPresheaf R).map (homOfLE (le_top : Eobj (basicOpens f) 0 x ≤ ⊤)).op) ≫
        Limits.Pi.map (fun x =>
          (etaI (basicOpens f) (specPresheaf R) i).app (op (Eobj (basicOpens f) 0 x))) =
      (etaI (basicOpens f) (specPresheaf R) i).app (op ⊤) ≫
        Limits.Pi.lift (fun x : (E (basicOpens f)).obj (op ⦋0⦌) |>.I =>
          (Qi (basicOpens f) (specPresheaf R) i).map
            (homOfLE (le_top : Eobj (basicOpens f) 0 x ≤ ⊤)).op) := by
    rw [pi_lift_comp_map, pi_comp_lift]
    refine Limits.Pi.hom_ext
      (f := fun x => (Qi (basicOpens f) (specPresheaf R) i).obj (op (Eobj (basicOpens f) 0 x)))
      _ _ (fun x => ?_)
    rw [Limits.Pi.lift_comp_π, Limits.Pi.lift_comp_π]
    exact ((etaI (basicOpens f) (specPresheaf R) i).naturality
      (homOfLE (le_top : Eobj (basicOpens f) 0 x ≤ ⊤)).op).symm
  rw [h1]
  exact hmain

end Work.DSF1.Cech

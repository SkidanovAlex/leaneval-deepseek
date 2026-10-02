import Mathlib
import Submission.Work.Thom.ATools
import Submission.Work.Cohomology.homotopyEquivDual

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open scoped unitInterval
open CategoryTheory MonoidalCategory

namespace Work.Thom

noncomputable section

/-- The inclusion of a subset, as a continuous map. -/
def cmIncl {X : Type} [TopologicalSpace X] (A : Set X) : C(A, X) :=
  ⟨Subtype.val, continuous_subtype_val⟩

@[simp] lemma cmIncl_apply {X : Type} [TopologicalSpace X] (A : Set X) (a : A) :
    cmIncl A a = (a : X) := rfl

/-- **The restriction of a homotopy of a pair to the pair.**  A homotopy `H` from `f` to `g` which
carries `A × I` into `B` restricts to a homotopy between `f|_A` and `g|_A`, viewed as maps
`A → B`. -/
def restrHomotopy {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y}
    {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g) (hf : ∀ x ∈ A, f x ∈ B)
    (hg : ∀ x ∈ A, g x ∈ B) (hH : ∀ t x, x ∈ A → H (t, x) ∈ B) :
    ContinuousMap.Homotopy (⟨fun a : A => ⟨f a, hf a a.2⟩, by fun_prop⟩ : C(A, B))
      (⟨fun a : A => ⟨g a, hg a a.2⟩, by fun_prop⟩ : C(A, B)) where
  toContinuousMap :=
    ⟨fun p : I × A => ⟨H (p.1, p.2), hH p.1 p.2 p.2.2⟩,
      Continuous.subtype_mk (H.continuous_toFun.comp
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))) _⟩
  map_zero_left := fun a => by
    apply Subtype.ext
    exact H.map_zero_left (a : X)
  map_one_left := fun a => by
    apply Subtype.ext
    exact H.map_one_left (a : X)

@[simp] lemma restrHomotopy_apply {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g)
    (hf : ∀ x ∈ A, f x ∈ B) (hg : ∀ x ∈ A, g x ∈ B) (hH : ∀ t x, x ∈ A → H (t, x) ∈ B)
    (p : I × A) :
    ((restrHomotopy H hf hg hH) p : Y) = H (p.1, p.2) := rfl


/-- The restriction of a homotopy of a pair, as a homotopy of morphisms of `TopCat`. -/
def restrHomotopyTop {X Y : TopCat} {A : Set X} {B : Set Y} {f g : X ⟶ Y}
    (H : TopCat.Homotopy f g) (hf : ∀ x ∈ A, f x ∈ B) (hg : ∀ x ∈ A, g x ∈ B)
    (hH : ∀ t x, x ∈ A → H (t, x) ∈ B) :
    TopCat.Homotopy
      (TopCat.ofHom (⟨fun a : ↥A => ⟨f a, hf a a.2⟩, by fun_prop⟩ : C(↥A, ↥B)))
      (TopCat.ofHom (⟨fun a : ↥A => ⟨g a, hg a a.2⟩, by fun_prop⟩ : C(↥A, ↥B))) :=
  restrHomotopy H hf hg hH


/-- The restricted homotopy, as a morphism `A ⊗ I ⟶ Y`, is the composite of the restriction
`A ⊗ I ⟶ X ⊗ I` with `H`. -/
lemma restrHomotopy_h {X Y : TopCat} {A : Set X} {B : Set Y} {f g : X ⟶ Y}
    (H : TopCat.Homotopy f g) (hf : ∀ x ∈ A, f x ∈ B) (hg : ∀ x ∈ A, g x ∈ B)
    (hH : ∀ t x, x ∈ A → H (t, x) ∈ B) :
    (restrHomotopyTop H hf hg hH).h ≫ TopCat.ofHom (cmIncl B)
      = (TopCat.ofHom (cmIncl A) ▷ TopCat.I) ≫ H.h := by
  ext p
  simp only [CategoryTheory.comp_apply, ContinuousMap.coe_mk, TopCat.Homotopy.h_hom_apply,
    TopCat.whiskerRight_apply, cmIncl, continuous_subtype_val, ContinuousMap.coe_mk]
  rfl

end

end Work.Thom

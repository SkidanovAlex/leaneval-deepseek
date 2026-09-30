/-
# A group scheme over a field is separated

For any field `K` and any group object `G` in the category `Over (Spec K)` of schemes over `K`,
the structure morphism `G.hom : G.left ⟶ Spec K` is separated.

This is [Stacks, Lemma 39.7.3] (tag 047L): a group scheme over a field is a separated scheme.

The proof follows [Stacks, Lemma 39.6.1] (tag 047G): the diagonal `Δ : G ⟶ G ×_K G` is the base
change of the identity section `e : Spec K ⟶ G` along the morphism `φ : G ×_K G ⟶ G` sending a
pair of points `(g, g')` to `ι(g) · g'`.  Since `e` is a closed immersion (this is the Mathlib
instance `IsClosedImmersion η[G].left`, valid for any group object in `Over (Spec K)` over a
field), so is `Δ`, which is exactly separatedness of `G.hom`.
-/

import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace Work.Universal

noncomputable section

universe u v

namespace GrpObjSep

/-! ## The general computation in a cartesian monoidal category

We work with a group object `G` in a cartesian monoidal category and study the morphism
`φ : G ⊗ G ⟶ G`, `(g, g') ↦ ι g * g'`.  Its fibre over the identity is the diagonal. -/

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

/-- For a group object `G`, the morphism `φ : G ⊗ G ⟶ G` with `φ (g, g') = ι g * g'`. -/
def phi (G : C) [GrpObj G] : G ⊗ G ⟶ G :=
  (GrpObj.inv (X := G) ⊗ₘ 𝟙 G) ≫ MonObj.mul (X := G)

/-- The diagonal composed with `φ` is the identity section: `Δ ≫ φ = e ∘ toUnit`. -/
theorem phi_diag (G : C) [GrpObj G] :
    lift (𝟙 G) (𝟙 G) ≫ phi G = toUnit G ≫ MonObj.one (X := G) := by
  rw [phi]
  rw [← Category.assoc, lift_map]
  rw [Category.id_comp, Category.comp_id]
  exact GrpObj.left_inv (X := G)

/-- Pointwise, `φ` computes the "difference" `x⁻¹ * y`, i.e. `(x, y) ↦ ι x * y`. -/
theorem snd_phi (G : C) [GrpObj G] {T : C} (b : T ⟶ G ⊗ G) :
    b ≫ phi G = (b ≫ fst G G)⁻¹ * (b ≫ snd G G) := by
  rw [phi]
  rw [← lift_comp_fst_snd b]
  rw [← Category.assoc]
  rw [lift_map]
  simp only [Category.comp_id, lift_fst, lift_snd, Hom.mul_def, Hom.inv_def]

/-- If `b : T ⟶ G ⊗ G` lands in the fibre of `φ` over the identity, its two components agree:
this is the computation `ι x * y = 1 ⟹ y = x`, i.e. the diagonal is the fibre of `φ` over `e`. -/
theorem fst_eq_snd_of (G : C) [GrpObj G] {T : C} (b : T ⟶ G ⊗ G)
    (h : b ≫ phi G = toUnit T ≫ MonObj.one (X := G)) :
    b ≫ fst G G = b ≫ snd G G := by
  have h1 : (b ≫ fst G G)⁻¹ * (b ≫ snd G G) = 1 := by
    rw [← snd_phi G b, h, Hom.one_def]
  exact inv_mul_eq_one.mp h1

/-- **The diagonal of a group object is the base change of the identity section along `φ`.**

The square
```
  G --toUnit G--> 𝟙_
  |                |
  Δ                η
  v                v
 G ⊗ G ---φ---->  G
```
is a pullback. -/
theorem isPullback_diag (G : C) [GrpObj G] :
    IsPullback (toUnit G) (lift (𝟙 G) (𝟙 G)) (MonObj.one (X := G)) (phi G) := by
  suffices hlim : Limits.IsLimit
      (PullbackCone.mk (toUnit G) (lift (𝟙 G) (𝟙 G)) (phi_diag G).symm) from
    IsPullback.of_isLimit hlim
  refine PullbackCone.IsLimit.mk (phi_diag G).symm (fun s => s.snd ≫ fst G G) ?_ ?_ ?_
  · intro s
    exact toUnit_unique _ _
  · intro s
    have hcond : s.snd ≫ phi G = toUnit s.pt ≫ MonObj.one (X := G) := by
      rw [← s.condition]
      rw [toUnit_unique s.fst (toUnit s.pt)]
    have hfs := fst_eq_snd_of G s.snd hcond
    have hAA : lift (s.snd ≫ fst G G) (s.snd ≫ fst G G)
        = lift (s.snd ≫ fst G G) (s.snd ≫ snd G G) := congrArg _ hfs
    rw [comp_lift]
    simp only [Category.comp_id]
    rw [hAA, lift_comp_fst_snd]
  · intro s m _ hm2
    rw [← hm2, Category.assoc, lift_fst, Category.comp_id]

variable {X : AlgebraicGeometry.Scheme}

/-- The diagonal `Δ : G ⟶ G ⊗ G` computed in `Over X` induces the usual diagonal of the
structure morphism `G.hom` on the underlying schemes. -/
theorem diag_left (G : Over X) :
    (lift (𝟙 G) (𝟙 G) : G ⟶ G ⊗ G).left = pullback.diagonal G.hom := by
  rw [Over.lift_left, pullback.diagonal]
  simp only [Over.id_left]

end GrpObjSep

/-! ## The scheme-theoretic consequence -/

/-- **A group scheme over a field is separated.**  For any field `K` and any group object `G`
in `Over (Spec K)`, the structure morphism `G.hom : G.left ⟶ Spec K` is separated. -/
theorem isSeparated_hom_of_grpObj {K : Type _} [Field K]
    (G : CategoryTheory.Over (AlgebraicGeometry.Spec (CommRingCat.of K)))
    [CategoryTheory.GrpObj G] : AlgebraicGeometry.IsSeparated G.hom := by
  let X := AlgebraicGeometry.Spec (CommRingCat.of K)
  have key := GrpObjSep.isPullback_diag (C := Over X) G
  have key' := Functor.map_isPullback (Over.forget X) key
  simp only [Over.forget_map, Over.toUnit_left, GrpObjSep.diag_left G] at key'
  exact ⟨MorphismProperty.of_isPullback key'
    (inferInstance : AlgebraicGeometry.IsClosedImmersion (MonObj.one (X := G)).left)⟩

end

end Work.Universal

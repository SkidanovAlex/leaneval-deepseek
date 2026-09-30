import Mathlib
import Submission.Work.GenusZero.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


open CategoryTheory Limits AlgebraicGeometry
open scoped Classical MonObj MonoidalCategory CategoryTheory.Obj

namespace Work.CurveFacts

universe u

noncomputable section

/-!
## Base change of points is multiplicative

`Work.GenusZero.ptBaseChange F A` is the transpose, along the adjunction
`Over.map (specMap k F) ⊣ Over.pullback (specMap k F)`, of the identity of `𝟙_ (Sch F)`; it is
therefore the composite of the unit of the adjunction with the pullback functor applied to a point.
Writing `u` for that unit, `ptBaseChange F A x = u ≫ (bcFun F).map x`, and the result follows from
the multiplicativity of `(bcFun F).map` together with the (general) multiplicativity of
precomposition with a morphism out of the tensor unit.
-/

/-- The pullback condition for the unit `ptBaseChangeUnit` below, stated in the exact form
`pullback.lift` expects. -/
theorem ptBaseChangeUnit_witness {k : Type u} [Field k] {F : Type u} [Field F] [Algebra k F] :
    (𝟙 (Spec (CommRingCat.of F)) : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of F)) ≫
      Over.hom (Work.GenusZero.specOf k F) =
      𝟙 (Spec (CommRingCat.of F)) ≫ Work.Descent.specMap k F := by
  rw [Category.id_comp, Category.id_comp, Work.GenusZero.specOf_hom]

/-- The unit of the adjunction `Over.map (specMap k F) ⊣ Over.pullback (specMap k F)`, evaluated
at the terminal object `𝟙_ (Sch F)`.  Its underlying morphism of schemes is the diagonal
`Spec F ⟶ Spec F ×_{Spec k} Spec F`. -/
def ptBaseChangeUnit {k : Type u} [Field k] {F : Type u} [Field F] [Algebra k F] :
    𝟙_ (Work.GenusZero.Sch F) ⟶
      (Work.GenusZero.bcFun F).obj (Work.GenusZero.specOf k F) :=
  Over.homMk
    (pullback.lift (𝟙 (Spec (CommRingCat.of F))) (𝟙 (Spec (CommRingCat.of F)))
      ptBaseChangeUnit_witness)
    (by
      show pullback.lift (𝟙 (Spec (CommRingCat.of F))) (𝟙 (Spec (CommRingCat.of F)))
          ptBaseChangeUnit_witness ≫
          pullback.snd (Over.hom (Work.GenusZero.specOf k F)) (Work.Descent.specMap k F) = 𝟙 _
      rw [pullback.lift_snd])

/-- The first projection of `ptBaseChangeUnit`. -/
theorem ptBaseChangeUnit_fst {k : Type u} [Field k] {F : Type u} [Field F] [Algebra k F] :
    (ptBaseChangeUnit (k := k) (F := F)).left ≫
      pullback.fst (Over.hom (Work.GenusZero.specOf k F)) (Work.Descent.specMap k F) =
      𝟙 (Spec (CommRingCat.of F)) := by
  show pullback.lift (𝟙 (Spec (CommRingCat.of F))) (𝟙 (Spec (CommRingCat.of F)))
      ptBaseChangeUnit_witness ≫
      pullback.fst (Over.hom (Work.GenusZero.specOf k F)) (Work.Descent.specMap k F) = 𝟙 _
  rw [pullback.lift_fst]

/-- The second projection of `ptBaseChangeUnit`. -/
theorem ptBaseChangeUnit_snd {k : Type u} [Field k] {F : Type u} [Field F] [Algebra k F] :
    (ptBaseChangeUnit (k := k) (F := F)).left ≫
      pullback.snd (Over.hom (Work.GenusZero.specOf k F)) (Work.Descent.specMap k F) =
      𝟙 (Spec (CommRingCat.of F)) := by
  show pullback.lift (𝟙 (Spec (CommRingCat.of F))) (𝟙 (Spec (CommRingCat.of F)))
      ptBaseChangeUnit_witness ≫
      pullback.snd (Over.hom (Work.GenusZero.specOf k F)) (Work.Descent.specMap k F) = 𝟙 _
  rw [pullback.lift_snd]

/-- `ptBaseChange F A` is the composite of the adjunction unit `ptBaseChangeUnit` with the base
change functor applied to the point. -/
theorem ptBaseChange_eq {k : Type u} [Field k] {F : Type u} [Field F] [Algebra k F]
    (A : Work.GenusZero.Sch k) (x : Work.GCBasics.specOf k F ⟶ A) :
    Work.GenusZero.ptBaseChange (k := k) F A x =
      ptBaseChangeUnit (k := k) (F := F) ≫ (Work.GenusZero.bcFun F).map x := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · rw [Work.GenusZero.ptBaseChange_left, pullback.lift_fst, Over.comp_left, Category.assoc,
      Work.GenusZero.bcFun_map_left_fst, ← Category.assoc, ptBaseChangeUnit_fst]
    simp
  · rw [Work.GenusZero.ptBaseChange_left, pullback.lift_snd, Over.comp_left, Category.assoc,
      Work.GenusZero.bcFun_map_left_snd, ptBaseChangeUnit_snd]

/-- Precomposition with a morphism out of the tensor unit preserves products, for the monoid
structure on `Hom(-, M)` of a monoid object `M` of a cartesian monoidal category. -/
lemma comp_mul_of_monObj {C : Type*} [Category C] [CartesianMonoidalCategory C]
    {X M : C} [MonObj M] (u : 𝟙_ C ⟶ X) (a b : X ⟶ M) :
    u ≫ (a * b) = (u ≫ a) * (u ≫ b) := by
  rw [Hom.mul_def, Hom.mul_def, ← Category.assoc, CartesianMonoidalCategory.comp_lift]

/-- Precomposition with a morphism out of the tensor unit preserves the unit, for the monoid
structure on `Hom(-, M)` of a monoid object `M` of a cartesian monoidal category. -/
lemma comp_one_of_monObj {C : Type*} [Category C] [CartesianMonoidalCategory C]
    {X M : C} [MonObj M] (u : 𝟙_ C ⟶ X) :
    u ≫ (1 : X ⟶ M) = 1 := by
  rw [Hom.one_def, ← Category.assoc,
    SemiCartesianMonoidalCategory.toUnit_unique (u ≫ SemiCartesianMonoidalCategory.toUnit X)
      (SemiCartesianMonoidalCategory.toUnit (𝟙_ C)), Hom.one_def]

/-- `ptBaseChange F A`, as a monoid homomorphism. -/
def ptBaseChangeMonoidHom {k : Type u} [Field k] {F : Type u} [Field F] [Algebra k F]
    (A : Work.GenusZero.Sch k) [CategoryTheory.GrpObj A] [CategoryTheory.IsCommMonObj A] :
    (Work.GCBasics.specOf k F ⟶ A) →*
      (𝟙_ (Work.GenusZero.Sch F) ⟶ (Work.GenusZero.bcFun F).obj A) where
  toFun := Work.GenusZero.ptBaseChange (k := k) F A
  map_one' := by
    rw [ptBaseChange_eq (k := k) (F := F) A (1 : Work.GCBasics.specOf k F ⟶ A),
      Functor.map_one, comp_one_of_monObj]
  map_mul' := by
    intro x y
    rw [ptBaseChange_eq (k := k) (F := F) A (x * y), ptBaseChange_eq (k := k) (F := F) A x,
      ptBaseChange_eq (k := k) (F := F) A y, Functor.map_mul, comp_mul_of_monObj]

end

/-- Base change of points of a group scheme along a field extension `F/k` commutes with finite
products of points: `ptBaseChange F A (∏ i, u i) = ∏ i, ptBaseChange F A (u i)`.

Here `Work.GenusZero.ptBaseChange F A : (specOf k F ⟶ A) → (𝟙_ (Sch F) ⟶ A_F)` is defined
concretely as `Over.homMk (pullback.lift x.left 𝟙 _) _`; it is the transpose of the pullback
`Over.pullback (Spec.map k→F)` along the adjunction `Over.map ⊣ Over.pullback`, hence a bijection.
The multiplication is the one induced by `GrpObj A` (and, on the base change `A_F`, by its
transport along the monoidal functor `Over.pullback`). -/
theorem ptBaseChange_prod {k : Type u} [Field k] {F : Type u} [Field F] [Algebra k F]
    {A : Work.GenusZero.Sch k} [CategoryTheory.GrpObj A] [CategoryTheory.IsCommMonObj A]
    {I : Type u} [Fintype I] (u : I → (Work.GCBasics.specOf k F ⟶ A)) :
    Work.GenusZero.ptBaseChange (k := k) F A (∏ i, u i) =
      ∏ i, Work.GenusZero.ptBaseChange (k := k) F A (u i) := by
  have h := map_prod (ptBaseChangeMonoidHom (k := k) (F := F) A) u Finset.univ
  exact h

end Work.CurveFacts

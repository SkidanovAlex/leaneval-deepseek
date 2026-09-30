import Mathlib
import Submission.Work.SymQuot.RelQuot.tensorIncl_range
import Submission.Work.SymQuot.RelQuot.specFixedPoints_lift

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.SymQuot.RelQuot

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct MonoidalCategory

universe u

noncomputable section


/-- **The universal property of `Spec (C ^ Γ)` in `Sch/K`.**

Let `C` be a `K`-algebra with an action of the finite group `Γ` by `K`-algebra automorphisms,
and let `f : Spec C ⟶ Z` be a morphism of `K`-schemes which is invariant under the action of `Γ`.
Then `f` factors uniquely through the morphism `Spec (C^Γ) ⟶ Spec C` induced by the inclusion of
the fixed subalgebra.

This is the `Over (Spec K)`-version of `Work.SymQuot.RelQuot.specFixedPoints_lift`: the extra
content is that the unique factorisation is itself a morphism of `K`-schemes.  It is obtained by
applying `specFixedPoints_lift` twice -- once to `f.left` and once to the structure morphism of
`Spec C` -- and using the uniqueness in the latter to identify the structure morphism of
`Spec (C^Γ)`. -/
theorem specFixedPoints_lift_over {K : Type u} [Field K] {Γ : Type u} [Group Γ] [Fintype Γ]
    (C : Type u) [CommRing C] [Algebra K C] [MulSemiringAction Γ C] [SMulCommClass Γ K C]
    {Z : Work.SpecLin.Sch K}
    (f : Work.SpecLin.specOf (K := K) C ⟶ Z)
    (hf : ∀ g : Γ, Work.SpecLin.specOfMap (MulSemiringAction.toAlgHom K C g) ≫ f = f) :
    ∃! h : Work.SpecLin.specOf (K := K) ↥(FixedPoints.subalgebra K C Γ) ⟶ Z,
      Work.SpecLin.specOfMap (Subalgebra.val (FixedPoints.subalgebra K C Γ)) ≫ h = f := by
  classical
  have hf_left : ∀ g : Γ,
      Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom Γ C g)) ≫ f.left = f.left := by
    intro g
    have h := congrArg (fun m : Work.SpecLin.specOf (K:=K) C ⟶ Z => m.left) (hf g)
    rw [show (Work.SpecLin.specOfMap (MulSemiringAction.toAlgHom K C g) ≫ f).left
        = Spec.map (CommRingCat.ofHom (MulSemiringAction.toAlgHom K C g).toRingHom) ≫ f.left
        from rfl] at h
    rw [show (MulSemiringAction.toAlgHom K C g).toRingHom = MulSemiringAction.toRingHom Γ C g
        from RingHom.ext (fun x => by
          show (MulSemiringAction.toAlgHom K C g) x = (MulSemiringAction.toRingHom Γ C g) x
          rw [MulSemiringAction.toAlgHom_apply, MulSemiringAction.toRingHom_apply])] at h
    exact h
  obtain ⟨h', hh', huniq'⟩ := specFixedPoints_lift (Γ := Γ) C f.left hf_left
  have hg0_inv : ∀ g : Γ,
      Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom Γ C g)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K C)) =
      Spec.map (CommRingCat.ofHom (algebraMap K C)) := by
    intro g
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 1
    ext k
    simp only [CommRingCat.hom_ofHom]
    rw [RingHom.comp_apply, MulSemiringAction.toRingHom_apply]
    exact smul_algebraMap g k
  obtain ⟨q, hq, huniq_q⟩ := specFixedPoints_lift (Γ := Γ) C
      (Spec.map (CommRingCat.ofHom (algebraMap K C))) hg0_inv
  have hq_eq : q = Spec.map (CommRingCat.ofHom
      (algebraMap K ↥(FixedPoints.subalgebra K C Γ))) := by
    symm
    apply huniq_q
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 1
  have hover : h' ≫ Z.hom = Spec.map (CommRingCat.ofHom
      (algebraMap K ↥(FixedPoints.subalgebra K C Γ))) := by
    rw [← hq_eq]
    apply huniq_q
    rw [← Category.assoc, hh', Over.w f]
    rfl
  refine ⟨Over.homMk h' hover, ?_, ?_⟩
  · apply Over.OverMorphism.ext
    show Spec.map (CommRingCat.ofHom (Subalgebra.val (FixedPoints.subalgebra K C Γ)).toRingHom)
        ≫ h' = f.left
    rw [show (Subalgebra.val (FixedPoints.subalgebra K C Γ)).toRingHom
        = Subring.subtype (FixedPoints.subring C Γ) from rfl]
    exact hh'
  · intro h₁ hh₁
    apply Over.OverMorphism.ext
    apply huniq'
    have h : (Work.SpecLin.specOfMap (Subalgebra.val (FixedPoints.subalgebra K C Γ))
        ≫ h₁).left = f.left := by rw [hh₁]
    rw [Over.comp_left, show (Work.SpecLin.specOfMap (Subalgebra.val (FixedPoints.subalgebra K C Γ))).left
        = Spec.map (CommRingCat.ofHom (Subalgebra.val (FixedPoints.subalgebra K C Γ)).toRingHom) from rfl,
      show (Subalgebra.val (FixedPoints.subalgebra K C Γ)).toRingHom
        = Subring.subtype (FixedPoints.subring C Γ) from rfl] at h
    exact h

/-- The `K`-algebra map `A^Γ ⊗[K] B ⟶ (A ⊗[K] B)^Γ` induced by `tensorIncl`, using that the
range of `tensorIncl` is the fixed subalgebra. -/
noncomputable def tensorInclToFixed {K : Type u} [Field K] {Γ : Type u} [Group Γ] [Fintype Γ]
    (A : Type u) [CommRing A] [Algebra K A] [MulSemiringAction Γ A] [SMulCommClass Γ K A]
    (B : Type u) [CommRing B] [Algebra K B] :
    (↥(FixedPoints.subalgebra K A Γ) ⊗[K] B) →ₐ[K]
      ↥(FixedPoints.subalgebra K (A ⊗[K] B) Γ) where
  toFun x := ⟨tensorIncl A B x, by
    have h : tensorIncl A B x ∈ Set.range (tensorIncl A B) := Set.mem_range_self x
    rw [(tensorIncl_range A B).2] at h
    exact h⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ x y)
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ x y)
  commutes' k := Subtype.ext (by
    show (tensorIncl A B) (algebraMap K (↥(FixedPoints.subalgebra K A Γ) ⊗[K] B) k) =
      ((algebraMap K ↥(FixedPoints.subalgebra K (A ⊗[K] B) Γ) k :
        ↥(FixedPoints.subalgebra K (A ⊗[K] B) Γ)) : A ⊗[K] B)
    rw [AlgHom.commutes]
    rfl)

/-- `tensorInclToFixed` is compatible with the inclusions into `A ⊗[K] B`. -/
lemma val_comp_tensorInclToFixed {K : Type u} [Field K] {Γ : Type u} [Group Γ] [Fintype Γ]
    (A : Type u) [CommRing A] [Algebra K A] [MulSemiringAction Γ A] [SMulCommClass Γ K A]
    (B : Type u) [CommRing B] [Algebra K B] :
    (Subalgebra.val (FixedPoints.subalgebra K (A ⊗[K] B) Γ)).comp (tensorInclToFixed A B)
      = tensorIncl A B := by
  apply AlgHom.ext
  intro x
  rfl

/-- `tensorInclToFixed` is bijective: `tensorIncl` is injective with range the fixed points. -/
lemma bijective_tensorInclToFixed {K : Type u} [Field K] {Γ : Type u} [Group Γ] [Fintype Γ]
    (A : Type u) [CommRing A] [Algebra K A] [MulSemiringAction Γ A] [SMulCommClass Γ K A]
    (B : Type u) [CommRing B] [Algebra K B] :
    Function.Bijective (tensorInclToFixed (K:=K) (Γ:=Γ) A B) := by
  refine ⟨?_, ?_⟩
  · intro x y hxy
    exact (tensorIncl_range A B).1 (Subtype.ext_iff.mp hxy)
  · intro y
    have hy : (y : A ⊗[K] B) ∈ {z : A ⊗[K] B | ∀ g : Γ, tensorAct A B g z = z} :=
      fun g => y.2 g
    rw [← (tensorIncl_range A B).2] at hy
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, Subtype.ext hx⟩

open CategoryTheory Limits AlgebraicGeometry in
open scoped TensorProduct MonoidalCategory in
theorem specOf_tensorIncl_factor {K : Type u} [Field K] {Γ : Type u} [Group Γ] [Fintype Γ]
    {A : Type u} [CommRing A] [Algebra K A] [MulSemiringAction Γ A] [SMulCommClass Γ K A]
    {B : Type u} [CommRing B] [Algebra K B] {Z : Work.SpecLin.Sch K}
    (f : Work.SpecLin.specOf (K := K) (A ⊗[K] B) ⟶ Z)
    (hf : ∀ g : Γ, Work.SpecLin.specOfMap
      (Work.SymQuot.RelQuot.tensorAct (K := K) (Γ := Γ) A B g) ≫ f = f) :
    ∃! h : Work.SpecLin.specOf (K := K) (↥(FixedPoints.subalgebra K A Γ) ⊗[K] B) ⟶ Z,
      Work.SpecLin.specOfMap (Work.SymQuot.RelQuot.tensorIncl (K := K) (Γ := Γ) A B) ≫ h = f := by
  classical
  have hf' : ∀ g : Γ, Work.SpecLin.specOfMap
      (MulSemiringAction.toAlgHom K (A ⊗[K] B) g) ≫ f = f := by
    intro g
    rw [show MulSemiringAction.toAlgHom K (A ⊗[K] B) g = tensorAct A B g from by
      apply AlgHom.ext; intro x; rw [MulSemiringAction.toAlgHom_apply]; rfl]
    exact hf g
  obtain ⟨hA, hhA, huniqA⟩ := specFixedPoints_lift_over (K:=K) (Γ:=Γ) (A ⊗[K] B) f hf'
  let φ : (↥(FixedPoints.subalgebra K A Γ) ⊗[K] B) ≃ₐ[K]
      ↥(FixedPoints.subalgebra K (A ⊗[K] B) Γ) :=
    AlgEquiv.ofBijective _ (bijective_tensorInclToFixed (K:=K) (Γ:=Γ) A B)
  have hφ' : (Subalgebra.val (FixedPoints.subalgebra K (A ⊗[K] B) Γ)).comp φ.toAlgHom
      = tensorIncl A B :=
    val_comp_tensorInclToFixed (K:=K) (Γ:=Γ) A B
  have key : Work.SpecLin.specOfMap (tensorIncl A B) =
      Work.SpecLin.specOfMap (Subalgebra.val (FixedPoints.subalgebra K (A ⊗[K] B) Γ)) ≫
        Work.SpecLin.specOfMap φ.toAlgHom := by
    rw [← hφ', Work.SpecLin.specOfMap_comp]
  have hcancel1 : Work.SpecLin.specOfMap φ.toAlgHom ≫ Work.SpecLin.specOfMap φ.symm.toAlgHom
      = 𝟙 (Work.SpecLin.specOf (K:=K) ↥(FixedPoints.subalgebra K (A ⊗[K] B) Γ)) := by
    rw [← Work.SpecLin.specOfMap_comp]
    have h : (φ.toAlgHom).comp (φ.symm.toAlgHom) = AlgHom.id K _ := by
      apply AlgHom.ext; intro x; simp
    rw [h, Work.SpecLin.specOfMap_id]
  have hcancel2 : Work.SpecLin.specOfMap φ.symm.toAlgHom ≫ Work.SpecLin.specOfMap φ.toAlgHom
      = 𝟙 (Work.SpecLin.specOf (K:=K) (↥(FixedPoints.subalgebra K A Γ) ⊗[K] B)) := by
    rw [← Work.SpecLin.specOfMap_comp]
    have h : (φ.symm.toAlgHom).comp (φ.toAlgHom) = AlgHom.id K _ := by
      apply AlgHom.ext; intro x; simp
    rw [h, Work.SpecLin.specOfMap_id]
  refine ⟨Work.SpecLin.specOfMap φ.symm.toAlgHom ≫ hA, ?_, ?_⟩
  · show Work.SpecLin.specOfMap (tensorIncl A B)
        ≫ (Work.SpecLin.specOfMap φ.symm.toAlgHom ≫ hA) = f
    rw [key]
    rw [show (Work.SpecLin.specOfMap (Subalgebra.val (FixedPoints.subalgebra K (A ⊗[K] B) Γ))
            ≫ Work.SpecLin.specOfMap φ.toAlgHom)
          ≫ (Work.SpecLin.specOfMap φ.symm.toAlgHom ≫ hA)
        = Work.SpecLin.specOfMap (Subalgebra.val (FixedPoints.subalgebra K (A ⊗[K] B) Γ))
          ≫ ((Work.SpecLin.specOfMap φ.toAlgHom ≫ Work.SpecLin.specOfMap φ.symm.toAlgHom)
            ≫ hA)
        from by simp only [Category.assoc]]
    rw [hcancel1, Category.id_comp, hhA]
  · intro h₁ hh₁
    have hh₁' : Work.SpecLin.specOfMap (Subalgebra.val (FixedPoints.subalgebra K (A ⊗[K] B) Γ))
        ≫ (Work.SpecLin.specOfMap φ.toAlgHom ≫ h₁) = f := by
      rw [← Category.assoc, ← key, hh₁]
    have h1 : Work.SpecLin.specOfMap φ.toAlgHom ≫ h₁ = hA := huniqA _ hh₁'
    calc h₁ = 𝟙 _ ≫ h₁ := (Category.id_comp _).symm
      _ = (Work.SpecLin.specOfMap φ.symm.toAlgHom ≫ Work.SpecLin.specOfMap φ.toAlgHom) ≫ h₁ := by
            rw [hcancel2]
      _ = Work.SpecLin.specOfMap φ.symm.toAlgHom ≫ (Work.SpecLin.specOfMap φ.toAlgHom ≫ h₁) :=
            Category.assoc _ _ _
      _ = Work.SpecLin.specOfMap φ.symm.toAlgHom ≫ hA := by rw [h1]

end

end Work.SymQuot.RelQuot

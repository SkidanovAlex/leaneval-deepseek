import Mathlib
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits
section DiscreteNat

/-- The natural transformation on the discrete category with components `f i`. -/
noncomputable def discreteNatTrans {C : Type*} [Category C] {ι : Type} {A B : ι → C}
    (f : ∀ i, A i ⟶ B i) : Discrete.functor A ⟶ Discrete.functor B :=
  Discrete.natTrans (fun i => f i.as)

lemma discreteNatTrans_app {C : Type*} [Category C] {ι : Type} {A B : ι → C}
    (f : ∀ i, A i ⟶ B i) (i : Discrete ι) : (discreteNatTrans f).app i = f i.as := rfl

end DiscreteNat

section SigmaHelpers

variable {C : Type*} [Category C]

/-- The coproduct of a composite family of morphisms is the composite of the coproducts. -/
lemma Sigma.map_comp' {ι : Type} {A B D : ι → C}
    (f : ∀ i, A i ⟶ B i) (g : ∀ i, B i ⟶ D i)
    [HasCoproduct A] [HasCoproduct B] [HasCoproduct D] :
    Limits.Sigma.map f ≫ Limits.Sigma.map g = Limits.Sigma.map (fun i => f i ≫ g i) := by
  apply Sigma.hom_ext
  intro i
  rw [← Category.assoc, Sigma.ι_map, Category.assoc, Sigma.ι_map, Sigma.ι_map, Category.assoc]

lemma Sigma.map_zero' {ι : Type} [HasZeroMorphisms C] {A B : ι → C}
    [HasCoproduct A] [HasCoproduct B] : Limits.Sigma.map (fun i => (0 : A i ⟶ B i)) = 0 := by
  apply Sigma.hom_ext
  intro i
  rw [Sigma.ι_map]
  simp

/-- The coproduct of a family of morphisms is the `colimMap` of the corresponding
natural transformation between discrete functors. -/
lemma Sigma.map_eq_colimMap {ι : Type} {A B : ι → C}
    (f : ∀ i, A i ⟶ B i) [HasCoproduct A] [HasCoproduct B] :
    Limits.Sigma.map f = colimMap (discreteNatTrans f) := by
  apply Sigma.hom_ext
  intro i
  rw [Sigma.ι_map, ι_colimMap]
  simp [discreteNatTrans_app]

end SigmaHelpers

section KernelsCokernels

variable {C : Type*} [Category C] [HasZeroMorphisms C]

end KernelsCokernels

section CoprodComplex

variable {C : Type*} [Category C] [Preadditive C]

/-- The **pointwise coproduct** of a family of chain complexes: in each degree it is the
coproduct of the terms, and the differentials are the coproducts of the differentials. -/
noncomputable def coprodComplex {ι : Type} [HasCoproductsOfShape ι C]
    (F : ι → ChainComplex C ℕ) : ChainComplex C ℕ where
  X n := ∐ (fun i => (F i).X n)
  d n m := Limits.Sigma.map (fun i => (F i).d n m)
  shape n m h := by
    rw [show (fun i => (F i).d n m) = (fun i => (0 : (F i).X n ⟶ (F i).X m)) from
      funext fun i => (F i).shape n m h]
    exact Sigma.map_zero'
  d_comp_d' n m k hnm hmk := by
    rw [Sigma.map_comp']
    have h : (fun i => (F i).d n m ≫ (F i).d m k) = (fun i => (0 : (F i).X n ⟶ (F i).X k)) :=
      funext fun i => (F i).d_comp_d n m k
    rw [h, Sigma.map_zero']

@[simp] lemma coprodComplex_d {ι : Type} [HasCoproductsOfShape ι C]
    (F : ι → ChainComplex C ℕ) (n m : ℕ) :
    (coprodComplex F).d n m = Limits.Sigma.map (fun i => (F i).d n m) := rfl

end CoprodComplex

section CoprodShortComplex

variable {C : Type*} [Category C] [Preadditive C]

/-- The **pointwise coproduct** of a family of short complexes. -/
noncomputable def coprodShortComplex {ι : Type} [HasCoproductsOfShape ι C]
    (S : ι → ShortComplex C) : ShortComplex C where
  X₁ := ∐ (fun i => (S i).X₁)
  X₂ := ∐ (fun i => (S i).X₂)
  X₃ := ∐ (fun i => (S i).X₃)
  f := Limits.Sigma.map (fun i => (S i).f)
  g := Limits.Sigma.map (fun i => (S i).g)
  zero := by
    rw [Sigma.map_comp']
    have h : (fun i => (S i).f ≫ (S i).g) = (fun i => (0 : (S i).X₁ ⟶ (S i).X₃)) :=
      funext fun i => (S i).zero
    rw [h, Sigma.map_zero']

end CoprodShortComplex

section Kernel

variable {C : Type*} [Category C] [HasZeroMorphisms C]

end Kernel

section Cokernel

variable {C : Type*} [Category C] [HasZeroMorphisms C]

end Cokernel

end Work.SSSR

import Mathlib

/-!
# Auxiliary material for the homology of a coproduct of chain complexes

In this file we collect the elementary constructions and lemmas used in the proof that
the homology of a coproduct of chain complexes of `ℤ`-modules is the coproduct of the
homologies (Serre finiteness project, `Work.SSS.homology_sigma`).

* `discreteNatTrans` : the natural transformation on a discrete category induced by a family
  of morphisms;
* the behaviour of the "coproduct of a family of morphisms" under composition and zero;
* `coprodComplex` : the pointwise coproduct of a family of chain complexes;
* the (co)kernels of such a coproduct, which is where the exactness of coproducts (AB4/AB5)
  enters.
-/

namespace Work.SSS

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

/-- The fork exhibiting the coproduct of the kernels as the kernel of the coproduct. -/
lemma sigmaMap_kernel_condition {ι : Type} {A B : ι → C} (f : ∀ i, A i ⟶ B i)
    [HasKernels C] [HasCoproduct A] [HasCoproduct B] [HasCoproduct (fun i => kernel (f i))] :
    Limits.Sigma.map (fun i => kernel.ι (f i)) ≫ Limits.Sigma.map f = 0 := by
  rw [Sigma.map_comp']
  have h : (fun i => kernel.ι (f i) ≫ f i) = (fun i => (0 : kernel (f i) ⟶ B i)) :=
    funext fun i => kernel.condition (f i)
  rw [h, Sigma.map_zero']

/-- The cofork exhibiting the coproduct of the cokernels as the cokernel of the coproduct. -/
lemma sigmaMap_cokernel_condition {ι : Type} {A B : ι → C} (f : ∀ i, A i ⟶ B i)
    [HasCokernels C] [HasCoproduct A] [HasCoproduct B] [HasCoproduct (fun i => cokernel (f i))] :
    Limits.Sigma.map f ≫ Limits.Sigma.map (fun i => cokernel.π (f i)) = 0 := by
  rw [Sigma.map_comp']
  have h : (fun i => f i ≫ cokernel.π (f i)) = (fun i => (0 : A i ⟶ cokernel (f i))) :=
    funext fun i => cokernel.condition (f i)
  rw [h, Sigma.map_zero']

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

@[simp] lemma coprodComplex_X {ι : Type} [HasCoproductsOfShape ι C]
    (F : ι → ChainComplex C ℕ) (n : ℕ) :
    (coprodComplex F).X n = ∐ (fun i => (F i).X n) := rfl

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

@[simp] lemma coprodShortComplex_X₁ {ι : Type} [HasCoproductsOfShape ι C]
    (S : ι → ShortComplex C) : (coprodShortComplex S).X₁ = ∐ (fun i => (S i).X₁) := rfl

@[simp] lemma coprodShortComplex_X₂ {ι : Type} [HasCoproductsOfShape ι C]
    (S : ι → ShortComplex C) : (coprodShortComplex S).X₂ = ∐ (fun i => (S i).X₂) := rfl

@[simp] lemma coprodShortComplex_X₃ {ι : Type} [HasCoproductsOfShape ι C]
    (S : ι → ShortComplex C) : (coprodShortComplex S).X₃ = ∐ (fun i => (S i).X₃) := rfl

@[simp] lemma coprodShortComplex_f {ι : Type} [HasCoproductsOfShape ι C]
    (S : ι → ShortComplex C) : (coprodShortComplex S).f = Limits.Sigma.map (fun i => (S i).f) := rfl

@[simp] lemma coprodShortComplex_g {ι : Type} [HasCoproductsOfShape ι C]
    (S : ι → ShortComplex C) : (coprodShortComplex S).g = Limits.Sigma.map (fun i => (S i).g) := rfl

end CoprodShortComplex

section Kernel

variable {C : Type*} [Category C] [HasZeroMorphisms C]

/-- **Coproducts commute with kernels**: the coproduct of the kernels is the kernel of
the coproduct of the morphisms. -/
noncomputable def isLimit_sigmaMap_kernel {ι : Type} {A B : ι → C} (f : ∀ i, A i ⟶ B i)
    [HasKernels C] [HasCoproduct A] [HasCoproduct B] [HasCoproduct (fun i => kernel (f i))]
    [HasColimitsOfShape (Discrete ι) C]
    [PreservesLimit (parallelPair
      (Discrete.natTrans (fun (i : Discrete ι) => f i.as) :
        Discrete.functor A ⟶ Discrete.functor B) 0)
      (colim (J := Discrete ι) (C := C))] :
    IsLimit (KernelFork.ofι (Limits.Sigma.map (fun i => kernel.ι (f i)))
      (sigmaMap_kernel_condition f) : KernelFork (Limits.Sigma.map f)) := by
  let α : Discrete.functor A ⟶ Discrete.functor B :=
    Discrete.natTrans (fun (i : Discrete ι) => f i.as)
  let k : Discrete.functor (fun i => kernel (f i)) ⟶ Discrete.functor A :=
    Discrete.natTrans (fun (i : Discrete ι) => kernel.ι (f i.as))
  have hk : k ≫ α = 0 := by
    ext i
    simp [k, α, kernel.condition]
  have hlim : IsLimit (KernelFork.ofι k hk) := by
    apply evaluationJointlyReflectsLimits
    intro i
    refine (KernelFork.isLimitMapConeEquiv (KernelFork.ofι k hk)
      ((evaluation (Discrete ι) C).obj i)).2 ?_
    refine IsLimit.mk (fun s => (kernelIsKernel (f i.as)).lift s) ?_ ?_
    · intro s j
      exact (kernelIsKernel (f i.as)).fac s j
    · intro s m hm
      exact (kernelIsKernel (f i.as)).uniq s m hm
  have h3 : IsLimit ((KernelFork.ofι k hk).map (colim (J := Discrete ι) (C := C))) :=
    (KernelFork.isLimitMapConeEquiv (KernelFork.ofι k hk)
      (colim (J := Discrete ι) (C := C))).1
      (isLimitOfPreserves (colim (J := Discrete ι) (C := C)) hlim)
  have hdiag : colimMap α = Limits.Sigma.map f := (Sigma.map_eq_colimMap f).symm
  let e : parallelPair (colimMap α) 0 ≅ parallelPair (Limits.Sigma.map f) 0 :=
    parallelPair.ext (Iso.refl _) (Iso.refl _) (by simp [hdiag]) (by simp)
  have hcon : IsLimit ((Cone.postcompose e.hom).obj
      ((KernelFork.ofι k hk).map (colim (J := Discrete ι) (C := C)))) :=
    (IsLimit.postcomposeHomEquiv e _).symm h3
  refine IsLimit.ofIsoLimit hcon (Fork.ext (Iso.refl _) ?_)
  show (𝟙 _) ≫ Fork.ι (KernelFork.ofι (Limits.Sigma.map (fun i => kernel.ι (f i)))
      (sigmaMap_kernel_condition f) : KernelFork (Limits.Sigma.map f)) =
    Fork.ι ((Cone.postcompose e.hom).obj
      ((KernelFork.ofι k hk).map (colim (J := Discrete ι) (C := C))))
  rw [Category.id_comp, KernelFork.ι_ofι]
  show Limits.Sigma.map (fun i => kernel.ι (f i)) =
    ((Cone.postcompose e.hom).obj
      ((KernelFork.ofι k hk).map (colim (J := Discrete ι) (C := C)))).π.app
        WalkingParallelPair.zero
  have h1 : ((KernelFork.ofι k hk).map (colim (J := Discrete ι) (C := C))).π.app
      WalkingParallelPair.zero = colimMap k := by
    show Fork.ι ((KernelFork.ofι k hk).map (colim (J := Discrete ι) (C := C))) = colimMap k
    rw [KernelFork.map_ι, KernelFork.ι_ofι]
    rfl
  have hcomp : ((Cone.postcompose e.hom).obj ((KernelFork.ofι k hk).map
      (colim (J := Discrete ι) (C := C)))).π.app WalkingParallelPair.zero
      = ((KernelFork.ofι k hk).map (colim (J := Discrete ι) (C := C))).π.app
        WalkingParallelPair.zero := by
    rw [Cone.postcompose_obj_π, NatTrans.comp_app]
    rw [show e.hom.app WalkingParallelPair.zero = 𝟙 _ from rfl, Category.comp_id]
  rw [hcomp, h1]
  exact Sigma.map_eq_colimMap (fun i => kernel.ι (f i))

end Kernel

section Cokernel

variable {C : Type*} [Category C] [HasZeroMorphisms C]

/-- **Coproducts commute with cokernels**: the coproduct of the cokernels is the cokernel of
the coproduct of the morphisms. -/
noncomputable def isColimit_sigmaMap_cokernel {ι : Type} {A B : ι → C} (f : ∀ i, A i ⟶ B i)
    [HasCokernels C] [HasCoproduct A] [HasCoproduct B] [HasCoproduct (fun i => cokernel (f i))]
    [HasColimitsOfShape (Discrete ι) C]
    [PreservesColimit (parallelPair 0
      (Discrete.natTrans (fun (i : Discrete ι) => f i.as) :
        Discrete.functor A ⟶ Discrete.functor B))
      (colim (J := Discrete ι) (C := C))] :
    IsColimit (CokernelCofork.ofπ (Limits.Sigma.map (fun i => cokernel.π (f i)))
      (sigmaMap_cokernel_condition f) : CokernelCofork (Limits.Sigma.map f)) := by
  let α : Discrete.functor A ⟶ Discrete.functor B :=
    Discrete.natTrans (fun (i : Discrete ι) => f i.as)
  let k : Discrete.functor B ⟶ Discrete.functor (fun i => cokernel (f i)) :=
    Discrete.natTrans (fun (i : Discrete ι) => cokernel.π (f i.as))
  have hk : α ≫ k = 0 := by
    ext i
    simp [k, α, cokernel.condition]
  have hcolim : IsColimit (CokernelCofork.ofπ k hk) := by
    apply evaluationJointlyReflectsColimits
    intro i
    refine (CokernelCofork.isColimitMapCoconeEquiv (CokernelCofork.ofπ k hk)
      ((evaluation (Discrete ι) C).obj i)).2 ?_
    refine IsColimit.mk (fun s => (cokernelIsCokernel (f i.as)).desc s) ?_ ?_
    · intro s j
      exact (cokernelIsCokernel (f i.as)).fac s j
    · intro s m hm
      exact (cokernelIsCokernel (f i.as)).uniq s m hm
  have h3 : IsColimit ((CokernelCofork.ofπ k hk).map (colim (J := Discrete ι) (C := C))) :=
    (CokernelCofork.isColimitMapCoconeEquiv (CokernelCofork.ofπ k hk)
      (colim (J := Discrete ι) (C := C))).1
      (isColimitOfPreserves (colim (J := Discrete ι) (C := C)) hcolim)
  have hdiag : colimMap α = Limits.Sigma.map f := (Sigma.map_eq_colimMap f).symm
  let sc : CokernelCofork (Limits.Sigma.map f) :=
    CokernelCofork.ofπ (Limits.Sigma.map (fun i => cokernel.π (f i)))
      (sigmaMap_cokernel_condition f)
  let e : parallelPair (colimMap α) 0 ≅ parallelPair (Limits.Sigma.map f) 0 :=
    parallelPair.ext (Iso.refl _) (Iso.refl _) (by simp [hdiag]) (by simp)
  have h1 : Cofork.π ((CokernelCofork.ofπ k hk).map (colim (J := Discrete ι) (C := C))) =
      colimMap k := by
    rw [CokernelCofork.map_π, CokernelCofork.π_ofπ]
    rfl
  have hcomp2 : Cofork.π ((Cocone.precompose e.hom).obj sc) =
      Limits.Sigma.map (fun i => cokernel.π (f i)) := by
    show ((Cocone.precompose e.hom).obj sc).ι.app WalkingParallelPair.one =
      Limits.Sigma.map (fun i => cokernel.π (f i))
    rw [Cocone.precompose_obj_ι, NatTrans.comp_app,
      show e.hom.app WalkingParallelPair.one = 𝟙 _ from rfl, Category.id_comp]
    show Cofork.π sc = Limits.Sigma.map (fun i => cokernel.π (f i))
    rw [CokernelCofork.π_ofπ]
  have hcomp1 : Cofork.π ((CokernelCofork.ofπ k hk).map (colim (J := Discrete ι) (C := C))) ≫
      (Iso.refl ((CokernelCofork.ofπ k hk).map (colim (J := Discrete ι) (C := C))).pt).hom =
      Limits.Sigma.map (fun i => cokernel.π (f i)) := by
    rw [Iso.refl_hom, h1]
    exact (Category.comp_id (colimMap k)).trans
      (Sigma.map_eq_colimMap (fun i => cokernel.π (f i))).symm
  have hpre : IsColimit ((Cocone.precompose e.hom).obj sc) := by
    refine IsColimit.ofIsoColimit h3 (Cofork.ext (Iso.refl _) ?_)
    exact hcomp1.trans hcomp2.symm
  exact IsColimit.precomposeHomEquiv e sc hpre

end Cokernel

end Work.SSS

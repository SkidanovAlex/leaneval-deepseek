import Mathlib
import Submission.Work.SSSR.HomologySigmaAux
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits
section Helpers

variable {C : Type*} [Category C] [HasZeroMorphisms C]

lemma sigmaMap_kernel_zero' {ι : Type} {A B D : ι → C} (f : ∀ i, A i ⟶ B i)
    (k : ∀ i, D i ⟶ A i) (hk : ∀ i, k i ≫ f i = 0) [HasCoproduct A] [HasCoproduct B]
    [HasCoproduct D] :
    Limits.Sigma.map k ≫ Limits.Sigma.map f = 0 := by
  refine (Sigma.map_comp' k f).trans ?_
  have h : (fun i => k i ≫ f i) = (fun _ => 0) := funext hk
  rw [h, Sigma.map_zero']

lemma sigmaMap_cokernel_zero' {ι : Type} {A B D : ι → C} (f : ∀ i, A i ⟶ B i)
    (c : ∀ i, B i ⟶ D i) (hc : ∀ i, f i ≫ c i = 0) [HasCoproduct A] [HasCoproduct B]
    [HasCoproduct D] :
    Limits.Sigma.map f ≫ Limits.Sigma.map c = 0 := by
  refine (Sigma.map_comp' f c).trans ?_
  have h : (fun i => f i ≫ c i) = (fun _ => 0) := funext hc
  rw [h, Sigma.map_zero']

end Helpers

section KernelFork

variable {C : Type*} [Category C] [HasZeroMorphisms C]

noncomputable def isLimit_sigmaMap_kernelFork {ι : Type} {A B D : ι → C} (f : ∀ i, A i ⟶ B i)
    (κ : ∀ i, D i ⟶ A i) (hκ : ∀ i, κ i ≫ f i = 0)
    (H : ∀ i, IsLimit (KernelFork.ofι (κ i) (hκ i)))
    [HasColimitsOfShape (Discrete ι) C]
    [PreservesLimit (parallelPair (Discrete.natTrans (fun (i : Discrete ι) => f i.as) :
      Discrete.functor A ⟶ Discrete.functor B) 0) (colim (J := Discrete ι) (C := C))]
    (hκ' : Limits.Sigma.map κ ≫ Limits.Sigma.map f = 0) :
    IsLimit (KernelFork.ofι (Limits.Sigma.map κ) hκ' : KernelFork (Limits.Sigma.map f)) := by
  let α : Discrete.functor A ⟶ Discrete.functor B :=
    Discrete.natTrans (fun (i : Discrete ι) => f i.as)
  let k : Discrete.functor D ⟶ Discrete.functor A :=
    Discrete.natTrans (fun (i : Discrete ι) => κ i.as)
  have hk : k ≫ α = 0 := by
    ext i
    simp [k, α, hκ i.as]
  have hlim : IsLimit (KernelFork.ofι k hk) := by
    apply evaluationJointlyReflectsLimits
    intro i
    refine (KernelFork.isLimitMapConeEquiv (KernelFork.ofι k hk)
      ((evaluation (Discrete ι) C).obj i)).2 ?_
    refine IsLimit.mk (fun s => (H i.as).lift s) ?_ ?_
    · intro s j
      exact (H i.as).fac s j
    · intro s m hm
      exact (H i.as).uniq s m hm
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
  show (𝟙 _) ≫ Fork.ι (KernelFork.ofι (Limits.Sigma.map κ) hκ' : KernelFork (Limits.Sigma.map f)) =
    Fork.ι ((Cone.postcompose e.hom).obj
      ((KernelFork.ofι k hk).map (colim (J := Discrete ι) (C := C))))
  rw [Category.id_comp, KernelFork.ι_ofι]
  show Limits.Sigma.map κ =
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
  exact Sigma.map_eq_colimMap κ

noncomputable def isColimit_sigmaMap_cokernelCofork {ι : Type} {A B D : ι → C} (f : ∀ i, A i ⟶ B i)
    (c : ∀ i, B i ⟶ D i) (hc : ∀ i, f i ≫ c i = 0)
    (H : ∀ i, IsColimit (CokernelCofork.ofπ (c i) (hc i)))
    [HasColimitsOfShape (Discrete ι) C]
    [PreservesColimit (parallelPair 0 (Discrete.natTrans (fun (i : Discrete ι) => f i.as) :
      Discrete.functor A ⟶ Discrete.functor B)) (colim (J := Discrete ι) (C := C))]
    (hc' : Limits.Sigma.map f ≫ Limits.Sigma.map c = 0) :
    IsColimit (CokernelCofork.ofπ (Limits.Sigma.map c) hc' : CokernelCofork (Limits.Sigma.map f)) := by
  let α : Discrete.functor A ⟶ Discrete.functor B :=
    Discrete.natTrans (fun (i : Discrete ι) => f i.as)
  let k : Discrete.functor B ⟶ Discrete.functor D :=
    Discrete.natTrans (fun (i : Discrete ι) => c i.as)
  have hk : α ≫ k = 0 := by
    ext i
    simp [k, α, hc i.as]
  have hcolim : IsColimit (CokernelCofork.ofπ k hk) := by
    apply evaluationJointlyReflectsColimits
    intro i
    refine (CokernelCofork.isColimitMapCoconeEquiv (CokernelCofork.ofπ k hk)
      ((evaluation (Discrete ι) C).obj i)).2 ?_
    refine IsColimit.mk (fun s => (H i.as).desc s) ?_ ?_
    · intro s j
      exact (H i.as).fac s j
    · intro s m hm
      exact (H i.as).uniq s m hm
  have h3 : IsColimit ((CokernelCofork.ofπ k hk).map (colim (J := Discrete ι) (C := C))) :=
    (CokernelCofork.isColimitMapCoconeEquiv (CokernelCofork.ofπ k hk)
      (colim (J := Discrete ι) (C := C))).1
      (isColimitOfPreserves (colim (J := Discrete ι) (C := C)) hcolim)
  have hdiag : colimMap α = Limits.Sigma.map f := (Sigma.map_eq_colimMap f).symm
  let sc : CokernelCofork (Limits.Sigma.map f) :=
    CokernelCofork.ofπ (Limits.Sigma.map c) hc'
  let e : parallelPair (colimMap α) 0 ≅ parallelPair (Limits.Sigma.map f) 0 :=
    parallelPair.ext (Iso.refl _) (Iso.refl _) (by simp [hdiag]) (by simp)
  have h1 : Cofork.π ((CokernelCofork.ofπ k hk).map (colim (J := Discrete ι) (C := C))) =
      colimMap k := by
    rw [CokernelCofork.map_π, CokernelCofork.π_ofπ]
    rfl
  have hcomp2 : Cofork.π ((Cocone.precompose e.hom).obj sc) = Limits.Sigma.map c := by
    show ((Cocone.precompose e.hom).obj sc).ι.app WalkingParallelPair.one = Limits.Sigma.map c
    rw [Cocone.precompose_obj_ι, NatTrans.comp_app,
      show e.hom.app WalkingParallelPair.one = 𝟙 _ from rfl, Category.id_comp]
    show Cofork.π sc = Limits.Sigma.map c
    rw [CokernelCofork.π_ofπ]
  have hcomp1 : Cofork.π ((CokernelCofork.ofπ k hk).map (colim (J := Discrete ι) (C := C))) ≫
      (Iso.refl ((CokernelCofork.ofπ k hk).map (colim (J := Discrete ι) (C := C))).pt).hom =
      Limits.Sigma.map c := by
    rw [Iso.refl_hom, h1]
    exact (Category.comp_id (colimMap k)).trans (Sigma.map_eq_colimMap c).symm
  have hpre : IsColimit ((Cocone.precompose e.hom).obj sc) := by
    refine IsColimit.ofIsoColimit h3 (Cofork.ext (Iso.refl _) ?_)
    exact hcomp1.trans hcomp2.symm
  exact IsColimit.precomposeHomEquiv e sc hpre

end KernelFork

section LiftCompare

variable {C : Type*} [Category C] [HasZeroMorphisms C]

lemma lift_sigmaMap_kernelFork {ι : Type} {A B D E : ι → C} (f : ∀ i, A i ⟶ B i)
    (k : ∀ i, D i ⟶ A i) (l : ∀ i, E i ⟶ A i) (hk : ∀ i, k i ≫ f i = 0)
    (hl : ∀ i, l i ≫ f i = 0) (H : ∀ i, IsLimit (KernelFork.ofι (k i) (hk i)))
    [HasCoproductsOfShape ι C]
    (hk' : Limits.Sigma.map k ≫ Limits.Sigma.map f = 0)
    (hl' : Limits.Sigma.map l ≫ Limits.Sigma.map f = 0)
    (hi : IsLimit (KernelFork.ofι (Limits.Sigma.map k) hk')) :
    hi.lift (KernelFork.ofι (Limits.Sigma.map l) hl') =
      Limits.Sigma.map (fun i => (H i).lift (KernelFork.ofι (l i) (hl i))) := by
  let φ : ∀ i, E i ⟶ D i := fun i => (H i).lift (KernelFork.ofι (l i) (hl i))
  have hφ : ∀ i, φ i ≫ k i = l i := by
    intro i
    dsimp only [φ]
    simpa only [KernelFork.ι_ofι] using Fork.IsLimit.lift_ι (H i) (t := KernelFork.ofι (l i) (hl i))
  apply Fork.IsLimit.hom_ext hi
  rw [Fork.IsLimit.lift_ι]
  show Limits.Sigma.map l = Limits.Sigma.map φ ≫ Limits.Sigma.map k
  rw [Sigma.map_comp' φ k]
  exact (congrArg Limits.Sigma.map (funext hφ)).symm

lemma IsLimit.lift_comp_conePointIso {A B K K' X : C} {f : A ⟶ B} {κ : K ⟶ A} {κ' : K' ⟶ A}
    {l : X ⟶ A} (hκ : κ ≫ f = 0) (hκ' : κ' ≫ f = 0) (hl : l ≫ f = 0)
    (HK : IsLimit (KernelFork.ofι κ hκ)) (HK' : IsLimit (KernelFork.ofι κ' hκ'))
    (e : K' ≅ K) (he : e.hom ≫ κ = κ') :
    HK'.lift (KernelFork.ofι l hl : KernelFork f) ≫ e.hom
      = HK.lift (KernelFork.ofι l hl : KernelFork f) := by
  apply Fork.IsLimit.hom_ext HK
  show (HK'.lift (KernelFork.ofι l hl : KernelFork f) ≫ e.hom) ≫ κ
      = HK.lift (KernelFork.ofι l hl : KernelFork f) ≫ κ
  rw [Category.assoc, he]
  exact (Fork.IsLimit.lift_ι HK' (t := (KernelFork.ofι l hl : KernelFork f))).trans
    (Fork.IsLimit.lift_ι HK (t := (KernelFork.ofι l hl : KernelFork f))).symm

lemma lift_sigmaMap_eq_sigmaMap_lift {ι : Type} {A B D E : ι → C} (f : ∀ i, A i ⟶ B i)
    (k : ∀ i, D i ⟶ A i) (l : ∀ i, E i ⟶ A i) (hk : ∀ i, k i ≫ f i = 0)
    (hl : ∀ i, l i ≫ f i = 0) (H : ∀ i, IsLimit (KernelFork.ofι (k i) (hk i)))
    [HasCoproductsOfShape ι C]
    (hk' : Limits.Sigma.map k ≫ Limits.Sigma.map f = 0)
    (hl' : Limits.Sigma.map l ≫ Limits.Sigma.map f = 0)
    (hi : IsLimit (KernelFork.ofι (Limits.Sigma.map k) hk'))
    {K : C} {κ : K ⟶ ∐ fun i => A i} (hκ : κ ≫ Limits.Sigma.map f = 0)
    (HK : IsLimit (KernelFork.ofι κ hκ))
    (e : (∐ fun i => D i) ≅ K) (he : e.hom ≫ κ = Limits.Sigma.map k) :
    HK.lift (KernelFork.ofι (Limits.Sigma.map l) hl') =
      Limits.Sigma.map (fun i => (H i).lift (KernelFork.ofι (l i) (hl i))) ≫ e.hom := by
  have h1 : hi.lift (KernelFork.ofι (Limits.Sigma.map l) hl') =
      Limits.Sigma.map (fun i => (H i).lift (KernelFork.ofι (l i) (hl i))) :=
    lift_sigmaMap_kernelFork f k l hk hl H hk' hl' hi
  have h2 : hi.lift (KernelFork.ofι (Limits.Sigma.map l) hl') ≫ e.hom =
      HK.lift (KernelFork.ofι (Limits.Sigma.map l) hl') :=
    IsLimit.lift_comp_conePointIso hκ hk' hl' HK hi e he
  rw [h1] at h2
  exact h2.symm

end LiftCompare

section CompInv

variable {C : Type*} [Category C]

lemma comp_inv_eq_id_comp {A B B' : C} (f : A ⟶ B) (f' : A ⟶ B') (e : B' ≅ B)
    (h : f = f' ≫ e.hom) : f ≫ e.symm.hom = 𝟙 A ≫ f' := by
  calc f ≫ e.symm.hom = (f' ≫ e.hom) ≫ e.symm.hom := by rw [h]
    _ = f' ≫ (e.hom ≫ e.symm.hom) := by rw [Category.assoc]
    _ = f' ≫ 𝟙 B' := by rw [show e.hom ≫ e.symm.hom = 𝟙 B' from e.hom_inv_id]
    _ = f' := by rw [Category.comp_id]
    _ = 𝟙 A ≫ f' := by rw [Category.id_comp]

end CompInv

end Work.SSSR

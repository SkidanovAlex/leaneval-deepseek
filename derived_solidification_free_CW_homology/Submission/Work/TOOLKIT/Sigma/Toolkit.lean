import Mathlib
import Submission.Work.TOOLKIT.Sigma.Pieces

/-!
# Coproducts of kernels, cokernels and degrees of complexes

This file collects the basic exactness facts about small coproducts in an abelian category `C`,
used in `Submission.Work.TOOLKIT.Sigma.quasiIso_sigma`:

* the coproduct of a family of kernels is the kernel of the coproduct (AB4),
* the coproduct of a family of cokernels is the cokernel of the coproduct,
* the coproduct complex of light condensed abelian groups is computed degreewise, together with
  the compatibility with the differentials.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open HomologicalComplex
open _root_.LightCondensed _root_.LightCondensed.Solid
open scoped CategoryTheory.Pretriangulated.Opposite

namespace Work.TOOLKIT

noncomputable section

/-! ## Auxiliary comparison lemmas -/

/-- The isomorphism `PreservesKernel.iso` is compatible with the kernel inclusions. -/
lemma PreservesKernel.iso_hom_ι {C D : Type*} [Category* C] [Category* D]
    [HasZeroMorphisms C] [HasZeroMorphisms D]
    (G : C ⥤ D) [G.PreservesZeroMorphisms] {X Y : C} (f : X ⟶ Y) [HasKernel f]
    [HasKernel (G.map f)] [PreservesLimit (parallelPair f 0) G] :
    (PreservesKernel.iso G f).hom ≫ kernel.ι (G.map f) = G.map (kernel.ι f) := by
  rw [← PreservesKernel.iso_inv_ι G f, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- The naturality of `Sigma.isoColimit`. -/
lemma sigmaIsoColimit_inv_map {α : Type*} {C : Type*} [Category* C] (X : Discrete α ⥤ C)
    {Y : α → C} (β : X ⟶ Discrete.functor Y) [HasCoproductsOfShape α C] [HasColimit X] :
    (Sigma.isoColimit X).inv ≫ Limits.Sigma.map (fun j => β.app ⟨j⟩) = colimMap β := by
  have h : (Sigma.isoColimit X).hom ≫ colimMap β
      = Limits.Sigma.map (fun j => β.app ⟨j⟩) := by
    apply Limits.Sigma.hom_ext
    intro j
    rw [Sigma.ι_isoColimit_hom_assoc, ι_colimMap, Limits.Sigma.ι_map]
    rfl
  rw [← h, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- `Sigma.map` followed by `Sigma.desc`. -/
lemma sigma_map_desc {β : Type*} {C : Type*} [Category* C] {f g : β → C}
    [HasCoproduct f] [HasCoproduct g] (p : ∀ b, g b ⟶ f b)
    {P : C} (q : ∀ b, f b ⟶ P) :
    Limits.Sigma.map p ≫ Limits.Sigma.desc q = Limits.Sigma.desc (fun b => p b ≫ q b) := by
  apply Limits.Sigma.hom_ext
  intro b
  rw [Limits.Sigma.ι_map_assoc, Limits.Sigma.ι_comp_desc, Limits.Sigma.ι_comp_desc]

/-! ## AB4: coproducts of kernels and of cokernels -/

/-- **AB4: the coproduct of kernels is the kernel of the coproduct.** -/
theorem isIso_sigmaKernelHom {C : Type*} [Category* C] [Abelian C] {J : Type}
    (A B : J → C) (φ : ∀ j, A j ⟶ B j)
    [HasCoproduct A] [HasCoproduct B] [HasCoproduct (fun j => kernel (φ j))]
    [HasColimitsOfShape (Discrete J) C] [HasExactColimitsOfShape (Discrete J) C] :
    IsIso (sigmaKernelHom A B φ) := by
  let ψ : Discrete.functor A ⟶ Discrete.functor B := Discrete.natTrans (fun t => φ t.as)
  have hψ : ∀ j : J, ψ.app ⟨j⟩ = φ j := fun j => by
    dsimp only [ψ]
    rw [Discrete.natTrans_app]
  set κ : (∐ fun j => kernel (φ j)) ⟶ (∐ A) := Limits.Sigma.map (fun j => kernel.ι (φ j))
    with hκ
  have hcond : κ ≫ Limits.Sigma.map φ = 0 := by
    rw [hκ]
    rw [Limits.Sigma.map_comp_map]
    apply Limits.Sigma.hom_ext
    intro j
    rw [Limits.Sigma.ι_map, kernel.condition, zero_comp, comp_zero]
  have h₁ : IsLimit (KernelFork.ofι (colim.map (kernel.ι ψ))
      (show colim.map (kernel.ι ψ) ≫ colim.map ψ = 0 by
        rw [← Functor.map_comp, kernel.condition, Functor.map_zero])) :=
    isLimitForkMapOfIsLimit' (colim (J := Discrete J) (C := C)) (kernel.condition ψ)
      (kernelIsKernel ψ)
  let qk (j : J) : (kernel ψ).obj ⟨j⟩ ≅ kernel (φ j) :=
    (PreservesKernel.iso ((evaluation (Discrete J) C).obj ⟨j⟩) ψ) ≪≫ kernelIsoOfEq (hψ j)
  have qk_ι (j : J) : (qk j).hom ≫ kernel.ι (φ j) = (kernel.ι ψ).app ⟨j⟩ := by
    dsimp only [qk]
    rw [Iso.trans_hom, Category.assoc, kernelIsoOfEq_hom_comp_ι]
    rw [PreservesKernel.iso_hom_ι]
    rfl
  let δ : colim.obj (kernel ψ) ≅ (∐ fun j => kernel (φ j)) :=
    (Sigma.isoColimit (kernel ψ)).symm ≪≫ Limits.Sigma.mapIso (fun j => qk j)
  have δ_κ : δ.hom ≫ κ = colim.map (kernel.ι ψ) := by
    dsimp only [δ]
    rw [Iso.trans_hom, Category.assoc]
    rw [show (Limits.Sigma.mapIso (fun j => qk j)).hom
      = Limits.Sigma.map (fun j => (qk j).hom) from rfl]
    rw [Limits.Sigma.map_comp_map]
    rw [show (fun j => (qk j).hom ≫ kernel.ι (φ j)) = (fun j => (kernel.ι ψ).app ⟨j⟩) from by
      funext j
      exact qk_ι j]
    exact sigmaIsoColimit_inv_map (kernel ψ) (kernel.ι ψ)
  have h₂ : IsLimit (KernelFork.ofι κ hcond) :=
    IsLimit.ofIsoLimit h₁ (Fork.ext δ δ_κ)
  have h₃ : IsLimit (KernelFork.ofι (kernel.ι (Limits.Sigma.map φ))
      (kernel.condition (Limits.Sigma.map φ))) := kernelIsKernel _
  have hΦ : (IsLimit.conePointUniqueUpToIso h₂ h₃).hom ≫ kernel.ι (Limits.Sigma.map φ)
      = κ := by
    have h := IsLimit.conePointUniqueUpToIso_hom_comp h₂ h₃ WalkingParallelPair.zero
    simpa using h
  have hσ : sigmaKernelHom A B φ ≫ kernel.ι (Limits.Sigma.map φ) = κ := by
    rw [hκ]
    rw [sigmaKernelHom, kernel.lift_ι]
    apply Limits.Sigma.hom_ext
    intro j
    rw [Limits.Sigma.ι_comp_desc, Limits.Sigma.ι_map]
  have hEq : sigmaKernelHom A B φ = (IsLimit.conePointUniqueUpToIso h₂ h₃).hom := by
    rw [← cancel_mono (kernel.ι (Limits.Sigma.map φ)), hσ]
    exact hΦ.symm
  rw [hEq]
  exact inferInstance

/-- **The cokernel of a coproduct is the coproduct of the cokernels.** -/
theorem isIso_sigmaCokernelHom {C : Type*} [Category* C] [Abelian C] {J : Type}
    (A B : J → C) (φ : ∀ j, A j ⟶ B j)
    [HasCoproduct A] [HasCoproduct B] [HasCoproduct (fun j => cokernel (φ j))] :
    IsIso (sigmaCokernelHom A B φ) := by
  have hz : Limits.Sigma.map (fun a => φ a ≫ cokernel.π (φ a)) = 0 := by
    apply Limits.Sigma.hom_ext
    intro j
    rw [Limits.Sigma.ι_map, cokernel.condition, zero_comp, comp_zero]
  have h : Limits.Sigma.map φ ≫ Limits.Sigma.map (fun j => cokernel.π (φ j)) = 0 := by
    rw [Limits.Sigma.map_comp_map, hz]
  have hcond (j : J) : φ j ≫ Limits.Sigma.ι B j ≫ cokernel.π (Limits.Sigma.map φ) = 0 := by
    rw [← Category.assoc, ← Limits.Sigma.ι_map, Category.assoc, cokernel.condition, comp_zero]
  let inv : cokernel (Limits.Sigma.map φ) ⟶ (∐ fun j => cokernel (φ j)) :=
    cokernel.desc (Limits.Sigma.map φ) (Limits.Sigma.map (fun j => cokernel.π (φ j))) h
  have hinv : cokernel.π (Limits.Sigma.map φ) ≫ inv
      = Limits.Sigma.map (fun j => cokernel.π (φ j)) := cokernel.π_desc _ _ _
  have h1 : sigmaCokernelHom A B φ ≫ inv = 𝟙 _ := by
    apply Limits.Sigma.hom_ext
    intro j
    have e1 : Limits.Sigma.ι (fun j => cokernel (φ j)) j ≫ (sigmaCokernelHom A B φ ≫ inv)
        = cokernel.desc (φ j) (Limits.Sigma.ι B j ≫ cokernel.π (Limits.Sigma.map φ))
            (hcond j) ≫ inv := by
      rw [← Category.assoc]
      unfold sigmaCokernelHom
      rw [Limits.Sigma.ι_comp_desc]
    have e2 : cokernel.desc (φ j) (Limits.Sigma.ι B j ≫ cokernel.π (Limits.Sigma.map φ))
          (hcond j) ≫ inv
        = Limits.Sigma.ι (fun j => cokernel (φ j)) j := by
      rw [← cancel_epi (cokernel.π (φ j))]
      rw [cokernel.π_desc_assoc, Category.assoc, hinv, Limits.Sigma.ι_map]
    rw [e1, e2, Category.comp_id]
  have h2 : inv ≫ sigmaCokernelHom A B φ = 𝟙 _ := by
    rw [← cancel_epi (cokernel.π (Limits.Sigma.map φ)), Category.comp_id, ← Category.assoc, hinv]
    unfold sigmaCokernelHom
    rw [sigma_map_desc]
    have h3 : (fun j => cokernel.π (φ j) ≫ cokernel.desc (φ j)
        (Limits.Sigma.ι B j ≫ cokernel.π (Limits.Sigma.map φ)) (hcond j))
        = (fun j => Limits.Sigma.ι B j ≫ cokernel.π (Limits.Sigma.map φ)) := by
      funext j
      rw [cokernel.π_desc]
    rw [h3]
    apply Limits.Sigma.hom_ext
    intro j
    rw [Limits.Sigma.ι_comp_desc]
  exact ⟨inv, h1, h2⟩

/-! ## The coproduct complex is computed degreewise -/

/-- The diagram `Discrete.functor K ⋙ eval i` is canonically the constant-index diagram
`j ↦ (K j).X i`. -/
noncomputable def cpxDiagIso {J : Type} (K : J → Cpx) (i : ℤ) :
    (Discrete.functor K ⋙ HomologicalComplex.eval LightCondAb (ComplexShape.up ℤ) i)
      ≅ Discrete.functor (fun j => (K j).X i) :=
  Discrete.natIso (fun _ => Iso.refl _)

/-- The comparison between the coproduct of the degree `i` parts and the degree `i` part of the
coproduct complex. -/
noncomputable def sigmaXIso {J : Type} (K : J → Cpx) [HasCoproduct K] (i : ℤ) :
    (∐ fun j => (K j).X i) ≅ (∐ K).X i :=
  ((preservesColimitIso (HomologicalComplex.eval LightCondAb (ComplexShape.up ℤ) i)
      (Discrete.functor K)) ≪≫ colim.mapIso (cpxDiagIso K i)).symm

/-- The comparison `sigmaXIso` is compatible with the inclusions. -/
lemma sigmaXIso_ι {J : Type} (K : J → Cpx) [HasCoproduct K] (i : ℤ) (j : J) :
    (Limits.Sigma.ι K j).f i ≫ (sigmaXIso K i).inv
      = Limits.Sigma.ι (fun j => (K j).X i) j := by
  have hmap : (Limits.Sigma.ι K j).f i
      = (HomologicalComplex.eval LightCondAb (ComplexShape.up ℤ) i).map
          (colimit.ι (Discrete.functor K) ⟨j⟩) := rfl
  rw [sigmaXIso, Iso.symm_inv, Iso.trans_hom, hmap, ι_preservesColimitIso_hom_assoc]
  rw [colim.mapIso_hom]
  rw [show colim.map (cpxDiagIso K i).hom = colimMap (cpxDiagIso K i).hom from rfl]
  rw [ι_colimMap]
  rfl

/-- The comparison `sigmaXIso` commutes with the differentials of the coproduct complex. -/
lemma sigmaXIso_d {J : Type} (K : J → Cpx) [HasCoproduct K] (i j : ℤ) :
    (sigmaXIso K i).hom ≫ (∐ K).d i j
      = Limits.Sigma.map (fun j' => (K j').d i j) ≫ (sigmaXIso K j).hom := by
  apply Sigma.hom_ext
  intro j'
  have h1 : Limits.Sigma.ι (fun j' => (K j').X i) j' ≫ (sigmaXIso K i).hom
      = (Limits.Sigma.ι K j').f i := by
    have h := sigmaXIso_ι K i j'
    rw [← h, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have h2 : Limits.Sigma.ι (fun j' => (K j').X j) j' ≫ (sigmaXIso K j).hom
      = (Limits.Sigma.ι K j').f j := by
    have h := sigmaXIso_ι K j j'
    rw [← h, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc, h1, Hom.comm, ← Category.assoc, Limits.Sigma.ι_map, Category.assoc, h2]

/-! ## Comparing (co)kernels along canonical cofork structures -/

/-- The canonical iso from a morphism whose fork is a limit. -/
lemma kernel_isoOfIsLimit_hom_ι {C : Type*} [Category* C] [HasZeroMorphisms C] {X Y Z : C}
    (f : X ⟶ Y) [HasKernel f] (k : Z ⟶ X) (w : k ≫ f = 0)
    (h : IsLimit (KernelFork.ofι k w)) :
    (IsLimit.conePointUniqueUpToIso (s := KernelFork.ofι k w)
      (t := KernelFork.ofι (kernel.ι f) (kernel.condition f)) h (kernelIsKernel f)).hom
      ≫ kernel.ι f = k := by
  have h2 := IsLimit.conePointUniqueUpToIso_hom_comp (s := KernelFork.ofι k w)
    (t := KernelFork.ofι (kernel.ι f) (kernel.condition f)) h (kernelIsKernel f)
    WalkingParallelPair.zero
  simpa using h2

/-- The canonical iso to a cokernel: it is compatible with the projections. -/
lemma cokernel_isoOfIsColimit_π {C : Type*} [Category* C] [HasZeroMorphisms C] {X Y Z : C}
    (f : X ⟶ Y) [HasCokernel f] (k : Y ⟶ Z) (w : f ≫ k = 0)
    (h : IsColimit (CokernelCofork.ofπ k w)) :
    cokernel.π f ≫ (IsColimit.coconePointUniqueUpToIso
      (s := CokernelCofork.ofπ (cokernel.π f) (cokernel.condition f))
      (t := CokernelCofork.ofπ k w) (cokernelIsCokernel f) h).hom = k := by
  have h2 := IsColimit.comp_coconePointUniqueUpToIso_hom
    (s := CokernelCofork.ofπ (cokernel.π f) (cokernel.condition f))
    (t := CokernelCofork.ofπ k w) (cokernelIsCokernel f) h WalkingParallelPair.one
  simpa using h2

/-- The comparison of the cycles with the kernel of the differential, in degree `i`. -/
noncomputable def cyclesKernelIso {J : Type} (K : J → Cpx) (i : ℤ) (j : J) :
    (K j).cycles i ≅ kernel ((K j).d i (i+1)) :=
  IsLimit.conePointUniqueUpToIso
    (s := KernelFork.ofι ((K j).iCycles i) ((K j).iCycles_d i (i+1)))
    (t := KernelFork.ofι (kernel.ι ((K j).d i (i+1))) (kernel.condition _))
    ((K j).cyclesIsKernel (i := i) (j := i+1) (by simp))
    (kernelIsKernel _)

lemma cyclesKernelIso_ι {J : Type} (K : J → Cpx) (i : ℤ) (j : J) :
    (cyclesKernelIso K i j).hom ≫ kernel.ι ((K j).d i (i+1)) = (K j).iCycles i :=
  kernel_isoOfIsLimit_hom_ι _ _ _ ((K j).cyclesIsKernel (i := i) (j := i+1) (by simp))

/-- The comparison of the opcycles with the cokernel of the differential, in degree `i`. -/
noncomputable def opcyclesCokernelIso {J : Type} (K : J → Cpx) (i : ℤ) (j : J) :
    cokernel ((K j).d (i-1) i) ≅ (K j).opcycles i :=
  IsColimit.coconePointUniqueUpToIso
    (s := CokernelCofork.ofπ (cokernel.π ((K j).d (i-1) i)) (cokernel.condition _))
    (t := CokernelCofork.ofπ ((K j).pOpcycles i) ((K j).d_pOpcycles (i-1) i))
    (cokernelIsCokernel _)
    ((K j).opcyclesIsCokernel (i := i-1) (j := i) (by simp))

lemma opcyclesCokernelIso_π {J : Type} (K : J → Cpx) (i : ℤ) (j : J) :
    cokernel.π ((K j).d (i-1) i) ≫ (opcyclesCokernelIso K i j).hom = (K j).pOpcycles i :=
  cokernel_isoOfIsColimit_π _ _ _ ((K j).opcyclesIsCokernel (i := i-1) (j := i) (by simp))

/-- The comparison of the cycles with the kernel of the differential, for a single complex. -/
noncomputable def cyclesKernelIso' (M : Cpx) (i : ℤ) : M.cycles i ≅ kernel (M.d i (i+1)) :=
  IsLimit.conePointUniqueUpToIso
    (s := KernelFork.ofι (M.iCycles i) (M.iCycles_d i (i+1)))
    (t := KernelFork.ofι (kernel.ι (M.d i (i+1))) (kernel.condition _))
    (M.cyclesIsKernel (i := i) (j := i+1) (by simp)) (kernelIsKernel _)

lemma cyclesKernelIso'_ι (M : Cpx) (i : ℤ) :
    (cyclesKernelIso' M i).hom ≫ kernel.ι (M.d i (i+1)) = M.iCycles i :=
  kernel_isoOfIsLimit_hom_ι _ _ _ (M.cyclesIsKernel (i := i) (j := i+1) (by simp))

/-- The comparison of the opcycles with the cokernel of the differential, for a single complex. -/
noncomputable def opcyclesCokernelIso' (M : Cpx) (i : ℤ) :
    cokernel (M.d (i-1) i) ≅ M.opcycles i :=
  IsColimit.coconePointUniqueUpToIso
    (s := CokernelCofork.ofπ (cokernel.π (M.d (i-1) i)) (cokernel.condition _))
    (t := CokernelCofork.ofπ (M.pOpcycles i) (M.d_pOpcycles (i-1) i))
    (cokernelIsCokernel _) (M.opcyclesIsCokernel (i := i-1) (j := i) (by simp))

lemma opcyclesCokernelIso'_π (M : Cpx) (i : ℤ) :
    cokernel.π (M.d (i-1) i) ≫ (opcyclesCokernelIso' M i).hom = M.pOpcycles i :=
  cokernel_isoOfIsColimit_π _ _ _ (M.opcyclesIsCokernel (i := i-1) (j := i) (by simp))

/-- `Sigma.desc` of a family of composites. -/
lemma sigma_desc_comp {β : Type*} {C : Type*} [Category* C] {f : β → C} [HasCoproduct f]
    {P Q : C} (u : ∀ b, f b ⟶ P) (w : P ⟶ Q) :
    Limits.Sigma.desc (fun b => u b ≫ w) = Limits.Sigma.desc u ≫ w := by
  apply Limits.Sigma.hom_ext
  intro b
  rw [Limits.Sigma.ι_comp_desc_assoc, Limits.Sigma.ι_comp_desc]

/-- The comparison map of kernels is compatible with the kernel inclusions. -/
lemma sigmaKernelHom_ι {C : Type*} [Category* C] [Abelian C] {J : Type}
    (A B : J → C) (φ : ∀ j, A j ⟶ B j)
    [HasCoproduct A] [HasCoproduct B] [HasCoproduct (fun j => kernel (φ j))] :
    sigmaKernelHom A B φ ≫ kernel.ι (Limits.Sigma.map φ)
      = Limits.Sigma.map (fun j => kernel.ι (φ j)) := by
  rw [sigmaKernelHom, kernel.lift_ι]
  apply Limits.Sigma.hom_ext
  intro j
  rw [Limits.Sigma.ι_comp_desc, Limits.Sigma.ι_map]

/-- The comparison map on cycles of a family of complexes. -/
noncomputable def sigmaCyclesHom {J : Type} (K : J → Cpx) [HasCoproduct K] (i : ℤ) :
    (∐ fun j => (K j).cycles i) ⟶ (∐ K).cycles i :=
  Limits.Sigma.desc (fun j => cyclesMap (Limits.Sigma.ι K j) i)

/-- The comparison map on opcycles of a family of complexes. -/
noncomputable def sigmaOpcyclesHom {J : Type} (K : J → Cpx) [HasCoproduct K] (i : ℤ) :
    (∐ fun j => (K j).opcycles i) ⟶ (∐ K).opcycles i :=
  Limits.Sigma.desc (fun j => opcyclesMap (Limits.Sigma.ι K j) i)

/-- The comparison map on homology of a family of complexes. -/
noncomputable def sigmaHomologyMap {J : Type} (K : J → Cpx) [HasCoproduct K] (i : ℤ) :
    (∐ fun j => (K j).homology i) ⟶ (∐ K).homology i :=
  Limits.Sigma.desc (fun j => homologyMap (Limits.Sigma.ι K j) i)

end

end Work.TOOLKIT

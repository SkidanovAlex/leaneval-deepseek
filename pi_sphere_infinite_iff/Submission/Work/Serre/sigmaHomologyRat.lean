import Mathlib
import Submission.Work.Serre.coprodChainAux
import Submission.Work.Serre.coprodKernelRat

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Homology commutes with coproducts of chain complexes over `ℚ`

For a family of chain complexes `K i` over `ModuleCat ℚ`, the canonical comparison map

`∐ i, (K i).homology m ⟶ (∐ i, K i).homology m`

(`Work.Serre.sigmaHomologyMap`) is an isomorphism, and it is natural in the family.  Consequently,
if a family of chain maps `f i : K i ⟶ L i` induces isomorphisms on `H_m`, then so does the
coproduct `∐ i, f i`.

The proof goes through the comparison of cycles
`Work.Serre.sigmaCyclesMap : ∐ i, (K i).cycles m ≅ (∐ i, K i).cycles m`, which is built from the
degreewise comparisons and the fact that coproducts of kernels are kernels
(`Work.Serre.isIso_sigmaKernelMap`), and a five-lemma style argument using the exactness of the
"cycles → homology" sequence.
-/

namespace Work.Serre

open CategoryTheory Limits
open CategoryTheory.Limits ModuleCat

noncomputable section

variable {ι : Type}

/-! ## The comparison in each degree -/

theorem isIso_sigmaDegreeMap (K : ι → ChainComplex (ModuleCat ℚ) ℕ) (n : ℕ) :
    IsIso (sigmaDegreeMap ℚ K n) := by
  haveI hpres : PreservesColimit (Discrete.functor K)
      (HomologicalComplex.eval (ModuleCat ℚ) (ComplexShape.down ℕ) n) :=
    PreservesColimitsOfShape.preservesColimit
  let e : (Discrete.functor K ⋙ HomologicalComplex.eval (ModuleCat ℚ) (ComplexShape.down ℕ) n)
      ≅ Discrete.functor (fun i =>
          (HomologicalComplex.eval (ModuleCat ℚ) (ComplexShape.down ℕ) n).obj (K i)) :=
    Discrete.compNatIsoDiscrete K _
  have he : ∀ i, e.inv.app ⟨i⟩ = 𝟙 _ := by
    intro i
    simp [e, Discrete.compNatIsoDiscrete]
  have hiso : IsIso (colim.map e.inv ≫ (preservesColimitIso
      (HomologicalComplex.eval (ModuleCat ℚ) (ComplexShape.down ℕ) n)
      (Discrete.functor K)).inv) :=
    IsIso.comp_isIso' (inferInstance : IsIso (colim.map e.inv))
      (inferInstance : IsIso (preservesColimitIso
        (HomologicalComplex.eval (ModuleCat ℚ) (ComplexShape.down ℕ) n)
        (Discrete.functor K)).inv)
  have h : sigmaDegreeMap ℚ K n = colim.map e.inv ≫ (preservesColimitIso
      (HomologicalComplex.eval (ModuleCat ℚ) (ComplexShape.down ℕ) n)
      (Discrete.functor K)).inv := by
    apply Limits.Sigma.hom_ext
    intro i
    rw [sigmaDegreeMap_ι]
    show (Limits.Sigma.ι K i).f n
      = colimit.ι (Discrete.functor (fun i =>
          (HomologicalComplex.eval (ModuleCat ℚ) (ComplexShape.down ℕ) n).obj (K i))) ⟨i⟩
        ≫ (colim.map e.inv ≫ (preservesColimitIso
            (HomologicalComplex.eval (ModuleCat ℚ) (ComplexShape.down ℕ) n)
            (Discrete.functor K)).inv)
    rw [← Category.assoc, colimit.ι_map, he i, Category.id_comp,
      ι_preservesColimitIso_inv]
    rfl
  rw [h]
  exact hiso

/-! ## Cycles vs the kernel of the differential -/

variable (K : ChainComplex (ModuleCat ℚ) ℕ) (m : ℕ)

/-- The comparison `K.cycles m ⟶ kernel (K.d m (c.next m))`. -/
def cyclesToKernel : K.cycles m ⟶ kernel (K.d m ((ComplexShape.down ℕ).next m)) :=
  kernel.lift (K.d m ((ComplexShape.down ℕ).next m)) (K.iCycles m)
    (K.iCycles_d m ((ComplexShape.down ℕ).next m))

/-- The comparison `kernel (K.d m (c.next m)) ⟶ K.cycles m`. -/
def kernelToCycles : kernel (K.d m ((ComplexShape.down ℕ).next m)) ⟶ K.cycles m :=
  K.liftCycles (kernel.ι (K.d m ((ComplexShape.down ℕ).next m)))
    ((ComplexShape.down ℕ).next m) rfl (kernel.condition _)

theorem cyclesToKernel_comp_kernel_ι :
    cyclesToKernel K m ≫ kernel.ι (K.d m ((ComplexShape.down ℕ).next m)) = K.iCycles m :=
  kernel.lift_ι _ _ _

theorem kernelToCycles_comp_iCycles :
    kernelToCycles K m ≫ K.iCycles m = kernel.ι (K.d m ((ComplexShape.down ℕ).next m)) :=
  K.liftCycles_i _ _ _ _

theorem cyclesToKernel_kernelToCycles : cyclesToKernel K m ≫ kernelToCycles K m = 𝟙 (K.cycles m) := by
  rw [← cancel_mono (K.iCycles m), Category.assoc, kernelToCycles_comp_iCycles,
    cyclesToKernel_comp_kernel_ι, Category.id_comp]

theorem kernelToCycles_cyclesToKernel :
    kernelToCycles K m ≫ cyclesToKernel K m = 𝟙 (kernel (K.d m ((ComplexShape.down ℕ).next m))) := by
  rw [← cancel_mono (kernel.ι (K.d m ((ComplexShape.down ℕ).next m))), Category.assoc,
    cyclesToKernel_comp_kernel_ι, kernelToCycles_comp_iCycles, Category.id_comp]

/-- The canonical isomorphism `K.cycles m ≅ kernel (K.d m (c.next m))`. -/
def cyclesKernelIso : K.cycles m ≅ kernel (K.d m ((ComplexShape.down ℕ).next m)) :=
  ⟨cyclesToKernel K m, kernelToCycles K m, cyclesToKernel_kernelToCycles K m,
    kernelToCycles_cyclesToKernel K m⟩

@[simp]
theorem cyclesKernelIso_hom : (cyclesKernelIso K m).hom = cyclesToKernel K m := rfl

@[simp]
theorem cyclesKernelIso_inv : (cyclesKernelIso K m).inv = kernelToCycles K m := rfl

theorem isIso_cyclesToKernel : IsIso (cyclesToKernel K m) := by
  rw [← cyclesKernelIso_hom]
  infer_instance

theorem isIso_kernelToCycles : IsIso (kernelToCycles K m) := by
  rw [← cyclesKernelIso_inv]
  infer_instance

/-! ## The comparison of cycles of a coproduct -/

/-- The coproduct of the comparisons `K i.cycles m ⟶ kernel (K i.d m (c.next m))`. -/
def cyclesKernelSigmaMap (K : ι → ChainComplex (ModuleCat ℚ) ℕ) (m : ℕ) :
    (∐ fun i => (K i).cycles m) ⟶
      (∐ fun i => kernel ((K i).d m ((ComplexShape.down ℕ).next m))) :=
  Limits.Sigma.map (fun i => cyclesToKernel (K i) m)

/-- The comparison `∐ kernel (K i.d m (c.next m)) ⟶ kernel ((∐ K).d m (c.next m))`. -/
def cyclesKernelSigmaMapComp (K : ι → ChainComplex (ModuleCat ℚ) ℕ) (m : ℕ) :
    (∐ fun i => kernel ((K i).d m ((ComplexShape.down ℕ).next m))) ⟶
      kernel ((∐ K).d m ((ComplexShape.down ℕ).next m)) :=
  sigmaKernelMap (fun i => (K i).d m ((ComplexShape.down ℕ).next m)) ≫
    kernel.map (Limits.Sigma.map (fun i => (K i).d m ((ComplexShape.down ℕ).next m)))
      ((∐ K).d m ((ComplexShape.down ℕ).next m))
      (sigmaDegreeMap ℚ K m) (sigmaDegreeMap ℚ K ((ComplexShape.down ℕ).next m))
      (sigmaDegreeMap_d ℚ K m ((ComplexShape.down ℕ).next m)).symm

/-- The comparison `∐ i, (K i).cycles m ⟶ (∐ i, K i).cycles m`. -/
def sigmaCyclesMap (K : ι → ChainComplex (ModuleCat ℚ) ℕ) (m : ℕ) :
    (∐ fun i => (K i).cycles m) ⟶ (∐ K).cycles m :=
  cyclesKernelSigmaMap K m ≫
    (cyclesKernelSigmaMapComp K m ≫ (cyclesKernelIso (∐ K) m).inv)

theorem isIso_cyclesKernelSigmaMap (K : ι → ChainComplex (ModuleCat ℚ) ℕ) (m : ℕ) :
    IsIso (cyclesKernelSigmaMap K m) := by
  haveI : ∀ i, IsIso (cyclesToKernel (K i) m) := fun i => isIso_cyclesToKernel (K i) m
  rw [cyclesKernelSigmaMap]
  infer_instance

theorem isIso_cyclesKernelSigmaMapComp (K : ι → ChainComplex (ModuleCat ℚ) ℕ) (m : ℕ) :
    IsIso (cyclesKernelSigmaMapComp K m) := by
  haveI : IsIso (sigmaDegreeMap ℚ K m) := isIso_sigmaDegreeMap K m
  haveI : IsIso (sigmaDegreeMap ℚ K ((ComplexShape.down ℕ).next m)) :=
    isIso_sigmaDegreeMap K _
  haveI : IsIso (sigmaKernelMap (fun i => (K i).d m ((ComplexShape.down ℕ).next m))) :=
    isIso_sigmaKernelMap _
  rw [cyclesKernelSigmaMapComp]
  infer_instance

theorem isIso_sigmaCyclesMap (K : ι → ChainComplex (ModuleCat ℚ) ℕ) (m : ℕ) :
    IsIso (sigmaCyclesMap K m) := by
  have h1 : IsIso (cyclesKernelSigmaMap K m) := isIso_cyclesKernelSigmaMap K m
  have h2 : IsIso (cyclesKernelSigmaMapComp K m) := isIso_cyclesKernelSigmaMapComp K m
  have h3 : IsIso (cyclesKernelSigmaMap K m ≫
      (cyclesKernelSigmaMapComp K m ≫ (cyclesKernelIso (∐ K) m).inv)) := by
    haveI := h1
    haveI := h2
    infer_instance
  exact h3

theorem cyclesKernelSigmaMap_comp_map (K : ι → ChainComplex (ModuleCat ℚ) ℕ) (m : ℕ) :
    cyclesKernelSigmaMap K m ≫
        Limits.Sigma.map (fun i => kernel.ι ((K i).d m ((ComplexShape.down ℕ).next m)))
      = Limits.Sigma.map (fun i => HomologicalComplex.iCycles (K i) m) := by
  rw [cyclesKernelSigmaMap, Limits.Sigma.map_comp_map]
  congr 1
  funext i
  exact cyclesToKernel_comp_kernel_ι (K i) m

theorem cyclesKernelSigmaMapComp_comp_kernel_ι (K : ι → ChainComplex (ModuleCat ℚ) ℕ) (m : ℕ) :
    cyclesKernelSigmaMapComp K m ≫ kernel.ι ((∐ K).d m ((ComplexShape.down ℕ).next m))
      = Limits.Sigma.map (fun i => kernel.ι ((K i).d m ((ComplexShape.down ℕ).next m)))
        ≫ sigmaDegreeMap ℚ K m := by
  rw [cyclesKernelSigmaMapComp, Category.assoc, kernel.lift_ι, ← Category.assoc,
    sigmaKernelMap_comp_ι]

theorem sigmaCyclesMap_comp_iCycles (K : ι → ChainComplex (ModuleCat ℚ) ℕ) (m : ℕ) :
    sigmaCyclesMap K m ≫ HomologicalComplex.iCycles (∐ K) m
      = Limits.Sigma.map (fun i => HomologicalComplex.iCycles (K i) m) ≫ sigmaDegreeMap ℚ K m := by
  have h1 := cyclesKernelSigmaMap_comp_map K m
  have h2 := cyclesKernelSigmaMapComp_comp_kernel_ι K m
  have h3 : (cyclesKernelIso (∐ K) m).inv ≫ HomologicalComplex.iCycles (∐ K) m
      = kernel.ι ((∐ K).d m ((ComplexShape.down ℕ).next m)) :=
    kernelToCycles_comp_iCycles (∐ K) m
  calc sigmaCyclesMap K m ≫ HomologicalComplex.iCycles (∐ K) m
      = cyclesKernelSigmaMap K m ≫ (cyclesKernelSigmaMapComp K m ≫
          ((cyclesKernelIso (∐ K) m).inv ≫ HomologicalComplex.iCycles (∐ K) m)) := by
        rw [sigmaCyclesMap]
        simp only [Category.assoc]
    _ = cyclesKernelSigmaMap K m ≫ (cyclesKernelSigmaMapComp K m ≫
          kernel.ι ((∐ K).d m ((ComplexShape.down ℕ).next m))) := by rw [h3]
    _ = cyclesKernelSigmaMap K m ≫ (Limits.Sigma.map
          (fun i => kernel.ι ((K i).d m ((ComplexShape.down ℕ).next m)))
          ≫ sigmaDegreeMap ℚ K m) := by rw [h2]
    _ = Limits.Sigma.map (fun i => HomologicalComplex.iCycles (K i) m)
          ≫ sigmaDegreeMap ℚ K m := by rw [← Category.assoc, h1]

theorem iota_sigmaCyclesMap (K : ι → ChainComplex (ModuleCat ℚ) ℕ) (m : ℕ) (i : ι) :
    Limits.Sigma.ι (fun i => (K i).cycles m) i ≫ sigmaCyclesMap K m
      = HomologicalComplex.cyclesMap (Limits.Sigma.ι K i) m := by
  rw [← cancel_mono (HomologicalComplex.iCycles (∐ K) m)]
  rw [Category.assoc, sigmaCyclesMap_comp_iCycles, ← Category.assoc, Limits.Sigma.ι_map,
    Category.assoc, sigmaDegreeMap_ι, HomologicalComplex.cyclesMap_i]

theorem sigmaMap_toCycles_comp_homologyπ (K : ι → ChainComplex (ModuleCat ℚ) ℕ) (m : ℕ) :
    Limits.Sigma.map (fun i => (K i).toCycles ((ComplexShape.down ℕ).prev m) m)
      ≫ Limits.Sigma.map (fun i => HomologicalComplex.homologyπ (K i) m) = 0 := by
  apply Limits.Sigma.hom_ext
  intro i
  rw [← Category.assoc, Limits.Sigma.ι_map, Category.assoc, Limits.Sigma.ι_map,
    ← Category.assoc, HomologicalComplex.toCycles_comp_homologyπ]
  simp

/-- The compatibility of `sigmaCyclesMap` with `toCycles` and the degreewise comparisons. -/
theorem sigmaCyclesMap_toCycles_comp (K : ι → ChainComplex (ModuleCat ℚ) ℕ) (m : ℕ) :
    sigmaDegreeMap ℚ K ((ComplexShape.down ℕ).prev m)
        ≫ (∐ K).toCycles ((ComplexShape.down ℕ).prev m) m
        ≫ HomologicalComplex.iCycles (∐ K) m
      = (Limits.Sigma.map (fun i => (K i).toCycles ((ComplexShape.down ℕ).prev m) m)
          ≫ sigmaCyclesMap K m) ≫ HomologicalComplex.iCycles (∐ K) m := by
  rw [Category.assoc, HomologicalComplex.toCycles_i, sigmaCyclesMap_comp_iCycles,
    ← Category.assoc, Limits.Sigma.map_comp_map]
  simp only [HomologicalComplex.toCycles_i]
  exact sigmaDegreeMap_d ℚ K ((ComplexShape.down ℕ).prev m) m

/-! ## A cycle of vanishing homology class is a boundary -/

theorem sc_toCycles_eq_of_homologyπ_eq_zero (S : ShortComplex (ModuleCat ℚ))
    (z : S.cycles) (h : S.homologyπ z = 0) :
    ∃ v : S.X₁, S.toCycles v = z := by
  have hzero : S.homologyι (S.homologyπ z) = 0 := by rw [h, map_zero]
  have hpop : S.pOpcycles ((S.iCycles).hom z) = 0 := by
    have hh := congrArg (fun (g : S.cycles ⟶ S.opcycles) => g z)
      (ShortComplex.homology_π_ι S)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hh
    rw [← hh]
    exact hzero
  have hmem := (ShortComplex.moduleCat_pOpcycles_eq_zero_iff S ((S.iCycles).hom z)).mp hpop
  obtain ⟨v, hv⟩ := LinearMap.mem_range.mp hmem
  refine ⟨v, ?_⟩
  apply (ModuleCat.mono_iff_injective S.iCycles).mp inferInstance
  rw [← ModuleCat.comp_apply, ShortComplex.toCycles_i]
  exact hv

/-- A cycle whose homology class vanishes is a boundary. -/
theorem exists_toCycles_eq_of_homologyπ_eq_zero (K : ChainComplex (ModuleCat ℚ) ℕ) (m : ℕ)
    (z : K.cycles m) (h : K.homologyπ m z = 0) :
    ∃ v : K.X ((ComplexShape.down ℕ).prev m),
      K.toCycles ((ComplexShape.down ℕ).prev m) m v = z := by
  have hc := K.homologyIsCokernel (i := (ComplexShape.down ℕ).prev m) (j := m) rfl
  let e : cokernel (K.toCycles ((ComplexShape.down ℕ).prev m) m) ≅ K.homology m :=
    IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) hc
  have hπ : cokernel.π (K.toCycles ((ComplexShape.down ℕ).prev m) m) ≫ e.hom
      = K.homologyπ m :=
    IsColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit _) hc _
  have hz0 : cokernel.π (K.toCycles ((ComplexShape.down ℕ).prev m) m) z = 0 := by
    have h1 : e.hom (cokernel.π (K.toCycles ((ComplexShape.down ℕ).prev m) m) z) = 0 := by
      have h2 := congrArg (fun (g : K.cycles m ⟶ K.homology m) => g z) hπ
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h2.trans h
    have hinj : Function.Injective e.hom :=
      (ConcreteCategory.bijective_of_isIso e.hom).1
    exact hinj (by rw [h1, map_zero])
  have hexact : (ShortComplex.mk (K.toCycles ((ComplexShape.down ℕ).prev m) m)
      (cokernel.π (K.toCycles ((ComplexShape.down ℕ).prev m) m))
      (cokernel.condition _)).Exact := ShortComplex.exact_cokernel _
  obtain ⟨v, hv⟩ := (ShortComplex.moduleCat_exact_iff _).mp hexact z hz0
  exact ⟨v, hv⟩

/-! ## The comparison on homology -/

/-- The canonical comparison `∐ i, H_m(K i) ⟶ H_m(∐ i, K i)`. -/
def sigmaHomologyMap (K : ι → ChainComplex (ModuleCat ℚ) ℕ) (m : ℕ) :
    (∐ fun i => (K i).homology m) ⟶ (∐ K).homology m :=
  Limits.Sigma.desc (fun i => HomologicalComplex.homologyMap (Limits.Sigma.ι K i) m)

theorem sigmaHomologyMap_ι (K : ι → ChainComplex (ModuleCat ℚ) ℕ) (m : ℕ) (i : ι) :
    Limits.Sigma.ι (fun i => (K i).homology m) i ≫ sigmaHomologyMap K m
      = HomologicalComplex.homologyMap (Limits.Sigma.ι K i) m :=
  Limits.Sigma.ι_desc _ _

theorem sigmaCyclesMap_comp_homologyπ (K : ι → ChainComplex (ModuleCat ℚ) ℕ) (m : ℕ) :
    sigmaCyclesMap K m ≫ HomologicalComplex.homologyπ (∐ K) m
      = Limits.Sigma.map (fun i => HomologicalComplex.homologyπ (K i) m)
        ≫ sigmaHomologyMap K m := by
  apply Limits.Sigma.hom_ext
  intro i
  calc Limits.Sigma.ι (fun i => (K i).cycles m) i
        ≫ (sigmaCyclesMap K m ≫ HomologicalComplex.homologyπ (∐ K) m)
      = (Limits.Sigma.ι (fun i => (K i).cycles m) i ≫ sigmaCyclesMap K m)
          ≫ HomologicalComplex.homologyπ (∐ K) m := (Category.assoc _ _ _).symm
    _ = HomologicalComplex.cyclesMap (Limits.Sigma.ι K i) m
          ≫ HomologicalComplex.homologyπ (∐ K) m := by rw [iota_sigmaCyclesMap]
    _ = HomologicalComplex.homologyπ (K i) m
          ≫ HomologicalComplex.homologyMap (Limits.Sigma.ι K i) m :=
        (HomologicalComplex.homologyπ_naturality (φ := Limits.Sigma.ι K i) (i := m)).symm
    _ = HomologicalComplex.homologyπ (K i) m
          ≫ (Limits.Sigma.ι (fun i => (K i).homology m) i ≫ sigmaHomologyMap K m) := by
        rw [sigmaHomologyMap_ι]
    _ = (HomologicalComplex.homologyπ (K i) m ≫ Limits.Sigma.ι (fun i => (K i).homology m) i)
          ≫ sigmaHomologyMap K m := (Category.assoc _ _ _).symm
    _ = (Limits.Sigma.ι (fun i => (K i).cycles m) i
          ≫ Limits.Sigma.map (fun i => HomologicalComplex.homologyπ (K i) m))
          ≫ sigmaHomologyMap K m := by rw [Limits.Sigma.ι_map]
    _ = Limits.Sigma.ι (fun i => (K i).cycles m) i
          ≫ (Limits.Sigma.map (fun i => HomologicalComplex.homologyπ (K i) m)
            ≫ sigmaHomologyMap K m) := Category.assoc _ _ _

/-- **Homology commutes with coproducts of chain complexes over `ℚ`.** -/
theorem isIso_sigmaHomologyMap (K : ι → ChainComplex (ModuleCat ℚ) ℕ) (m : ℕ) :
    IsIso (sigmaHomologyMap K m) := by
  classical
  haveI hκ : IsIso (sigmaCyclesMap K m) := isIso_sigmaCyclesMap K m
  haveI hdeg : IsIso (sigmaDegreeMap ℚ K ((ComplexShape.down ℕ).prev m)) :=
    isIso_sigmaDegreeMap K _
  have hsquare := sigmaCyclesMap_comp_homologyπ K m
  haveI hg : Epi (Limits.Sigma.map (fun i => HomologicalComplex.homologyπ (K i) m)) :=
    inferInstance
  haveI hg' : Epi (HomologicalComplex.homologyπ (∐ K) m) := inferInstance
  refine (ConcreteCategory.isIso_iff_bijective (sigmaHomologyMap K m)).mpr ⟨?_, ?_⟩
  · intro a b hab
    obtain ⟨za, hza⟩ := (ModuleCat.epi_iff_surjective _).mp hg a
    obtain ⟨zb, hzb⟩ := (ModuleCat.epi_iff_surjective _).mp hg b
    have hsa : ((∐ K).homologyπ m) (sigmaCyclesMap K m za)
        = (sigmaHomologyMap K m)
            ((Limits.Sigma.map (fun i => HomologicalComplex.homologyπ (K i) m)) za) := by
      have h := congrArg
        (fun (g : (∐ fun i => (K i).cycles m) ⟶ (∐ K).homology m) => g za) hsquare
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h
    have hsb : ((∐ K).homologyπ m) (sigmaCyclesMap K m zb)
        = (sigmaHomologyMap K m)
            ((Limits.Sigma.map (fun i => HomologicalComplex.homologyπ (K i) m)) zb) := by
      have h := congrArg
        (fun (g : (∐ fun i => (K i).cycles m) ⟶ (∐ K).homology m) => g zb) hsquare
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h
    have hπ0 : (∐ K).homologyπ m
        (sigmaCyclesMap K m za - sigmaCyclesMap K m zb) = 0 := by
      rw [map_sub, hsa, hsb, hza, hzb, hab, sub_self]
    obtain ⟨w, hw⟩ := exists_toCycles_eq_of_homologyπ_eq_zero (∐ K) m
      (sigmaCyclesMap K m za - sigmaCyclesMap K m zb) hπ0
    obtain ⟨v, hv⟩ := (ModuleCat.epi_iff_surjective _).mp
      (inferInstance : Epi (sigmaDegreeMap ℚ K ((ComplexShape.down ℕ).prev m))) w
    have hstep : (∐ K).toCycles ((ComplexShape.down ℕ).prev m) m
        (sigmaDegreeMap ℚ K ((ComplexShape.down ℕ).prev m) v)
        = sigmaCyclesMap K m (Limits.Sigma.map
            (fun i => (K i).toCycles ((ComplexShape.down ℕ).prev m) m) v) := by
      apply (ModuleCat.mono_iff_injective (HomologicalComplex.iCycles (∐ K) m)).mp inferInstance
      have h := congrArg (fun (g : (∐ fun i => (K i).X ((ComplexShape.down ℕ).prev m))
          ⟶ (∐ K).X m) => g v) (sigmaCyclesMap_toCycles_comp K m)
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h
    have hzw : (Limits.Sigma.map
        (fun i => (K i).toCycles ((ComplexShape.down ℕ).prev m) m)) v = za - zb := by
      have hinj : Function.Injective (sigmaCyclesMap K m) :=
        (ConcreteCategory.bijective_of_isIso (sigmaCyclesMap K m)).1
      refine hinj ?_
      have h1 : sigmaCyclesMap K m
          ((Limits.Sigma.map
            (fun i => (K i).toCycles ((ComplexShape.down ℕ).prev m) m)) v)
          = sigmaCyclesMap K m za - sigmaCyclesMap K m zb := by
        rw [← hstep, hv, hw]
      rw [h1, map_sub]
    have hzero : (Limits.Sigma.map (fun i => HomologicalComplex.homologyπ (K i) m))
        ((Limits.Sigma.map
          (fun i => (K i).toCycles ((ComplexShape.down ℕ).prev m) m)) v) = 0 := by
      rw [← ModuleCat.comp_apply, sigmaMap_toCycles_comp_homologyπ]
      simp
    have hab' : a - b = 0 := by
      have h1 : (Limits.Sigma.map (fun i => HomologicalComplex.homologyπ (K i) m))
          ((Limits.Sigma.map
            (fun i => (K i).toCycles ((ComplexShape.down ℕ).prev m) m)) v) = a - b := by
        rw [hzw, map_sub, hza, hzb]
      rw [← h1, hzero]
    exact sub_eq_zero.mp hab'
  · intro y
    obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective _).mp hg' y
    obtain ⟨w, hw⟩ := (ModuleCat.epi_iff_surjective (sigmaCyclesMap K m)).mp
      (inferInstance : Epi (sigmaCyclesMap K m)) z
    refine ⟨(Limits.Sigma.map (fun i => HomologicalComplex.homologyπ (K i) m)) w, ?_⟩
    have hw' : ((∐ K).homologyπ m) (sigmaCyclesMap K m w)
        = (sigmaHomologyMap K m)
            ((Limits.Sigma.map (fun i => HomologicalComplex.homologyπ (K i) m)) w) := by
      have h := congrArg
        (fun (g : (∐ fun i => (K i).cycles m) ⟶ (∐ K).homology m) => g w) hsquare
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h
    rw [← hw', hw, hz]

/-! ## Naturality and the main conclusion -/

theorem homologyMap_sigma_natural {K L : ι → ChainComplex (ModuleCat ℚ) ℕ}
    (f : ∀ i, K i ⟶ L i) (m : ℕ) :
    Limits.Sigma.map (fun i => HomologicalComplex.homologyMap (f i) m) ≫ sigmaHomologyMap L m
      = sigmaHomologyMap K m ≫ HomologicalComplex.homologyMap (Limits.Sigma.map f) m := by
  apply Limits.Sigma.hom_ext
  intro i
  calc Limits.Sigma.ι (fun i => (K i).homology m) i
        ≫ (Limits.Sigma.map (fun i => HomologicalComplex.homologyMap (f i) m) ≫ sigmaHomologyMap L m)
      = (Limits.Sigma.ι (fun i => (K i).homology m) i
          ≫ Limits.Sigma.map (fun i => HomologicalComplex.homologyMap (f i) m))
          ≫ sigmaHomologyMap L m := (Category.assoc _ _ _).symm
    _ = (HomologicalComplex.homologyMap (f i) m
          ≫ Limits.Sigma.ι (fun i => (L i).homology m) i) ≫ sigmaHomologyMap L m := by
        rw [Limits.Sigma.ι_map]
    _ = HomologicalComplex.homologyMap (f i) m
          ≫ (Limits.Sigma.ι (fun i => (L i).homology m) i ≫ sigmaHomologyMap L m) :=
        Category.assoc _ _ _
    _ = HomologicalComplex.homologyMap (f i) m
          ≫ HomologicalComplex.homologyMap (Limits.Sigma.ι L i) m := by rw [sigmaHomologyMap_ι]
    _ = HomologicalComplex.homologyMap (f i ≫ Limits.Sigma.ι L i) m :=
        (HomologicalComplex.homologyMap_comp _ _ _).symm
    _ = HomologicalComplex.homologyMap (Limits.Sigma.ι K i ≫ Limits.Sigma.map f) m := by
        rw [Limits.Sigma.ι_map]
    _ = HomologicalComplex.homologyMap (Limits.Sigma.ι K i) m
          ≫ HomologicalComplex.homologyMap (Limits.Sigma.map f) m :=
        HomologicalComplex.homologyMap_comp _ _ _
    _ = (Limits.Sigma.ι (fun i => (K i).homology m) i ≫ sigmaHomologyMap K m)
          ≫ HomologicalComplex.homologyMap (Limits.Sigma.map f) m := by rw [sigmaHomologyMap_ι]
    _ = Limits.Sigma.ι (fun i => (K i).homology m) i
          ≫ (sigmaHomologyMap K m ≫ HomologicalComplex.homologyMap (Limits.Sigma.map f) m) :=
        Category.assoc _ _ _

/-- **If every member of a family of chain maps induces an isomorphism on `H_m`, then so does the
coproduct of the family.** -/
theorem isIso_homologyMap_sigma {K L : ι → ChainComplex (ModuleCat ℚ) ℕ} (f : ∀ i, K i ⟶ L i)
    (m : ℕ) (h : ∀ i, IsIso (HomologicalComplex.homologyMap (f i) m)) :
    IsIso (HomologicalComplex.homologyMap (Limits.Sigma.map f) m) := by
  haveI hK : IsIso (sigmaHomologyMap K m) := isIso_sigmaHomologyMap K m
  haveI hL : IsIso (sigmaHomologyMap L m) := isIso_sigmaHomologyMap L m
  haveI hsum : IsIso (Limits.Sigma.map (fun i => HomologicalComplex.homologyMap (f i) m)) := by
    haveI : ∀ i, IsIso (HomologicalComplex.homologyMap (f i) m) := h
    exact Limits.Sigma.map_isIso _
  have h2 : HomologicalComplex.homologyMap (Limits.Sigma.map f) m
      = (asIso (sigmaHomologyMap K m)).inv
        ≫ Limits.Sigma.map (fun i => HomologicalComplex.homologyMap (f i) m)
        ≫ (asIso (sigmaHomologyMap L m)).hom := by
    rw [asIso_hom, asIso_inv, ← cancel_epi (sigmaHomologyMap K m),
      ← homologyMap_sigma_natural f m]
    simp
  rw [h2]
  infer_instance

end

end Work.Serre

import Mathlib
import Submission.Work.TOOLKIT.Sigma.Toolkit
import Submission.Work.TOOLKIT.Coprod.quasiIso_colimMap

/-!
# Homology commutes with small coproducts

For a small family `K : J → Cpx` of cochain complexes of light condensed abelian groups, the
canonical comparison map
`∐ j, Hᵢ(K j) ⟶ Hᵢ(∐ j, K j)`, i.e. `Work.TOOLKIT.sigmaHomologyMap K i`, is an isomorphism,
compatibly with the coproduct inclusions:

`Sigma.ι (fun j => (K j).homology i) j ≫ sigmaHomologyMap K i = homologyMap (Sigma.ι K j) i`.

`LightCondAb` is a Grothendieck abelian category, hence satisfies AB4: small coproducts are
exact.

The input from AB4 is the isomorphism `c := Work.TOOLKIT.sigmaCyclesHom K i`, which identifies
the coproduct of the cycles with the cycles of the coproduct
(`Work.RESOL.isIso_sigmaCyclesHom`).  With `α := Work.TOOLKIT.sigmaXIso K (i-1)` the connecting
maps `toCycles` satisfy `α ≫ toCycles = Sigma.map toCycles ≫ c`
(`sigmaXIso_toCycles`), whence `toCycles ≫ c⁻¹ = α⁻¹ ≫ Sigma.map toCycles`.  Homology in
degree `i` is the cokernel of `toCycles : X (i-1) ⟶ cycles i`; the desired inverse of
`sigmaHomologyMap K i` is therefore the map on cokernels induced by `c⁻¹ ≫ Sigma.map homologyπ`.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open HomologicalComplex
open _root_.LightCondensed _root_.LightCondensed.Solid
open scoped CategoryTheory.Pretriangulated.Opposite

namespace Work.RESOL

noncomputable section

set_option maxHeartbeats 1600000

variable {J : Type}

/-! ## Elementary compatibility lemmas -/

/-- A coproduct of zero morphisms is zero. -/
lemma sigma_map_zero_of {C : Type*} [Category* C] [HasZeroMorphisms C] {J : Type} (A B : J → C)
    [HasCoproduct A] [HasCoproduct B] :
    Limits.Sigma.map (fun j => (0 : A j ⟶ B j)) = 0 := by
  apply Limits.Sigma.hom_ext
  intro j
  rw [Limits.Sigma.ι_map]
  simp

/-- The defining property of the canonical isomorphism `sigmaXIso`: it is compatible with the
coproduct inclusions of `K`. -/
lemma sigmaXIso_ι_hom (K : J → CochainComplex LightCondAb ℤ) [HasCoproduct K] (i : ℤ) (j : J) :
    (Limits.Sigma.ι K j).f i
      = Limits.Sigma.ι (fun j => (K j).X i) j ≫ (Work.TOOLKIT.sigmaXIso K i).hom := by
  rw [← Work.TOOLKIT.sigmaXIso_ι K i j, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The definition of `Work.TOOLKIT.sigmaCyclesHom`. -/
lemma sigmaCyclesHom_eq (K : J → CochainComplex LightCondAb ℤ) [HasCoproduct K] (i : ℤ) :
    Work.TOOLKIT.sigmaCyclesHom K i
      = Limits.Sigma.desc (fun j => cyclesMap (Limits.Sigma.ι K j) i) := rfl

/-- The definition of `Work.TOOLKIT.sigmaHomologyMap`. -/
lemma sigmaHomologyMap_eq (K : J → CochainComplex LightCondAb ℤ) [HasCoproduct K] (i : ℤ) :
    Work.TOOLKIT.sigmaHomologyMap K i
      = Limits.Sigma.desc (fun j => homologyMap (Limits.Sigma.ι K j) i) := rfl

/-- `Work.TOOLKIT.sigmaCyclesHom` is compatible with the coproduct inclusions. -/
lemma sigmaCyclesHom_apply (K : J → CochainComplex LightCondAb ℤ) [HasCoproduct K] (i : ℤ)
    (j : J) :
    Limits.Sigma.ι (fun j => (K j).cycles i) j ≫ Work.TOOLKIT.sigmaCyclesHom K i
      = cyclesMap (Limits.Sigma.ι K j) i :=
  Limits.Sigma.ι_comp_desc _ j

/-- `Work.TOOLKIT.sigmaHomologyMap` is compatible with the coproduct inclusions. -/
lemma sigmaHomologyMap_ι (K : J → CochainComplex LightCondAb ℤ) [HasCoproduct K] (i : ℤ)
    (j : J) :
    Limits.Sigma.ι (fun j => (K j).homology i) j ≫ Work.TOOLKIT.sigmaHomologyMap K i
      = homologyMap (Limits.Sigma.ι K j) i :=
  Limits.Sigma.ι_comp_desc _ j

/-! ## Compatibility of `sigmaCyclesHom` and `toCycles` with the canonical isomorphisms -/

/-- `Work.TOOLKIT.sigmaCyclesHom` is characterised by its composition with the cycle inclusions. -/
lemma sigmaCyclesHom_iCycles (K : J → CochainComplex LightCondAb ℤ) [HasCoproduct K] (i : ℤ) :
    Work.TOOLKIT.sigmaCyclesHom K i ≫ (∐ K).iCycles i
      = Limits.Sigma.map (fun j => (K j).iCycles i)
        ≫ (Work.TOOLKIT.sigmaXIso K i).hom := by
  have h1 : Work.TOOLKIT.sigmaCyclesHom K i ≫ (∐ K).iCycles i
      = Limits.Sigma.desc (fun j => (K j).iCycles i ≫ (Limits.Sigma.ι K j).f i) := by
    rw [sigmaCyclesHom_eq, ← Work.TOOLKIT.sigma_desc_comp]
    congr 1
    funext j
    rw [cyclesMap_i]
  have h2 : Limits.Sigma.desc (fun j => (K j).iCycles i ≫ (Limits.Sigma.ι K j).f i)
      = Limits.Sigma.desc (fun j => (K j).iCycles i
          ≫ Limits.Sigma.ι (fun j => (K j).X i) j ≫ (Work.TOOLKIT.sigmaXIso K i).hom) := by
    congr 1
    funext j
    rw [sigmaXIso_ι_hom]
  have h3 : Limits.Sigma.desc (fun j => (K j).iCycles i
          ≫ Limits.Sigma.ι (fun j => (K j).X i) j ≫ (Work.TOOLKIT.sigmaXIso K i).hom)
      = Limits.Sigma.desc (fun j => (K j).iCycles i
          ≫ Limits.Sigma.ι (fun j => (K j).X i) j) ≫ (Work.TOOLKIT.sigmaXIso K i).hom := by
    apply Limits.Sigma.hom_ext
    intro j
    rw [Limits.Sigma.ι_comp_desc, Limits.Sigma.ι_comp_desc_assoc, Category.assoc]
  have h4 : Limits.Sigma.desc (fun j => (K j).iCycles i
        ≫ Limits.Sigma.ι (fun j => (K j).X i) j)
      = Limits.Sigma.map (fun j => (K j).iCycles i) := by
    apply Limits.Sigma.hom_ext
    intro j
    rw [Limits.Sigma.ι_comp_desc, Limits.Sigma.ι_map]
  rw [h1, h2, h3, h4]

/-- The connecting map `toCycles` is compatible with the canonical isomorphism `sigmaXIso` and
the cycle comparison `sigmaCyclesHom`. -/
lemma sigmaXIso_toCycles (K : J → CochainComplex LightCondAb ℤ) [HasCoproduct K] (i : ℤ) :
    (Work.TOOLKIT.sigmaXIso K (i-1)).hom ≫ (∐ K).toCycles (i-1) i
      = Limits.Sigma.map (fun j => (K j).toCycles (i-1) i)
        ≫ Work.TOOLKIT.sigmaCyclesHom K i := by
  apply (cancel_mono ((∐ K).iCycles i)).1
  rw [Category.assoc, HomologicalComplex.toCycles_i, Work.TOOLKIT.sigmaXIso_d]
  rw [Category.assoc, sigmaCyclesHom_iCycles, ← Category.assoc, Limits.Sigma.map_comp_map]
  simp [HomologicalComplex.toCycles_i]

/-- The composite of the connecting maps is zero: boundaries die in homology. -/
lemma sigma_toCycles_homologyπ (K : J → CochainComplex LightCondAb ℤ) [HasCoproduct K] (i : ℤ) :
    Limits.Sigma.map (fun j => (K j).toCycles (i-1) i)
      ≫ Limits.Sigma.map (fun j => (K j).homologyπ i) = 0 := by
  rw [Limits.Sigma.map_comp_map (fun j => (K j).homologyπ i)
    (fun j => (K j).toCycles (i-1) i)]
  rw [show (fun j => (K j).toCycles (i-1) i ≫ (K j).homologyπ i) = fun _ => 0 from
    funext fun j => HomologicalComplex.toCycles_comp_homologyπ (K j) (i-1) i]
  exact sigma_map_zero_of _ _

/-- The key identity: the inverse of the cycle comparison, precomposed with `toCycles`, is the
coproduct of the connecting maps. -/
lemma toCycles_inv_sigmaCyclesHom (K : J → CochainComplex LightCondAb ℤ) [HasCoproduct K]
    (i : ℤ) (hci : IsIso (Work.TOOLKIT.sigmaCyclesHom K i)) :
    (∐ K).toCycles (i-1) i ≫ inv (Work.TOOLKIT.sigmaCyclesHom K i)
      = (Work.TOOLKIT.sigmaXIso K (i-1)).inv
        ≫ Limits.Sigma.map (fun j => (K j).toCycles (i-1) i) := by
  haveI := hci
  have hcomp := sigmaXIso_toCycles K i
  have htc : (∐ K).toCycles (i-1) i
      = (Work.TOOLKIT.sigmaXIso K (i-1)).inv
        ≫ Limits.Sigma.map (fun j => (K j).toCycles (i-1) i)
        ≫ Work.TOOLKIT.sigmaCyclesHom K i := by
    calc (∐ K).toCycles (i-1) i
        = (Work.TOOLKIT.sigmaXIso K (i-1)).inv
            ≫ ((Work.TOOLKIT.sigmaXIso K (i-1)).hom ≫ (∐ K).toCycles (i-1) i) := by
          rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
      _ = (Work.TOOLKIT.sigmaXIso K (i-1)).inv
            ≫ (Limits.Sigma.map (fun j => (K j).toCycles (i-1) i)
                ≫ Work.TOOLKIT.sigmaCyclesHom K i) := by rw [hcomp]
      _ = (Work.TOOLKIT.sigmaXIso K (i-1)).inv
            ≫ Limits.Sigma.map (fun j => (K j).toCycles (i-1) i)
            ≫ Work.TOOLKIT.sigmaCyclesHom K i := rfl
  rw [htc]
  simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]

/-! ## AB4: the coproduct of the cycles is the cycles of the coproduct

This is the only input from AB4 (small coproducts are exact in `LightCondAb`); everything else
in this file is formal.  We prove it here so that the file is self-contained. -/

/-- The inverse of `kernel.mapIso` is compatible with the kernel inclusions. -/
lemma kernel_mapIso_inv_ι_aux {C : Type*} [Category* C] [HasZeroMorphisms C] {X Y X' Y' : C}
    (f : X ⟶ Y) [HasKernel f] (f' : X' ⟶ Y') [HasKernel f'] (p : X ≅ X') (q : Y ≅ Y')
    (w : f ≫ q.hom = p.hom ≫ f') :
    (kernel.mapIso f f' p q w).inv ≫ kernel.ι f = kernel.ι f' ≫ p.inv := by
  have h : (kernel.mapIso f f' p q w).hom ≫ kernel.ι f' = kernel.ι f ≫ p.hom := by
    rw [show (kernel.mapIso f f' p q w).hom = kernel.map f f' p.hom q.hom w from rfl]
    rw [kernel.map, kernel.lift_ι]
  rw [← cancel_epi (kernel.mapIso f f' p q w).hom]
  rw [Iso.hom_inv_id_assoc, ← Category.assoc, h, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

/-- **AB4 for cycles**: the coproduct of the cycles is the cycles of the coproduct. -/
lemma isIso_sigmaCyclesHom_aux (K : J → CochainComplex LightCondAb ℤ) [HasCoproduct K] (i : ℤ) :
    IsIso (Work.TOOLKIT.sigmaCyclesHom K i) := by
  have hker : IsIso (Work.TOOLKIT.sigmaKernelHom (fun j => (K j).X i) (fun j => (K j).X (i+1))
      (fun j => (K j).d i (i+1))) := Work.TOOLKIT.isIso_sigmaKernelHom _ _ _
  have hw : (∐ K).d i (i+1) ≫ (Work.TOOLKIT.sigmaXIso K (i+1)).symm.hom
      = (Work.TOOLKIT.sigmaXIso K i).symm.hom
        ≫ Limits.Sigma.map (fun j => (K j).d i (i+1)) := by
    have e1 : (Work.TOOLKIT.sigmaXIso K i).hom
          ≫ ((∐ K).d i (i+1) ≫ (Work.TOOLKIT.sigmaXIso K (i+1)).inv)
        = Limits.Sigma.map (fun j => (K j).d i (i+1)) := by
      rw [← Category.assoc, Work.TOOLKIT.sigmaXIso_d, Category.assoc, Iso.hom_inv_id,
        Category.comp_id]
    have e2 : (Work.TOOLKIT.sigmaXIso K i).hom
          ≫ ((Work.TOOLKIT.sigmaXIso K i).inv
              ≫ Limits.Sigma.map (fun j => (K j).d i (i+1)))
        = Limits.Sigma.map (fun j => (K j).d i (i+1)) := by
      rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rw [Iso.symm_hom, Iso.symm_hom, ← cancel_epi (Work.TOOLKIT.sigmaXIso K i).hom]
    exact e1.trans e2.symm
  set e : kernel ((∐ K).d i (i+1)) ≅ kernel (Limits.Sigma.map (fun j => (K j).d i (i+1))) :=
    kernel.mapIso ((∐ K).d i (i+1)) (Limits.Sigma.map (fun j => (K j).d i (i+1)))
      (Work.TOOLKIT.sigmaXIso K i).symm (Work.TOOLKIT.sigmaXIso K (i+1)).symm hw with he
  set A : (∐ fun j => (K j).cycles i) ⟶ (∐ fun j => kernel ((K j).d i (i+1))) :=
    (Limits.Sigma.mapIso (fun j => Work.TOOLKIT.cyclesKernelIso K i j)).hom with hA
  set B : (∐ fun j => kernel ((K j).d i (i+1)))
      ⟶ kernel (Limits.Sigma.map (fun j => (K j).d i (i+1))) :=
    Work.TOOLKIT.sigmaKernelHom (fun j => (K j).X i) (fun j => (K j).X (i+1))
      (fun j => (K j).d i (i+1)) with hB
  set Cn : kernel (Limits.Sigma.map (fun j => (K j).d i (i+1))) ⟶ kernel ((∐ K).d i (i+1)) :=
    e.inv with hCn
  set Dn : kernel ((∐ K).d i (i+1)) ⟶ (∐ K).cycles i :=
    (Work.TOOLKIT.cyclesKernelIso' (∐ K) i).inv with hDn
  set Φ : (∐ fun j => (K j).cycles i) ⟶ (∐ K).cycles i := A ≫ B ≫ Cn ≫ Dn with hΦ
  have hAiso : IsIso A := by rw [hA]; infer_instance
  have hBiso : IsIso B := by rw [hB]; exact hker
  have hCniso : IsIso Cn := by rw [hCn]; infer_instance
  have hDniso : IsIso Dn := by rw [hDn]; infer_instance
  have hΦiso : IsIso Φ := by
    have h1 : IsIso A := hAiso
    have h2 : IsIso B := hBiso
    have h3 : IsIso Cn := hCniso
    have h4 : IsIso Dn := hDniso
    rw [hΦ]
    infer_instance
  have hstepA : Dn ≫ (∐ K).iCycles i = kernel.ι ((∐ K).d i (i+1)) := by
    rw [hDn, ← Work.TOOLKIT.cyclesKernelIso'_ι (∐ K) i, ← Category.assoc, Iso.inv_hom_id,
      Category.id_comp]
  have hstepB : Cn ≫ kernel.ι ((∐ K).d i (i+1))
      = kernel.ι (Limits.Sigma.map (fun j => (K j).d i (i+1)))
        ≫ (Work.TOOLKIT.sigmaXIso K i).hom := by
    rw [hCn, he, kernel_mapIso_inv_ι_aux, Iso.symm_inv]
  have hstepC : B ≫ kernel.ι (Limits.Sigma.map (fun j => (K j).d i (i+1)))
      = Limits.Sigma.map (fun j => kernel.ι ((K j).d i (i+1))) := by
    rw [hB]
    exact Work.TOOLKIT.sigmaKernelHom_ι _ _ _
  have hstepD : A ≫ Limits.Sigma.map (fun j => kernel.ι ((K j).d i (i+1)))
      = Limits.Sigma.map (fun j => (K j).iCycles i) := by
    rw [hA]
    rw [show (Limits.Sigma.mapIso (fun j => Work.TOOLKIT.cyclesKernelIso K i j)).hom
        = Limits.Sigma.map (fun j => (Work.TOOLKIT.cyclesKernelIso K i j).hom) from rfl]
    rw [Limits.Sigma.map_comp_map]
    congr 1
    funext j
    exact Work.TOOLKIT.cyclesKernelIso_ι K i j
  have hBC : B ≫ kernel.ι (Limits.Sigma.map (fun j => (K j).d i (i+1)))
        ≫ (Work.TOOLKIT.sigmaXIso K i).hom
      = Limits.Sigma.map (fun j => kernel.ι ((K j).d i (i+1)))
        ≫ (Work.TOOLKIT.sigmaXIso K i).hom := by
    rw [← Category.assoc, hstepC]
  have hAD : A ≫ Limits.Sigma.map (fun j => kernel.ι ((K j).d i (i+1)))
        ≫ (Work.TOOLKIT.sigmaXIso K i).hom
      = Limits.Sigma.map (fun j => (K j).iCycles i) ≫ (Work.TOOLKIT.sigmaXIso K i).hom := by
    rw [← Category.assoc, hstepD]
  have hΦic : Φ ≫ (∐ K).iCycles i
      = Limits.Sigma.map (fun j => (K j).iCycles i) ≫ (Work.TOOLKIT.sigmaXIso K i).hom := by
    rw [hΦ]
    simp only [Category.assoc]
    rw [hstepA, hstepB, hBC, hAD]
  have hEq : Work.TOOLKIT.sigmaCyclesHom K i = Φ := by
    rw [← cancel_mono ((∐ K).iCycles i), sigmaCyclesHom_iCycles, hΦic]
  rwa [hEq]

/-! ## The main result -/

theorem isIso_sigmaHomologyMap {J : Type} (K : J → CochainComplex LightCondAb ℤ)
    [CategoryTheory.Limits.HasCoproduct K] (i : ℤ) :
    CategoryTheory.IsIso (Work.TOOLKIT.sigmaHomologyMap K i) := by
  have hci : IsIso (Work.TOOLKIT.sigmaCyclesHom K i) := isIso_sigmaCyclesHom_aux K i
  haveI : IsIso (Work.TOOLKIT.sigmaCyclesHom K i) := hci
  set k : (∐ K).cycles i ⟶ (∐ fun j => (K j).homology i) :=
    inv (Work.TOOLKIT.sigmaCyclesHom K i) ≫ Limits.Sigma.map (fun j => (K j).homologyπ i)
    with hk
  have hkzero : (∐ K).toCycles (i-1) i ≫ k = 0 := by
    rw [hk, ← Category.assoc, toCycles_inv_sigmaCyclesHom K i hci, Category.assoc,
      sigma_toCycles_homologyπ, comp_zero]
  set invm : (∐ K).homology i ⟶ (∐ fun j => (K j).homology i) :=
    Cofork.IsColimit.desc ((∐ K).homologyIsCokernel (i-1) i (by simp)) k
      (by rw [zero_comp]; exact hkzero) with hinvm
  have hfac : (∐ K).homologyπ i ≫ invm = k :=
    Cofork.IsColimit.π_desc' _ k (by rw [zero_comp]; exact hkzero)
  refine IsIso.mk ⟨invm, ?_, ?_⟩
  · -- `sigmaHomologyMap K i ≫ invm = 𝟙`
    apply Limits.Sigma.hom_ext
    intro j
    rw [← Category.assoc, sigmaHomologyMap_ι, Category.comp_id]
    rw [← cancel_epi ((K j).homologyπ i)]
    rw [← Category.assoc, homologyπ_naturality, Category.assoc, hfac]
    rw [← sigmaCyclesHom_apply, hk, Category.assoc, IsIso.hom_inv_id_assoc,
      Limits.Sigma.ι_map]
  · -- `invm ≫ sigmaHomologyMap K i = 𝟙`
    rw [← cancel_epi ((∐ K).homologyπ i)]
    rw [← Category.assoc, hfac, hk, Category.assoc, sigmaHomologyMap_eq]
    rw [Work.TOOLKIT.sigma_map_desc]
    rw [show (fun j => (K j).homologyπ i ≫ homologyMap (Limits.Sigma.ι K j) i)
        = fun j => cyclesMap (Limits.Sigma.ι K j) i ≫ (∐ K).homologyπ i from
      funext fun j => homologyπ_naturality (Limits.Sigma.ι K j) i]
    rw [Work.TOOLKIT.sigma_desc_comp, ← sigmaCyclesHom_eq]
    rw [IsIso.inv_hom_id_assoc, Category.comp_id]

end

end Work.RESOL

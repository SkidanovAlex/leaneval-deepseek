import Mathlib
import Submission.Work.Cohomology.sphereHomologyTop
import Submission.Work.Serre.sigmaChainsIso
import Submission.Work.Serre.LevCopDefs
import Submission.Work.Serre.levCopIso
import Submission.Work.Serre.kernel_sigma_map_iso
import Submission.Work.Serre.homology_coproduct_iso

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The homology of a disjoint union

The singular chain complex of a disjoint union `Σ i, X i` is the coproduct of the singular chain
complexes of the pieces (`Work.Serre.chainSigmaIso`), and homology commutes with coproducts
(`Work.Serre.homology_coproduct_iso`, `Work.Serre.levCopIso`), so the canonical map

`∐ i, Hₙ(Xᵢ; ℤ) ⟶ Hₙ(Σ i, Xᵢ; ℤ)`

induced by the inclusions of the pieces is an isomorphism.
-/

open CategoryTheory CategoryTheory.Limits

namespace Work.Serre

noncomputable section

/-! ## Coproduct naturality -/

/-- Coproduct naturality: `Sigma.desc` of a family followed by a common morphism. -/
theorem sigma_desc_comp {ι : Type} {A : ι → ModuleCat ℤ} {P Q : ModuleCat ℤ}
    (f : ∀ i, A i ⟶ P) (g : P ⟶ Q) :
    Limits.Sigma.desc f ≫ g = Limits.Sigma.desc (fun i => f i ≫ g) := by
  apply Limits.Sigma.hom_ext
  intro i
  rw [← Category.assoc, Limits.Sigma.ι_desc, Limits.Sigma.ι_desc]

/-! ## The levelwise coproduct of chain complexes -/

/-- The coproduct of a family of chain complexes is the levelwise coproduct, compatibly with the
inclusions of the pieces. -/
theorem levCopIsoι {ι : Type} (K : ι → ChainComplex (ModuleCat ℤ) ℕ) :
    ∃ (e : (∐ K) ≅ levCop K), ∀ i, Sigma.ι K i ≫ e.hom = levCopι K i := by
  classical
  let s : Cocone (Discrete.functor K) :=
    Cofan.mk (levCop K) (fun i => levCopι K i)
  have hs : IsColimit s := by
    apply HomologicalComplex.isColimitOfEval (Discrete.functor K) s
    intro n
    let f : ι → ModuleCat ℤ := fun i => (K i).X n
    let e : Discrete.functor K ⋙ HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n
        ≅ Discrete.functor f :=
      Discrete.natIso (fun i => Iso.refl _)
    let c₂ : Cofan f :=
      Cofan.mk ((HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n).mapCocone s).pt
        (fun i => Sigma.ι f i)
    have hc₂ : IsColimit c₂ :=
      IsColimit.ofIsoColimit (coproductIsCoproduct f)
        (Cofan.ext (Iso.refl _) (fun i => Category.comp_id _))
    have hG : IsColimit ((Cocone.precompose e.hom).obj c₂) :=
      (IsColimit.precomposeHomEquiv e c₂).symm hc₂
    refine IsColimit.ofIsoColimit (r := (Cocone.precompose e.hom).obj c₂) hG ?_
    refine Cocone.ext (Iso.refl _) ?_
    intro j
    simp only [Cocone.precompose_obj_pt, Cocone.precompose_obj_ι, Iso.refl_hom,
      Functor.mapCocone_ι_app, Category.comp_id]
    rfl
  refine ⟨IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) hs, ?_⟩
  intro i
  exact IsColimit.comp_coconePointUniqueUpToIso_hom _ _ _

/-! ## The comparison morphism at the level of the levelwise coproduct -/

/-- The inclusion of `(K i).sc n` into the levelwise coproduct short complex. -/
def inclSC {ι : Type} (K : ι → ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) (i : ι) :
    (K i).sc n ⟶ levShort K n :=
  ShortComplex.homMk (Limits.Sigma.ι (fun j => ((K j).sc n).X₁) i)
    (Limits.Sigma.ι (fun j => ((K j).sc n).X₂) i)
    (Limits.Sigma.ι (fun j => ((K j).sc n).X₃) i)
    (by rw [levShort_f]; exact Limits.Sigma.ι_map _ i)
    (by rw [levShort_g]; exact Limits.Sigma.ι_map _ i)

/-- The canonical map `∐ i, Hₙ(K i) ⟶ Hₙ(levCop K)` is an isomorphism. -/
theorem sigma_desc_levCopι_isIso {ι : Type} (K : ι → ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) :
    IsIso (Limits.Sigma.desc (fun i => HomologicalComplex.homologyMap (levCopι K i) n)) := by
  classical
  obtain ⟨ψ, hψ⟩ := levShort_cycles_iso K n
  have hmap : ∀ i, HomologicalComplex.homologyMap (levCopι K i) n
      = ShortComplex.homologyMap (inclSC K n i) := fun i => rfl
  have hcyc : ∀ i, ShortComplex.cyclesMap (inclSC K n i)
      = Limits.Sigma.ι (fun j => ((K j).sc n).cycles) i ≫ ψ.hom := by
    intro i
    rw [← cancel_mono (levShort K n).iCycles]
    rw [ShortComplex.cyclesMap_i, Category.assoc, hψ, Limits.Sigma.ι_map]
    rfl
  have hto : (levShort K n).toCycles
      = Limits.Sigma.map (fun i => ((K i).sc n).toCycles) ≫ ψ.hom := by
    rw [← cancel_mono (levShort K n).iCycles, ShortComplex.toCycles_i, Category.assoc, hψ,
      Limits.Sigma.map_comp_map,
      show (fun i => ((K i).sc n).toCycles ≫ ((K i).sc n).iCycles) = (fun i => ((K i).sc n).f)
        from funext (fun i => ShortComplex.toCycles_i _)]
  have hk : (levShort K n).toCycles
      ≫ (ψ.inv ≫ Limits.Sigma.map (fun i => ((K i).sc n).homologyπ)) = 0 := by
    rw [hto]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    apply Limits.Sigma.hom_ext
    intro i
    rw [← Category.assoc, Limits.Sigma.ι_map, Category.assoc, Limits.Sigma.ι_map,
      ← Category.assoc, ShortComplex.toCycles_comp_homologyπ]
    simp
  let Φ : (levShort K n).homology ⟶ ∐ fun i => ((K i).sc n).homology :=
    (levShort K n).descHomology (ψ.inv ≫ Limits.Sigma.map (fun i => ((K i).sc n).homologyπ)) hk
  let Ψ : (∐ fun i => ((K i).sc n).homology) ⟶ (levShort K n).homology :=
    Limits.Sigma.desc (fun i => ShortComplex.homologyMap (inclSC K n i))
  have hΦ : (levShort K n).homologyπ ≫ Φ
      = ψ.inv ≫ Limits.Sigma.map (fun i => ((K i).sc n).homologyπ) := by
    dsimp only [Φ]
    exact ShortComplex.π_descHomology _ _ _
  have hψhom : Limits.Sigma.desc (fun i => ShortComplex.cyclesMap (inclSC K n i)) = ψ.hom := by
    apply Limits.Sigma.hom_ext
    intro i
    rw [Limits.Sigma.ι_desc]
    exact hcyc i
  have hcomp : Limits.Sigma.map (fun i => ((K i).sc n).homologyπ) ≫ Ψ
      = ψ.hom ≫ (levShort K n).homologyπ := by
    dsimp only [Ψ]
    apply Limits.Sigma.hom_ext
    intro i
    rw [← Category.assoc, Limits.Sigma.ι_map, Category.assoc, Limits.Sigma.ι_desc]
    rw [ShortComplex.homologyπ_naturality, hcyc i, Category.assoc]
  have hΦΨ : Φ ≫ Ψ = 𝟙 _ := by
    rw [← cancel_epi (levShort K n).homologyπ]
    rw [← Category.assoc, hΦ, Category.assoc, hcomp, ← Category.assoc, Iso.inv_hom_id,
      Category.id_comp, Category.comp_id]
  have hΨΦ : Ψ ≫ Φ = 𝟙 _ := by
    dsimp only [Ψ]
    apply Limits.Sigma.hom_ext
    intro i
    rw [← Category.assoc, Limits.Sigma.ι_desc, Category.comp_id]
    rw [← cancel_epi ((K i).sc n).homologyπ]
    rw [← Category.assoc, ShortComplex.homologyπ_naturality, Category.assoc, hΦ, hcyc i,
      Category.assoc, Iso.hom_inv_id_assoc, Limits.Sigma.ι_map]
  have hΨiso : IsIso Ψ := IsIso.mk ⟨Φ, hΨΦ, hΦΨ⟩
  exact hΨiso

/-! ## Descent to the genuine coproduct -/

/-- The canonical map `∐ i, Hₙ(K i) ⟶ Hₙ(∐ i, K i)` is an isomorphism. -/
theorem sigma_desc_sigmaι_isIso {ι : Type} (K : ι → ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) :
    IsIso (Limits.Sigma.desc (fun i => HomologicalComplex.homologyMap (Sigma.ι K i) n)) := by
  obtain ⟨e, he⟩ := levCopIsoι K
  have hcomm : Limits.Sigma.desc (fun i => HomologicalComplex.homologyMap (Sigma.ι K i) n)
      ≫ HomologicalComplex.homologyMap e.hom n
      = Limits.Sigma.desc (fun i => HomologicalComplex.homologyMap (levCopι K i) n) := by
    rw [sigma_desc_comp]
    congr 1
    funext i
    rw [← HomologicalComplex.homologyMap_comp, he i]
  haveI hf : IsIso (HomologicalComplex.homologyMap e.hom n) :=
    Iso.isIso_hom (HomologicalComplex.homologyMapIso e n)
  haveI hg : IsIso (Limits.Sigma.desc (fun i => HomologicalComplex.homologyMap (Sigma.ι K i) n)
      ≫ HomologicalComplex.homologyMap e.hom n) := by
    rw [hcomm]
    exact sigma_desc_levCopι_isIso K n
  exact IsIso.of_isIso_comp_right
    (Limits.Sigma.desc (fun i => HomologicalComplex.homologyMap (Sigma.ι K i) n))
    (HomologicalComplex.homologyMap e.hom n)

/-! ## The singular chains of a disjoint union -/

/-- The simplicial chain functor with coefficients in `ℤ`, packaged for the singular chains of a
topological space. -/
abbrev ssetChainC : SSet ⥤ ChainComplex (ModuleCat ℤ) ℕ :=
  (SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)

/-- The inverse of `chainSigmaMap` in terms of the comparison maps of the singular simplicial
sets. -/
theorem chainSigmaIso_inv_eq {ι : Type} (X : ι → Type) [∀ i, TopologicalSpace (X i)] :
    (chainSigmaIso ℤ ι X).inv
      = (chainCoprodComp ℤ ι (fun j => TopCat.toSSet.obj (TopCat.of (X j))))
        ≫ ssetChainC.map (sigmaToSSetHom ι X) := rfl

/-- The chain map induced by the inclusion of a piece of a disjoint union, in terms of the inverse
of `chainSigmaMap`. -/
theorem chainMap_eq_sigmaι_chainSigmaMap_inv {ι : Type} (X : ι → Type)
    [∀ i, TopologicalSpace (X i)] (i : ι) :
    Work.Cohomology.chainMap ℤ (TopCat.of (X i)) (TopCat.of (Σ j, X j))
        (TopCat.ofHom ⟨Sigma.mk i, continuous_sigmaMk⟩)
      = Limits.Sigma.ι (fun j => Work.Cohomology.singularChains ℤ (TopCat.of (X j))) i
        ≫ (chainSigmaIso ℤ ι X).inv := by
  have hσ : TopCat.sigmaι (fun j => TopCat.of (X j)) i
      = TopCat.ofHom ⟨Sigma.mk i, continuous_sigmaMk⟩ := rfl
  have h1 : Limits.Sigma.ι (fun j => TopCat.toSSet.obj (TopCat.of (X j))) i
      ≫ (asIso (sigmaToSSetHom ι X)).hom
      = TopCat.toSSet.map (TopCat.ofHom ⟨Sigma.mk i, continuous_sigmaMk⟩) := by
    rw [asIso_hom, ← hσ, sigmaToSSetHom, Limits.Sigma.ι_desc]
  rw [chainSigmaIso_inv_eq]
  change ssetChainC.map (TopCat.toSSet.map (TopCat.ofHom ⟨Sigma.mk i, continuous_sigmaMk⟩))
      = Limits.Sigma.ι (fun j => ssetChainC.obj (TopCat.toSSet.obj (TopCat.of (X j)))) i
        ≫ (chainCoprodComp ℤ ι (fun j => TopCat.toSSet.obj (TopCat.of (X j))))
        ≫ ssetChainC.map (sigmaToSSetHom ι X)
  rw [← Category.assoc,
    Sigma.ι_chainCoprodComp ℤ ι (fun j => TopCat.toSSet.obj (TopCat.of (X j))) i,
    ← Functor.map_comp, ← asIso_hom (sigmaToSSetHom ι X), h1]

/-- The chain map induced by the inclusion of a piece of a disjoint union is the corresponding
component of `chainSigmaMap`. -/
theorem chainMap_sigmaι_chainSigmaMap {ι : Type} (X : ι → Type) [∀ i, TopologicalSpace (X i)]
    (i : ι) :
    Work.Cohomology.chainMap ℤ (TopCat.of (X i)) (TopCat.of (Σ j, X j))
        (TopCat.ofHom ⟨Sigma.mk i, continuous_sigmaMk⟩)
      ≫ chainSigmaMap ℤ ι X
      = Limits.Sigma.ι (fun j => Work.Cohomology.singularChains ℤ (TopCat.of (X j))) i := by
  rw [chainMap_eq_sigmaι_chainSigmaMap_inv X i]
  change Limits.Sigma.ι (fun j => Work.Cohomology.singularChains ℤ (TopCat.of (X j))) i
      ≫ (chainSigmaIso ℤ ι X).inv ≫ (chainSigmaIso ℤ ι X).hom
      = Limits.Sigma.ι (fun j => Work.Cohomology.singularChains ℤ (TopCat.of (X j))) i
  rw [Iso.inv_hom_id, Category.comp_id]

/-! ## The target -/

/-- **The homology of a disjoint union is the direct sum of the homologies of the pieces.** -/
theorem serreC0SigmaHomology {ι : Type} (X : ι → Type) [∀ i, TopologicalSpace (X i)] (n : ℕ) :
    CategoryTheory.IsIso (CategoryTheory.Limits.Sigma.desc (fun i => HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (TopCat.of (X i)) (TopCat.of (Σ i, X i))
        (TopCat.ofHom ⟨Sigma.mk i, continuous_sigmaMk⟩)) n)) := by
  classical
  haveI hiso : IsIso (HomologicalComplex.homologyMap (chainSigmaMap ℤ ι X) n) :=
    Iso.isIso_hom (HomologicalComplex.homologyMapIso (chainSigmaIso ℤ ι X) n)
  haveI hstep : IsIso (Limits.Sigma.desc (fun i => HomologicalComplex.homologyMap
      (Limits.Sigma.ι (fun j => Work.Cohomology.singularChains ℤ (TopCat.of (X j))) i) n)) :=
    sigma_desc_sigmaι_isIso (fun j => Work.Cohomology.singularChains ℤ (TopCat.of (X j))) n
  have hcomp : ∀ i, HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ (TopCat.of (X i))
        (TopCat.of (Σ i, X i)) (TopCat.ofHom ⟨Sigma.mk i, continuous_sigmaMk⟩)) n
        ≫ HomologicalComplex.homologyMap (chainSigmaMap ℤ ι X) n
      = HomologicalComplex.homologyMap (Limits.Sigma.ι (fun j =>
            Work.Cohomology.singularChains ℤ (TopCat.of (X j))) i) n := by
    intro i
    rw [← HomologicalComplex.homologyMap_comp, chainMap_sigmaι_chainSigmaMap X i]
  have heq : Limits.Sigma.desc (fun i => HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
          (TopCat.of (X i)) (TopCat.of (Σ i, X i))
          (TopCat.ofHom ⟨Sigma.mk i, continuous_sigmaMk⟩)) n)
        ≫ HomologicalComplex.homologyMap (chainSigmaMap ℤ ι X) n
      = Limits.Sigma.desc (fun i => HomologicalComplex.homologyMap
          (Limits.Sigma.ι (fun j => Work.Cohomology.singularChains ℤ (TopCat.of (X j))) i) n) := by
    rw [sigma_desc_comp]
    exact congrArg Limits.Sigma.desc (funext hcomp)
  haveI hgf : IsIso (Limits.Sigma.desc (fun i => HomologicalComplex.homologyMap
        (Work.Cohomology.chainMap ℤ (TopCat.of (X i)) (TopCat.of (Σ i, X i))
          (TopCat.ofHom ⟨Sigma.mk i, continuous_sigmaMk⟩)) n)
        ≫ HomologicalComplex.homologyMap (chainSigmaMap ℤ ι X) n) := by
    rw [heq]
    exact hstep
  exact IsIso.of_isIso_comp_right
    (Limits.Sigma.desc (fun i => HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
        (TopCat.of (X i)) (TopCat.of (Σ i, X i))
        (TopCat.ofHom ⟨Sigma.mk i, continuous_sigmaMk⟩)) n))
    (HomologicalComplex.homologyMap (chainSigmaMap ℤ ι X) n)

end

end Work.Serre

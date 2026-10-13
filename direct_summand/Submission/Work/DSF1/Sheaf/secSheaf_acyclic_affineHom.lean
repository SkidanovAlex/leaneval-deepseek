import Mathlib
import Submission.Work.DSF1.Sheaf.acyclicAffineHomDefs
import Submission.Work.DSF1.Sheaf.affineHomStalk
import Submission.Work.DSF1.Sheaf.sectionsAffineAcyclic_proved
import Submission.Work.DSF1.Sheaf.pushforward_injective
import Submission.Work.DSF1.Sheaf.isZero_iff_forall_modStalk
import Submission.Work.DSF1.Sheaf.modStalk_preservesHomology
import Submission.Work.DSF1.Sheaf.unit_isIso_of_isZero_rightDerived
import Submission.Work.DSF1.Sheaf.rightDerived_iso_homology_of_acyclic_resolution
import Submission.Work.DSF1.Sheaf.rightDerived_isZero_of_acyclic_resolution
import Submission.Work.DSF1.Sheaf.rightDerived_comp_exact
import Submission.Work.DSEQ0.isZero_homology_sections_injectiveResolution
import Submission.Work.DSG1.enoughInjectives_sheafOfModules

/-!
# Acyclicity of `secSheaf W` for an affine open immersion

Target: `Work.DSF1.Sheaf.secSheaf_acyclic_affineHom`.

For an affine open `W` of a scheme `X` such that the open immersion `W.ι : W ⟶ X` is *affine*,
the sheaf `secSheaf W = (W.ι)_* 𝒪_W` is acyclic for `Γ(X,⊤)`: the unit of the right derived
functor of global sections is an isomorphism at `(secSheaf W)[0]`.

The mathematical content is the degeneration of the Leray spectral sequence for an affine
morphism: `R^q (W.ι)_* 𝒪_W = 0` for `q > 0`, because `V ⊓ W` is affine for every affine open
`V ⊆ X` (the hypothesis `IsAffineHom W.ι`) and `𝒪` has no higher cohomology on an affine scheme.

The proof has three steps.

* `Work.DSF1.Sheaf.isZero_homology_pushforward_injectiveResolution` (module `affineHomStalk`):
  pushing forward an injective resolution `I^•` of `𝒪_W` gives a complex `K^•` on `X` which is
  exact in positive degrees.  This is checked on stalks, using the acyclicity of the sections of
  `I^•` over affine opens of `W` (`Work.DSF1.Sheaf.sectionsAffineAcyclic_proved`, the "Serre vanishing"
  input).
* The augmentation `secSheaf W ⟶ K^•` is therefore a quasi-isomorphism, so
  `R^q Γ(X,⊤)(secSheaf W) ≅ H^q(Γ(X, K^•)) = H^q(Γ(W, I^•)) = 0` for `q > 0`, the last vanishing
  being Serre vanishing on the affine scheme `W`
  (`Work.DSEQ0.isZero_homology_sections_injectiveResolution`).
* The acyclicity criterion `Work.DSF1.Sheaf.unit_isIso_of_isZero_rightDerived` then concludes.
-/

namespace Work.DSF1.Sheaf

open CategoryTheory AlgebraicGeometry Opposite Limits HomologicalComplex

universe u v w x

set_option linter.style.haveILetI false

/-- If a short complex `S` has zero first map, then any additive functor preserving finite limits
preserves any left homology data of `S` (general universes). -/
private lemma preservesLeftHomologyData_of_f_eq_zero' {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type w} [Category.{x} D] [Abelian D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    {S : ShortComplex C} (h : S.LeftHomologyData) (hf : S.f = 0) : h.IsPreservedBy F := by
  refine ShortComplex.LeftHomologyData.IsPreservedBy.mk (by infer_instance) ?_
  have hf' : h.f' = 0 := by
    rw [← cancel_mono h.i, h.f'_i, hf]
    simp
  rw [hf']
  infer_instance

/-- For a cochain complex `K` indexed by `ℕ`, the first morphism of `K.sc 0` is zero, so any
additive left exact functor preserves the left homology of `K.sc 0`. -/
private lemma preservesLeftHomologyOf_sc_zero_nat' {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type w} [Category.{x} D] [Abelian D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] (K : CochainComplex C ℕ) :
    F.PreservesLeftHomologyOf (K.sc 0) := by
  have hf : (K.sc 0).f = 0 := by
    rw [HomologicalComplex.shortComplexFunctor_obj_f]
    exact HomologicalComplex.shape K _ _ (by simp [ComplexShape.up, ComplexShape.up'])
  haveI : (K.sc 0).leftHomologyData.IsPreservedBy F :=
    preservesLeftHomologyData_of_f_eq_zero' F (K.sc 0).leftHomologyData hf
  exact CategoryTheory.Functor.PreservesLeftHomologyOf.mk' F (K.sc 0).leftHomologyData

/-- A left exact additive functor commutes with `H⁰` of `ℕ`-indexed cochain complexes
(general universes). -/
private theorem isIso_homologyMap_zero_of_leftExact_nat' {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type w} [Category.{x} D] [Abelian D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    {K L : CochainComplex C ℕ} (f : K ⟶ L) [QuasiIso f] :
    IsIso (HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map f) 0) := by
  haveI hK : F.PreservesLeftHomologyOf (K.sc 0) := preservesLeftHomologyOf_sc_zero_nat' F K
  haveI hL : F.PreservesLeftHomologyOf (L.sc 0) := preservesLeftHomologyOf_sc_zero_nat' F L
  let Scf : K.sc 0 ⟶ L.sc 0 :=
    (HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℕ) 0).map f
  have hhom : IsIso (ShortComplex.homologyMap Scf) :=
    (quasiIsoAt_iff_isIso_homologyMap f 0).1 (QuasiIso.quasiIsoAt 0)
  let hhomIso := @asIso _ _ _ _ (ShortComplex.homologyMap Scf) hhom
  let Φ : ((K.sc 0).map F).homology ≅ F.obj ((L.sc 0).homology) :=
    ((K.sc 0).mapHomologyIso F).trans (F.mapIso hhomIso)
  have hsq : ShortComplex.homologyMap (F.mapShortComplex.map Scf) ≫
      ((L.sc 0).mapHomologyIso F).hom = Φ.hom :=
    ShortComplex.mapHomologyIso_hom_naturality (F := F) Scf
  have hX : ShortComplex.homologyMap (F.mapShortComplex.map Scf) =
      Φ.hom ≫ ((L.sc 0).mapHomologyIso F).inv := by
    rw [← hsq]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have h1 : ShortComplex.homologyMap (F.mapShortComplex.map Scf)
      ≫ (((L.sc 0).mapHomologyIso F).hom ≫ Φ.inv) = 𝟙 _ := by
    rw [← Category.assoc, hsq, Iso.hom_inv_id]
  have h2 : (((L.sc 0).mapHomologyIso F).hom ≫ Φ.inv)
      ≫ ShortComplex.homologyMap (F.mapShortComplex.map Scf) = 𝟙 _ := by
    rw [hX]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id]
  exact IsIso.mk ⟨((L.sc 0).mapHomologyIso F).hom ≫ Φ.inv, h1, h2⟩

end Work.DSF1.Sheaf

namespace Work.DSF1.Sheaf

open CategoryTheory AlgebraicGeometry Opposite Limits HomologicalComplex

universe u

set_option linter.style.haveILetI false

/-- **Leray vanishing for an affine open immersion.**  If `W` is an affine open of a scheme `X`
and the open immersion `W.ι : W ⟶ X` is affine, then the structure sheaf `𝒪_W` has no higher
direct images along `W.ι`: `R^q (W.ι)_* 𝒪_W = 0` for `q > 0`. -/
theorem isZero_rightDerived_pushforward_unit_affineHom (X : AlgebraicGeometry.Scheme.{u})
    (W : X.Opens) (hW : AlgebraicGeometry.IsAffineOpen W)
    (haff : AlgebraicGeometry.IsAffineHom (AlgebraicGeometry.Scheme.Opens.ι W))
    [HasDerivedCategory (SheafOfModules X.ringCatSheaf)]
    [HasDerivedCategory (SheafOfModules W.toScheme.ringCatSheaf)]
    [EnoughInjectives (SheafOfModules X.ringCatSheaf)]
    [EnoughInjectives (SheafOfModules W.toScheme.ringCatSheaf)] :
    ∀ q : ℕ, 0 < q → IsZero
      (((Work.DSF1.Sheaf.pushforwardι W).rightDerived q).obj (Work.DSF1.Sheaf.unitSheaf W)) := by
  haveI hEIW : EnoughInjectives W.toScheme.Modules :=
    Work.DSG1.enoughInjectives_sheafOfModules W.toScheme
  let I : CategoryTheory.InjectiveResolution (Work.DSF1.Sheaf.unitSheaf W) :=
    CategoryTheory.injectiveResolution _
  -- the resolved complex is exact in positive degrees
  have hKex : ∀ n : ℕ, 0 < n → IsZero (HomologicalComplex.homology
      (((Work.DSF1.Sheaf.pushforwardι W).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        I.cocomplex) n) := fun n hn =>
    isZero_homology_pushforward_injectiveResolution W haff I
      (fun U hU m hm => sectionsAffineAcyclic_proved U hU I m hm)
      (fun x => modStalk_preservesHomology x) n hn
  -- the terms are injective, hence acyclic
  have hac : ∀ n k : ℕ, 0 < k → IsZero
      (((Work.DSF1.Sheaf.pushforwardι W).rightDerived k).obj (I.cocomplex.X n)) := by
    intro n k hk
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    have hInjI := I.injective n
    have hInjK := @Work.DSF1.Sheaf.pushforward_injective X W (I.cocomplex.X n) hInjI
    haveI : CategoryTheory.Injective ((Work.DSF1.Sheaf.pushforwardι W).obj (I.cocomplex.X n)) :=
      hInjK
    exact Functor.isZero_rightDerived_obj_injective_succ
      (Work.DSF1.Sheaf.pushforwardι W) m (I.cocomplex.X n)
  intro q hq
  obtain ⟨e⟩ := Work.DSF1.Sheaf.rightDerived_iso_homology_of_acyclic_resolution
    (Work.DSF1.Sheaf.pushforwardι W) (Work.DSF1.Sheaf.unitSheaf W) I.cocomplex I.ι hac q
  exact IsZero.of_iso (hKex q hq) e

end Work.DSF1.Sheaf

namespace Work.DSF1.Sheaf

open CategoryTheory AlgebraicGeometry Opposite Limits HomologicalComplex

universe u

set_option linter.style.haveILetI false

/-- **The acyclicity of `secSheaf W`**: the higher right derived functors of `Γ(X,⊤)` vanish at
`secSheaf W = (W.ι)_* 𝒪_W`. -/
theorem isZero_rightDerived_secSheaf (X : AlgebraicGeometry.Scheme.{u}) (W : X.Opens)
    (hW : AlgebraicGeometry.IsAffineOpen W)
    (haff : AlgebraicGeometry.IsAffineHom (AlgebraicGeometry.Scheme.Opens.ι W))
    [HasDerivedCategory (SheafOfModules X.ringCatSheaf)]
    [HasDerivedCategory (ModuleCat (X.ringCatSheaf.obj.obj (Opposite.op (⊤ : X.Opens))))]
    [EnoughInjectives (SheafOfModules X.ringCatSheaf)] :
    ∀ q : ℕ, 0 < q → IsZero
      (((Work.DSF1.Sheaf.gammaTop X).rightDerived q).obj (Work.DSF1.secSheaf W)) := by
  haveI hEI : EnoughInjectives X.Modules := Work.DSG1.enoughInjectives_sheafOfModules X
  haveI hDCX : HasDerivedCategory X.Modules :=
    ‹HasDerivedCategory (SheafOfModules X.ringCatSheaf)›
  haveI hAddS : (Work.DSF1.Sheaf.sectionsFunctor X (⊤ : X.Opens)).Additive :=
    inferInstanceAs (((Work.DSF1.Sheaf.gammaTop X) ⋙
      forget₂ (ModuleCat (X.ringCatSheaf.obj.obj (Opposite.op (⊤ : X.Opens))))
        AddCommGrpCat.{u}).Additive)
  haveI hFLS : CategoryTheory.Limits.PreservesFiniteLimits
      (Work.DSF1.Sheaf.sectionsFunctor X (⊤ : X.Opens)) :=
    CategoryTheory.Limits.comp_preservesFiniteLimits
      (SheafOfModules.evaluation X.ringCatSheaf (Opposite.op (⊤ : X.Opens)))
      (forget₂ (ModuleCat (X.ringCatSheaf.obj.obj (Opposite.op (⊤ : X.Opens))))
        AddCommGrpCat.{u})
  -- an injective resolution of `𝒪_W` and its pushforward
  let I : CategoryTheory.InjectiveResolution (Work.DSF1.Sheaf.unitSheaf W) :=
    CategoryTheory.injectiveResolution _
  let K : CochainComplex X.Modules ℕ :=
    ((Work.DSF1.Sheaf.pushforwardι W).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  -- the crux: the pushed forward resolution is a resolution of `secSheaf W`
  have hKex : ∀ n : ℕ, 0 < n → CategoryTheory.Limits.IsZero (K.homology n) := fun n hn =>
    isZero_homology_pushforward_injectiveResolution W haff I
      (fun U hU m hm => sectionsAffineAcyclic_proved U hU I m hm)
      (fun x => modStalk_preservesHomology x) n hn
  -- its terms are injective, hence acyclic for the sections functor
  have hac : ∀ n k : ℕ, 0 < k → CategoryTheory.Limits.IsZero
      (((Work.DSF1.Sheaf.sectionsFunctor X (⊤ : X.Opens)).rightDerived k).obj (K.X n)) := by
    intro n k hk
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    have hInjI := I.injective n
    have hInjK := @Work.DSF1.Sheaf.pushforward_injective X W (I.cocomplex.X n) hInjI
    haveI : CategoryTheory.Injective (K.X n) := hInjK
    exact Functor.isZero_rightDerived_obj_injective_succ
      (Work.DSF1.Sheaf.sectionsFunctor X (⊤ : X.Opens)) m (K.X n)
  -- the sections of the pushed forward resolution vanish in positive degrees
  have hKH : ∀ k : ℕ, 0 < k → CategoryTheory.Limits.IsZero
      (HomologicalComplex.homology
        (((Work.DSF1.Sheaf.sectionsFunctor X (⊤ : X.Opens)).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj K) k) := by
    intro k hk
    have htop : ((AlgebraicGeometry.Scheme.Opens.ι W) ⁻¹ᵁ (⊤ : X.Opens)) = ⊤ :=
      AlgebraicGeometry.Scheme.Hom.preimage_top _
    haveI : AlgebraicGeometry.IsAffine W.toScheme := hW
    haveI hEIW : EnoughInjectives W.toScheme.Modules :=
      Work.DSG1.enoughInjectives_sheafOfModules W.toScheme
    show CategoryTheory.Limits.IsZero (HomologicalComplex.homology
      (((Work.DSF1.Sheaf.sectionsFunctor W.toScheme
        ((AlgebraicGeometry.Scheme.Opens.ι W) ⁻¹ᵁ (⊤ : X.Opens))).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj I.cocomplex) k)
    rw [htop]
    exact Work.DSEQ0.isZero_homology_sections_injectiveResolution W.toScheme I k hk
  -- the augmentation `secSheaf W ⟶ K` is a quasi-isomorphism
  let aug : (CochainComplex.single₀ X.Modules).obj (Work.DSF1.secSheaf W) ⟶ K :=
    (HomologicalComplex.singleMapHomologicalComplex (Work.DSF1.Sheaf.pushforwardι W)
        (ComplexShape.up ℕ) 0).inv.app (Work.DSF1.Sheaf.unitSheaf W) ≫
      ((Work.DSF1.Sheaf.pushforwardι W).mapHomologicalComplex (ComplexShape.up ℕ)).map I.ι
  have hqui : QuasiIso aug := by
    haveI hqI : QuasiIso I.ι := I.quasiIso
    refine (quasiIso_iff aug).mpr (fun j => (quasiIsoAt_iff_isIso_homologyMap aug j).mpr ?_)
    rcases j with _ | j
    · rw [HomologicalComplex.homologyMap_comp]
      haveI h1 : IsIso (HomologicalComplex.homologyMap
          ((HomologicalComplex.singleMapHomologicalComplex (Work.DSF1.Sheaf.pushforwardι W)
            (ComplexShape.up ℕ) 0).inv.app (Work.DSF1.Sheaf.unitSheaf W)) 0) :=
        Functor.map_isIso (HomologicalComplex.homologyFunctor X.Modules (ComplexShape.up ℕ) 0) _
      haveI h2 : IsIso (HomologicalComplex.homologyMap
          (((Work.DSF1.Sheaf.pushforwardι W).mapHomologicalComplex (ComplexShape.up ℕ)).map I.ι) 0) :=
        isIso_homologyMap_zero_of_leftExact_nat' (Work.DSF1.Sheaf.pushforwardι W) I.ι
      infer_instance
    · exact IsZero.isIso
        (HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℕ) 0 _ (j + 1) (by omega))
        (hKex (j + 1) (by omega)) _
  haveI := hqui
  -- the vanishing of the right derived functors of the sections functor at `secSheaf W`
  have hvan : ∀ q : ℕ, 0 < q → CategoryTheory.Limits.IsZero
      (((Work.DSF1.Sheaf.sectionsFunctor X (⊤ : X.Opens)).rightDerived q).obj
        (Work.DSF1.secSheaf W)) :=
    Work.DSF1.Sheaf.rightDerived_isZero_of_acyclic_resolution
      (Work.DSF1.Sheaf.sectionsFunctor X (⊤ : X.Opens)) (Work.DSF1.secSheaf W) K aug hac hKH
  -- transport along `forget₂` to the `ModuleCat`-valued evaluation functor
  intro q hq
  obtain ⟨e⟩ := Work.DSF1.Sheaf.rightDerived_comp_exact (Work.DSF1.Sheaf.gammaTop X)
    (forget₂ (ModuleCat (X.ringCatSheaf.obj.obj (Opposite.op (⊤ : X.Opens))))
      AddCommGrpCat.{u}) (Work.DSF1.secSheaf W) q
  exact isZero_of_isZero_obj
    (forget₂ (ModuleCat (X.ringCatSheaf.obj.obj (Opposite.op (⊤ : X.Opens))))
      AddCommGrpCat.{u})
    (((Work.DSF1.Sheaf.gammaTop X).rightDerived q).obj (Work.DSF1.secSheaf W))
    (IsZero.of_iso (hvan q hq) e.symm)

end Work.DSF1.Sheaf

namespace Work.DSF1.Sheaf

open CategoryTheory AlgebraicGeometry Opposite Limits HomologicalComplex

universe u

set_option linter.style.haveILetI false

theorem secSheaf_acyclic_affineHom (X : AlgebraicGeometry.Scheme.{u}) (W : X.Opens)
    (hW : AlgebraicGeometry.IsAffineOpen W)
    (haff : AlgebraicGeometry.IsAffineHom (AlgebraicGeometry.Scheme.Opens.ι W))
    [HasDerivedCategory (SheafOfModules X.ringCatSheaf)]
    [HasDerivedCategory (ModuleCat (X.ringCatSheaf.obj.obj (Opposite.op (⊤ : X.Opens))))] :
    CategoryTheory.IsIso
      ((SheafOfModules.evaluation X.ringCatSheaf (Opposite.op (⊤ : X.Opens))).rightDerivedFunctorPlusUnith.app
        ((HomotopyCategory.Plus.singleFunctor X.Modules 0).obj (Work.DSF1.secSheaf W))) := by
  haveI hEIS : EnoughInjectives (SheafOfModules X.ringCatSheaf) :=
    Work.DSG1.enoughInjectives_sheafOfModules X
  exact Work.DSF1.Sheaf.unit_isIso_of_isZero_rightDerived
    (SheafOfModules.evaluation X.ringCatSheaf (Opposite.op (⊤ : X.Opens)))
    (Work.DSF1.secSheaf W)
    (isZero_rightDerived_secSheaf X W hW haff)

end Work.DSF1.Sheaf

import Mathlib
import Submission.Work.SSGRoute.E1aClean.finPlaceDict
import Submission.Work.SSGRoute.E1aClean.phiCanDefs
import Submission.Work.SSGRoute.E1aClean.localDictFromFamily
import Submission.Work.SSGRoute.E1aClean.finPlaceSquare
import Submission.Work.SSGRoute.PT.E1aFinBox.mapExtAddHom_mk0_comp
import Submission.Work.SSGRoute.PT.E1aFinBox.extResEquivExplicit_natural
import Submission.Work.SSGRoute.PT.E1aFinBox.e1cEquiv_symm_mapH1
import Submission.Work.SSGRoute.PT.E1aFinBox.levelChangeTransferD_natural
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PT.E1aFinBox

open CategoryTheory SSGRoute.PTExt

attribute [local instance 10000] Work.SSGRoute.homCoind.instDistribMulActionAlgEquiv

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- **Coefficient naturality of the `H1loc` model bridge at an arbitrary subgroup.**

`Work.SSGRoute.E1aClean.h1locCoeffNatural` is the case `H = decomp k A` with the canonical
`decompDistribMulAction`; this is the same statement for an arbitrary subgroup `H ≤ Gal(Ω/k)` with
an arbitrary compatible `↥H`-action (assumed equal to the pullback of the `Gal(K/k)`-action along
`res k K`).  The map `F` is pointwise application of `f` on locally constant cocycles. -/
theorem h1locCoeffNaturalGen (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (H : Subgroup (Ω ≃ₐ[k] Ω))
    (E₁ : Type) [AddCommGroup E₁] [Module (ZMod p) E₁] [DistribMulAction (K ≃ₐ[k] K) E₁]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₁]
    (E₂ : Type) [AddCommGroup E₂] [Module (ZMod p) E₂] [DistribMulAction (K ≃ₐ[k] K) E₂]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₂]
    [instH₁ : DistribMulAction ↥H E₁] [instH₂ : DistribMulAction ↥H E₂]
    (hc₁ : ∀ (h : ↥H) (m : E₁), h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m)
    (hc₂ : ∀ (h : ↥H) (m : E₂), h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m)
    (f : E₁ →+ E₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : E₁), f (g • e) = g • f e) :
    ∃ F : Work.SSGRoute.H1loc p k Ω K E₁ H →+ Work.SSGRoute.H1loc p k Ω K E₂ H,
      (∀ (b : (Ω ≃ₐ[k] Ω) → E₁)
        (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) H b)
        (hl : SSGRoute.IsLocConstOn H b),
        F (Work.SSGRoute.toClass p k Ω K E₁ H b) =
          Work.SSGRoute.toClass p k Ω K E₂ H (fun g => f (b g))) ∧
      (∀ (x : Work.SSGRoute.H1loc p k Ω K E₁ H),
        Work.SSGRoute.H1locEquivH1 p k Ω K E₂ H hc₂ (F x) =
          Work.AbsoluteKummer.mapH1 f
            (fun (h : ↥H) (e : E₁) => by
              show f (h • e) = h • f e
              rw [hc₁ h e, hc₂ h (f e)]
              exact hf (SSGRoute.res k K (h : Ω ≃ₐ[k] Ω)) e)
            (Work.SSGRoute.H1locEquivH1 p k Ω K E₁ H hc₁ x)) := by
  classical
  have hfl : ∀ (c : ZMod p) (e : E₁), f (c • e) = c • f e := by
    intro c e
    have h1 : c • e = c.val • e := by
      conv_lhs => rw [← ZMod.natCast_zmod_val c]
      rw [Nat.cast_smul_eq_nsmul]
    have h2 : c • f e = c.val • f e := by
      conv_lhs => rw [← ZMod.natCast_zmod_val c]
      rw [Nat.cast_smul_eq_nsmul]
    rw [h1, h2, map_nsmul]
  let Gmap : ↥(Work.SSGRoute.lcCocycles p k Ω K E₁ H) →ₗ[ZMod p]
      ↥(Work.SSGRoute.lcCocycles p k Ω K E₂ H) :=
    { toFun := fun c => ⟨fun g => f (c.1 g), by
        obtain ⟨hc1, hc2⟩ := c.2
        refine ⟨?_, ?_⟩
        · intro g hg h hh
          simp only [hc1 g hg h hh, map_add, hf]
        · obtain ⟨U, hUo, hU⟩ := hc2
          exact ⟨U, hUo, fun g hg u hu huH => by simp only [hU g hg u hu huH]⟩⟩
      map_add' := fun a b => Subtype.ext (funext fun g => by simp)
      map_smul' := fun c a => Subtype.ext (funext fun g => by
        simp only [Submodule.coe_smul, Pi.smul_apply]
        exact hfl c (a.1 g)) }
  let hinc : Work.SSGRoute.cobQ p k Ω K E₁ H ≤
      Submodule.comap Gmap (Work.SSGRoute.cobQ p k Ω K E₂ H) := by
    intro x hx
    obtain ⟨m, hm⟩ := hx
    refine ⟨f m, fun g hg => ?_⟩
    have hxg : x.1 g = SSGRoute.res k K g • m - m := hm g hg
    show f (x.1 g) = SSGRoute.res k K g • f m - f m
    rw [hxg, map_sub, hf]
  refine ⟨(Submodule.mapQ (Work.SSGRoute.cobQ p k Ω K E₁ H)
      (Work.SSGRoute.cobQ p k Ω K E₂ H) Gmap hinc).toAddMonoidHom, ?_, ?_⟩
  · intro b hb hl
    have hb1 : b ∈ Work.SSGRoute.lcCocycles p k Ω K E₁ H := ⟨hb, hl⟩
    have hb2 : (fun g => f (b g)) ∈ Work.SSGRoute.lcCocycles p k Ω K E₂ H :=
      (Gmap ⟨b, hb1⟩).2
    rw [Work.SSGRoute.toClass, dif_pos hb1, Work.SSGRoute.toClass, dif_pos hb2,
      Submodule.mkQ_apply, Submodule.mkQ_apply]
    change (Submodule.mapQ (Work.SSGRoute.cobQ p k Ω K E₁ H)
        (Work.SSGRoute.cobQ p k Ω K E₂ H) Gmap hinc)
        (Submodule.Quotient.mk ⟨b, hb1⟩) =
      Submodule.Quotient.mk ⟨fun g => f (b g), hb2⟩
    rw [Submodule.mapQ_apply]
    congr 1
  · intro x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective
      (p := Work.SSGRoute.cobQ p k Ω K E₁ H) x
    change (Work.SSGRoute.H1locEquivH1 p k Ω K E₂ H hc₂)
        ((Submodule.mapQ (Work.SSGRoute.cobQ p k Ω K E₁ H)
          (Work.SSGRoute.cobQ p k Ω K E₂ H) Gmap hinc)
          (Submodule.Quotient.mk z))
      = Work.AbsoluteKummer.mapH1 f
          (fun (h : ↥H) (e : E₁) => by
            show f (h • e) = h • f e
            rw [hc₁ h e, hc₂ h (f e)]
            exact hf (SSGRoute.res k K (h : Ω ≃ₐ[k] Ω)) e)
          ((Work.SSGRoute.H1locEquivH1 p k Ω K E₁ H hc₁)
            (Submodule.Quotient.mk z))
    rw [Submodule.mapQ_apply]
    change (Work.SSGRoute.bridgeFwd p k Ω K E₂ H hc₂)
        (Submodule.Quotient.mk (Gmap z))
      = Work.AbsoluteKummer.mapH1 f
          (fun (h : ↥H) (e : E₁) => by
            show f (h • e) = h • f e
            rw [hc₁ h e, hc₂ h (f e)]
            exact hf (SSGRoute.res k K (h : Ω ≃ₐ[k] Ω)) e)
          ((Work.SSGRoute.bridgeFwd p k Ω K E₁ H hc₁)
            (Submodule.Quotient.mk z))
    rw [Work.SSGRoute.E1aClean.bridgeFwd_mk p k Ω K E₂ H hc₂ _,
      Work.SSGRoute.E1aClean.bridgeFwd_mk p k Ω K E₁ H hc₁ _]
    erw [Work.AbsoluteKummer.mapH1_H1π]
    congr 1

/-- **`h1locSubgroupEqEquiv` is the identity on `toClass`-classes.**  Transporting the local `H¹`
along a subgroup equality does not change the class represented by a cochain. -/
theorem h1locSubgroupEqEquiv_toClass {k : Type} [Field k] {Ω : Type} [Field Ω] [Algebra k Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    (p : ℕ) [Fact p.Prime] (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    {H H' : Subgroup (Ω ≃ₐ[k] Ω)} (h : H = H') (b : (Ω ≃ₐ[k] Ω) → M) :
    Work.SSGRoute.E1aClean.h1locSubgroupEqEquiv p M h
        (Work.SSGRoute.toClass p k Ω K M H b)
      = Work.SSGRoute.toClass p k Ω K M H' b := by
  cases h
  rfl

/-- **Naturality of the canonical coefficient transport `e1aCoeffNat`** (the second clause of
`Work.SSGRoute.PT.e1a_coeff_iso_natural`, from which `e1aCoeffNat` is chosen). -/
theorem e1aCoeffNat_natural (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E₁ : Type) [AddCommGroup E₁] [Module (ZMod p) E₁] [DistribMulAction (K ≃ₐ[k] K) E₁]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₁] [Finite E₁]
    (E₂ : Type) [AddCommGroup E₂] [Module (ZMod p) E₂] [DistribMulAction (K ≃ₐ[k] K) E₂]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₂] [Finite E₂]
    (f : E₁ →ₗ[ZMod p] E₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : E₁), f (g • e) = g • f e)
    (F : SSGRoute.PTExt.modRep (K ≃ₐ[k] K) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E₂ T)) ⟶
      SSGRoute.PTExt.modRep (K ≃ₐ[k] K) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E₁ T)))
    (hF : ∀ (φ : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E₂ T)) (e : E₁) (t : T),
      (show Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E₁ T) from F.hom φ)
        (TensorProduct.tmul (ZMod p) e t) = φ (TensorProduct.tmul (ZMod p) (f e) t))
    (e : E₁) :
    Work.SSGRoute.ExtChain.e1aCoeffNat p k Ω K ζ hζ hζK T hT E₂ (f e)
      = AddMonoidHom.comp (Work.SSGRoute.ExtChain.e1aCoeffNat p k Ω K ζ hζ hζK T hT E₁ e)
          (Rep.Hom.hom F).toAddMonoidHom :=
  (Classical.choose_spec
    (Work.SSGRoute.PT.e1a_coeff_iso_natural p k Ω K ζ hζ hζK T hT)).2 E₁ E₂ f hf F hF e

/-- **The `Eq.mp`/`AddEquiv.refl` transport of a type family commutes with premultiplication by a
degree-zero class.**  This is the coefficient bookkeeping of the sixth factor of `phiCan`'s chain
(see `Work.SSGRoute.E1aClean.eq_mp_congrArg_refl_apply`): transporting an `Ext`-class along an
equality of its *second* argument commutes with `Ext.comp`-ing a degree-zero class into the first
argument. -/
theorem eq_mp_congrArg_refl_comp {C : Type*} [CategoryTheory.Category C]
    [CategoryTheory.Abelian C] [CategoryTheory.HasExt C]
    {X₁ X₂ : C} {u₁ u₂ : C} (h : u₁ = u₂) (c : X₂ ⟶ X₁)
    (y : CategoryTheory.Abelian.Ext X₁ u₁ 1) :
    (Eq.mp (congrArg (fun S => CategoryTheory.Abelian.Ext X₂ u₁ 1 ≃+
        CategoryTheory.Abelian.Ext X₂ S 1) h)
      (AddEquiv.refl (CategoryTheory.Abelian.Ext X₂ u₁ 1)))
      ((CategoryTheory.Abelian.Ext.mk₀ c).comp y (zero_add 1))
    = (CategoryTheory.Abelian.Ext.mk₀ c).comp
        ((Eq.mp (congrArg (fun S => CategoryTheory.Abelian.Ext X₁ u₁ 1 ≃+
            CategoryTheory.Abelian.Ext X₁ S 1) h)
          (AddEquiv.refl (CategoryTheory.Abelian.Ext X₁ u₁ 1))) y) (zero_add 1) := by
  cases h
  rfl

end

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 2000000

open CategoryTheory SSGRoute.PTExt Work.SSGRoute.E1aClean in
theorem phiCan_natural (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (hAq : ∀ x : NumberField.RingOfIntegers ↥K, x ∈ q.asIdeal ↔ A.valuation (((x : ↥K) : Ω)) < 1)
    [hNorm : Normal ↥(decompField k Ω A) ↥(henselOverDecomp k Ω K A)]
    (e : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)) ≃*
      (↥(henselOverDecomp k Ω K A) ≃ₐ[↥(decompField k Ω A)] ↥(henselOverDecomp k Ω K A)))
    (hφres : ∀ g : Ω ≃ₐ[↥(decompField k Ω A)] Ω,
      levelTwoGroupHom k Ω K A hA q hAq e
          (SSGRoute.res ↥(decompField k Ω A) (henselOverDecomp k Ω K A) g)
        = SSGRoute.res k K (AlgEquiv.restrictScalars k g))
    (θ : Rep.res e.toMonoidHom
          (SSGRoute.PTExt.unitsK ↥(decompField k Ω A) ↥(henselOverDecomp k Ω K A)) ⟶
        SSGRoute.PTExt.localUnitsK (k := k) (NK.GlobalCFT.Place.ofFinite q))
    (hpush : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E]
        [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E],
        Function.Bijective ((CategoryTheory.Abelian.Ext.mk₀ θ).postcomp
          (Rep.res (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype
            (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
              (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))))
          (add_zero 1)))
    (E₁ : Type) [AddCommGroup E₁] [Module (ZMod p) E₁] [DistribMulAction (K ≃ₐ[k] K) E₁]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₁] [Finite E₁]
    (E₂ : Type) [AddCommGroup E₂] [Module (ZMod p) E₂] [DistribMulAction (K ≃ₐ[k] K) E₂]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₂] [Finite E₂]
    (f : E₁ →ₗ[ZMod p] E₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : E₁), f (g • e) = g • f e)
    (F : Work.SSGRoute.H1loc p k Ω K E₁ (SSGRoute.decomp k A) →+
          Work.SSGRoute.H1loc p k Ω K E₂ (SSGRoute.decomp k A))
    (hF1 : ∀ (b : (Ω ≃ₐ[k] Ω) → E₁)
      (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
      (hl : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b),
      F (Work.SSGRoute.toClass p k Ω K E₁ (SSGRoute.decomp k A) b) =
        Work.SSGRoute.toClass p k Ω K E₂ (SSGRoute.decomp k A) (fun g => f (b g)))
    (F' : SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
          (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E₂ T)) ⟶
        SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
          (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E₁ T)))
    (hF' : ∀ (φ : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E₂ T)) (e : E₁) (t : T),
      (show Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E₁ T) from F'.hom φ)
        (TensorProduct.tmul (ZMod p) e t) = φ (TensorProduct.tmul (ZMod p) (f e) t))
    (x : Work.SSGRoute.H1loc p k Ω K E₁ (SSGRoute.decomp k A)) :
    (phiCan p k Ω K ζ hζ hζK T hT A hA q hAq e hφres θ hpush E₂) (F x) =
      (CategoryTheory.Abelian.Ext.mk₀
        (Rep.resMap (SSGRoute.PTExt.decompK (k := k)
          (NK.GlobalCFT.Place.ofFinite q)).subtype F')).comp
        ((phiCan p k Ω K ζ hζ hζK T hT A hA q hAq e hφres θ hpush E₁) x) (zero_add 1) := by
  classical
  -- ## the level-change datum instances (`phiCan`'s body, verbatim)
  haveI hGal : IsGalois k Ω := IsAlgClosure.isGalois k Ω
  haveI hAlg : IsAlgClosure ↥(decompField k Ω A) Ω := decompField_isAlgClosure_via k Ω K A rfl
  haveI hFd : FiniteDimensional ↥(decompField k Ω A) ↥(henselOverDecomp k Ω K A) :=
    henselOverDecomp_finiteDimensional k Ω K A
  haveI hGl : IsGalois ↥(decompField k Ω A) ↥(henselOverDecomp k Ω K A) :=
    henselOverDecomp_isGalois k Ω K A
  haveI hChar : CharZero ↥(decompField k Ω A) := inferInstance
  haveI hTfin : Finite T := Work.SSGRoute.ExtChain.e1aFiniteT p k Ω K ζ T hT
  have hfix : (decompField k Ω A).fixingSubgroup = SSGRoute.decomp k A :=
    decompField_fixingSubgroup_via k Ω K A rfl
  -- ## the two coefficient representations and their restrictions
  let X₁ : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) :=
    SSGRoute.PTExt.modRep (K ≃ₐ[k] K) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E₁ T))
  let X₂ : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) :=
    SSGRoute.PTExt.modRep (K ≃ₐ[k] K) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E₂ T))
  haveI hDfin₁ : Finite (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E₁ T)) :=
    Work.SSGRoute.PT.finite_dualMod_tensor p E₁ T
  haveI hDfin₂ : Finite (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E₂ T)) :=
    Work.SSGRoute.PT.finite_dualMod_tensor p E₂ T
  haveI hXfin₁ : Module.Finite ℤ X₁.V := by
    change Module.Finite ℤ (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E₁ T))
    exact Module.Finite.of_finite
  haveI hXfin₂ : Module.Finite ℤ X₂.V := by
    change Module.Finite ℤ (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E₂ T))
    exact Module.Finite.of_finite
  let XD₁ : Rep.{0} SSGRoute.PTExt.Coeff
      ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)) :=
    Rep.res (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype X₁
  let XD₂ : Rep.{0} SSGRoute.PTExt.Coeff
      ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)) :=
    Rep.res (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype X₂
  let R₂₁ : Rep.{0} SSGRoute.PTExt.Coeff
      (↥(henselOverDecomp k Ω K A) ≃ₐ[↥(decompField k Ω A)] ↥(henselOverDecomp k Ω K A)) :=
    Rep.res e.symm.toMonoidHom XD₁
  let R₂₂ : Rep.{0} SSGRoute.PTExt.Coeff
      (↥(henselOverDecomp k Ω K A) ≃ₐ[↥(decompField k Ω A)] ↥(henselOverDecomp k Ω K A)) :=
    Rep.res e.symm.toMonoidHom XD₂
  haveI hR₂fin₁ : Module.Finite ℤ R₂₁.V := hXfin₁
  haveI hR₂fin₂ : Module.Finite ℤ R₂₂.V := hXfin₂
  -- ## the `G_k`-action on the two coefficient modules, pulled back from `Gal(K/k)`
  letI hΓE₁ : DistribMulAction (Ω ≃ₐ[k] Ω) E₁ := DistribMulAction.compHom E₁ (SSGRoute.res k K)
  letI hΓE₂ : DistribMulAction (Ω ≃ₐ[k] Ω) E₂ := DistribMulAction.compHom E₂ (SSGRoute.res k K)
  -- ## the intermediate coefficient maps
  obtain ⟨k₁, hk₁₁, hk₁₂⟩ := h1locCoeffNaturalGen p k Ω K ((decompField k Ω A).fixingSubgroup)
    E₁ E₂ (fun h m => rfl) (fun h m => rfl) f.toAddMonoidHom (fun g e => hf g e)
  have hfH' : Work.GroupCohomology.IsEquivariant ↥((decompField k Ω A).fixingSubgroup)
      f.toAddMonoidHom :=
    fun σ e => hf (SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω)) e
  let k₂ : Work.AbsoluteKummer.H1 ↥((decompField k Ω A).fixingSubgroup) E₁ →+
      Work.AbsoluteKummer.H1 ↥((decompField k Ω A).fixingSubgroup) E₂ :=
    Work.AbsoluteKummer.mapH1 f.toAddMonoidHom hfH'
  have hgT : Work.GroupCohomology.IsEquivariant ↥((decompField k Ω A).fixingSubgroup)
      (Work.SSGRoute.precompAddHom (Rep.Hom.hom F').toAddMonoidHom) :=
    fun σ m => Work.SSGRoute.ExtChain.E1cGeneric.precompAddHom_equivariant F'
      (σ : Ω ≃ₐ[k] Ω) m
  let k₃ : Work.AbsoluteKummer.H1 ↥((decompField k Ω A).fixingSubgroup)
        (Work.SSGRoute.homCoind k Ω K X₁) →+
      Work.AbsoluteKummer.H1 ↥((decompField k Ω A).fixingSubgroup)
        (Work.SSGRoute.homCoind k Ω K X₂) :=
    Work.AbsoluteKummer.mapH1 (Work.SSGRoute.precompAddHom (Rep.Hom.hom F').toAddMonoidHom) hgT
  let F'' : XD₂ ⟶ XD₁ :=
    Rep.resMap (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype F'
  let gR : R₂₂ ⟶ R₂₁ := Rep.resMap e.symm.toMonoidHom F''
  have hgB : Work.GroupCohomology.IsEquivariant (Ω ≃ₐ[↥(decompField k Ω A)] Ω)
      (Work.SSGRoute.precompAddHom (Rep.Hom.hom gR).toAddMonoidHom) :=
    Work.SSGRoute.ExtChain.E1cGeneric.precompAddHom_equivariant gR
  let k₄ : Work.AbsoluteKummer.H1 (Ω ≃ₐ[↥(decompField k Ω A)] Ω)
        (Work.SSGRoute.homCoind ↥(decompField k Ω A) Ω (henselOverDecomp k Ω K A) R₂₁) →+
      Work.AbsoluteKummer.H1 (Ω ≃ₐ[↥(decompField k Ω A)] Ω)
        (Work.SSGRoute.homCoind ↥(decompField k Ω A) Ω (henselOverDecomp k Ω K A) R₂₂) :=
    Work.AbsoluteKummer.mapH1 (Work.SSGRoute.precompAddHom (Rep.Hom.hom gR).toAddMonoidHom) hgB
  -- ## the outer factors
  let Y := Rep.res e.toMonoidHom
    (SSGRoute.PTExt.unitsK ↥(decompField k Ω A) ↥(henselOverDecomp k Ω K A))
  let A6₁ := extResEquivExplicit e XD₁ (Rep.res e.toMonoidHom
    (SSGRoute.PTExt.unitsK ↥(decompField k Ω A) ↥(henselOverDecomp k Ω K A)))
  let A6₂ := extResEquivExplicit e XD₂ (Rep.res e.toMonoidHom
    (SSGRoute.PTExt.unitsK ↥(decompField k Ω A) ↥(henselOverDecomp k Ω K A)))
  let A7₁ := AddEquiv.ofBijective
    ((CategoryTheory.Abelian.Ext.mk₀ θ).postcomp XD₁ (add_zero 1)) (hpush E₁)
  let A7₂ := AddEquiv.ofBijective
    ((CategoryTheory.Abelian.Ext.mk₀ θ).postcomp XD₂ (add_zero 1)) (hpush E₂)
  have hY : Rep.res e.symm.toMonoidHom (Rep.res e.toMonoidHom
      (SSGRoute.PTExt.unitsK ↥(decompField k Ω A) ↥(henselOverDecomp k Ω K A)))
      = SSGRoute.PTExt.unitsK ↥(decompField k Ω A) ↥(henselOverDecomp k Ω K A) :=
    res_comp_symm_self e _
  let C₁ : CategoryTheory.Abelian.Ext R₂₁
        (SSGRoute.PTExt.unitsK ↥(decompField k Ω A) ↥(henselOverDecomp k Ω K A)) 1 ≃+
      CategoryTheory.Abelian.Ext R₂₁ (Rep.res e.symm.toMonoidHom (Rep.res e.toMonoidHom
        (SSGRoute.PTExt.unitsK ↥(decompField k Ω A) ↥(henselOverDecomp k Ω K A)))) 1 :=
    Eq.mp (congrArg (fun S => CategoryTheory.Abelian.Ext R₂₁
        (SSGRoute.PTExt.unitsK ↥(decompField k Ω A) ↥(henselOverDecomp k Ω K A)) 1 ≃+
        CategoryTheory.Abelian.Ext R₂₁ S 1) hY.symm) (AddEquiv.refl _)
  let C₂ : CategoryTheory.Abelian.Ext R₂₂
        (SSGRoute.PTExt.unitsK ↥(decompField k Ω A) ↥(henselOverDecomp k Ω K A)) 1 ≃+
      CategoryTheory.Abelian.Ext R₂₂ (Rep.res e.symm.toMonoidHom (Rep.res e.toMonoidHom
        (SSGRoute.PTExt.unitsK ↥(decompField k Ω A) ↥(henselOverDecomp k Ω K A)))) 1 :=
    Eq.mp (congrArg (fun S => CategoryTheory.Abelian.Ext R₂₂
        (SSGRoute.PTExt.unitsK ↥(decompField k Ω A) ↥(henselOverDecomp k Ω K A)) 1 ≃+
        CategoryTheory.Abelian.Ext R₂₂ S 1) hY.symm) (AddEquiv.refl _)
  -- ## the eight naturality squares
  -- (1) the `H1loc` subgroup transport
  have hsq₁ : ∀ y : Work.SSGRoute.H1loc p k Ω K E₁ (SSGRoute.decomp k A),
      (h1locSubgroupEqEquiv p E₂ hfix.symm) (F y)
        = k₁ ((h1locSubgroupEqEquiv p E₁ hfix.symm) y) := by
    intro y
    obtain ⟨b, hb, hby⟩ := Work.SSGRoute.toClass_surjective p k Ω K E₁ (SSGRoute.decomp k A) y
    rw [← hby]
    obtain ⟨hb1, hb2⟩ := hb
    rw [hF1 b hb1 hb2]
    have hb1' : SSGRoute.IsCocycleOn (SSGRoute.res k K)
        ((decompField k Ω A).fixingSubgroup) b := by
      rw [hfix]; exact hb1
    have hb2' : SSGRoute.IsLocConstOn ((decompField k Ω A).fixingSubgroup) b := by
      rw [hfix]; exact hb2
    rw [h1locSubgroupEqEquiv_toClass p E₂ hfix.symm (fun g => f (b g)),
      h1locSubgroupEqEquiv_toClass p E₁ hfix.symm b]
    exact (hk₁₁ b hb1' hb2').symm
  -- (2) the model bridge at the fixing subgroup
  have hsq₂ : ∀ y : Work.SSGRoute.H1loc p k Ω K E₁ ((decompField k Ω A).fixingSubgroup),
      (Work.SSGRoute.H1locEquivH1 p k Ω K E₂ ((decompField k Ω A).fixingSubgroup)
        (fun h m => rfl)) (k₁ y)
        = k₂ ((Work.SSGRoute.H1locEquivH1 p k Ω K E₁ ((decompField k Ω A).fixingSubgroup)
            (fun h m => rfl)) y) :=
    fun y => hk₁₂ y
  -- (3) the canonical coefficient transport `Φd = e1aCoeffNat`
  have hsq₃ : ∀ y : Work.AbsoluteKummer.H1 ↥((decompField k Ω A).fixingSubgroup) E₁,
      (Work.SSGRoute.H1Equiv.h1AddEquiv
        (G := ↥((decompField k Ω A).fixingSubgroup))
        (Work.SSGRoute.ExtChain.e1aCoeffNat p k Ω K ζ hζ hζK T hT E₂)
        (fun σ e => Work.SSGRoute.ExtChain.e1aCoeffNat_equivariant p k Ω K ζ hζ hζK T hT E₂
          (σ : Ω ≃ₐ[k] Ω) e)
        (fun σ n => Work.SSGRoute.ExtChain.e1aCoeffNat_symm_equivariant p k Ω K ζ hζ hζK T hT E₂
          (σ : Ω ≃ₐ[k] Ω) n)) (k₂ y)
        = k₃ ((Work.SSGRoute.H1Equiv.h1AddEquiv
            (G := ↥((decompField k Ω A).fixingSubgroup))
            (Work.SSGRoute.ExtChain.e1aCoeffNat p k Ω K ζ hζ hζK T hT E₁)
            (fun σ e => Work.SSGRoute.ExtChain.e1aCoeffNat_equivariant p k Ω K ζ hζ hζK T hT E₁
              (σ : Ω ≃ₐ[k] Ω) e)
            (fun σ n => Work.SSGRoute.ExtChain.e1aCoeffNat_symm_equivariant p k Ω K ζ hζ hζK T hT E₁
              (σ : Ω ≃ₐ[k] Ω) n)) y) :=
    fun y => Work.SSGRoute.E1aClean.h1AddEquiv_natural
      (G := ↥((decompField k Ω A).fixingSubgroup))
      (Ψ₁ := Work.SSGRoute.ExtChain.e1aCoeffNat p k Ω K ζ hζ hζK T hT E₁)
      (hΨ₁ := fun σ e => Work.SSGRoute.ExtChain.e1aCoeffNat_equivariant p k Ω K ζ hζ hζK T hT E₁
        (σ : Ω ≃ₐ[k] Ω) e)
      (hΨ₁' := fun σ n =>
        Work.SSGRoute.ExtChain.e1aCoeffNat_symm_equivariant p k Ω K ζ hζ hζK T hT E₁
          (σ : Ω ≃ₐ[k] Ω) n)
      (Ψ₂ := Work.SSGRoute.ExtChain.e1aCoeffNat p k Ω K ζ hζ hζK T hT E₂)
      (hΨ₂ := fun σ e => Work.SSGRoute.ExtChain.e1aCoeffNat_equivariant p k Ω K ζ hζ hζK T hT E₂
        (σ : Ω ≃ₐ[k] Ω) e)
      (hΨ₂' := fun σ n =>
        Work.SSGRoute.ExtChain.e1aCoeffNat_symm_equivariant p k Ω K ζ hζ hζK T hT E₂
          (σ : Ω ≃ₐ[k] Ω) n)
      (f := f.toAddMonoidHom)
      (g := Work.SSGRoute.precompAddHom (Rep.Hom.hom F').toAddMonoidHom)
      (hf := hfH') (hg := hgT)
      (h := fun e => e1aCoeffNat_natural p k Ω K ζ hζ hζK T hT E₁ E₂ f hf F' hF' e) y
  -- (4) the level-change transfer
  have hsq₄ : ∀ y : Work.AbsoluteKummer.H1 ↥((decompField k Ω A).fixingSubgroup)
        (Work.SSGRoute.homCoind k Ω K X₁),
      (levelChangeTransferD p k Ω K A X₂ (levelTwoGroupHom k Ω K A hA q hAq e) hφres) (k₃ y)
        = k₄ ((levelChangeTransferD p k Ω K A X₁
            (levelTwoGroupHom k Ω K A hA q hAq e) hφres) y) :=
    fun y => levelChangeTransferD_natural p k Ω K A X₂ X₁ (levelTwoGroupHom k Ω K A hA q hAq e)
      hφres F' hgT hgB y
  -- (5) the `E1c` dictionary at the henselian level
  have hsq₅ : ∀ y : Work.AbsoluteKummer.H1 (Ω ≃ₐ[↥(decompField k Ω A)] Ω)
        (Work.SSGRoute.homCoind ↥(decompField k Ω A) Ω (henselOverDecomp k Ω K A) R₂₁),
      (Work.SSGRoute.ExtChain.E1cGeneric.e1cEquiv (k := ↥(decompField k Ω A)) (Ω := Ω)
        (K := henselOverDecomp k Ω K A) R₂₂).symm (k₄ y)
        = (CategoryTheory.Abelian.Ext.mk₀ gR).comp
            ((Work.SSGRoute.ExtChain.E1cGeneric.e1cEquiv (k := ↥(decompField k Ω A)) (Ω := Ω)
              (K := henselOverDecomp k Ω K A) R₂₁).symm y) (zero_add 1) :=
    fun y => e1cEquiv_symm_mapH1 (k := ↥(decompField k Ω A)) (Ω := Ω)
      (K := henselOverDecomp k Ω K A) R₂₂ R₂₁ gR hgB y
  -- (6) the `Eq.mp`-transport of the unit representation
  have hsq₆ : ∀ z : CategoryTheory.Abelian.Ext R₂₁
        (SSGRoute.PTExt.unitsK ↥(decompField k Ω A) ↥(henselOverDecomp k Ω K A)) 1,
      C₂ ((CategoryTheory.Abelian.Ext.mk₀ gR).comp z (zero_add 1))
        = (CategoryTheory.Abelian.Ext.mk₀ gR).comp (C₁ z) (zero_add 1) :=
    fun z => eq_mp_congrArg_refl_comp (X₁ := R₂₁) (X₂ := R₂₂) hY.symm gR z
  -- (7) the explicit `res`-functoriality on `Ext¹`
  have hsq₇ : ∀ z : CategoryTheory.Abelian.Ext R₂₁ (Rep.res e.symm.toMonoidHom
        (Rep.res e.toMonoidHom
          (SSGRoute.PTExt.unitsK ↥(decompField k Ω A) ↥(henselOverDecomp k Ω K A)))) 1,
      A6₂ ((CategoryTheory.Abelian.Ext.mk₀ gR).comp z (zero_add 1))
        = (CategoryTheory.Abelian.Ext.mk₀ F'').comp (A6₁ z) (zero_add 1) :=
    fun z => extResEquivExplicit_natural e XD₁ XD₂ _ F'' z
  -- (8) the push along `θ`
  have hsq₈ : ∀ z : CategoryTheory.Abelian.Ext XD₁ (Rep.res e.toMonoidHom
        (SSGRoute.PTExt.unitsK ↥(decompField k Ω A) ↥(henselOverDecomp k Ω K A))) 1,
      A7₂ ((CategoryTheory.Abelian.Ext.mk₀ F'').comp z (zero_add 1))
        = (CategoryTheory.Abelian.Ext.mk₀ F'').comp (A7₁ z) (zero_add 1) :=
    fun z => (ext_mk₀_comp_postcomp F'' θ z).symm
  -- ## the chain chase
  unfold Work.SSGRoute.E1aClean.phiCan
  simp only [AddEquiv.trans_apply]
  rw [hsq₁, hsq₂, hsq₃, hsq₄, hsq₅, hsq₆, hsq₇, hsq₈]

end Work.SSGRoute.PT.E1aFinBox

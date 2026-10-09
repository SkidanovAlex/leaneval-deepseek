import Mathlib
import Submission.Work.SSGRoute.E1aClean.globalDictionaryCanonDefs
import Submission.Work.SSGRoute.ExtChain.ChainGamma
import Submission.Work.SSGRoute.ExtChain.FreeCover
import Submission.Work.SSGRoute.ArchDictionary_aux.psiEMap_sub_betaRaw_mem_range
import Submission.Work.SSGRoute.ArchDictionary_aux.phi_sq_signs
import Submission.Work.SSGRoute.ArchDictionary_aux.place_localField_equiv_real_of_decompK_eq_bot
import Submission.Work.SSGRoute.PT.e1a_localComparison_bricks
import Submission.Work.SSGRoute.ArchDictionary_aux.SettingLemmas
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END


namespace Work.SSGRoute.ArchSplit2

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

/-- **(A2) The comparison square at a split real place, in sign form** (abstract in `ell`: only its
realization rule `hell` is used).

`p = 2`; `c` is a nontrivial involution of `Gal(Ω/k)` with the seam
`hlink : ∀ x, φ (c x) = conj (φ x)`, and `w = mk (φ|_K)`; `hbot : decompK w = ⊥` (so `res k K c = 1`
and `K_w = ℝ`).  For a global locally constant `1`-cocycle `b` and `m` in the dual of `E ⊗ T`, the
`w`-component of the canonical global class `extLoc w (extToIdeles (globalDictionaryCanon … b))` has
lift·2 functional vanishing exactly when the `⟨c⟩`-component `e1aCoeffNat … (b c) m` vanishes.

This is the "sign" computation of `ssg_arch2_2320.md` (a): take the primitive `y` of the global class
and write `y = liftOf c̃ · Φ̃`; then `c (w_v) = w_v · e1aCoeffNat … (b c) (coverMap v)`, so `φ (w_v)`
is real (resp. purely imaginary) according as the sign is `+1` (resp. `−1`), and a purely imaginary
square is negative.  Route: `extLoc_extToIdeles_eq`, `ExtChain.extRes_PhiE`,
`psiEMap_sub_betaRaw_mem_range`, `liftOf_spec`, `res_eq_one_of_decompK_eq_bot`, `phi_sq_signs`, with
`S := Rep.res (decompK w).subtype` of the E1c sequence and `eS := Iso.refl`; conclude with A1's
verification `hell` at that presentation.

File: `Submission/Work/SSGRoute/ArchSplit2/archSplit2_square_sign.lean`; namespace
`Work.SSGRoute.ArchSplit2`; imports as in A1's file. -/
theorem archSplit2_square_sign (p : ℕ) [Fact p.Prime] (hp : p = 2) (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (φ : Ω →+* ℂ)
    (hlink : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
    (w : NK.GlobalCFT.Place ↥K)
    (hw : w = NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk (φ.comp (algebraMap ↥K Ω))))
    (hbot : SSGRoute.PTExt.decompK (k := k) w = ⊥)
    (ell : CategoryTheory.Abelian.Ext
          (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
            (SSGRoute.PTExt.modRep (K ≃ₐ[k] K) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))))
          (SSGRoute.PTExt.localUnitsK (k := k) w) 1 →+
        Work.SSGRoute.DualMod p (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)))
    (hell : ∀ (S : CategoryTheory.ShortComplex (Rep.{0} SSGRoute.PTExt.Coeff ↥(SSGRoute.PTExt.decompK (k := k) w)))
          (hS : S.ShortExact)
          (eS : S.X₃ ≅ Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
            (SSGRoute.PTExt.modRep (K ≃ₐ[k] K) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))))
          (ψ : S.X₁ ⟶ SSGRoute.PTExt.localUnitsK (k := k) w) (v : S.X₂.V)
          (m : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)),
          Rep.Hom.hom eS.hom (Rep.Hom.hom S.g v) = m →
          (ell ((CategoryTheory.Abelian.Ext.mk₀ eS.inv).comp
              (hS.extClass.comp (CategoryTheory.Abelian.Ext.mk₀ ψ) (add_zero 1)) (zero_add 1)) m = 0 ↔
            ∃ (r : S.X₁.V) (u : (SSGRoute.PTExt.localUnitsK (k := k) w).V),
              Rep.Hom.hom S.f r = p • v ∧ p • u = Rep.Hom.hom ψ r))
    (b : (Ω ≃ₐ[k] Ω) → E)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b) (hl : SSGRoute.IsLocConstOn ⊤ b)
    (m : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)) :
    ell (SSGRoute.PTExt.extLoc (k := k) w (SSGRoute.PTExt.extToIdeles (k := k)
        (Work.SSGRoute.E1aClean.globalDictionaryCanon p k Ω K ζ hζ hζK T hT E b))) m = 0 ↔
      Work.SSGRoute.ExtChain.e1aCoeffNat p k Ω K ζ hζ hζK T hT E (b c) m = 0 := by
  classical
  subst hp
  haveI hTfin : Finite T := Work.SSGRoute.ExtChain.e1aFiniteT 2 k Ω K ζ T hT
  let E' : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) :=
    SSGRoute.PTExt.modRep (K ≃ₐ[k] K) (Work.SSGRoute.DualMod 2 (TensorProduct (ZMod 2) E T))
  let D : Subgroup (K ≃ₐ[k] K) := SSGRoute.PTExt.decompK (k := k) w
  have hGfin : Fintype (K ≃ₐ[k] K) := Fintype.ofFinite _
  have hDfin : Fintype ↥D := Fintype.ofFinite _
  -- the global canonical class
  set z : CategoryTheory.Abelian.Ext E' (SSGRoute.PTExt.unitsK k K) 1 :=
    Work.SSGRoute.E1aClean.globalDictionaryCanon 2 k Ω K ζ hζ hζK T hT E b with hz
  -- a primitive of `z`
  obtain ⟨y, hy⟩ :=
    Work.SSGRoute.ExtChain.E1cGeneric.PhiE_surjective (k := k) (Ω := Ω) (K := K) E' z
  -- the local presentation of the restriction
  let S₀ : CategoryTheory.ShortComplex (Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) :=
    Work.SSGRoute.freeCoverSES E'
  have hS₀ : S₀.ShortExact := Work.SSGRoute.freeCoverSES_shortExact E'
  let S : CategoryTheory.ShortComplex (Rep.{0} SSGRoute.PTExt.Coeff ↥D) :=
    (Work.SSGRoute.freeCoverSES E').map (Rep.resFunctor (k := SSGRoute.PTExt.Coeff) D.subtype)
  have hS : S.ShortExact := (Work.SSGRoute.freeCoverSES_shortExact E').map_of_exact _
  -- the local primitive
  let ψ : S.X₁ ⟶ SSGRoute.PTExt.localUnitsK (k := k) w :=
    (CategoryTheory.Abelian.Ext.addEquiv₀ (SSGRoute.PTExt.extRes D.subtype y)) ≫
      NK.HassePrinciple.unitsToLocalUnits k ↥K w
  -- the lift of `m` along the cover
  let v : S.X₂.V :=
    Finsupp.single (m : E'.V) (MonoidAlgebra.single (1 : K ≃ₐ[k] K) (1 : SSGRoute.PTExt.Coeff))
  have hv : Rep.Hom.hom S.g v = m := by
    rw [show S.g = Rep.resMap D.subtype (Work.SSGRoute.freeCover E') from rfl]
    change ConcreteCategory.hom (Work.SSGRoute.freeCover E') v = m
    exact Work.SSGRoute.freeCover_apply_single E' (m : E'.V)
  -- (1) the class identification
  have hclass : (CategoryTheory.Abelian.Ext.mk₀ (CategoryTheory.Iso.refl S.X₃).inv).comp
        (hS.extClass.comp (CategoryTheory.Abelian.Ext.mk₀ ψ) (add_zero 1)) (zero_add 1)
      = SSGRoute.PTExt.extLoc (k := k) w (SSGRoute.PTExt.extToIdeles (k := k) z) := by
    have hβ : hS.extClass.comp (CategoryTheory.Abelian.Ext.mk₀ ψ) (add_zero 1)
        = SSGRoute.PTExt.extLoc (k := k) w (SSGRoute.PTExt.extToIdeles (k := k) z) := by
      -- the global presentation and its connecting class
      haveI : Fintype (K ≃ₐ[k] K) := hGfin
      -- `mk₀ ψ` is the coefficient change of the primitive
      have hψ : (CategoryTheory.Abelian.Ext.mk₀ ψ)
          = (SSGRoute.PTExt.extRes D.subtype y).comp
              (CategoryTheory.Abelian.Ext.mk₀ (NK.HassePrinciple.unitsToLocalUnits k ↥K w))
              (zero_add 0) := by
        show CategoryTheory.Abelian.Ext.mk₀
            ((CategoryTheory.Abelian.Ext.addEquiv₀ (SSGRoute.PTExt.extRes D.subtype y)) ≫
              NK.HassePrinciple.unitsToLocalUnits k ↥K w)
          = (SSGRoute.PTExt.extRes D.subtype y).comp
              (CategoryTheory.Abelian.Ext.mk₀ (NK.HassePrinciple.unitsToLocalUnits k ↥K w))
              (zero_add 0)
        exact (CategoryTheory.Abelian.Ext.mk₀_comp_mk₀ _ _).symm.trans
          (congrArg (fun ξ => ξ.comp
              (CategoryTheory.Abelian.Ext.mk₀ (NK.HassePrinciple.unitsToLocalUnits k ↥K w))
              (zero_add 0))
            (CategoryTheory.Abelian.Ext.mk₀_addEquiv₀_apply
              (SSGRoute.PTExt.extRes D.subtype y)))
      -- `z` is the connecting class of the primitive
      have hz0 : z
          = hS₀.extClass.comp y (add_zero 1) := by
        rw [← hy]
        rfl
      -- the restricted connecting class
      have hSe : hS.extClass
          = CategoryTheory.Abelian.Ext.mapExactFunctor
              (Rep.resFunctor (k := SSGRoute.PTExt.Coeff) D.subtype)
              hS₀.extClass :=
        (CategoryTheory.Abelian.Ext.mapExactFunctor_extClass
          (Rep.resFunctor (k := SSGRoute.PTExt.Coeff) D.subtype) hS₀).symm
      -- the restricted class is the class of the restricted primitive
      have hres : SSGRoute.PTExt.extRes D.subtype z
          = hS.extClass.comp (SSGRoute.PTExt.extRes D.subtype y) (add_zero 1) := by
        show (Rep.resFunctor (k := SSGRoute.PTExt.Coeff) D.subtype).mapExtAddHom E'
              (SSGRoute.PTExt.unitsK k K) 1 z
            = hS.extClass.comp
                ((Rep.resFunctor (k := SSGRoute.PTExt.Coeff) D.subtype).mapExtAddHom
                  (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 E') (SSGRoute.PTExt.unitsK k K) 0 y)
                (add_zero 1)
        rw [hz0, Functor.mapExtAddHom_apply,
          CategoryTheory.Abelian.Ext.mapExactFunctor_comp]
        refine congrArg (fun ξ : CategoryTheory.Abelian.Ext S.X₃ S.X₁ 1 => ξ.comp
          ((Rep.resFunctor (k := SSGRoute.PTExt.Coeff) D.subtype).mapExtAddHom
            (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 E') (SSGRoute.PTExt.unitsK k K) 0 y)
          (add_zero 1)) hSe.symm
      have h1 : hS.extClass.comp (CategoryTheory.Abelian.Ext.mk₀ ψ) (add_zero 1)
          = hS.extClass.comp
              ((SSGRoute.PTExt.extRes D.subtype y).comp
                (CategoryTheory.Abelian.Ext.mk₀ (NK.HassePrinciple.unitsToLocalUnits k ↥K w))
                (zero_add 0)) (add_zero 1) :=
            congrArg (fun ξ : CategoryTheory.Abelian.Ext S.X₁
                (SSGRoute.PTExt.localUnitsK (k := k) w) 0 =>
                hS.extClass.comp ξ (add_zero 1)) hψ
      have h2 : hS.extClass.comp
              ((SSGRoute.PTExt.extRes D.subtype y).comp
                (CategoryTheory.Abelian.Ext.mk₀ (NK.HassePrinciple.unitsToLocalUnits k ↥K w))
                (zero_add 0)) (add_zero 1)
          = (hS.extClass.comp (SSGRoute.PTExt.extRes D.subtype y) (add_zero 1)).comp
                (CategoryTheory.Abelian.Ext.mk₀ (NK.HassePrinciple.unitsToLocalUnits k ↥K w))
                (add_zero 1) :=
            (CategoryTheory.Abelian.Ext.comp_assoc hS.extClass
                (SSGRoute.PTExt.extRes D.subtype y)
                (CategoryTheory.Abelian.Ext.mk₀ (NK.HassePrinciple.unitsToLocalUnits k ↥K w))
                (add_zero 1) (zero_add 0) (add_zero 1)).symm
      have h3 : (hS.extClass.comp (SSGRoute.PTExt.extRes D.subtype y) (add_zero 1)).comp
                (CategoryTheory.Abelian.Ext.mk₀ (NK.HassePrinciple.unitsToLocalUnits k ↥K w))
                (add_zero 1)
          = (SSGRoute.PTExt.extRes D.subtype z).comp
                (CategoryTheory.Abelian.Ext.mk₀ (NK.HassePrinciple.unitsToLocalUnits k ↥K w))
                (add_zero 1) :=
            congrArg (fun ξ : CategoryTheory.Abelian.Ext S.X₃
                  (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype (SSGRoute.PTExt.unitsK k K)) 1 =>
                ξ.comp
                (CategoryTheory.Abelian.Ext.mk₀ (NK.HassePrinciple.unitsToLocalUnits k ↥K w))
                (add_zero 1)) hres.symm
      have h4 : (SSGRoute.PTExt.extRes D.subtype z).comp
                (CategoryTheory.Abelian.Ext.mk₀ (NK.HassePrinciple.unitsToLocalUnits k ↥K w))
                (add_zero 1)
          = SSGRoute.PTExt.extLoc (k := k) w (SSGRoute.PTExt.extToIdeles (k := k) z) :=
            (Work.SSGRoute.SSGStage.extLoc_extToIdeles_eq w z).symm
      exact h1.trans (h2.trans (h3.trans h4))
    exact (CategoryTheory.Abelian.Ext.mk₀_id_comp
      (hS.extClass.comp (CategoryTheory.Abelian.Ext.mk₀ ψ) (add_zero 1))).trans hβ
  -- (2) the lift·2 functional vs the coefficient
  have hfinal : (∃ (r : S.X₁.V) (u : (SSGRoute.PTExt.localUnitsK (k := k) w).V),
        Rep.Hom.hom S.f r = 2 • v ∧ 2 • u = Rep.Hom.hom ψ r)
      ↔ Work.SSGRoute.ExtChain.e1aCoeffNat 2 k Ω K ζ hζ hζK T hT E (b c) m = 0 := by
    classical
    letI : DistribMulAction (Ω ≃ₐ[k] Ω) E := DistribMulAction.compHom E (SSGRoute.res k K)
    haveI hE'fin : Finite (E' : Type) := by
      change Finite (Work.SSGRoute.DualMod 2 (TensorProduct (ZMod 2) E T))
      exact Work.SSGRoute.PT.finite_dualMod_tensor 2 E T
    haveI hE'finZ : Module.Finite ℤ (E' : Type) := Module.Finite.of_finite
    -- `res k K c = 1`
    have hbotφ : SSGRoute.PTExt.decompK (k := k)
        (NK.GlobalCFT.Place.ofInfinite
          (NumberField.InfinitePlace.mk (φ.comp (algebraMap ↥K Ω)))) = ⊥ := by
      rw [← hw]; exact hbot
    have hres1 : SSGRoute.res k K c = 1 :=
      Work.SSGRoute.ArchDictionary.res_eq_one_of_decompK_eq_bot (k := k) (K := K)
        c hc2 hc1 φ hlink hbotφ
    -- the coefficient identification and the cocycle representing the E1c class
    let Φd := Work.SSGRoute.ExtChain.e1aCoeffNat 2 k Ω K ζ hζ hζK T hT E
    have hΦd : Work.GroupCohomology.IsEquivariant (Ω ≃ₐ[k] Ω) Φd.toAddMonoidHom :=
      fun σ e => Work.SSGRoute.ExtChain.e1aCoeffNat_equivariant 2 k Ω K ζ hζ hζK T hT E σ e
    have hΦd' : Work.GroupCohomology.IsEquivariant (Ω ≃ₐ[k] Ω) Φd.symm.toAddMonoidHom :=
      fun σ n => Work.SSGRoute.ExtChain.e1aCoeffNat_symm_equivariant 2 k Ω K ζ hζ hζK T hT E σ n
    have hbZ : b ∈ Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) E :=
      Work.SSGRoute.mem_absZ1_of_isCocycleOn_isLocConstOn (SSGRoute.res k K) hb hl
    let cf : Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K E') :=
      Work.AbsoluteKummer.mapZ1 Φd.toAddMonoidHom hΦd ⟨b, hbZ⟩
    have hcf : Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K E') cf
        = Work.SSGRoute.ExtChain.E1cGeneric.e1cMap E' z := by
      have hcls : Work.SSGRoute.ExtChain.E1cGeneric.e1cMap E' z
          = (Work.SSGRoute.H1Equiv.h1AddEquiv Φd hΦd hΦd')
              (Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) E ⟨b, hbZ⟩) := by
        rw [hz]
        dsimp only [Work.SSGRoute.E1aClean.globalDictionaryCanon,
          Work.SSGRoute.E1aClean.globalDictEquivCanon]
        rw [dif_pos hbZ, AddEquiv.trans_apply]
        change (Work.SSGRoute.ExtChain.E1cGeneric.e1cEquiv E')
            ((Work.SSGRoute.ExtChain.E1cGeneric.e1cEquiv E').symm
              ((Work.SSGRoute.H1Equiv.h1AddEquiv Φd hΦd hΦd')
                (Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) E ⟨b, hbZ⟩)))
          = (Work.SSGRoute.H1Equiv.h1AddEquiv Φd hΦd hΦd')
              (Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) E ⟨b, hbZ⟩)
        exact AddEquiv.apply_symm_apply _ _
      have hmap : (Work.SSGRoute.H1Equiv.h1AddEquiv Φd hΦd hΦd')
            (Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) E ⟨b, hbZ⟩)
          = Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K E') cf :=
        (Work.AbsoluteKummer.mapH1_H1π Φd.toAddMonoidHom hΦd ⟨b, hbZ⟩)
      exact (hcls.trans hmap).symm
    -- the primitive decomposition of `y` along the canonical cover
    have hmem : (Work.SSGRoute.ExtChain.E1cGeneric.PsiEMap
            (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 E') y
          - Work.SSGRoute.ExtChain.E1cGeneric.betaRaw E' cf)
        ∈ (Work.SSGRoute.ExtChain.E1cGeneric.piH0 E').range :=
      Work.SSGRoute.ArchDictionary_aux.psiEMap_sub_betaRaw_mem_range
        (k := k) (Ω := Ω) (K := K) (R := E') (z := z) (y := y) (hy := hy)
        (cf := cf) (hcf := hcf)
    obtain ⟨Φ₀, hΦ₀⟩ := hmem
    have hpt : ∀ r : (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 E').V,
        ((Work.SSGRoute.ExtChain.E1cGeneric.PsiEMap
            (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 E') y :
            Work.SSGRoute.homCoind k Ω K (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 E')))
            r
          = Work.SSGRoute.ExtChain.E1cGeneric.liftOf E' cf
              (Work.SSGRoute.ExtChain.E1cGeneric.kappa E' r)
            + (Φ₀ : Work.SSGRoute.ExtChain.E1cGeneric.E1cN E')
                (Work.SSGRoute.ExtChain.E1cGeneric.kappa E' r) := by
      intro r
      have h5 : ((Work.SSGRoute.ExtChain.E1cGeneric.PsiEMap
              (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 E') y :
              Work.SSGRoute.homCoind k Ω K (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 E')))
            r
          = ((Work.SSGRoute.ExtChain.E1cGeneric.betaRaw E' cf :
              Work.SSGRoute.homCoind k Ω K (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 E')))
              r
            + ((Work.SSGRoute.ExtChain.E1cGeneric.piH0 E' Φ₀ :
                Work.SSGRoute.homCoind k Ω K
                  (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 E'))) r := by
        have h := congrArg (fun z : ↥(Work.AbsoluteKummer.H0 (Ω ≃ₐ[k] Ω)
              (Work.SSGRoute.homCoind k Ω K
                (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 E'))) =>
              (z : Work.SSGRoute.homCoind k Ω K
                (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 E')) r) hΦ₀
        rw [AddSubgroup.coe_sub, AddMonoidHom.sub_apply] at h
        rw [h]
        abel
      have hb_r : ((Work.SSGRoute.ExtChain.E1cGeneric.betaRaw E' cf :
            Work.SSGRoute.homCoind k Ω K (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 E'))) r
          = Work.SSGRoute.ExtChain.E1cGeneric.liftOf E' cf
              (Work.SSGRoute.ExtChain.E1cGeneric.kappa E' r) := by
        rw [show (Work.SSGRoute.ExtChain.E1cGeneric.betaRaw E' cf :
              Work.SSGRoute.homCoind k Ω K (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 E'))
              = Work.SSGRoute.ExtChain.E1cGeneric.piH E'
                  (Work.SSGRoute.ExtChain.E1cGeneric.liftOf E' cf) from rfl]
        rw [Work.SSGRoute.ExtChain.E1cGeneric.piH_apply]
        rfl
      have hp_r : ((Work.SSGRoute.ExtChain.E1cGeneric.piH0 E' Φ₀ :
            Work.SSGRoute.homCoind k Ω K (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 E'))) r
          = (Φ₀ : Work.SSGRoute.ExtChain.E1cGeneric.E1cN E')
              (Work.SSGRoute.ExtChain.E1cGeneric.kappa E' r) := by
        rw [show (Work.SSGRoute.ExtChain.E1cGeneric.piH0 E' Φ₀ :
              Work.SSGRoute.homCoind k Ω K (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 E'))
              = Work.SSGRoute.ExtChain.E1cGeneric.piH E'
                  (Φ₀ : Work.SSGRoute.ExtChain.E1cGeneric.E1cN E') from rfl]
        rw [Work.SSGRoute.ExtChain.E1cGeneric.piH_apply]
        rfl
      rw [h5, hb_r, hp_r]
    -- the value of the cocycle at `c`
    have hcfc : ((cf : Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω)
            (Work.SSGRoute.homCoind k Ω K E')) :
        (Ω ≃ₐ[k] Ω) → Work.SSGRoute.homCoind k Ω K E') c = Φd (b c) := by
      show (Work.AbsoluteKummer.mapZ1 Φd.toAddMonoidHom hΦd ⟨b, hbZ⟩ :
        (Ω ≃ₐ[k] Ω) → Work.SSGRoute.homCoind k Ω K E') c = Φd (b c)
      rw [Work.AbsoluteKummer.mapZ1_apply]
      rfl
    -- the action of `c` on the chosen lift `liftOf cf`
    have hLc : ∀ x : (Work.SSGRoute.ExtChain.E1cGeneric.E1cF E').V,
        c • (Work.SSGRoute.ExtChain.E1cGeneric.liftOf E' cf x)
          = Work.SSGRoute.ExtChain.E1cGeneric.liftOf E' cf x
            + ((cf : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.homCoind k Ω K E') c)
                (Work.SSGRoute.ExtChain.E1cGeneric.coverMap E' x) := by
      intro x
      have h := congrFun (Work.SSGRoute.ExtChain.E1cGeneric.liftOf_spec E' cf) c
      rw [Work.GroupCohomology.d0_apply, Work.AbsoluteKummer.mapZ1_apply,
        Work.SSGRoute.ExtChain.E1cGeneric.iotaH_apply] at h
      have h3 := congrArg
        (fun (f : Work.SSGRoute.ExtChain.E1cGeneric.E1cN E') => f x) h
      rw [AddMonoidHom.sub_apply, Work.SSGRoute.homCoind.smul_apply] at h3
      rw [hres1] at h3
      simp only [map_one, inv_one, Module.End.one_apply] at h3
      rw [AddMonoidHom.comp_apply] at h3
      exact sub_eq_iff_eq_add'.mp h3
    -- the invariance of `Φ₀`
    have hΦc : ∀ x : (Work.SSGRoute.ExtChain.E1cGeneric.E1cF E').V,
        c • ((Φ₀ : Work.SSGRoute.ExtChain.E1cGeneric.E1cN E') x)
          = (Φ₀ : Work.SSGRoute.ExtChain.E1cGeneric.E1cN E') x := by
      intro x
      have h := congrArg
        (fun (f : Work.SSGRoute.ExtChain.E1cGeneric.E1cN E') => f x) (Φ₀.2 c)
      rw [Work.SSGRoute.homCoind.smul_apply] at h
      rw [hres1] at h
      simp only [map_one, inv_one, Module.End.one_apply] at h
      exact h
    -- the underlying coefficient homomorphism `Y₀ = addEquiv₀ y`
    let Y₀ : (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 E') ⟶ SSGRoute.PTExt.unitsK k K :=
      CategoryTheory.Abelian.Ext.addEquiv₀ y
    have hY : ∀ r : (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 E').V,
        ((Work.SSGRoute.ExtChain.E1cGeneric.PsiEMap
            (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 E') y :
            Work.SSGRoute.homCoind k Ω K (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 E'))) r
          = Additive.ofMul (Units.map (algebraMap ↥K Ω).toMonoidWithZeroHom
              (Additive.toMul (Rep.Hom.hom Y₀ r)) : Ωˣ) := by
      intro r
      rw [Work.SSGRoute.ExtChain.E1cGeneric.PsiEMap_apply_toCoindH0]
      exact Work.SSGRoute.toCoindH0_apply
        (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 E') Y₀ r
    -- the element of the syzygy whose image in `F` is `2 • v`
    have hm2 : (2 : ℕ) • m = 0 := by
      have h : ((2 : ℕ) : ZMod 2) = 0 := ZMod.natCast_self 2
      rw [← Nat.cast_smul_eq_nsmul (ZMod 2) 2 m, h, zero_smul]
    let vv : (Work.SSGRoute.ExtChain.E1cGeneric.E1cF E').V := v
    have hvfree : Rep.Hom.hom (Work.SSGRoute.freeCover E') vv = m := by
      have h := hv
      rw [show S.g = Rep.resMap D.subtype (Work.SSGRoute.freeCover E') from rfl] at h
      change Rep.Hom.hom (Work.SSGRoute.freeCover E') vv = m at h
      exact h
    have h2v : Rep.Hom.hom (Work.SSGRoute.freeCover E') ((2 : ℕ) • vv) = 0 := by
      have h1 : Rep.Hom.hom (Work.SSGRoute.freeCover E') ((2 : ℕ) • vv)
          = (2 : ℕ) • Rep.Hom.hom (Work.SSGRoute.freeCover E') vv :=
        map_nsmul (Rep.Hom.hom (Work.SSGRoute.freeCover E')) 2 vv
      rw [h1, hvfree]
      exact hm2
    have hgpt : (Rep.freeLift (k := SSGRoute.PTExt.Coeff) (G := K ≃ₐ[k] K)
          (A := Work.SSGRoute.ExtChain.E1cGeneric.E1cF E')
          (fun _ : PUnit => (2 : ℕ) • vv)) ≫ Work.SSGRoute.freeCover E' = 0 := by
      refine Rep.free_ext (k := SSGRoute.PTExt.Coeff) (G := K ≃ₐ[k] K) (α := PUnit)
        (A := E') _ 0 ?_
      intro x
      rw [Rep.comp_apply]
      simp only [Rep.freeLift, ConcreteCategory.hom_ofHom,
        Representation.freeLift_single_single]
      simpa using h2v
    let g₀ : Rep.free SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) PUnit ⟶
        Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 E' :=
      Limits.kernel.lift (Work.SSGRoute.freeCover E')
        (Rep.freeLift (k := SSGRoute.PTExt.Coeff) (G := K ≃ₐ[k] K)
          (A := Work.SSGRoute.ExtChain.E1cGeneric.E1cF E')
          (fun _ : PUnit => (2 : ℕ) • vv)) hgpt
    let r₀ : (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 E').V :=
      (Rep.Hom.hom g₀)
        (Finsupp.single PUnit.unit (MonoidAlgebra.single (1 : K ≃ₐ[k] K)
          (1 : SSGRoute.PTExt.Coeff)))
    have hκr₀ : Work.SSGRoute.ExtChain.E1cGeneric.kappa E' r₀ = (2 : ℕ) • vv := by
      have h := congrArg (fun (m : Rep.free SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) PUnit ⟶
            Work.SSGRoute.ExtChain.E1cGeneric.E1cF E') =>
          (Rep.Hom.hom m) (Finsupp.single PUnit.unit (MonoidAlgebra.single
            (1 : K ≃ₐ[k] K) (1 : SSGRoute.PTExt.Coeff))))
        (Limits.kernel.lift_ι (Work.SSGRoute.freeCover E')
          (Rep.freeLift (k := SSGRoute.PTExt.Coeff) (G := K ≃ₐ[k] K)
            (A := Work.SSGRoute.ExtChain.E1cGeneric.E1cF E')
            (fun _ : PUnit => (2 : ℕ) • vv)) hgpt)
      rw [Rep.comp_apply] at h
      show Work.SSGRoute.ExtChain.E1cGeneric.kappa E' r₀ = (2 : ℕ) • vv
      rw [show Work.SSGRoute.ExtChain.E1cGeneric.kappa E' r₀
          = (Rep.Hom.hom (CategoryTheory.Limits.kernel.ι (Work.SSGRoute.freeCover E'))) r₀
            from rfl, h]
      simp only [Rep.freeLift, ConcreteCategory.hom_ofHom,
        Representation.freeLift_single_single]
      simp
    have hκinj : Function.Injective (Work.SSGRoute.ExtChain.E1cGeneric.kappa E') := by
      haveI : CategoryTheory.Mono
          (CategoryTheory.Limits.kernel.ι (Work.SSGRoute.freeCover E')) := inferInstance
      have h : Function.Injective
          (Rep.Hom.hom (CategoryTheory.Limits.kernel.ι (Work.SSGRoute.freeCover E'))) :=
        (Rep.mono_iff_injective _).mp inferInstance
      intro a b hab
      exact h hab
    -- the action of `c` on the value `W v := liftOf cf v + Φ₀ v`
    have hWv : c • ((Work.SSGRoute.ExtChain.E1cGeneric.liftOf E' cf v)
          + ((Φ₀ : Work.SSGRoute.ExtChain.E1cGeneric.E1cN E') v))
        = ((Work.SSGRoute.ExtChain.E1cGeneric.liftOf E' cf v)
            + ((Φ₀ : Work.SSGRoute.ExtChain.E1cGeneric.E1cN E') v))
          + (((cf : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.homCoind k Ω K E') c)
              (Work.SSGRoute.ExtChain.E1cGeneric.coverMap E' v)) := by
      rw [smul_add, hLc v, hΦc v]
      abel
    -- `Ψ(y)(r₀) = 2 • (liftOf cf v + Φ₀ v)`
    have hB : ((Work.SSGRoute.ExtChain.E1cGeneric.PsiEMap
            (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 E') y :
            Work.SSGRoute.homCoind k Ω K (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 E'))) r₀
        = (2 : ℕ) • ((Work.SSGRoute.ExtChain.E1cGeneric.liftOf E' cf v)
            + ((Φ₀ : Work.SSGRoute.ExtChain.E1cGeneric.E1cN E') v)) := by
      rw [hpt r₀, hκr₀, map_nsmul, map_nsmul, two_nsmul, two_nsmul, two_nsmul]
      abel
    -- the value `z := toMul (liftOf cf v + Φ₀ v)`
    let Wv : Additive Ωˣ :=
      (Work.SSGRoute.ExtChain.E1cGeneric.liftOf E' cf) v
        + ((Φ₀ : Work.SSGRoute.ExtChain.E1cGeneric.E1cN E') v)
    let Y' : (NK.GlobalCFT.Place.localField ↥K w)ˣ :=
      Units.map (algebraMap ↥K (NK.GlobalCFT.Place.localField ↥K w)).toMonoidHom
        (Additive.toMul (α := (↥K)ˣ) (Rep.Hom.hom Y₀ r₀))
    let z : Ω := ((Additive.toMul Wv : Ωˣ) : Ω)
    have hz_ne : z ≠ 0 := Units.ne_zero (Additive.toMul Wv)
    -- `(cf c)(coverMap v) = e1aCoeffNat … (b c) m`
    have hz0 : ((cf : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.homCoind k Ω K E') c)
        (Work.SSGRoute.ExtChain.E1cGeneric.coverMap E' v)
        = Work.SSGRoute.ExtChain.e1aCoeffNat 2 k Ω K ζ hζ hζK T hT E (b c) m := by
      rw [hcfc, show Work.SSGRoute.ExtChain.E1cGeneric.coverMap E' v = m from hvfree]
    -- the multiplicative relation defining `z`
    have hzsq : (Units.map (algebraMap ↥K Ω).toMonoidWithZeroHom
          (Additive.toMul (α := (↥K)ˣ) (Rep.Hom.hom Y₀ r₀)) : Ωˣ)
        = Additive.toMul Wv * Additive.toMul Wv := by
      have h := congrArg Additive.toMul ((hY r₀).symm.trans hB)
      rw [two_nsmul, toMul_add, toMul_ofMul] at h
      simpa only [Wv, ← pow_two] using h
    -- the `c`-action on `z`
    have hcz : c z = z * (((Additive.toMul (((cf : (Ω ≃ₐ[k] Ω) →
        Work.SSGRoute.homCoind k Ω K E') c)
          (Work.SSGRoute.ExtChain.E1cGeneric.coverMap E' v)) : Ωˣ)) : Ω) := by
      have h := congrArg (fun u : Ωˣ => (u : Ω)) (congrArg Additive.toMul hWv)
      rw [Work.SSGRoute.addUnits_smul_toMulΩ] at h
      nth_rewrite 2 [toMul_add] at h
      rw [Units.val_mul] at h
      simpa only [Work.SSGRoute.algEquivUnitsMapΩ_coe, z, Wv] using h
    -- the value of the local primitive
    have hψval : Rep.Hom.hom ψ r₀ = Additive.ofMul Y' := by
      have h0 : CategoryTheory.Abelian.Ext.addEquiv₀ (SSGRoute.PTExt.extRes D.subtype y)
          = Rep.resMap D.subtype Y₀ := by
        rw [show SSGRoute.PTExt.extRes D.subtype y
            = (Rep.resFunctor D.subtype).mapExtAddHom _ _ 0 y from rfl,
          show y = CategoryTheory.Abelian.Ext.mk₀ (CategoryTheory.Abelian.Ext.addEquiv₀ y)
            from (CategoryTheory.Abelian.Ext.mk₀_addEquiv₀_apply y).symm,
          Functor.mapExtAddHom_apply, CategoryTheory.Abelian.Ext.mapExactFunctor_mk₀]
        rw [show CategoryTheory.Abelian.Ext.mk₀
              (Rep.resMap D.subtype (CategoryTheory.Abelian.Ext.addEquiv₀ y))
            = (CategoryTheory.Abelian.Ext.addEquiv₀).symm
                (Rep.resMap D.subtype (CategoryTheory.Abelian.Ext.addEquiv₀ y)) from rfl,
          AddEquiv.apply_symm_apply]
      rw [show ψ = (CategoryTheory.Abelian.Ext.addEquiv₀
            (SSGRoute.PTExt.extRes D.subtype y))
          ≫ NK.HassePrinciple.unitsToLocalUnits k ↥K w from rfl, h0]
      change Rep.Hom.hom (NK.HassePrinciple.unitsToLocalUnits k ↥K w)
          (Additive.ofMul (Additive.toMul (α := (↥K)ˣ) (Rep.Hom.hom (Rep.resMap D.subtype Y₀) r₀)))
        = Additive.ofMul Y'
      rw [NK.HassePrinciple.unitsToLocalUnits_apply]
      rfl
    -- the lift·2 condition is the square condition at `r₀`
    have hLHS : (∃ (r : (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 E').V)
          (u : (SSGRoute.PTExt.localUnitsK (k := k) w).V),
          Rep.Hom.hom S.f r = 2 • v ∧ 2 • u = Rep.Hom.hom ψ r)
        ↔ ∃ u : (SSGRoute.PTExt.localUnitsK (k := k) w).V,
            2 • u = Rep.Hom.hom ψ r₀ := by
      constructor
      · rintro ⟨r, u, hr, hu⟩
        have hr' : Work.SSGRoute.ExtChain.E1cGeneric.kappa E' r = (2 : ℕ) • vv := by
          have h := hr
          rw [show S.f = Rep.resMap D.subtype
                (CategoryTheory.Limits.kernel.ι (Work.SSGRoute.freeCover E')) from rfl] at h
          change Rep.Hom.hom (CategoryTheory.Limits.kernel.ι
              (Work.SSGRoute.freeCover E')) r = (2 : ℕ) • vv at h
          exact h
        have hrr : r = r₀ := hκinj (by rw [hr', hκr₀])
        subst hrr
        exact ⟨u, hu⟩
      · rintro ⟨u, hu⟩
        exact ⟨r₀, u, hκr₀, hu⟩
    have hcong : (∃ u : (SSGRoute.PTExt.localUnitsK (k := k) w).V,
          2 • u = Rep.Hom.hom ψ r₀)
        ↔ ∃ u : (SSGRoute.PTExt.localUnitsK (k := k) w).V,
            2 • u = Additive.ofMul Y' := by
      constructor
      · rintro ⟨u, hu⟩
        exact ⟨u, by rw [← hψval]; exact hu⟩
      · rintro ⟨u, hu⟩
        exact ⟨u, by rw [hψval]; exact hu⟩
    -- turn the `Additive`-valued equation into a square equation
    have hsq : (∃ u : (SSGRoute.PTExt.localUnitsK (k := k) w).V,
          2 • u = Additive.ofMul Y')
        ↔ ∃ u : (NK.GlobalCFT.Place.localField ↥K w)ˣ, u ^ 2 = Y' := by
      constructor
      · rintro ⟨u, hu⟩
        refine ⟨Additive.toMul u, ?_⟩
        show Additive.toMul (2 • u) = Y'
        exact congrArg Additive.toMul hu
      · rintro ⟨u, hu⟩
        refine ⟨Additive.ofMul u, ?_⟩
        show Additive.ofMul (u ^ 2) = Additive.ofMul Y'
        exact congrArg Additive.ofMul hu
    -- transport the squares along the real-place identification
    obtain ⟨e, he⟩ := Work.SSGRoute.ArchDictionary_aux.place_localField_equiv_real_of_decompK_eq_bot
      (p := 2) k Ω K c hc2 hc1 φ hlink w hw hbot
    have hZ : ((e (Y' : NK.GlobalCFT.Place.localField ↥K w) : ℝ) : ℂ) = φ z ^ 2 := by
      have h1 : (Y' : NK.GlobalCFT.Place.localField ↥K w)
          = algebraMap ↥K (NK.GlobalCFT.Place.localField ↥K w)
              (Additive.toMul (α := (↥K)ˣ) (Rep.Hom.hom Y₀ r₀)) := rfl
      rw [h1, he (Additive.toMul (α := (↥K)ˣ) (Rep.Hom.hom Y₀ r₀))]
      have h2 : (algebraMap ↥K Ω (Additive.toMul (α := (↥K)ˣ) (Rep.Hom.hom Y₀ r₀)))
          = ((Additive.toMul Wv * Additive.toMul Wv : Ωˣ) : Ω) := by
        rw [← hzsq]
        rfl
      rw [h2, Units.val_mul, map_mul, pow_two]
    have hstar : (∃ u : (NK.GlobalCFT.Place.localField ↥K w)ˣ, u ^ 2 = Y')
        ↔ ∃ u : ℝˣ, ((u : ℝ) : ℂ) ^ 2 = φ z ^ 2 := by
      constructor
      · rintro ⟨u, hu⟩
        refine ⟨Units.map e.toMonoidWithZeroHom u, ?_⟩
        have h := congrArg (fun uu : (NK.GlobalCFT.Place.localField ↥K w)ˣ =>
          e (uu : NK.GlobalCFT.Place.localField ↥K w)) hu
        simp only [Units.val_pow_eq_pow_val, map_pow] at h
        rw [← hZ, ← Complex.ofReal_pow]
        rw [show ((Units.map e.toMonoidWithZeroHom u : ℝˣ) : ℝ)
            = e (u : NK.GlobalCFT.Place.localField ↥K w) from Units.coe_map _ _]
        exact congrArg (fun r : ℝ => (r : ℂ)) h
      · rintro ⟨u, hu⟩
        refine ⟨Units.map e.symm.toMonoidWithZeroHom u, ?_⟩
        have h : (u : ℝ) ^ 2 = e (Y' : NK.GlobalCFT.Place.localField ↥K w) := by
          rw [← Complex.ofReal_pow] at hu
          rw [← hZ] at hu
          exact Complex.ofReal_injective hu
        have h2 : e ((Units.map e.symm.toMonoidWithZeroHom u :
            (NK.GlobalCFT.Place.localField ↥K w)ˣ) :
            NK.GlobalCFT.Place.localField ↥K w) = (u : ℝ) := by
          rw [Units.coe_map]
          exact e.apply_symm_apply u
        apply Units.ext
        apply e.injective
        rw [Units.val_pow_eq_pow_val, map_pow, h2, h]
    -- the sign computation
    have hsigned : (∃ u : (NK.GlobalCFT.Place.localField ↥K w)ˣ, u ^ 2 = Y')
        ↔ Work.SSGRoute.ExtChain.e1aCoeffNat 2 k Ω K ζ hζ hζK T hT E (b c) m = 0 := by
      rw [hstar]
      obtain ⟨hreal, himag⟩ := Work.SSGRoute.ArchDictionary_aux.phi_sq_signs φ c hlink
      constructor
      · rintro ⟨u, hu⟩
        by_contra hne
        have hz0ne : ((Additive.toMul (α := Ωˣ) (((cf : (Ω ≃ₐ[k] Ω) →
            Work.SSGRoute.homCoind k Ω K E') c)
              (Work.SSGRoute.ExtChain.E1cGeneric.coverMap E' v)) : Ωˣ) : Ω) ≠ 1 := by
          intro h1
          apply hne
          rw [← hz0]
          apply Additive.ofMul.injective
          exact Units.ext h1
        have h2 : (2 : ℕ) • (((cf : (Ω ≃ₐ[k] Ω) →
            Work.SSGRoute.homCoind k Ω K E') c)
              (Work.SSGRoute.ExtChain.E1cGeneric.coverMap E' v)) = 0 := by
          have h5 : (2 : ℕ) • (Work.SSGRoute.ExtChain.e1aCoeffNat 2 k Ω K ζ hζ hζK T hT E (b c) m)
              = 0 := by
            rw [show (2 : ℕ) • (Work.SSGRoute.ExtChain.e1aCoeffNat 2 k Ω K ζ hζ hζK T hT E (b c) m)
                = Work.SSGRoute.ExtChain.e1aCoeffNat 2 k Ω K ζ hζ hζK T hT E (b c)
                    ((2 : ℕ) • m) from (map_nsmul _ 2 m).symm, hm2]
            exact map_zero _
          rwa [← hz0] at h5
        have h3 : ((Additive.toMul (α := Ωˣ) (((cf : (Ω ≃ₐ[k] Ω) →
            Work.SSGRoute.homCoind k Ω K E') c)
              (Work.SSGRoute.ExtChain.E1cGeneric.coverMap E' v)) : Ωˣ) : Ω) ^ 2 = 1 := by
          have h := congrArg (fun u : Ωˣ => (u : Ω)) (congrArg Additive.toMul h2)
          rw [two_nsmul, toMul_add, toMul_zero] at h
          rw [pow_two]
          exact h
        have h4 : ((Additive.toMul (α := Ωˣ) (((cf : (Ω ≃ₐ[k] Ω) →
            Work.SSGRoute.homCoind k Ω K E') c)
              (Work.SSGRoute.ExtChain.E1cGeneric.coverMap E' v)) : Ωˣ) : Ω) = -1 := by
          rcases sq_eq_one_iff.mp h3 with h | h
          · exact absurd h hz0ne
          · exact h
        exact himag z (by rw [hcz, h4]; ring_nf) hz_ne ⟨u, hu⟩
      · intro h0
        have hz0zero : ((cf : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.homCoind k Ω K E') c)
            (Work.SSGRoute.ExtChain.E1cGeneric.coverMap E' v) = 0 := by
          rw [hz0, h0]
        have h4 : ((Additive.toMul (α := Ωˣ) (((cf : (Ω ≃ₐ[k] Ω) →
            Work.SSGRoute.homCoind k Ω K E') c)
              (Work.SSGRoute.ExtChain.E1cGeneric.coverMap E' v)) : Ωˣ) : Ω) = 1 := by
          rw [hz0zero, toMul_zero]
          simp
        exact hreal z (by rw [hcz, h4, mul_one]) hz_ne

    exact hLHS.trans (hcong.trans (hsq.trans hsigned))
  have hiff := hell S hS (CategoryTheory.Iso.refl S.X₃) ψ v m hv
  have h1 : ell (SSGRoute.PTExt.extLoc (k := k) w (SSGRoute.PTExt.extToIdeles (k := k) z)) m = 0
      ↔ ell ((CategoryTheory.Abelian.Ext.mk₀ (CategoryTheory.Iso.refl S.X₃).inv).comp
            (hS.extClass.comp (CategoryTheory.Abelian.Ext.mk₀ ψ) (add_zero 1))
            (zero_add 1)) m = 0 := by
    rw [← hclass]
  exact (h1.trans hiff).trans hfinal

end Work.SSGRoute.ArchSplit2

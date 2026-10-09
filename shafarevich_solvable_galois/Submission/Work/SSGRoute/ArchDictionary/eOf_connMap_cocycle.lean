import Mathlib
import Submission.Work.SSGRoute.ArchDictionary.extOneDictNaturalH1
import Submission.Work.SSGRoute.eCoh_delta
import Submission.Work.SSGRoute.LeadArch2.gammaHom_H1pi_eq_eCoh_or_neg
import Submission.Work.SSGRoute.eCoh_map
import Submission.Work.SSGRoute.exists_e_zero_natural
import Submission.Work.SSGRoute.ArchDictionary.extOneDictNatural
import Submission.Work.SSGRoute.ArchDictionary.eCohZeroInvSign
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! Guidance from the project lead (the requester):

Lead design archp2_1008. READ Submission/_lead_design/archp2_1008/ARCHP2_PLAN.md (and .lean). The old localCoeffP2/archPhiDef route can NEVER satisfy the comparison square: see the D_4 model in ARCHP2_model.lean (decide). This route uses Phi := ArchSeamP2.archPhiOf and Psi := seamCoeffLoc (the seam-push of e1aCoeffNat), from the installed module Submission.Work.SSGRoute.ArchDictionary.archSeamDefs. The statement is lead-checked and elaborates. Copy any helper you need from the plan .lean; do not import _lead_design. No native_decide; never write maxHeartbeats 0.
-/

namespace Work.SSGRoute.ArchDictionary

open CategoryTheory CategoryTheory.Limits SSGRoute.PTExt Work.SSGRoute.ArchDictionary

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000
set_option backward.defeqAttrib.useBackward true

private lemma eOf_unfold {G : Type} [Group G] (N : Rep.{0} Coeff G) (hInj : Module.Injective Coeff N.V)
    (X : ∀ M : Rep.{0} Coeff G, Rep.{0} Coeff (⊥ : Subgroup G))
    (hX : ∀ M, Nonempty (homRep (Rep.free Coeff G M.V) N ≅
      Rep.coind (⊥ : Subgroup G).subtype (X M)))
    (M : Rep.{0} Coeff G) (a : Abelian.Ext (NatH1.pres M).X₁ N 0) :
    NatH1.eOf N hInj X hX M (CokerNat.connMap (SSGRoute.ses_shortExact M) N a)
      = (NatH1.gammaIso N M).symm (CokerNat.connMapCov (NatH1.dpres_shortExact N hInj M)
          (unitRep G) (NatH1.cEq N M a)) := by

    haveI : Subsingleton (Abelian.Ext (unitRep G) (NatH1.dpres N M).X₂ 1) :=
      ext_one_homRepFree_subsingleton G M.V N (X M) (hX M)
    show (NatH1.gammaIso N M).symm ((NatH1.e2 N hInj M).symm
      (NatH1.cmp N M (NatH1.e1 N M (CokerNat.connMap (SSGRoute.ses_shortExact M) N a)))) = _
    rw [show NatH1.e1 N M (CokerNat.connMap (SSGRoute.ses_shortExact M) N a)
        = (QuotientAddGroup.mk' (CokerNat.preMap (NatH1.pres M) N).range) a from
      CokerNat.cokerIso_apply_connMap (SSGRoute.ses_shortExact M) N a]
    rw [show NatH1.cmp N M ((QuotientAddGroup.mk' (CokerNat.preMap (NatH1.pres M) N).range) a)
        = (QuotientAddGroup.mk' (CokerNat.postMap (NatH1.dpres N M) (unitRep G)).range)
            (NatH1.cEq N M a) from NatH1.cHom_mk' N M a]
    exact congrArg (NatH1.gammaIso N M).symm
      (CokerNat.cokerIsoCov_symm_mk (NatH1.dpres_shortExact N hInj M) (unitRep G)
        (NatH1.cEq N M a))

private lemma psi_mem_Z1 {G : Type} [Group G] (N : Rep.{0} Coeff G) (M : Rep.{0} Coeff G) (atil : (Rep.free Coeff G M.V).V →+ N.V)
    (ψ : G → (M.V →ₗ[Coeff] N.V))
    (hψ : ∀ g f, ψ g (Rep.Hom.hom (freeCover M) f)
      = N.ρ g (atil ((Rep.free Coeff G M.V).ρ g⁻¹ f)) - atil f) :
    ψ ∈ @Work.GroupCohomology.Z1 G (M.V →ₗ[Coeff] N.V) _ _ (homRepDistribMulAction M N) := by

    rw [Work.GroupCohomology.mem_Z1_iff]
    intro g h
    ext m
    obtain ⟨f, rfl⟩ : ∃ f, Rep.Hom.hom (freeCover M) f = m :=
      ⟨Finsupp.single m (MonoidAlgebra.single 1 1), Work.SSGRoute.freeCover_apply_single_gen M m⟩
    rw [LinearMap.add_apply,
      Work.SSGRoute.homRep_smul_apply M N g (ψ h) (Rep.Hom.hom (freeCover M) f),
      ← Rep.hom_comm_apply (freeCover M) g⁻¹ f]
    rw [hψ h ((Rep.free Coeff G M.V).ρ g⁻¹ f), hψ g f, hψ (g * h) f]
    rw [mul_inv_rev, map_sub]
    rw [map_mul (N.ρ) g h, show N.ρ g * N.ρ h = (N.ρ g).comp (N.ρ h) from rfl,
      LinearMap.comp_apply]
    rw [map_mul (Rep.free Coeff G M.V).ρ h⁻¹ g⁻¹,
      show (Rep.free Coeff G M.V).ρ h⁻¹ * (Rep.free Coeff G M.V).ρ g⁻¹
        = ((Rep.free Coeff G M.V).ρ h⁻¹).comp ((Rep.free Coeff G M.V).ρ g⁻¹) from rfl,
      LinearMap.comp_apply]
    abel

private lemma gammaIso_apply {G : Type} [Group G] (N M : Rep.{0} Coeff G) (y : homH1 G M N) :
    (NatH1.gammaIso N M) y
      = Work.SSGRoute.ExtH1.gammaHom G (M.V →ₗ[Coeff] N.V)
          (Work.SSGRoute.augSES_shortExact G) y := rfl

set_option maxHeartbeats 12000000 in
private lemma key {G : Type} [Group G] (N : Rep.{0} Coeff G) (hInj : Module.Injective Coeff N.V)
    (M : Rep.{0} Coeff G) (a : Abelian.Ext (NatH1.pres M).X₁ N 0)
    (atil : (Rep.free Coeff G M.V).V →+ N.V)
    (hatil : ∀ r, atil (Rep.Hom.hom (Limits.kernel.ι (freeCover M)) r)
      = Rep.Hom.hom (Abelian.Ext.addEquiv₀ a) r)
    (ψ : G → (M.V →ₗ[Coeff] N.V))
    (hψ : ∀ g f, ψ g (Rep.Hom.hom (freeCover M) f)
      = N.ρ g (atil ((Rep.free Coeff G M.V).ρ g⁻¹ f)) - atil f)
    (hzZ : ψ ∈ @Work.GroupCohomology.Z1 G (M.V →ₗ[Coeff] N.V) _ _ (homRepDistribMulAction M N)) :
    (NatH1.gammaIso N M) (Work.GroupCohomology.H1π G (M.V →ₗ[Coeff] N.V) ⟨ψ, hzZ⟩)
        = CokerNat.connMapCov (NatH1.dpres_shortExact N hInj M) (unitRep G) (NatH1.cEq N M a) ∨
      (NatH1.gammaIso N M) (Work.GroupCohomology.H1π G (M.V →ₗ[Coeff] N.V) ⟨ψ, hzZ⟩)
        = -CokerNat.connMapCov (NatH1.dpres_shortExact N hInj M) (unitRep G)
            (NatH1.cEq N M a) := by
  let P : ShortComplex (Rep.{0} Coeff G) := NatH1.dpres N M
  have hP : P.ShortExact := NatH1.dpres_shortExact N hInj M
  let φc : unitRep G ⟶ P.X₃ :=
    (Work.SSGRoute.unitHomEquiv (NatH1.pres M).X₁ N).symm (Abelian.Ext.addEquiv₀ a)
  let x₀ := Work.SSGRoute.eZeroToInv G P.X₃ φc
  have hx₀ : ∀ r : ↥(Limits.kernel (freeCover M)),
      (show ↥(Limits.kernel (freeCover M)) →ₗ[Coeff] ↥N from (x₀ : ↥P.X₃)) r
        = (Rep.Hom.hom (Abelian.Ext.addEquiv₀ a)) r := by
    intro r
    change (show ↥(Limits.kernel (freeCover M)) →ₗ[Coeff] ↥N from
        (Rep.Hom.hom φc) (1 : Coeff)) r = (Rep.Hom.hom (Abelian.Ext.addEquiv₀ a)) r
    rw [← AddEquiv.apply_symm_apply (Work.SSGRoute.unitHomEquiv (NatH1.pres M).X₁ N)
      (Abelian.Ext.addEquiv₀ a)]
    exact (Work.SSGRoute.unitHomEquiv_apply (NatH1.pres M).X₁ N φc r).symm
  -- the additive lift `atil`, linearised
  let atilₗ : (Rep.free Coeff G M.V).V →ₗ[Coeff] N.V :=
    { toFun := fun f => atil f
      map_add' := fun f f' => atil.map_add f f'
      map_smul' := fun c f => by
        obtain ⟨z⟩ := c
        simp only [RingHom.id_apply]
        rw [show (ULift.up z : Coeff) = ((z : ℤ) : Coeff) from rfl]
        rw [Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
        exact atil.map_zsmul z f }
  let ιₗ : ↥(Limits.kernel (freeCover M)) →ₗ[Coeff] (Rep.free Coeff G M.V).V :=
    { toFun := fun r => Rep.Hom.hom (Limits.kernel.ι (freeCover M)) r
      map_add' := fun a b => Work.SSGRoute.inter_add _ _ (Limits.kernel.ι (freeCover M)) a b
      map_smul' := fun c a => by
        obtain ⟨z⟩ := c
        simp only [RingHom.id_apply]
        rw [show (ULift.up z : Coeff) = ((z : ℤ) : Coeff) from rfl,
          Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
        exact Work.SSGRoute.inter_zsmul _ _ (Limits.kernel.ι (freeCover M)) z a }
  have hι : (Rep.Hom.hom P.g) atilₗ = atilₗ.comp ιₗ := by
    apply LinearMap.ext
    intro r
    rw [show (show ↥(Limits.kernel (freeCover M)) →ₗ[Coeff] ↥N from
          (Rep.Hom.hom P.g) atilₗ) r
        = (show (Rep.free Coeff G M.V).V →ₗ[Coeff] ↥N from atilₗ)
            ((Rep.Hom.hom (Limits.kernel.ι (freeCover M))) r) from
      Work.SSGRoute.homRepPre_apply (NatH1.pres M).X₂ (NatH1.pres M).X₁ N (NatH1.pres M).f
        atilₗ r]
    rfl
  have hy₂ : (Rep.Hom.hom P.g) atilₗ = (x₀ : ↥P.X₃) := by
    rw [hι]
    apply LinearMap.ext
    intro r
    rw [LinearMap.comp_apply, hx₀ r]
    change atil (Rep.Hom.hom (Limits.kernel.ι (freeCover M)) r)
      = (Rep.Hom.hom (Abelian.Ext.addEquiv₀ a)) r
    exact hatil r
  have hx : ⇑(Rep.Hom.hom P.f) ∘ (ψ : G → ↑P.X₁)
      = (ConcreteCategory.hom (groupCohomology.d₀₁ P.X₂)) atilₗ := by
    funext g
    rw [Function.comp_apply, groupCohomology.d₀₁_hom_apply]
    apply LinearMap.ext
    intro f
    rw [LinearMap.sub_apply]
    have hL : (show (Rep.free Coeff G M.V).V →ₗ[Coeff] ↥N from
          (Rep.Hom.hom P.f) (ψ g)) f
        = (ψ g) (Rep.Hom.hom (freeCover M) f) :=
      Work.SSGRoute.homRepPre_apply (NatH1.pres M).X₃ (NatH1.pres M).X₂ N (NatH1.pres M).g
        (ψ g) f
    have hR : (show (Rep.free Coeff G M.V).V →ₗ[Coeff] ↥N from (P.X₂.ρ g) atilₗ) f
        = (N.ρ g) (atil (((Rep.free Coeff G M.V).ρ g⁻¹) f)) := by
      rw [Work.SSGRoute.homRep_rho_apply]
      rfl
    rw [hL, hR]
    exact hψ g f
  have hδ := groupCohomology.δ₀_apply (X := P) hP x₀ atilₗ hy₂ (ψ : G → ↑P.X₁) hx
  -- #### Step 4: assemble
  have hψc : (ψ : G → (M.V →ₗ[Coeff] N.V))
      ∈ groupCohomology.cocycles₁ (modRep G (M.V →ₗ[Coeff] N.V)) :=
    groupCohomology.mem_cocycles₁_of_comp_eq_d₀₁ hP hx
  have hE0 : SSGRoute.PTExt.eCoh 0 G P.X₃ ((groupCohomology.H0Iso P.X₃).inv x₀)
        = Abelian.Ext.mk₀ φc ∨
      SSGRoute.PTExt.eCoh 0 G P.X₃ ((groupCohomology.H0Iso P.X₃).inv x₀)
        = -Abelian.Ext.mk₀ φc :=
    eCohZeroInvSign P.X₃ φc
  have hcEq : NatH1.cEq N M a = Abelian.Ext.mk₀ φc := by
    show (Work.SSGRoute.unitHomExtEquiv (NatH1.pres M).X₁ N).symm a = Abelian.Ext.mk₀ φc
    rw [show a = Abelian.Ext.mk₀ (Abelian.Ext.addEquiv₀ a) from
      Work.SSGRoute.ext_eq_mk₀_addEquiv₀ a]
    exact Work.SSGRoute.unitHomExtEquiv_symm_mk₀ (NatH1.pres M).X₁ N
      (Abelian.Ext.addEquiv₀ a)
  have hE1 := Work.SSGRoute.eCoh_delta 0 G P hP ((groupCohomology.H0Iso P.X₃).inv x₀)
  rw [hδ] at hE1
  have hZ : SSGRoute.PTExt.eCoh 1 G P.X₁
        ((groupCohomology.H1π P.X₁) ⟨(ψ : G → ↑P.X₁),
          groupCohomology.mem_cocycles₁_of_comp_eq_d₀₁ hP hx⟩)
      = CokerNat.connMapCov hP (unitRep G) (NatH1.cEq N M a) ∨
      SSGRoute.PTExt.eCoh 1 G P.X₁
        ((groupCohomology.H1π P.X₁) ⟨(ψ : G → ↑P.X₁),
          groupCohomology.mem_cocycles₁_of_comp_eq_d₀₁ hP hx⟩)
      = -CokerNat.connMapCov hP (unitRep G) (NatH1.cEq N M a) := by
    rcases hE0 with hE0 | hE0 <;> rcases hE1 with hE1 | hE1
    · left
      rw [hE1, hE0, ← hcEq]
      exact (CokerNat.connMapCov_apply hP (unitRep G) (NatH1.cEq N M a)).symm
    · right
      rw [hE1, hE0, ← hcEq]
      exact congrArg Neg.neg (CokerNat.connMapCov_apply hP (unitRep G) (NatH1.cEq N M a)).symm
    · right
      rw [hE1, hE0, ← hcEq, Abelian.Ext.neg_comp]
      exact congrArg Neg.neg (CokerNat.connMapCov_apply hP (unitRep G) (NatH1.cEq N M a)).symm
    · left
      rw [hE1, hE0, ← hcEq, Abelian.Ext.neg_comp, neg_neg]
      exact (CokerNat.connMapCov_apply hP (unitRep G) (NatH1.cEq N M a)).symm
  -- the class of `ψ` in the two realisations, with the `modRep` spelling of the coefficient
  let Ψ : ↥(Work.GroupCohomology.Z1 G (M.V →ₗ[Coeff] N.V)) := ⟨ψ, hzZ⟩
  have hZc : SSGRoute.PTExt.eCoh 1 G (modRep G (M.V →ₗ[Coeff] N.V))
        ((groupCohomology.H1π (modRep G (M.V →ₗ[Coeff] N.V)))
          ⟨(Ψ : G → (M.V →ₗ[Coeff] N.V)), hψc⟩)
      = CokerNat.connMapCov hP (unitRep G) (NatH1.cEq N M a) ∨
      SSGRoute.PTExt.eCoh 1 G (modRep G (M.V →ₗ[Coeff] N.V))
        ((groupCohomology.H1π (modRep G (M.V →ₗ[Coeff] N.V)))
          ⟨(Ψ : G → (M.V →ₗ[Coeff] N.V)), hψc⟩)
      = -CokerNat.connMapCov hP (unitRep G) (NatH1.cEq N M a) := hZ
  -- `B1`: the two degree-one bridges agree up to sign
  have hB1 := Work.SSGRoute.LeadArch2.gammaHom_H1pi_eq_eCoh_or_neg (G := G)
    (M := (M.V →ₗ[Coeff] N.V)) Ψ hψc
  -- combine
  have hkey : (NatH1.gammaIso N M) (Work.GroupCohomology.H1π G (M.V →ₗ[Coeff] N.V) ⟨ψ, hzZ⟩)
      = CokerNat.connMapCov hP (unitRep G) (NatH1.cEq N M a) ∨
      (NatH1.gammaIso N M) (Work.GroupCohomology.H1π G (M.V →ₗ[Coeff] N.V) ⟨ψ, hzZ⟩)
      = -CokerNat.connMapCov hP (unitRep G) (NatH1.cEq N M a) := by
    rcases hB1 with hB1 | hB1 <;> rcases hZc with hZc | hZc
    · left
      rw [gammaIso_apply N M, hB1, hZc]
    · right
      rw [gammaIso_apply N M, hB1, hZc]
    · right
      rw [gammaIso_apply N M, hB1, hZc]
    · left
      rw [gammaIso_apply N M, hB1, hZc, neg_neg]
  exact hkey

theorem eOf_connMap_cocycle {G : Type} [Group G]
    (N : Rep.{0} Coeff G) (hInj : Module.Injective Coeff N.V)
    (X : ∀ M : Rep.{0} Coeff G, Rep.{0} Coeff (⊥ : Subgroup G))
    (hX : ∀ M, Nonempty (homRep (Rep.free Coeff G M.V) N ≅
      Rep.coind (⊥ : Subgroup G).subtype (X M)))
    (M : Rep.{0} Coeff G) (a : Abelian.Ext (NatH1.pres M).X₁ N 0)
    (atil : (Rep.free Coeff G M.V).V →+ N.V)
    (hatil : ∀ r, atil (Rep.Hom.hom (Limits.kernel.ι (freeCover M)) r)
      = Rep.Hom.hom (Abelian.Ext.addEquiv₀ a) r)
    (ψ : G → (M.V →ₗ[Coeff] N.V))
    (hψ : ∀ g f, ψ g (Rep.Hom.hom (freeCover M) f)
      = N.ρ g (atil ((Rep.free Coeff G M.V).ρ g⁻¹ f)) - atil f) :
    ∃ hz : ψ ∈ @Work.GroupCohomology.Z1 G (M.V →ₗ[Coeff] N.V) _ _ (homRepDistribMulAction M N),
      NatH1.eOf N hInj X hX M (CokerNat.connMap (SSGRoute.ses_shortExact M) N a)
          = @Work.GroupCohomology.H1π G (M.V →ₗ[Coeff] N.V) _ _ (homRepDistribMulAction M N)
              ⟨ψ, hz⟩ ∨
        NatH1.eOf N hInj X hX M (CokerNat.connMap (SSGRoute.ses_shortExact M) N a)
          = -@Work.GroupCohomology.H1π G (M.V →ₗ[Coeff] N.V) _ _ (homRepDistribMulAction M N)
              ⟨ψ, hz⟩ := by
  classical
  obtain hzZ := psi_mem_Z1 N M atil ψ hψ
  refine ⟨hzZ, ?_⟩
  rw [eOf_unfold N hInj X hX M a]
  rcases key N hInj M a atil hatil ψ hψ hzZ with hk | hk
  · left
    rw [AddEquiv.symm_apply_eq]
    exact hk.symm
  · right
    rw [AddEquiv.symm_apply_eq, map_neg]
    exact (neg_neg _).symm.trans (congrArg Neg.neg hk).symm

end Work.SSGRoute.ArchDictionary

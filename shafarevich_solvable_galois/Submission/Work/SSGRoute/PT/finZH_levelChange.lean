import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.PT.finHalfData
import Submission.Work.SSGRoute.baseChangeDefs
import Submission.Work.SSGRoute.extHMap_gammaHom_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PT

set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped TensorProduct
open SSGRoute.PTExt CategoryTheory

section RepAux

variable {G H : Type} [Group G] [Group H]

lemma finZH_lc_resMap_hom_apply {X Y : Rep.{0} Coeff G} (f : H →* G) (p : X ⟶ Y) (x : X.V) :
    (Rep.Hom.hom (Rep.resMap f p)) x = (Rep.Hom.hom p) x := rfl

lemma finZH_lc_eqToHom_res_hom_self (f₁ f₂ : H →* G) (X : Rep.{0} Coeff G)
    (h : Rep.res f₁ X = Rep.res f₂ X) (x : (Rep.res f₁ X).V) :
    (Rep.Hom.hom (eqToHom h)) x = x := by
  rw [Work.SSGRoute.Y3Test.eqToHom_hom_eq_self h x rfl (Subsingleton.elim _ _)]

/-- v4.35 port helper: `eqToHom` between two `modRep` structures on the same carrier is the
identity on elements (stated on the common carrier, so no carrier unification is needed). -/
lemma finZH_lc_eqToHom_modRep_self {M : Type} [AddCommGroup M] {i₁ i₂ : DistribMulAction G M}
    (h : @SSGRoute.PTExt.modRep G M _ _ i₁ = @SSGRoute.PTExt.modRep G M _ _ i₂) (m : M) :
    (Rep.Hom.hom (eqToHom h)) m = m := by
  rw [Work.SSGRoute.Y3Test.eqToHom_hom_eq_self h m rfl (Subsingleton.elim _ _)]

end RepAux

/-- **Level change of the local class `finZH`.**  For `K ≤ L ≤ L'` with places of `L`, `L'` under
the same finite place `A` of `Ω`, the class `finZH` at the upper level is the transport (along the
place-glue comparison `PT.finZF_eq`) of the local inflation of the class at the lower level, along
the restriction `ρ` of decomposition groups.  These are the level-`L` and level-`L'` classes
`[b]_L = ExtH1.gammaHom (H1π (fun σ ↦ b₀ σ))` of the factorised cocycle. -/
theorem finZH_levelChange {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω]
    {K L L' : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    [NumberField L] [FiniteDimensional k L] [IsGalois k L]
    [NumberField L'] [FiniteDimensional k L'] [IsGalois k L']
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
    [Algebra ↥K ↥L'] [IsScalarTower k ↥K ↥L'] [IsScalarTower ↥K ↥L' Ω]
    [Algebra ↥L ↥L'] [IsScalarTower k ↥L ↥L'] [IsScalarTower ↥L ↥L' Ω]
    [IsScalarTower ↥K ↥L ↥L']
    (p : ℕ) [Fact p.Prime]
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (hKL : K ≤ L) (hKL' : K ≤ L') (hLL : L ≤ L')
    (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
    (b₀ : (↥L ≃ₐ[k] ↥L) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (b₀' : (↥L' ≃ₐ[k] ↥L') → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (hb₀ : ∀ σ ∈ SSGRoute.decomp k A, b σ = b₀ (AlgEquiv.restrictNormalHom L σ))
    (hb₀' : ∀ σ ∈ SSGRoute.decomp k A, b σ = b₀' (AlgEquiv.restrictNormalHom L' σ))
    (hw' : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite
      (SSGRoute.PT.finQW L' A hA))
      (NK.GlobalCFT.Place.ofFinite (SSGRoute.PT.finQW L A hA)))
    (hZF : SSGRoute.PT.finZF hKL' A hA = (SSGRoute.PT.finZF hKL A hA).comp
      (SSGRoute.decompKRestrict k (↥L) (↥L')
        (NK.GlobalCFT.Place.ofFinite (SSGRoute.PT.finQW L A hA))
        (NK.GlobalCFT.Place.ofFinite (SSGRoute.PT.finQW L' A hA)) hw')) :
    SSGRoute.PTExt.extHMap
        (SSGRoute.decompKRestrict k (↥L) (↥L')
          (NK.GlobalCFT.Place.ofFinite (SSGRoute.PT.finQW L A hA))
          (NK.GlobalCFT.Place.ofFinite (SSGRoute.PT.finQW L' A hA)) hw')
        (CategoryTheory.CategoryStruct.id _)
        (SSGRoute.PT.finZH p K T M L hKL A hA b hb b₀ hb₀)
      = (SSGRoute.PT.finZH p K T M L' hKL' A hA b hb b₀' hb₀').comp
        (CategoryTheory.Abelian.Ext.mk₀ (CategoryTheory.eqToHom (congrArg (fun t =>
          Rep.res t
          (Rep.res (SSGRoute.PTExt.decompK (k := k)
            (NK.GlobalCFT.Place.ofFinite (SSGRoute.PT.finQ K A hA))).subtype
            (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K)
              (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))))) hZF)))
        (add_zero 1) := by

  have hb₀compat : ∀ τ : ↥L' ≃ₐ[k] ↥L', τ ∈ decompK (k := k)
      (NK.GlobalCFT.Place.ofFinite (finQW L' A hA)) →
      b₀' τ = b₀ (AlgEquiv.restrictNormalHom L τ) := by
    intro τ hτ
    have hτ' : τ ∈ (SSGRoute.decomp k A).map (SSGRoute.res k L') := by
      rw [finQW_glue L' A hA]; exact hτ
    obtain ⟨σ, hσ, hστ⟩ := Subgroup.mem_map.mp hτ'
    have hres := IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply (F := k) ↥L ↥L'
      (K₃ := Ω) σ
    rw [← hστ, ← hb₀' σ hσ, hb₀ σ hσ, hres]

  letI instL : DistribMulAction ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite (finQW L A hA)))
      (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)) :=
    DistribMulAction.compHom _ ((decompK (k := k)
      (NK.GlobalCFT.Place.ofFinite (finQ K A hA))).subtype.comp (finZF hKL A hA))
  let instH : DistribMulAction ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite (finQW L' A hA)))
      (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)) :=
    DistribMulAction.compHom _ (decompKRestrict k (↥L) (↥L')
      (NK.GlobalCFT.Place.ofFinite (finQW L A hA))
      (NK.GlobalCFT.Place.ofFinite (finQW L' A hA)) hw')
  let instA : DistribMulAction ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite (finQW L' A hA)))
      (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)) :=
    DistribMulAction.compHom _ ((decompK (k := k)
      (NK.GlobalCFT.Place.ofFinite (finQ K A hA))).subtype.comp (finZF hKL' A hA))
  letI : DistribMulAction ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite (finQW L' A hA)))
      (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)) := instA

  have hzL : (fun σ : ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite (finQW L A hA))) =>
      b₀ ((σ : ↥L ≃ₐ[k] ↥L))) ∈ Work.GroupCohomology.Z1 _
        (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)) := by
    rw [Work.GroupCohomology.mem_Z1_iff, Work.GroupCohomology.IsCrossedHom]
    intro g h
    rw [factorised_isCrossedHom p k Ω K L hKL A hA (finQ K A hA) (fun x => finQ_spec K A hA x)
      (finQW L A hA) (fun y => finQW_spec L A hA y) (finQW_glue L A hA)
      (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)) b hb b₀ hb₀ g h]
    show b₀ ((g : ↥L ≃ₐ[k] ↥L)) + (galRes k (↥K) (↥L) (g : ↥L ≃ₐ[k] ↥L)) • b₀ ((h : ↥L ≃ₐ[k] ↥L))
      = (((finZF hKL A hA) g : ↥(decompK (k := k)
          (NK.GlobalCFT.Place.ofFinite (finQ K A hA)))) : ↥K ≃ₐ[k] ↥K) • b₀ ((h : ↥L ≃ₐ[k] ↥L))
        + b₀ ((g : ↥L ≃ₐ[k] ↥L))
    rw [finZF_spec hKL A hA g]
    abel

  have hzL' : (fun σ : ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite (finQW L' A hA))) =>
      b₀' ((σ : ↥L' ≃ₐ[k] ↥L'))) ∈ @Work.GroupCohomology.Z1 _ _ _ _ instA := by
    rw [Work.GroupCohomology.mem_Z1_iff, Work.GroupCohomology.IsCrossedHom]
    intro g h
    rw [factorised_isCrossedHom p k Ω K L' hKL' A hA (finQ K A hA) (fun x => finQ_spec K A hA x)
      (finQW L' A hA) (fun y => finQW_spec L' A hA y) (finQW_glue L' A hA)
      (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)) b hb b₀' hb₀' g h]
    show b₀' ((g : ↥L' ≃ₐ[k] ↥L')) + (galRes k (↥K) (↥L') (g : ↥L' ≃ₐ[k] ↥L')) • b₀' ((h : ↥L' ≃ₐ[k] ↥L'))
      = (((finZF hKL' A hA) g : ↥(decompK (k := k)
          (NK.GlobalCFT.Place.ofFinite (finQ K A hA)))) : ↥K ≃ₐ[k] ↥K) • b₀' ((h : ↥L' ≃ₐ[k] ↥L'))
        + b₀' ((g : ↥L' ≃ₐ[k] ↥L'))
    rw [finZF_spec hKL' A hA g]
    abel

  have hzrho : (fun h : ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite (finQW L' A hA))) =>
      b₀ (((decompKRestrict k (↥L) (↥L') (NK.GlobalCFT.Place.ofFinite (finQW L A hA))
        (NK.GlobalCFT.Place.ofFinite (finQW L' A hA)) hw') h : ↥L ≃ₐ[k] ↥L)))
      ∈ @Work.GroupCohomology.Z1 ↥(decompK (k := k)
          (NK.GlobalCFT.Place.ofFinite (finQW L' A hA)))
          (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)) _ _ instH := by
    rw [Work.GroupCohomology.mem_Z1_iff, Work.GroupCohomology.IsCrossedHom]
    intro g h
    have h1 := (Work.GroupCohomology.mem_Z1_iff _ _ _).mp hzL
      ((decompKRestrict k (↥L) (↥L') (NK.GlobalCFT.Place.ofFinite (finQW L A hA))
        (NK.GlobalCFT.Place.ofFinite (finQW L' A hA)) hw') g)
      ((decompKRestrict k (↥L) (↥L') (NK.GlobalCFT.Place.ofFinite (finQW L A hA))
        (NK.GlobalCFT.Place.ofFinite (finQW L' A hA)) hw') h)
    show b₀ (((decompKRestrict k (↥L) (↥L') (NK.GlobalCFT.Place.ofFinite (finQW L A hA))
        (NK.GlobalCFT.Place.ofFinite (finQW L' A hA)) hw') (g * h) : ↥L ≃ₐ[k] ↥L))
      = (decompKRestrict k (↥L) (↥L') (NK.GlobalCFT.Place.ofFinite (finQW L A hA))
          (NK.GlobalCFT.Place.ofFinite (finQW L' A hA)) hw') g
          • b₀ (((decompKRestrict k (↥L) (↥L') (NK.GlobalCFT.Place.ofFinite (finQW L A hA))
            (NK.GlobalCFT.Place.ofFinite (finQW L' A hA)) hw') h : ↥L ≃ₐ[k] ↥L))
        + b₀ (((decompKRestrict k (↥L) (↥L') (NK.GlobalCFT.Place.ofFinite (finQW L A hA))
            (NK.GlobalCFT.Place.ofFinite (finQW L' A hA)) hw') g : ↥L ≃ₐ[k] ↥L))
    rw [map_mul]
    exact h1

  have hf : @Work.GroupCohomology.IsEquivariant ↥(decompK (k := k)
        (NK.GlobalCFT.Place.ofFinite (finQW L' A hA)))
      (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)) (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)) _ _ _
      instA instH (AddMonoidHom.id (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T))) := by
    intro g m
    show (((decompK (k := k) (NK.GlobalCFT.Place.ofFinite (finQ K A hA))).subtype
        (finZF hKL' A hA g) : ↥K ≃ₐ[k] ↥K)) • m
      = (((decompK (k := k) (NK.GlobalCFT.Place.ofFinite (finQ K A hA))).subtype
        ((finZF hKL A hA).comp (decompKRestrict k (↥L) (↥L')
          (NK.GlobalCFT.Place.ofFinite (finQW L A hA))
          (NK.GlobalCFT.Place.ofFinite (finQW L' A hA)) hw') g) : ↥K ≃ₐ[k] ↥K)) • m
    rw [hZF]

  have hL : finZH p K T M L hKL A hA b hb b₀ hb₀
      = (Work.SSGRoute.ExtH1.gammaHom ↥(decompK (k := k)
          (NK.GlobalCFT.Place.ofFinite (finQW L A hA))) (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T))
          (Work.SSGRoute.augSES_shortExact _))
        ((Work.GroupCohomology.H1π _ _) ⟨fun σ : ↥(decompK (k := k)
          (NK.GlobalCFT.Place.ofFinite (finQW L A hA))) => b₀ ((σ : ↥L ≃ₐ[k] ↥L)), hzL⟩) := by
    rw [finZH, finLevelClass]

  have hL' : finZH p K T M L' hKL' A hA b hb b₀' hb₀'
      = @Work.SSGRoute.ExtH1.gammaHom ↥(decompK (k := k)
          (NK.GlobalCFT.Place.ofFinite (finQW L' A hA))) _
          (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)) _ instA _
          (Work.SSGRoute.augSES_shortExact _)
        (@Work.GroupCohomology.H1π ↥(decompK (k := k)
            (NK.GlobalCFT.Place.ofFinite (finQW L' A hA)))
            (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)) _ _ instA
          ⟨fun σ : ↥(decompK (k := k)
            (NK.GlobalCFT.Place.ofFinite (finQW L' A hA))) => b₀' ((σ : ↥L' ≃ₐ[k] ↥L')), hzL'⟩) := by
    rw [finZH, finLevelClass]

  have hstep2 := Work.SSGRoute.extHMap_gammaHom_eq
    (decompKRestrict k (↥L) (↥L') (NK.GlobalCFT.Place.ofFinite (finQW L A hA))
      (NK.GlobalCFT.Place.ofFinite (finQW L' A hA)) hw')
    (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T))
    (⟨fun σ : ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite (finQW L A hA))) =>
      b₀ ((σ : ↥L ≃ₐ[k] ↥L)), hzL⟩ : ↥(Work.GroupCohomology.Z1
        ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite (finQW L A hA)))
        (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T))))

  have hmapZ1 : @Work.GroupCohomology.mapZ1 ↥(decompK (k := k)
        (NK.GlobalCFT.Place.ofFinite (finQW L' A hA)))
      (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)) (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T))
      _ _ _ instA instH
      (AddMonoidHom.id (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T))) hf
      ⟨fun σ : ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite (finQW L' A hA))) =>
        b₀' ((σ : ↥L' ≃ₐ[k] ↥L')), hzL'⟩
      = ⟨fun h : ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite (finQW L' A hA))) =>
        b₀ (((decompKRestrict k (↥L) (↥L') (NK.GlobalCFT.Place.ofFinite (finQW L A hA))
          (NK.GlobalCFT.Place.ofFinite (finQW L' A hA)) hw') h : ↥L ≃ₐ[k] ↥L)), hzrho⟩ := by
    apply Subtype.ext
    funext g
    rw [Work.GroupCohomology.mapZ1_coe, Work.GroupCohomology.mapCochain1_apply]
    exact hb₀compat (g : ↥L' ≃ₐ[k] ↥L') g.2

  have hH1 : (@Work.GroupCohomology.H1π ↥(decompK (k := k)
        (NK.GlobalCFT.Place.ofFinite (finQW L' A hA)))
        (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)) _ _ instH)
      ⟨fun h : ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite (finQW L' A hA))) =>
        b₀ (((decompKRestrict k (↥L) (↥L') (NK.GlobalCFT.Place.ofFinite (finQW L A hA))
          (NK.GlobalCFT.Place.ofFinite (finQW L' A hA)) hw') h : ↥L ≃ₐ[k] ↥L)), hzrho⟩
      = (@Work.GroupCohomology.mapH1 ↥(decompK (k := k)
            (NK.GlobalCFT.Place.ofFinite (finQW L' A hA)))
          (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)) (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T))
          _ _ _ instA instH
          (AddMonoidHom.id (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T))) hf)
        ((@Work.GroupCohomology.H1π ↥(decompK (k := k)
            (NK.GlobalCFT.Place.ofFinite (finQW L' A hA)))
            (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)) _ _ instA)
          ⟨fun σ : ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite (finQW L' A hA))) =>
            b₀' ((σ : ↥L' ≃ₐ[k] ↥L')), hzL'⟩) := by
    rw [Work.GroupCohomology.mapH1_H1π, hmapZ1]
  haveI hZC : SMulCommClass (↥K ≃ₐ[k] ↥K) ℤ (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)) :=
    ⟨fun g n m => map_zsmul (AddMonoidHom.mk' (fun m => g • m) (fun a b => smul_add g a b)) n m⟩
  haveI hCC : SMulCommClass (↥K ≃ₐ[k] ↥K) Coeff (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)) :=
    ⟨fun g c m => smul_comm g c.down m⟩
  haveI hCpA : SMulCommClass ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite (finQW L' A hA))) Coeff (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)) :=
    ⟨fun g c m => smul_comm ((decompK (k := k) (NK.GlobalCFT.Place.ofFinite (finQ K A hA))).subtype (finZF hKL' A hA g)) c m⟩
  letI : DistribMulAction ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite (finQW L' A hA))) (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)) := instH
  haveI hCpH : SMulCommClass ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite (finQW L' A hA))) Coeff (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)) :=
    ⟨fun g c m => smul_comm ((decompK (k := k) (NK.GlobalCFT.Place.ofFinite (finQ K A hA))).subtype ((finZF hKL A hA) ((decompKRestrict k (↥L) (↥L') (NK.GlobalCFT.Place.ofFinite (finQW L A hA))
      (NK.GlobalCFT.Place.ofFinite (finQW L' A hA)) hw') g))) c m⟩
  letI : DistribMulAction ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite (finQW L' A hA))) (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)) := instA
  have e1 : Rep.res (finZF hKL' A hA) (Rep.res (decompK (k := k) (NK.GlobalCFT.Place.ofFinite (finQ K A hA))).subtype
      (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)))) = @SSGRoute.PTExt.modRep ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite (finQW L' A hA))) (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)) _ _ instA := rfl
  have e2 : Rep.res ((finZF hKL A hA).comp (decompKRestrict k (↥L) (↥L') (NK.GlobalCFT.Place.ofFinite (finQW L A hA))
      (NK.GlobalCFT.Place.ofFinite (finQW L' A hA)) hw')) (Rep.res (decompK (k := k) (NK.GlobalCFT.Place.ofFinite (finQ K A hA))).subtype
      (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)))) = @SSGRoute.PTExt.modRep ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite (finQW L' A hA))) (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)) _ _ instH := rfl
  have hmod : @SSGRoute.PTExt.modRep ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite (finQW L' A hA))) (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)) _ _ instA
      = @SSGRoute.PTExt.modRep ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite (finQW L' A hA))) (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)) _ _ instH :=
    e1.symm.trans ((congrArg (fun t => Rep.res t (Rep.res (decompK (k := k) (NK.GlobalCFT.Place.ofFinite (finQ K A hA))).subtype
      (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T))))) hZF).trans e2)
  have hstep4 := @Work.SSGRoute.gammaHom_natural_coeff ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite (finQW L' A hA))) _ (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)) (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)) _ instA hCpA _
      instH hCpH (Work.SSGRoute.augSES_shortExact _) (AddMonoidHom.id (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T))) hf
      (eqToHom hmod) (fun m => finZH_lc_eqToHom_modRep_self hmod m)
      (@Work.GroupCohomology.H1π ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite (finQW L' A hA))) (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)) _ _ instA
        ⟨fun σ : ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite (finQW L' A hA))) => b₀' ((σ : ↥L' ≃ₐ[k] ↥L')), hzL'⟩)

  refine (congrArg (fun y => extHMap (decompKRestrict k (↥L) (↥L')
      (NK.GlobalCFT.Place.ofFinite (finQW L A hA))
      (NK.GlobalCFT.Place.ofFinite (finQW L' A hA)) hw') (𝟙 _) y) hL).trans ?_
  refine hstep2.trans ?_
  refine (congrArg (fun y => @Work.SSGRoute.ExtH1.gammaHom ↥(decompK (k := k)
      (NK.GlobalCFT.Place.ofFinite (finQW L' A hA))) _
      (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)) _ instH _
      (Work.SSGRoute.augSES_shortExact _) y) hH1).trans ?_
  refine hstep4.trans ?_
  exact (congrArg (fun y => y.comp (Abelian.Ext.mk₀ (eqToHom (congrArg (fun t => Rep.res t
      (Rep.res (decompK (k := k) (NK.GlobalCFT.Place.ofFinite (finQ K A hA))).subtype
        (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T))))) hZF)))
      (add_zero 1)) hL').symm


end Work.SSGRoute.PT

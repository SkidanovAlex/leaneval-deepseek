import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RepresentationTheory.Coinduced
import Mathlib.RingTheory.Henselian
import Mathlib.Tactic.Have
import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Submission.Work.SSGRoute.ArchDictionary.archPhiOf_natural
import Submission.Work.SSGRoute.ArchDictionary.ss2SeamAtilCocycle
import Submission.Work.SSGRoute.ArchDictionary.ss2SquareLHS
import Submission.Work.SSGRoute.ArchNat.eOfConnMapCocycle
import Submission.Work.SSGRoute.E1aClean.finPlaceDict
import Submission.Work.SSGRoute.PT.E1aFinBox.freeCoverCompat_comp_hom
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ArchDictionary

open CategoryTheory CategoryTheory.Limits SSGRoute.PTExt Work.SSGRoute.ArchDictionary
  Work.SSGRoute.ArchDictionary.ArchSeamP2

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.lazyProjDelta false
set_option backward.isDefEq.lazyWhnfCore false

/-! ## Auxiliary group-cohomology facts -/

/-- `H¹(G,E)` is killed by `2` when `E` is. -/
theorem two_nsmul_H1_eq_zero {G E : Type} [Group G] [AddCommGroup E]
    [DistribMulAction G E] (h2 : ∀ e : E, (2 : ℕ) • e = 0)
    (x : Work.GroupCohomology.H1 G E) : (2 : ℕ) • x = 0 := by
  induction x using Work.GroupCohomology.H1_induction_on with
  | h f =>
    rw [← map_nsmul, show (2 : ℕ) • f = 0 from ?_, map_zero]
    exact Subtype.ext (funext fun g => h2 ((f : G → E) g))

/-! ## The `E1c` lift of the canonical global class

The canonical global dictionary class of a globally locally constant cocycle `b` is the `ΦE`-image of
an `Ext⁰` class `y`, and the canonical `E1c` lift `ñ` of `e1aCoeffNat ∘ b` satisfies
`iotaH (e1aCoeffNat (b σ)) = d⁰ñ(σ)` (the crossed-homomorphism condition). -/

theorem ss2GlobalDictLift {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    (T : Type) [AddCommGroup T] [Module (ZMod 2) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod 2) T]
    (hζ : IsPrimitiveRoot (-1 : Ω) 2) (hζK : (-1 : Ω) ∈ K)
    (hT : SSGRoute.IsCyclotomicDual 2 (T := T) (SSGRoute.res k K) (-1 : Ω))
    (E : Type) [AddCommGroup E] [Module (ZMod 2) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod 2) E] [Finite E]
    (b : (Ω ≃ₐ[k] Ω) → E) (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b)
    (hl : SSGRoute.IsLocConstOn ⊤ b) :
    ∃ (ñ : Work.SSGRoute.ExtChain.E1cGeneric.E1cN (Eprime 2 k Ω K T E))
      (y : CategoryTheory.Abelian.Ext
        (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 (Eprime 2 k Ω K T E)) (unitsK k K) 0),
      Work.SSGRoute.E1aClean.globalDictionaryCanon 2 k Ω K (-1) hζ hζK T hT E b
          = Work.SSGRoute.ExtChain.E1cGeneric.PhiE (Eprime 2 k Ω K T E) y ∧
        ((Work.SSGRoute.ExtChain.E1cGeneric.PsiEMap
            (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 (Eprime 2 k Ω K T E)) y :
              Work.SSGRoute.homCoind k Ω K
                (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 (Eprime 2 k Ω K T E)))
          = Work.SSGRoute.ExtChain.E1cGeneric.piH (Eprime 2 k Ω K T E) ñ) ∧
        (∀ σ : Ω ≃ₐ[k] Ω,
          Work.SSGRoute.ExtChain.E1cGeneric.iotaH (Eprime 2 k Ω K T E)
              (Work.SSGRoute.ExtChain.e1aCoeffNat 2 k Ω K (-1) hζ hζK T hT E (b σ))
            = Work.GroupCohomology.d0 (Ω ≃ₐ[k] Ω)
                (Work.SSGRoute.ExtChain.E1cGeneric.E1cN (Eprime 2 k Ω K T E)) ñ σ) := by
  classical
  haveI hTfin : Finite T := Work.SSGRoute.ExtChain.e1aFiniteT 2 k Ω K (-1) T hT
  haveI hdmt : Finite (Work.SSGRoute.DualMod 2 (TensorProduct (ZMod 2) E T)) :=
    Work.SSGRoute.PT.finite_dualMod_tensor 2 E T
  haveI hfinX : Finite (Eprime 2 k Ω K T E).V := by
    change Finite (Work.SSGRoute.DualMod 2 (TensorProduct (ZMod 2) E T))
    infer_instance
  haveI hmodfinX : Module.Finite ℤ (Eprime 2 k Ω K T E).V := Module.Finite.of_finite
  letI : DistribMulAction (Ω ≃ₐ[k] Ω) E := DistribMulAction.compHom E (SSGRoute.res k K)
  have hbZ : b ∈ Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) E :=
    Work.SSGRoute.mem_absZ1_of_isCocycleOn_isLocConstOn (SSGRoute.res k K) hb hl
  let X : Rep.{0} Coeff (K ≃ₐ[k] K) := Eprime 2 k Ω K T E
  let c₁ : ↥(Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K X)) :=
    Work.AbsoluteKummer.mapZ1
      (Work.SSGRoute.ExtChain.e1aCoeffNat 2 k Ω K (-1) hζ hζK T hT E).toAddMonoidHom
      (fun σ e => Work.SSGRoute.ExtChain.e1aCoeffNat_equivariant 2 k Ω K (-1) hζ hζK T hT E σ e)
      ⟨b, hbZ⟩
  let ñ : Work.SSGRoute.ExtChain.E1cGeneric.E1cN X :=
    Work.SSGRoute.ExtChain.E1cGeneric.liftOf X c₁
  have hñ : ∀ σ : Ω ≃ₐ[k] Ω,
      Work.SSGRoute.ExtChain.E1cGeneric.iotaH X
          (Work.SSGRoute.ExtChain.e1aCoeffNat 2 k Ω K (-1) hζ hζK T hT E (b σ))
        = Work.GroupCohomology.d0 (Ω ≃ₐ[k] Ω)
            (Work.SSGRoute.ExtChain.E1cGeneric.E1cN X) ñ σ := by
    intro σ
    have h := congrFun (Work.SSGRoute.ExtChain.E1cGeneric.liftOf_spec X c₁) σ
    rw [Work.AbsoluteKummer.mapZ1_apply] at h
    rw [h]
    rfl
  have hmem : Work.SSGRoute.ExtChain.E1cGeneric.piH X ñ ∈
      Work.AbsoluteKummer.H0 (Ω ≃ₐ[k] Ω)
        (Work.SSGRoute.homCoind k Ω K (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 X)) := by
    rw [← Work.SSGRoute.ExtChain.E1cGeneric.d0_eq_zero_iff]
    funext σ
    rw [Work.SSGRoute.ExtChain.E1cGeneric.d0_piH]
    show Work.SSGRoute.ExtChain.E1cGeneric.piH X
      ((Work.GroupCohomology.d0 (Ω ≃ₐ[k] Ω)
        (Work.SSGRoute.ExtChain.E1cGeneric.E1cN X)) ñ σ) = 0
    rw [← hñ σ, Work.SSGRoute.ExtChain.E1cGeneric.piH_iotaH]
  let y : CategoryTheory.Abelian.Ext (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 X) (unitsK k K) 0 :=
    (Work.SSGRoute.ExtChain.E1cGeneric.PsiE (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 X)).symm
      ⟨Work.SSGRoute.ExtChain.E1cGeneric.piH X ñ, hmem⟩
  have hy2' : Work.SSGRoute.ExtChain.E1cGeneric.PsiEMap
      (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 X) y
      = ⟨Work.SSGRoute.ExtChain.E1cGeneric.piH X ñ, hmem⟩ := by
    rw [Work.SSGRoute.ExtChain.E1cGeneric.PsiEMap]
    exact AddEquiv.apply_symm_apply _ _
  have hy2 : ((Work.SSGRoute.ExtChain.E1cGeneric.PsiEMap
      (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 X) y) :
        Work.SSGRoute.homCoind k Ω K (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 X))
      = Work.SSGRoute.ExtChain.E1cGeneric.piH X ñ :=
    congrArg Subtype.val hy2'
  have h1 : Work.SSGRoute.H1Equiv.h1AddEquiv
      (Work.SSGRoute.ExtChain.e1aCoeffNat 2 k Ω K (-1) hζ hζK T hT E)
      (fun σ e => Work.SSGRoute.ExtChain.e1aCoeffNat_equivariant 2 k Ω K (-1) hζ hζK T hT E σ e)
      (fun σ n => Work.SSGRoute.ExtChain.e1aCoeffNat_symm_equivariant 2 k Ω K (-1) hζ hζK T hT E σ n)
      (Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) E ⟨b, hbZ⟩)
      = Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K X) c₁ :=
    Work.AbsoluteKummer.mapH1_H1π
      (Work.SSGRoute.ExtChain.e1aCoeffNat 2 k Ω K (-1) hζ hζK T hT E).toAddMonoidHom
      (fun σ e => Work.SSGRoute.ExtChain.e1aCoeffNat_equivariant 2 k Ω K (-1) hζ hζK T hT E σ e)
      ⟨b, hbZ⟩
  have h2 : Work.SSGRoute.E1aClean.globalDictEquivCanon 2 k Ω K (-1) hζ hζK T hT E
      (Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) E ⟨b, hbZ⟩)
      = (Work.SSGRoute.ExtChain.E1cGeneric.e1cEquiv (k := k) (Ω := Ω) (K := K) X).symm
          (Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω)
            (Work.SSGRoute.homCoind k Ω K X) c₁) := by
    dsimp only [Work.SSGRoute.E1aClean.globalDictEquivCanon, AddEquiv.trans_apply]
    rw [h1]
  refine ⟨ñ, y, ?_, ?_, ?_⟩
  · dsimp only [Work.SSGRoute.E1aClean.globalDictionaryCanon]
    rw [dif_pos hbZ, h2]
    refine (AddEquiv.symm_apply_eq _).mpr ?_
    rw [show (Work.SSGRoute.ExtChain.E1cGeneric.e1cEquiv (k := k) (Ω := Ω) (K := K) X)
          (Work.SSGRoute.ExtChain.E1cGeneric.PhiE X y)
        = (Work.SSGRoute.ExtChain.E1cGeneric.e1cMap (k := k) (Ω := Ω) (K := K) X)
            (Work.SSGRoute.ExtChain.E1cGeneric.PhiE X y) from rfl]
    exact (Work.SSGRoute.ExtChain.E1cGeneric.e1cMap_eq_H1π_of_cocycle_lift
      (k := k) (Ω := Ω) (K := K) X c₁ ñ hñ y hy2.symm).symm
  · exact hy2
  · intro σ
    exact hñ σ

/-- **The right-hand side of the comparison square.**  The localised global dictionary class at the
seam place is the connecting-map class `CokerNat.connMap (ses (E'|_D)) (K_wˣ) a` of an explicit
degree-zero class `a` of the canonical cover, and the seam lift
(`ArchSeamP2b.seamUnitsCan` composed with the `E1c` lift `ñ`, inflated along `Φ.τ₂`) restricts to
`a` — so the already-proved `ArchNat.eOf_connMap_cocycle` computes the `eOf`-image of the
right-hand side as the `H¹`-class of the cochain `g ↦ Ψ (b (lift g))`. -/
theorem archSeamSquareRHS {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    [NumberField ↥K]
    (T : Type) [AddCommGroup T] [Module (ZMod 2) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod 2) T]
    (hζ : IsPrimitiveRoot (-1 : Ω) 2) (hζK : (-1 : Ω) ∈ K)
    (hT : SSGRoute.IsCyclotomicDual 2 (T := T) (SSGRoute.res k K) (-1 : Ω))
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (φ : Ω →+* ℂ)
    (hlink : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
    (hne : decompK (k := k) (seamPlace (K := K) φ) ≠ ⊥)
    (E : Type) [AddCommGroup E] [Module (ZMod 2) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod 2) E] [Finite E]
    (b : (Ω ≃ₐ[k] Ω) → E) (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b)
    (hl : SSGRoute.IsLocConstOn ⊤ b) :
    ∃ (ñ : Work.SSGRoute.ExtChain.E1cGeneric.E1cN (Eprime 2 k Ω K T E))
      (y : CategoryTheory.Abelian.Ext
        (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 (Eprime 2 k Ω K T E)) (unitsK k K) 0)
      (Φ : CategoryTheory.ShortComplex.Hom
        (Work.SSGRoute.freeCoverSES
          (Rep.res (decompK (k := k) (seamPlace (K := K) φ)).subtype (Eprime 2 k Ω K T E)))
        ((Work.SSGRoute.freeCoverSES (Eprime 2 k Ω K T E)).map
          (Rep.resFunctor (k := SSGRoute.PTExt.Coeff)
            (decompK (k := k) (seamPlace (K := K) φ)).subtype)))
      (a : CategoryTheory.Abelian.Ext
        (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover
          (Rep.res (decompK (k := k) (seamPlace (K := K) φ)).subtype (Eprime 2 k Ω K T E))))
        (localUnitsK (k := k) (seamPlace (K := K) φ)) 0),
      Work.SSGRoute.E1aClean.globalDictionaryCanon 2 k Ω K (-1) hζ hζK T hT E b
          = Work.SSGRoute.ExtChain.E1cGeneric.PhiE (Eprime 2 k Ω K T E) y ∧
      ((Work.SSGRoute.ExtChain.E1cGeneric.PsiEMap
            (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 (Eprime 2 k Ω K T E)) y :
          Work.SSGRoute.homCoind k Ω K
            (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 (Eprime 2 k Ω K T E)))
        = Work.SSGRoute.ExtChain.E1cGeneric.piH (Eprime 2 k Ω K T E) ñ) ∧
      (∀ σ : Ω ≃ₐ[k] Ω,
        Work.SSGRoute.ExtChain.E1cGeneric.iotaH (Eprime 2 k Ω K T E)
            (Work.SSGRoute.ExtChain.e1aCoeffNat 2 k Ω K (-1) hζ hζK T hT E (b σ))
          = Work.GroupCohomology.d0 (Ω ≃ₐ[k] Ω)
              (Work.SSGRoute.ExtChain.E1cGeneric.E1cN (Eprime 2 k Ω K T E)) ñ σ) ∧
      Φ.τ₂ = Work.SSGRoute.PT.freeCoverCompat
        (decompK (k := k) (seamPlace (K := K) φ)).subtype (Eprime 2 k Ω K T E) ∧
      Φ.τ₃ = CategoryTheory.CategoryStruct.id
        (Rep.res (decompK (k := k) (seamPlace (K := K) φ)).subtype (Eprime 2 k Ω K T E)) ∧
      (extLoc (k := k) (seamPlace (K := K) φ) (extToIdeles (k := k)
            (Work.SSGRoute.E1aClean.globalDictionaryCanon 2 k Ω K (-1) hζ hζK T hT E b)))
        = CokerNat.connMap
            (SSGRoute.ses_shortExact
              (Rep.res (decompK (k := k) (seamPlace (K := K) φ)).subtype
                (Eprime 2 k Ω K T E)))
            (localUnitsK (k := k) (seamPlace (K := K) φ)) a ∧
      (∀ r : (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover
          (Rep.res (decompK (k := k) (seamPlace (K := K) φ)).subtype
            (Eprime 2 k Ω K T E)))).V,
        (MonoidHom.toAdditive (ArchSeamP2b.seamUnitsCan (K := K) φ hne))
            (ñ (Rep.Hom.hom Φ.τ₂ (Rep.Hom.hom
              (CategoryTheory.Limits.kernel.ι (Work.SSGRoute.freeCover
                (Rep.res (decompK (k := k) (seamPlace (K := K) φ)).subtype
                  (Eprime 2 k Ω K T E)))) r)))
          = Rep.Hom.hom (CategoryTheory.Abelian.Ext.addEquiv₀ a) r) := by
  classical
  haveI hTfin : Finite T := Work.SSGRoute.ExtChain.e1aFiniteT 2 k Ω K (-1) T hT
  haveI hFinD : Fintype ↥(decompK (k := k) (seamPlace (K := K) φ)) := Fintype.ofFinite _
  letI : DistribMulAction (Ω ≃ₐ[k] Ω) E := DistribMulAction.compHom E (SSGRoute.res k K)
  have hbZ : b ∈ Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) E :=
    Work.SSGRoute.mem_absZ1_of_isCocycleOn_isLocConstOn (SSGRoute.res k K) hb hl
  letI hInst : DistribMulAction ↥(decompK (k := k) (seamPlace (K := K) φ))
      ((Eprime 2 k Ω K T E).V →ₗ[Coeff] (localUnitsK (k := k) (seamPlace (K := K) φ)).V) :=
    Work.SSGRoute.homRepDistribMulAction
      (Rep.res (decompK (k := k) (seamPlace (K := K) φ)).subtype (Eprime 2 k Ω K T E)) (localUnitsK (k := k) (seamPlace (K := K) φ))
  -- the canonical global class and its E1c lift
  obtain ⟨ñ, y, hzdict, hy2, hñ⟩ := ss2GlobalDictLift T hζ hζK hT E b hb hl
  -- the comparison of the free covers at the complex place
  obtain ⟨Φ, hΦ₂, hΦ₃, hΦmap⟩ :=
    Work.SSGRoute.PT.PhiEgen_res_compat (decompK (k := k) (seamPlace (K := K) φ)).subtype
      (Eprime 2 k Ω K T E) (unitsK k K)
  let a₀ : CategoryTheory.Abelian.Ext
      (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover
        (Rep.res (decompK (k := k) (seamPlace (K := K) φ)).subtype (Eprime 2 k Ω K T E))))
      (Rep.res (decompK (k := k) (seamPlace (K := K) φ)).subtype (unitsK k K)) 0 :=
    (CategoryTheory.Abelian.Ext.mk₀ Φ.τ₁).comp
      ((Rep.resFunctor (k := SSGRoute.PTExt.Coeff) (decompK (k := k) (seamPlace (K := K) φ)).subtype).mapExtAddHom
        (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 (Eprime 2 k Ω K T E)) (unitsK k K) 0 y)
      (zero_add 0)
  let a' : CategoryTheory.Abelian.Ext
      (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover
        (Rep.res (decompK (k := k) (seamPlace (K := K) φ)).subtype (Eprime 2 k Ω K T E))))
      (localUnitsK (k := k) (seamPlace (K := K) φ)) 0 :=
    a₀.comp (CategoryTheory.Abelian.Ext.mk₀
      (NK.HassePrinciple.unitsToLocalUnits (K := k) (L := ↥K) (seamPlace (K := K) φ))) (add_zero 0)
  have hRHS : SSGRoute.PTExt.extLoc (k := k) (seamPlace (K := K) φ)
        (SSGRoute.PTExt.extToIdeles (k := k)
          (Work.SSGRoute.ExtChain.E1cGeneric.PhiE (k := k) (Ω := Ω) (K := K)
            (Eprime 2 k Ω K T E) y))
      = CokerNat.connMap
          (SSGRoute.ses_shortExact
            (Rep.res (decompK (k := k) (seamPlace (K := K) φ)).subtype (Eprime 2 k Ω K T E)))
          (localUnitsK (k := k) (seamPlace (K := K) φ)) a' := by
    rw [SSGRoute.SSGStage.extLoc_extToIdeles_eq]
    rw [show SSGRoute.PTExt.extRes (decompK (k := k) (seamPlace (K := K) φ)).subtype
          (Work.SSGRoute.ExtChain.E1cGeneric.PhiE (k := k) (Ω := Ω) (K := K)
            (Eprime 2 k Ω K T E) y)
        = (Rep.resFunctor (k := SSGRoute.PTExt.Coeff) (decompK (k := k) (seamPlace (K := K) φ)).subtype).mapExtAddHom
            (Eprime 2 k Ω K T E) (unitsK k K) 1
            (Work.SSGRoute.ExtChain.E1cGeneric.PhiE (k := k) (Ω := Ω) (K := K)
              (Eprime 2 k Ω K T E) y)
        from (CategoryTheory.Functor.mapExtAddHom_apply
          (F := Rep.resFunctor (k := SSGRoute.PTExt.Coeff) (decompK (k := k) (seamPlace (K := K) φ)).subtype)
          (Eprime 2 k Ω K T E) (unitsK k K) 1
          (Work.SSGRoute.ExtChain.E1cGeneric.PhiE (k := k) (Ω := Ω) (K := K)
            (Eprime 2 k Ω K T E) y)).symm]
    rw [show Work.SSGRoute.ExtChain.E1cGeneric.PhiE (k := k) (Ω := Ω) (K := K)
          (Eprime 2 k Ω K T E)
        = Work.SSGRoute.PT.PhiEgen (Eprime 2 k Ω K T E) (unitsK k K) from rfl]
    rw [hΦmap y]
    show (Work.SSGRoute.PT.PhiEgen
          (Rep.res (decompK (k := k) (seamPlace (K := K) φ)).subtype (Eprime 2 k Ω K T E))
          (Rep.res (decompK (k := k) (seamPlace (K := K) φ)).subtype (unitsK k K)) a₀).comp
        (CategoryTheory.Abelian.Ext.mk₀
          (NK.HassePrinciple.unitsToLocalUnits (K := k) (L := ↥K) (seamPlace (K := K) φ))) (add_zero 1)
      = CokerNat.connMap
          (SSGRoute.ses_shortExact
            (Rep.res (decompK (k := k) (seamPlace (K := K) φ)).subtype (Eprime 2 k Ω K T E)))
          (localUnitsK (k := k) (seamPlace (K := K) φ)) a'
    rw [CokerNat.connMap_apply, Work.SSGRoute.PT.PhiEgen_apply]
    exact CategoryTheory.Abelian.Ext.comp_assoc_of_second_deg_zero _ _ _ _
  -- the lift used in the D3 hypothesis
  let atil : (Rep.free Coeff ↥(decompK (k := k) (seamPlace (K := K) φ))
      (Rep.res (decompK (k := k) (seamPlace (K := K) φ)).subtype (Eprime 2 k Ω K T E)).V).V →+
      (localUnitsK (k := k) (seamPlace (K := K) φ)).V :=
    (MonoidHom.toAdditive (Work.SSGRoute.ArchDictionary.ArchSeamP2b.seamUnitsCan
      (K := K) φ hne)).comp (ñ.comp ((Rep.Hom.hom Φ.τ₂).toAddMonoidHom))
  -- the `Ext⁰` bookkeeping: `addEquiv₀ a'` restricted to the syzygy
  have hmk₀ : ∀ {X Y : Rep.{0} Coeff ↥(decompK (k := k) (seamPlace (K := K) φ))} (f : X ⟶ Y),
      CategoryTheory.Abelian.Ext.addEquiv₀ (CategoryTheory.Abelian.Ext.mk₀ f) = f := by
    intro X Y f
    apply (CategoryTheory.Abelian.Ext.mk₀_bijective X Y).injective
    rw [CategoryTheory.Abelian.Ext.mk₀_addEquiv₀_apply]
  have hcomp₀ : ∀ {X Y Z : Rep.{0} Coeff ↥(decompK (k := k) (seamPlace (K := K) φ))}
      (x : CategoryTheory.Abelian.Ext X Y 0) (z : CategoryTheory.Abelian.Ext Y Z 0),
      CategoryTheory.Abelian.Ext.addEquiv₀ (x.comp z (zero_add 0))
        = (CategoryTheory.Abelian.Ext.addEquiv₀ x) ≫ (CategoryTheory.Abelian.Ext.addEquiv₀ z) := by
    intro X Y Z x z
    conv_lhs => rw [← CategoryTheory.Abelian.Ext.mk₀_addEquiv₀_apply x,
                    ← CategoryTheory.Abelian.Ext.mk₀_addEquiv₀_apply z]
    rw [CategoryTheory.Abelian.Ext.mk₀_comp_mk₀]
    exact hmk₀ _
  have hmapExt : ∀ {X Y : Rep.{0} Coeff (K ≃ₐ[k] K)}
      (z : CategoryTheory.Abelian.Ext X Y 0),
      CategoryTheory.Abelian.Ext.addEquiv₀
        ((Rep.resFunctor (k := SSGRoute.PTExt.Coeff) (decompK (k := k) (seamPlace (K := K) φ)).subtype).mapExtAddHom
          X Y 0 z)
        = (Rep.resFunctor (k := SSGRoute.PTExt.Coeff) (decompK (k := k) (seamPlace (K := K) φ)).subtype).map
            (CategoryTheory.Abelian.Ext.addEquiv₀ z) := by
    intro X Y z
    conv_lhs => rw [← CategoryTheory.Abelian.Ext.mk₀_addEquiv₀_apply z]
    rw [CategoryTheory.Functor.mapExtAddHom_apply,
      CategoryTheory.Abelian.Ext.mapExactFunctor_mk₀]
    exact hmk₀ _
  have hmapExtVal : ∀ {X Y : Rep.{0} Coeff (K ≃ₐ[k] K)}
      (z : CategoryTheory.Abelian.Ext X Y 0) (x : X.V),
      Rep.Hom.hom (CategoryTheory.Abelian.Ext.addEquiv₀
        ((Rep.resFunctor (k := SSGRoute.PTExt.Coeff) (decompK (k := k) (seamPlace (K := K) φ)).subtype).mapExtAddHom
          X Y 0 z)) x
        = Rep.Hom.hom (CategoryTheory.Abelian.Ext.addEquiv₀ z) x := by
    intro X Y z x
    exact congrFun (congrArg (fun (m : Rep.res (decompK (k := k) (seamPlace (K := K) φ)).subtype X ⟶
        Rep.res (decompK (k := k) (seamPlace (K := K) φ)).subtype Y) => ⇑(Rep.Hom.hom m)) (hmapExt z)) x
  let hUTL : Rep.res (decompK (k := k) (seamPlace (K := K) φ)).subtype (unitsK k ↥K) ⟶
      localUnitsK (k := k) (seamPlace (K := K) φ) :=
    NK.HassePrinciple.unitsToLocalUnits (K := k) (L := ↥K) (seamPlace (K := K) φ)
  have hda : ∀ r : (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover
        (Rep.res (decompK (k := k) (seamPlace (K := K) φ)).subtype (Eprime 2 k Ω K T E)))).V,
      (CategoryTheory.Abelian.Ext.addEquiv₀ a') r
        = hUTL ((CategoryTheory.Abelian.Ext.addEquiv₀ y) (Φ.τ₁ r)) := by
    intro r
    rw [show a' = a₀.comp (CategoryTheory.Abelian.Ext.mk₀
        (NK.HassePrinciple.unitsToLocalUnits (K := k) (L := ↥K) (seamPlace (K := K) φ))) (add_zero 0) from rfl]
    rw [show a₀ = (CategoryTheory.Abelian.Ext.mk₀ Φ.τ₁).comp
        ((Rep.resFunctor (k := SSGRoute.PTExt.Coeff) (decompK (k := k) (seamPlace (K := K) φ)).subtype).mapExtAddHom
          (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 (Eprime 2 k Ω K T E))
          (unitsK k K) 0 y) (zero_add 0) from rfl]
    simp only [hcomp₀]
    simp only [Rep.hom_comp]
    simp only [hmk₀]
    change Rep.Hom.hom hUTL
        ((CategoryTheory.Abelian.Ext.addEquiv₀
          ((Rep.resFunctor (k := SSGRoute.PTExt.Coeff) (decompK (k := k) (seamPlace (K := K) φ)).subtype).mapExtAddHom
            (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 (Eprime 2 k Ω K T E))
            (unitsK k K) 0 y))
          ((Rep.Hom.hom Φ.τ₁) r))
      = Rep.Hom.hom hUTL ((CategoryTheory.Abelian.Ext.addEquiv₀ y) ((Rep.Hom.hom Φ.τ₁) r))
    rw [hmapExtVal (z := y) (x := (Rep.Hom.hom Φ.τ₁) r)]
  -- the commutation square of the comparison
  have hcomm : ∀ r : (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover
        (Rep.res (decompK (k := k) (seamPlace (K := K) φ)).subtype (Eprime 2 k Ω K T E)))).V,
      Φ.τ₂ ((CategoryTheory.Limits.kernel.ι (Work.SSGRoute.freeCover
            (Rep.res (decompK (k := k) (seamPlace (K := K) φ)).subtype (Eprime 2 k Ω K T E)))) r)
        = (CategoryTheory.Limits.kernel.ι
            (Work.SSGRoute.freeCover (Eprime 2 k Ω K T E))) (Φ.τ₁ r) := by
    intro r
    have h := congrArg (fun (m : CategoryTheory.Limits.kernel
        (Work.SSGRoute.freeCover (Rep.res (decompK (k := k) (seamPlace (K := K) φ)).subtype
          (Eprime 2 k Ω K T E))) ⟶
        Rep.res (decompK (k := k) (seamPlace (K := K) φ)).subtype
          (Rep.free Coeff (K ≃ₐ[k] K) (Eprime 2 k Ω K T E).V)) => m r)
      (CategoryTheory.ShortComplex.Hom.comm₁₂ Φ)
    simp only [CategoryTheory.ShortComplex.map_f] at h
    calc Φ.τ₂ ((CategoryTheory.Limits.kernel.ι (Work.SSGRoute.freeCover
          (Rep.res (decompK (k := k) (seamPlace (K := K) φ)).subtype (Eprime 2 k Ω K T E)))) r)
        = ((CategoryTheory.Limits.kernel.ι (Work.SSGRoute.freeCover
            (Rep.res (decompK (k := k) (seamPlace (K := K) φ)).subtype (Eprime 2 k Ω K T E)))) ≫ Φ.τ₂) r := rfl
      _ = (Φ.τ₁ ≫ Rep.resMap (decompK (k := k) (seamPlace (K := K) φ)).subtype
            (CategoryTheory.Limits.kernel.ι
              (Work.SSGRoute.freeCover (Eprime 2 k Ω K T E)))) r := h.symm
      _ = (CategoryTheory.Limits.kernel.ι
            (Work.SSGRoute.freeCover (Eprime 2 k Ω K T E))) (Φ.τ₁ r) := rfl
  -- the seam lift restricted to the syzygy is `addEquiv₀ a'`
  have hRHS' : SSGRoute.PTExt.extLoc (k := k) (seamPlace (K := K) φ)
      (SSGRoute.PTExt.extToIdeles (k := k)
        (Work.SSGRoute.E1aClean.globalDictionaryCanon 2 k Ω K (-1) hζ hζK T hT E b))
      = CokerNat.connMap
          (SSGRoute.ses_shortExact
            (Rep.res (decompK (k := k) (seamPlace (K := K) φ)).subtype (Eprime 2 k Ω K T E)))
          (localUnitsK (k := k) (seamPlace (K := K) φ)) a' := by
    rw [hzdict]
    exact hRHS
  have hatil : ∀ r : (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover
        (Rep.res (decompK (k := k) (seamPlace (K := K) φ)).subtype (Eprime 2 k Ω K T E)))).V,
      (MonoidHom.toAdditive (ArchSeamP2b.seamUnitsCan (K := K) φ hne))
          (ñ (Rep.Hom.hom Φ.τ₂ (Rep.Hom.hom
            (CategoryTheory.Limits.kernel.ι (Work.SSGRoute.freeCover
              (Rep.res (decompK (k := k) (seamPlace (K := K) φ)).subtype
                (Eprime 2 k Ω K T E)))) r)))
        = Rep.Hom.hom (CategoryTheory.Abelian.Ext.addEquiv₀ a') r := by
    intro r
    rw [hcomm r]
    change (MonoidHom.toAdditive (ArchSeamP2b.seamUnitsCan (K := K) φ hne))
        ((Work.SSGRoute.ExtChain.E1cGeneric.piH (Eprime 2 k Ω K T E) ñ)
          (Rep.Hom.hom Φ.τ₁ r))
      = Rep.Hom.hom (CategoryTheory.Abelian.Ext.addEquiv₀ a') r
    rw [← hy2]
    rw [show (Work.SSGRoute.ExtChain.E1cGeneric.PsiEMap
          (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 (Eprime 2 k Ω K T E)) y :
          Work.SSGRoute.homCoind k Ω K
            (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 (Eprime 2 k Ω K T E)))
        = Work.SSGRoute.toCoindH0
            (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 (Eprime 2 k Ω K T E))
            (CategoryTheory.Abelian.Ext.addEquiv₀ y) from
      congrArg Subtype.val (Work.SSGRoute.ExtChain.E1cGeneric.PsiEMap_apply_toCoindH0
        (k := k) (Ω := Ω) (K := K)
        (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 (Eprime 2 k Ω K T E)) y)]
    rw [Work.SSGRoute.toCoindH0_apply]
    have hsu : (MonoidHom.toAdditive (ArchSeamP2b.seamUnitsCan (K := K) φ hne))
        (Additive.ofMul (Units.map (algebraMap ↥K Ω).toMonoidWithZeroHom
          (Additive.toMul (Rep.Hom.hom (CategoryTheory.Abelian.Ext.addEquiv₀ y)
            (Rep.Hom.hom Φ.τ₁ r)))))
        = Rep.Hom.hom hUTL (Rep.Hom.hom (CategoryTheory.Abelian.Ext.addEquiv₀ y)
              (Rep.Hom.hom Φ.τ₁ r)) := by
      have hA : Rep.Hom.hom hUTL (Rep.Hom.hom (CategoryTheory.Abelian.Ext.addEquiv₀ y)
            (Rep.Hom.hom Φ.τ₁ r))
          = Additive.ofMul (NK.HassePrinciple.unitsToLocalUnitsHom (seamPlace (K := K) φ)
              (Additive.toMul (Rep.Hom.hom (CategoryTheory.Abelian.Ext.addEquiv₀ y)
                (Rep.Hom.hom Φ.τ₁ r)))) := by
        dsimp only [hUTL]
        rfl
      rw [hA]
      show (MonoidHom.toAdditive (ArchSeamP2b.seamUnitsCan (K := K) φ hne))
          (Additive.ofMul (Units.map (algebraMap ↥K Ω).toMonoidHom
            (Additive.toMul (Rep.Hom.hom (CategoryTheory.Abelian.Ext.addEquiv₀ y)
              (Rep.Hom.hom Φ.τ₁ r)))))
        = Additive.ofMul (NK.HassePrinciple.unitsToLocalUnitsHom (seamPlace (K := K) φ)
            (Additive.toMul (Rep.Hom.hom (CategoryTheory.Abelian.Ext.addEquiv₀ y)
              (Rep.Hom.hom Φ.τ₁ r))))
      exact ArchSeamP2b.seamUnitsCan_on_K (K := K) φ hne
        (Additive.toMul (Rep.Hom.hom (CategoryTheory.Abelian.Ext.addEquiv₀ y)
          (Rep.Hom.hom Φ.τ₁ r)))
    rw [hsu, ← hda r]
  exact ⟨ñ, y, Φ, a', hzdict, hy2, hñ, hΦ₂, hΦ₃, hRHS', hatil⟩

/-- **The comparison square (S) of the archimedean `p = 2` dictionary — the lead's ARCHP2 dispatch
D2** (verbatim: `ArchDictionary/archPhiSeam_square.lean` / `_lead_design/archp2_1008/dispatch/`,
only the name changed).  This is the SINGLE remaining statement of the whole `E1aClean` leaf
(measured: the leaf closure `Work.SSGRoute.E1aClean.localDictionary_natural_family_arch_pt` has
exactly this one hole).  Route: `Submission/Work/SSGRoute/PT/E1aUnr/ROUTE_archPhiSeam_square2.md`
(the lead's 7-step route from `_lead_design/archp2_1008/ARCHP2_PLAN.md` §3, the available bricks,
and the warning that `seamUnits_equivariant` is FALSE — use `seamUnitsCan` from `archSeamDefs2`). -/
theorem archPhiSeam_square2 {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    (T : Type) [AddCommGroup T] [Module (ZMod 2) T]
    [DistribMulAction (K ≃ₐ[k] K) T] [SMulCommClass (K ≃ₐ[k] K) (ZMod 2) T]
    (hζ : IsPrimitiveRoot (-1 : Ω) 2) (hζK : (-1 : Ω) ∈ K)
    (hT : SSGRoute.IsCyclotomicDual 2 (T := T) (SSGRoute.res k K) (-1 : Ω))
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (φ : Ω →+* ℂ)
    (hlink : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x)) (w : NK.GlobalCFT.Place ↥K)
    (hw : w = NK.GlobalCFT.Place.ofInfinite
      (NumberField.InfinitePlace.mk (φ.comp (algebraMap ↥K Ω))))
    (hne : decompK (k := k) w ≠ ⊥)
    (E : Type) [AddCommGroup E] [Module (ZMod 2) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod 2) E] [Finite E]
    (Ψ : E ≃+ ((Eprime 2 k Ω K T E).V →ₗ[Coeff] (localUnitsK (k := k) w).V))
    (hΨv : ∀ e, Ψ e = seamCoeffLoc T hζ hζK hT c hc2 hc1 φ hlink w hw hne E e)
    (hΦ : @Work.GroupCohomology.IsEquivariant ↥(decompK (k := k) w) E
      ((Eprime 2 k Ω K T E).V →ₗ[Coeff] (localUnitsK (k := k) w).V) _ _ _ (dcAct K E w)
      (Work.SSGRoute.homRepDistribMulAction
        (Rep.res (decompK (k := k) w).subtype (Eprime 2 k Ω K T E)) (localUnitsK (k := k) w))
      Ψ.toAddMonoidHom)
    (hΨ : @Work.GroupCohomology.IsEquivariant ↥(decompK (k := k) w)
      ((Eprime 2 k Ω K T E).V →ₗ[Coeff] (localUnitsK (k := k) w).V) E _ _ _
      (Work.SSGRoute.homRepDistribMulAction
        (Rep.res (decompK (k := k) w).subtype (Eprime 2 k Ω K T E)) (localUnitsK (k := k) w))
      (dcAct K E w) Ψ.symm.toAddMonoidHom)
    (b : (Ω ≃ₐ[k] Ω) → E) (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b)
    (hl : SSGRoute.IsLocConstOn ⊤ b) :
    archPhiOf c hc2 hc1 φ hlink w hw hne E
        (Rep.res (decompK (k := k) w).subtype (Eprime 2 k Ω K T E)) Ψ hΦ hΨ
        (AcOfFun (K := K) (E := E) c b) =
      extLoc (k := k) w (extToIdeles (k := k)
        (Work.SSGRoute.E1aClean.globalDictionaryCanon 2 k Ω K (-1) hζ hζK T hT E b)) := by
  classical
  subst hw
  -- ## the two sides of the square and the data attached to them
  obtain ⟨ψZ, hz₁, hLHS, hψZval⟩ :=
    ss2SquareLHS (K := K) (T := T) hζ hζK hT c hc2 hc1 φ hlink hne E Ψ hΦ hΨ b hb hl
  obtain ⟨ñ, y, Φ, a, hdict, hy2, hñ, hΦ₂, hΦ₃, hRHS, hatil⟩ :=
    archSeamSquareRHS (K := K) (T := T) hζ hζK hT c hc2 hc1 φ hlink hne E b hb hl
  -- ## step 6: the value rule of `ψZ`
  have hψ : ∀ (g : ↥(decompK (k := k) (seamPlace (K := K) φ)))
      (f : (Rep.free Coeff ↥(decompK (k := k) (seamPlace (K := K) φ))
        (Rep.res (decompK (k := k) (seamPlace (K := K) φ)).subtype (Eprime 2 k Ω K T E)).V).V),
      let atil : (Rep.free Coeff ↥(decompK (k := k) (seamPlace (K := K) φ))
          (Rep.res (decompK (k := k) (seamPlace (K := K) φ)).subtype
            (Eprime 2 k Ω K T E)).V).V →+
          (localUnitsK (k := k) (seamPlace (K := K) φ)).V :=
        (MonoidHom.toAdditive (ArchSeamP2b.seamUnitsCan (K := K) φ hne)).comp
          (ñ.comp ((Rep.Hom.hom Φ.τ₂).toAddMonoidHom))
      ψZ g (Rep.Hom.hom (freeCover (Rep.res (decompK (k := k) (seamPlace (K := K) φ)).subtype
          (Eprime 2 k Ω K T E))) f)
        = (localUnitsK (k := k) (seamPlace (K := K) φ)).ρ g
            (atil (((Rep.free Coeff ↥(decompK (k := k) (seamPlace (K := K) φ))
              (Rep.res (decompK (k := k) (seamPlace (K := K) φ)).subtype
                (Eprime 2 k Ω K T E)).V).ρ g⁻¹) f))
          - atil f := by
    intro g f
    rw [hψZval g]
    exact ss2SeamAtilCocycle (K := K) (T := T) hζ hζK hT c hc2 hc1 φ hlink hne E Ψ hΨv b hb
      Φ hΦ₂ hΦ₃ ñ hñ g f
  -- ## step 5: the dictionary of the connecting class
  obtain ⟨hz₂, hD3⟩ := Work.SSGRoute.ArchNat.eOf_connMap_cocycle
    (G := ↥(decompK (k := k) (seamPlace (K := K) φ)))
    (N := localUnitsK (k := k) (seamPlace (K := K) φ))
    (hInj := moduleInjective_coeff_of_divisible _
      (localUnitsK_divisible_of_decompK_ne_bot (k := k) (Ω := Ω) (K := K) φ
        (seamPlace (K := K) φ) rfl hne))
    (X := fun M => Classical.choose (homRepFree_coind_iso _ M.V _))
    (hX := fun M => Classical.choose_spec (homRepFree_coind_iso _ M.V _))
    (M := Rep.res (decompK (k := k) (seamPlace (K := K) φ)).subtype (Eprime 2 k Ω K T E))
    (a := a)
    (atil := (MonoidHom.toAdditive (ArchSeamP2b.seamUnitsCan (K := K) φ hne)).comp
      (ñ.comp ((Rep.Hom.hom Φ.τ₂).toAddMonoidHom)))
    (hatil := hatil) (ψ := ψZ) (hψ := hψ)
  -- ## the two sides in the `eOf` picture
  let eD := NatH1.eOf (N := localUnitsK (k := k) (seamPlace (K := K) φ))
    (moduleInjective_coeff_of_divisible _
      (localUnitsK_divisible_of_decompK_ne_bot (k := k) (Ω := Ω) (K := K) φ
        (seamPlace (K := K) φ) rfl hne))
    (fun M => Classical.choose (homRepFree_coind_iso _ M.V _))
    (fun M => Classical.choose_spec (homRepFree_coind_iso _ M.V _))
    (Rep.res (decompK (k := k) (seamPlace (K := K) φ)).subtype (Eprime 2 k Ω K T E))
  let AL := archPhiOf c hc2 hc1 φ hlink (seamPlace (K := K) φ) rfl hne E
    (Rep.res (decompK (k := k) (seamPlace (K := K) φ)).subtype (Eprime 2 k Ω K T E))
    Ψ hΦ hΨ (AcOfFun (K := K) (E := E) c b)
  let AR := extLoc (k := k) (seamPlace (K := K) φ) (extToIdeles (k := k)
    (Work.SSGRoute.E1aClean.globalDictionaryCanon 2 k Ω K (-1) hζ hζK T hT E b))
  let CM := CokerNat.connMap
    (SSGRoute.ses_shortExact (Rep.res (decompK (k := k) (seamPlace (K := K) φ)).subtype
      (Eprime 2 k Ω K T E)))
    (localUnitsK (k := k) (seamPlace (K := K) φ)) a
  have hL : eD AL = @Work.GroupCohomology.H1π ↥(decompK (k := k) (seamPlace (K := K) φ)) ((Eprime 2 k Ω K T E).V →ₗ[Coeff] (localUnitsK (k := k) (seamPlace (K := K) φ)).V) _ _ (Work.SSGRoute.homRepDistribMulAction (Rep.res (decompK (k := k) (seamPlace (K := K) φ)).subtype (Eprime 2 k Ω K T E)) (localUnitsK (k := k) (seamPlace (K := K) φ)))
      ⟨ψZ, hz₁⟩ := hLHS
  have hRm : eD AR = eD CM := congrArg eD hRHS
  have h2m : ∀ m : (Eprime 2 k Ω K T E).V, (2 : ℕ) • m = 0 :=
    fun m => Work.SSGRoute.E1aClean.dualMod_p_smul_eq_zero 2 (TensorProduct (ZMod 2) E T) m
  have hlin : ∀ e : (Rep.res (decompK (k := k) (seamPlace (K := K) φ)).subtype
        (Eprime 2 k Ω K T E)).V →ₗ[Coeff]
        (localUnitsK (k := k) (seamPlace (K := K) φ)).V, (2 : ℕ) • e = 0 := by
    intro e
    refine LinearMap.ext (fun m => ?_)
    change (2 : ℕ) • (e m) = 0
    rw [← map_nsmul, h2m m, map_zero]
  have h2t : (2 : ℕ) • (eD AL) = 0 :=
    @two_nsmul_H1_eq_zero ↥(decompK (k := k) (seamPlace (K := K) φ))
      ((Eprime 2 k Ω K T E).V →ₗ[Coeff] (localUnitsK (k := k) (seamPlace (K := K) φ)).V) _ _
      (Work.SSGRoute.homRepDistribMulAction (Rep.res (decompK (k := k) (seamPlace (K := K) φ)).subtype (Eprime 2 k Ω K T E)) (localUnitsK (k := k) (seamPlace (K := K) φ)))
      hlin (eD AL)
  have hcls : @Work.GroupCohomology.H1π ↥(decompK (k := k) (seamPlace (K := K) φ)) ((Eprime 2 k Ω K T E).V →ₗ[Coeff] (localUnitsK (k := k) (seamPlace (K := K) φ)).V) _ _ (Work.SSGRoute.homRepDistribMulAction (Rep.res (decompK (k := k) (seamPlace (K := K) φ)).subtype (Eprime 2 k Ω K T E)) (localUnitsK (k := k) (seamPlace (K := K) φ)))
      ⟨ψZ, hz₂⟩ = @Work.GroupCohomology.H1π ↥(decompK (k := k) (seamPlace (K := K) φ)) ((Eprime 2 k Ω K T E).V →ₗ[Coeff] (localUnitsK (k := k) (seamPlace (K := K) φ)).V) _ _ (Work.SSGRoute.homRepDistribMulAction (Rep.res (decompK (k := k) (seamPlace (K := K) φ)).subtype (Eprime 2 k Ω K T E)) (localUnitsK (k := k) (seamPlace (K := K) φ))) ⟨ψZ, hz₁⟩ := by congr 1
  have hdisj : eD CM = eD AL ∨ eD CM = -eD AL := by
    rcases hD3 with h | h
    · left
      have h1 : eD CM = @Work.GroupCohomology.H1π ↥(decompK (k := k) (seamPlace (K := K) φ)) ((Eprime 2 k Ω K T E).V →ₗ[Coeff] (localUnitsK (k := k) (seamPlace (K := K) φ)).V) _ _ (Work.SSGRoute.homRepDistribMulAction (Rep.res (decompK (k := k) (seamPlace (K := K) φ)).subtype (Eprime 2 k Ω K T E)) (localUnitsK (k := k) (seamPlace (K := K) φ))) ⟨ψZ, hz₂⟩ := h
      exact h1.trans (hcls.trans hL.symm)
    · right
      have h1 : eD CM = -@Work.GroupCohomology.H1π ↥(decompK (k := k) (seamPlace (K := K) φ)) ((Eprime 2 k Ω K T E).V →ₗ[Coeff] (localUnitsK (k := k) (seamPlace (K := K) φ)).V) _ _ (Work.SSGRoute.homRepDistribMulAction (Rep.res (decompK (k := k) (seamPlace (K := K) φ)).subtype (Eprime 2 k Ω K T E)) (localUnitsK (k := k) (seamPlace (K := K) φ))) ⟨ψZ, hz₂⟩ := h
      rw [hcls] at h1
      exact h1.trans (congrArg Neg.neg hL.symm)
  have hfin : eD AR = eD AL := by
    rcases hdisj with h | h
    · exact hRm.trans h
    · rw [hRm, h, neg_eq_iff_add_eq_zero, ← two_nsmul]
      exact h2t
  exact (eD.injective hfin).symm

end Work.SSGRoute.ArchDictionary

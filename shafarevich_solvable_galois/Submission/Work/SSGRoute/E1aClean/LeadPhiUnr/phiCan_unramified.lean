import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Submission.Work.SSGRoute.E1aClean.LeadPhiUnr.e1cHensel_comp_val_eq_zero_of_unramified
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.E1aClean.LeadPhiUnr

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

attribute [local instance 10000] Work.SSGRoute.homCoind.instDistribMulActionAlgEquiv

/-- Postcomposition of `extResEquivExplicit`-images. -/
theorem extResEquivExplicit_comp_post {G G' : Type} [Group G] [Group G'] (e : G ≃* G')
    (X Y Z : Rep.{0} Coeff G)
    (y : CategoryTheory.Abelian.Ext (Rep.res e.symm.toMonoidHom X)
      (Rep.res e.symm.toMonoidHom Y) 1)
    (χ : Y ⟶ Z) :
    (extResEquivExplicit e X Y y).comp (CategoryTheory.Abelian.Ext.mk₀ χ) (add_zero 1)
      = extResEquivExplicit e X Z
          (y.comp (CategoryTheory.Abelian.Ext.mk₀ (Rep.resMap e.symm.toMonoidHom χ))
            (add_zero 1)) := by
  haveI : (Rep.resFunctor (k := Coeff) e.symm.toMonoidHom).IsEquivalence :=
    Work.SSGRoute.resFunctor_isEquivalence e
  have key : ∀ (A B : Rep.{0} Coeff G)
      (z : CategoryTheory.Abelian.Ext (Rep.res e.symm.toMonoidHom A)
        (Rep.res e.symm.toMonoidHom B) 1),
      CategoryTheory.Abelian.Ext.mapExactFunctor
        (Rep.resFunctor (k := Coeff) e.symm.toMonoidHom)
        (extResEquivExplicit e A B z) = z := by
    intro A B z
    change (extResEquivExplicit e A B).symm (extResEquivExplicit e A B z) = z
    exact AddEquiv.symm_apply_apply _ _
  refine (extResEquivExplicit e X Z).symm.injective ?_
  rw [extResEquivExplicit_symm_apply, extResEquivExplicit_symm_apply]
  rw [Functor.mapExtAddHom_apply, Functor.mapExtAddHom_apply]
  rw [CategoryTheory.Abelian.Ext.mapExactFunctor_comp,
    CategoryTheory.Abelian.Ext.mapExactFunctor_mk₀]
  rw [key X Y y, key X Z _]

/-- The cast of a morphism of representations along an equality of `Rep` objects acts on elements
by the induced cast of the carriers. -/
theorem rep_ndrec_hom_apply {k : Type} [Semiring k] {G : Type} [Monoid G] {A B Y : Rep k G}
    (h : A = B) (χ : A ⟶ Y) (x : B.V) :
    (h ▸ χ).hom x = χ.hom (cast (congrArg Rep.V h.symm) x) := by
  cases h
  rfl

/-- The `Rep.res`-restriction cast acts trivially on elements. -/
theorem rep_ndrec_hom_apply_of_res {k : Type} [Semiring k] {G G' : Type} [Group G]
    [Group G'] (e : G ≃* G') (M Y : Rep k G')
    (h : Rep.res e.symm.toMonoidHom (Rep.res e.toMonoidHom M) = M)
    (χ : Rep.res e.symm.toMonoidHom (Rep.res e.toMonoidHom M) ⟶ Y) (x : M.V) :
    (h ▸ χ).hom x = χ.hom x := by
  rw [rep_ndrec_hom_apply]
  have hcast : cast (congrArg Rep.V h.symm) x = x := by
    rw [show congrArg Rep.V h.symm = rfl from Subsingleton.elim _ _]
    rfl
  rw [hcast]

/-- `h1Transfer` on `H1π`-classes. -/
theorem h1Transfer_H1π {G G' : Type} [Group G] [TopologicalSpace G] [Group G']
    [TopologicalSpace G'] {M M' : Type} [AddCommGroup M] [DistribMulAction G M]
    [AddCommGroup M'] [DistribMulAction G' M']
    (Φ : G' ≃* G) (hΦ : IsHomeomorph (Φ : G' → G)) (Ψ : M' ≃+ M)
    (hΨ : ∀ (g' : G') (m' : M'), Ψ (g' • m') = Φ g' • Ψ m')
    (f : ↥(Work.AbsoluteKummer.Z1 G' M')) :
    Work.SSGRoute.PT.h1Transfer Φ hΦ Ψ hΨ (Work.AbsoluteKummer.H1π G' M' f)
      = Work.AbsoluteKummer.H1π G M
          (Work.SSGRoute.PT.z1Transfer Φ
            (Work.SSGRoute.PT.continuous_symm_of_isHomeomorph_mulEquiv Φ hΦ) Ψ hΨ f) := by
  show Work.SSGRoute.PT.h1TransferAddHom Φ
      (Work.SSGRoute.PT.continuous_symm_of_isHomeomorph_mulEquiv Φ hΦ) Ψ hΨ
      (Work.AbsoluteKummer.H1π G' M' f) = _
  rw [Work.SSGRoute.PT.h1TransferAddHom_mk]

/-- The model bridge at an equal subgroup is the identity on `toClass`-classes. -/
theorem h1locSubgroupEqEquiv_toClass {k : Type} [Field k] {Ω : Type} [Field Ω] [Algebra k Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    (p : ℕ) [Fact p.Prime] (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    {H H' : Subgroup (Ω ≃ₐ[k] Ω)} (h : H = H') (b : (Ω ≃ₐ[k] Ω) → M) :
    h1locSubgroupEqEquiv p M h (Work.SSGRoute.toClass p k Ω K M H b)
      = Work.SSGRoute.toClass p k Ω K M H' b := by
  cases h
  rfl

/-- The coercion of `(fixingSubgroupEquiv).symm g` is `restrictScalars k g`. -/
theorem fixingSubgroupEquiv_symm_coe_eq_restrictScalars' {k : Type} [Field k] {Ω : Type} [Field Ω]
    [Algebra k Ω] {K : IntermediateField k Ω} (A : ValuationSubring Ω)
    (g : Ω ≃ₐ[↥(decompField k Ω A)] Ω) :
    ((↑((IntermediateField.fixingSubgroupEquiv (decompField k Ω A)).symm g) : Ω ≃ₐ[k] Ω))
      = AlgEquiv.restrictScalars k g :=
  AlgEquiv.ext (fun _ => rfl)

/-- The local valuation is invariant under the decomposition action. -/
theorem valUnitsAddHom_smul_eq (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (σ : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)))
    (y : Additive ((q.adicCompletion ↥K)ˣ)) :
    NK.HassePrinciple.valUnitsAddHom.{0} ↥K q
        ((SSGRoute.PTExt.localUnitsK (k := k) (NK.GlobalCFT.Place.ofFinite q)).ρ σ y)
      = NK.HassePrinciple.valUnitsAddHom.{0} ↥K q y := by
  let u : (q.adicCompletion ↥K)ˣ := Additive.toMul y
  have hy : y = Additive.ofMul u := rfl
  rw [hy]
  have hact : (SSGRoute.PTExt.localUnitsK (k := k) (NK.GlobalCFT.Place.ofFinite q)).ρ σ
      (Additive.ofMul u)
      = Additive.ofMul ((NK.HassePrinciple.localUnitsEquiv (K := k) (L := ↥K)
          (NK.GlobalCFT.Place.ofFinite q) σ) u) := rfl
  exact (congrArg (NK.HassePrinciple.valUnitsAddHom ↥K q) hact).trans
    (congrArg ULift.up (NK.HassePrinciple.adicVal_localUnitsEquiv (K := k) q σ u))

/-- **The equivariance of the valuation along the canonical embedding**: an image of the
coefficient morphism `θ u = Units.map φ u` has the same valuation as `φ u` at every element of
`Gal(K^h/k^h)`. -/
theorem valUnitsAddHom_unitsMap_gal (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [NumberField ↥K] (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (e : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)) ≃*
      (↥(henselOverDecomp k Ω K A) ≃ₐ[↥(decompField k Ω A)] ↥(henselOverDecomp k Ω K A)))
    (θ : Rep.res e.toMonoidHom
          (SSGRoute.PTExt.unitsK ↥(decompField k Ω A) ↥(henselOverDecomp k Ω K A)) ⟶
        SSGRoute.PTExt.localUnitsK (k := k) (NK.GlobalCFT.Place.ofFinite q))
    (φ : ↥(henselOverDecomp k Ω K A) →+*
        NK.GlobalCFT.Place.localField ↥K (NK.GlobalCFT.Place.ofFinite q))
    (hθ : ∀ u : (↥(henselOverDecomp k Ω K A))ˣ,
        Rep.Hom.hom θ (Additive.ofMul u) = Additive.ofMul (Units.map φ.toMonoidHom u)) :
    ∀ (g : ↥(henselOverDecomp k Ω K A) ≃ₐ[↥(decompField k Ω A)]
          ↥(henselOverDecomp k Ω K A)) (x : (↥(henselOverDecomp k Ω K A))ˣ),
      NK.HassePrinciple.valUnitsAddHom.{0} ↥K q
          (Additive.ofMul (Units.map φ.toMonoidHom
            (Units.map (g : _ →+* _).toMonoidHom x)))
        = NK.HassePrinciple.valUnitsAddHom.{0} ↥K q
            (Additive.ofMul (Units.map φ.toMonoidHom x)) := by
  intro g x
  have h1a : (Rep.res e.toMonoidHom (SSGRoute.PTExt.unitsK ↥(decompField k Ω A)
        ↥(henselOverDecomp k Ω K A))).ρ (e.symm g) (Additive.ofMul x)
      = Additive.ofMul (Units.map (g : _ →+* _).toMonoidHom x) := by
    show (SSGRoute.PTExt.unitsK ↥(decompField k Ω A) ↥(henselOverDecomp k Ω K A)).ρ
      (e.toMonoidHom (e.symm g)) (Additive.ofMul x) = _
    rw [show e.toMonoidHom (e.symm g) = g from MulEquiv.apply_symm_apply e g]
    rfl
  have hint : Rep.Hom.hom θ ((Rep.res e.toMonoidHom (SSGRoute.PTExt.unitsK ↥(decompField k Ω A)
        ↥(henselOverDecomp k Ω K A))).ρ (e.symm g) (Additive.ofMul x))
      = (SSGRoute.PTExt.localUnitsK (k := k) (NK.GlobalCFT.Place.ofFinite q)).ρ (e.symm g)
          (Rep.Hom.hom θ (Additive.ofMul x)) :=
    LinearMap.congr_fun
      (Representation.IntertwiningMap.isIntertwining' (Rep.Hom.hom θ) (e.symm g))
      (Additive.ofMul x)
  have h2 : Additive.ofMul (Units.map φ.toMonoidHom (Units.map (g : _ →+* _).toMonoidHom x))
      = (SSGRoute.PTExt.localUnitsK (k := k) (NK.GlobalCFT.Place.ofFinite q)).ρ (e.symm g)
          (Additive.ofMul (Units.map φ.toMonoidHom x)) :=
    (hθ (Units.map (g : _ →+* _).toMonoidHom x)).symm.trans
      ((congrArg (Rep.Hom.hom θ) h1a.symm).trans
        (hint.trans (congrArg
          ((SSGRoute.PTExt.localUnitsK (k := k) (NK.GlobalCFT.Place.ofFinite q)).ρ (e.symm g))
          (hθ x))))
  have h3 := congrArg (NK.HassePrinciple.valUnitsAddHom ↥K q) h2
  rw [h3]
  exact valUnitsAddHom_smul_eq k Ω K q (e.symm g)
    (Additive.ofMul (Units.map φ.toMonoidHom x))

theorem phiCan_unramified (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (hAq : ∀ x : NumberField.RingOfIntegers ↥K,
      x ∈ q.asIdeal ↔ A.valuation (((x : ↥K) : Ω)) < 1)
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
    (φ : ↥(henselOverDecomp k Ω K A) →+*
        NK.GlobalCFT.Place.localField ↥K (NK.GlobalCFT.Place.ofFinite q))
    (hθ : ∀ u : (↥(henselOverDecomp k Ω K A))ˣ,
        Rep.Hom.hom θ (Additive.ofMul u) = Additive.ofMul (Units.map φ.toMonoidHom u))
    (hφ : ∀ x : ↥K, φ ⟨(x : Ω), le_henselField k Ω K A x.2⟩ =
        algebraMap ↥K (NK.GlobalCFT.Place.localField ↥K (NK.GlobalCFT.Place.ofFinite q)) x)
    (hφint : ∀ x : (↥(henselOverDecomp k Ω K A))ˣ,
        Units.map φ.toMonoidHom x ∈ NK.GlobalCFT.Place.localUnits ↥K (NK.GlobalCFT.Place.ofFinite q)
          ↔ A.valuation (((x : ↥(henselOverDecomp k Ω K A)) : Ω)) = 1) :
    ¬ A.valuation (p : Ω) < 1 → ¬ SSGRoute.IsRamifiedIn k K A →
      ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
        [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E] (b : (Ω ≃ₐ[k] Ω) → E),
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
        SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
        (∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k A σ → b σ = 0) →
        SSGRoute.PTExt.IsUnramifiedExt (NK.GlobalCFT.Place.ofFinite q)
          (phiCan p k Ω K ζ hζ hζK T hT A hA q hAq e hφres θ hpush E
            (Work.SSGRoute.toClass p k Ω K E (SSGRoute.decomp k A) b)) := by
  intro hp hram E _ _ _ _ _ b hb hl hInertia
  rw [Work.SSGRoute.ValuationSES.isUnramifiedExt_iff_comp_valHom]
  classical
  haveI hGal : IsGalois k Ω := IsAlgClosure.isGalois k Ω
  haveI hAlg : IsAlgClosure ↥(decompField k Ω A) Ω := decompField_isAlgClosure_via k Ω K A rfl
  haveI hFd : FiniteDimensional ↥(decompField k Ω A) ↥(henselOverDecomp k Ω K A) :=
    henselOverDecomp_finiteDimensional k Ω K A
  haveI hGl : IsGalois ↥(decompField k Ω A) ↥(henselOverDecomp k Ω K A) :=
    henselOverDecomp_isGalois k Ω K A
  haveI hChar : CharZero ↥(decompField k Ω A) := inferInstance
  let H' : Subgroup (Ω ≃ₐ[k] Ω) := (decompField k Ω A).fixingSubgroup
  have hfix : H' = SSGRoute.decomp k A := decompField_fixingSubgroup_via k Ω K A rfl
  haveI hTfin : Finite T := Work.SSGRoute.ExtChain.e1aFiniteT p k Ω K ζ T hT
  haveI hDfin : Finite (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)) :=
    Work.SSGRoute.PT.finite_dualMod_tensor p E T
  let X : Rep.{0} Coeff (K ≃ₐ[k] K) :=
    SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))
  let XD : Rep.{0} Coeff ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)) :=
    Rep.res (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype X
  let R₂ : Rep.{0} Coeff (↥(henselOverDecomp k Ω K A) ≃ₐ[↥(decompField k Ω A)]
      ↥(henselOverDecomp k Ω K A)) := Rep.res e.symm.toMonoidHom XD
  haveI hXfin : Module.Finite ℤ X.V := by
    change Module.Finite ℤ (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))
    exact Module.Finite.of_finite
  haveI hR₂fin : Module.Finite ℤ R₂.V := hXfin
  haveI hXf : Finite (X : Type) := by
    change Finite (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))
    exact hDfin
  let Φd : E ≃+ Work.SSGRoute.homCoind k Ω K X :=
    Work.SSGRoute.ExtChain.e1aCoeffNat p k Ω K ζ hζ hζK T hT E
  haveI hEfin : Finite E := inferInstance
  letI hGammaE : DistribMulAction (Ω ≃ₐ[k] Ω) E := DistribMulAction.compHom E (SSGRoute.res k K)
  have hΦ : Work.GroupCohomology.IsEquivariant H'
      (Φd.toAddMonoidHom : E →+ Work.SSGRoute.homCoind k Ω K X) :=
    fun h' e => Work.SSGRoute.ExtChain.e1aCoeffNat_equivariant p k Ω K ζ hζ hζK T hT E
      (h' : Ω ≃ₐ[k] Ω) e
  have hΨ : Work.GroupCohomology.IsEquivariant H'
      (Φd.symm.toAddMonoidHom : Work.SSGRoute.homCoind k Ω K X →+ E) :=
    fun h' n => Work.SSGRoute.ExtChain.e1aCoeffNat_symm_equivariant p k Ω K ζ hζ hζK T hT E
      (h' : Ω ≃ₐ[k] Ω) n
  let U : Rep.{0} Coeff (↥(henselOverDecomp k Ω K A) ≃ₐ[↥(decompField k Ω A)]
      ↥(henselOverDecomp k Ω K A)) :=
    SSGRoute.PTExt.unitsK ↥(decompField k Ω A) ↥(henselOverDecomp k Ω K A)
  let Yl : Rep.{0} Coeff ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)) :=
    Rep.res e.toMonoidHom U
  let x₀ : Work.SSGRoute.H1loc p k Ω K E (SSGRoute.decomp k A) :=
    Work.SSGRoute.toClass p k Ω K E (SSGRoute.decomp k A) b
  have hbC : b ∈ Work.SSGRoute.lcCocycles p k Ω K E H' := ⟨hfix.symm ▸ hb, hfix.symm ▸ hl⟩
  let z₁ : ↥(Work.SSGRoute.lcCocycles p k Ω K E H') := ⟨b, hbC⟩
  let x₁ : Work.SSGRoute.H1loc p k Ω K E H' := h1locSubgroupEqEquiv p E hfix.symm x₀
  let x₂ : Work.AbsoluteKummer.H1 ↥H' E :=
    Work.SSGRoute.H1locEquivH1 p k Ω K E H' (fun h m => rfl) x₁
  let x₃ : Work.AbsoluteKummer.H1 ↥H' (Work.SSGRoute.homCoind k Ω K X) :=
    Work.SSGRoute.H1Equiv.h1AddEquiv Φd hΦ hΨ x₂
  let x₄ : Work.AbsoluteKummer.H1 (Ω ≃ₐ[↥(decompField k Ω A)] Ω)
      (Work.SSGRoute.homCoind ↥(decompField k Ω A) Ω (henselOverDecomp k Ω K A)
        (Rep.res (levelTwoGroupHom k Ω K A hA q hAq e) X)) :=
    levelChangeTransferD p k Ω K A X (levelTwoGroupHom k Ω K A hA q hAq e) hφres x₃
  have hx₂ : x₂ = Work.AbsoluteKummer.H1π ↥H' E
      (Work.SSGRoute.restrictCocycle p k Ω K E H' (fun h m => rfl) z₁) := by
    dsimp only [x₂, x₁, x₀]
    rw [h1locSubgroupEqEquiv_toClass p E hfix.symm b]
    dsimp only [Work.SSGRoute.H1locEquivH1]
    rw [Work.SSGRoute.toClass, dif_pos hbC, Submodule.mkQ_apply]
    exact Work.SSGRoute.E1aClean.bridgeFwd_mk p k Ω K E H' (fun h m => rfl) z₁
  have hx₃ : x₃ = Work.AbsoluteKummer.H1π ↥H' (Work.SSGRoute.homCoind k Ω K X)
      (Work.AbsoluteKummer.mapZ1 Φd.toAddMonoidHom hΦ
        (Work.SSGRoute.restrictCocycle p k Ω K E H' (fun h m => rfl) z₁)) := by
    dsimp only [x₃]
    rw [hx₂]
    change Work.AbsoluteKummer.mapH1 Φd.toAddMonoidHom hΦ
      (Work.AbsoluteKummer.H1π ↥H' E
        (Work.SSGRoute.restrictCocycle p k Ω K E H' (fun h m => rfl) z₁)) = _
    rw [Work.AbsoluteKummer.mapH1_H1π]
  let c₁ : ↥(Work.AbsoluteKummer.Z1 ↥H' (Work.SSGRoute.homCoind k Ω K X)) :=
    Work.AbsoluteKummer.mapZ1 Φd.toAddMonoidHom hΦ
      (Work.SSGRoute.restrictCocycle p k Ω K E H' (fun h m => rfl) z₁)
  let χ₀ : Rep.res e.symm.toMonoidHom (Rep.res e.toMonoidHom U) ⟶
      Rep.res e.symm (SSGRoute.PTExt.unitRep
        (↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)))) :=
    Rep.resMap e.symm.toMonoidHom (θ ≫
      NK.HassePrinciple.localUnitsValHom (K := k) (L := ↥K) q)
  let Z₀ : Rep.{0} Coeff ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)) :=
    SSGRoute.PTExt.unitRep (↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)))
  let μ₀ := (res_comp_symm_self e (SSGRoute.PTExt.unitsK ↥(decompField k Ω A) ↥(henselOverDecomp k Ω K A))) ▸ χ₀
  let c₂ : ↥(Work.AbsoluteKummer.Z1 (Ω ≃ₐ[↥(decompField k Ω A)] Ω)
      (Work.SSGRoute.homCoind ↥(decompField k Ω A) Ω (henselOverDecomp k Ω K A)
        (Rep.res (levelTwoGroupHom k Ω K A hA q hAq e) X))) :=
    Work.SSGRoute.PT.z1Transfer (IntermediateField.fixingSubgroupEquiv (decompField k Ω A))
      (Work.SSGRoute.PT.continuous_symm_of_isHomeomorph_mulEquiv
        (IntermediateField.fixingSubgroupEquiv (decompField k Ω A))
        (Work.SSGRoute.PTembedding.isHomeomorph_fixingSubgroupEquiv (decompField k Ω A)))
      (levelTwoCoeffEquiv A X (levelTwoGroupHom k Ω K A hA q hAq e))
      (by
        intro g' m'
        rw [Subgroup.smul_def]
        convert (Work.SSGRoute.E1aClean.homCoind_levelChange_smul A X
          (levelTwoGroupHom k Ω K A hA q hAq e) hφres
          ((IntermediateField.fixingSubgroupEquiv (decompField k Ω A)) g') m').symm using 1
        · rw [show ((↑g' : Ω ≃ₐ[k] Ω))
              = AlgEquiv.restrictScalars k
                ((IntermediateField.fixingSubgroupEquiv (decompField k Ω A)) g') from
              AlgEquiv.ext (fun x => rfl)]
          rfl
        · rfl)
      c₁
  let x₅ : CategoryTheory.Abelian.Ext R₂ U 1 :=
    (Work.SSGRoute.ExtChain.E1cGeneric.e1cEquiv (k := ↥(decompField k Ω A))
      (Ω := Ω) (K := henselOverDecomp k Ω K A) R₂).symm x₄
  let x₆ : CategoryTheory.Abelian.Ext R₂ (Rep.res e.symm.toMonoidHom (Rep.res e.toMonoidHom U)) 1 :=
    (Eq.mp (congrArg (fun S => CategoryTheory.Abelian.Ext R₂ U 1 ≃+
      CategoryTheory.Abelian.Ext R₂ S 1) (res_comp_symm_self e (SSGRoute.PTExt.unitsK ↥(decompField k Ω A) ↥(henselOverDecomp k Ω K A))).symm) (AddEquiv.refl _)) x₅
  let x₇ : CategoryTheory.Abelian.Ext XD Yl 1 := extResEquivExplicit e XD Yl x₆
  let y : CategoryTheory.Abelian.Ext XD
      (SSGRoute.PTExt.localUnitsK (k := k) (NK.GlobalCFT.Place.ofFinite q)) 1 :=
    (AddEquiv.ofBijective
        ((CategoryTheory.Abelian.Ext.mk₀ θ).postcomp XD (add_zero 1)) (hpush E)) x₇
  change y.comp (CategoryTheory.Abelian.Ext.mk₀
      (NK.HassePrinciple.localUnitsValHom (K := k) (L := ↥K) q)) (add_zero 1) = 0
  dsimp only [y]
  rw [AddEquiv.ofBijective_apply, Work.SSGRoute.E1aClean.postcomp_mk₀_comp_mk₀]
  dsimp only [x₇]
  rw [extResEquivExplicit_comp_post]
  rw [(extResEquivExplicit e XD
        (SSGRoute.PTExt.unitRep ↥(SSGRoute.PTExt.decompK (k := k)
          (NK.GlobalCFT.Place.ofFinite q)))).map_eq_zero_iff]
  dsimp only [x₆]
  rw [Work.SSGRoute.E1aClean.eq_mp_congrArg_refl_apply_ext (h := (res_comp_symm_self e (SSGRoute.PTExt.unitsK ↥(decompField k Ω A) ↥(henselOverDecomp k Ω K A))).symm),
    Work.SSGRoute.E1aClean.ext_ndrec_comp_mk₀ (h := (res_comp_symm_self e (SSGRoute.PTExt.unitsK ↥(decompField k Ω A) ↥(henselOverDecomp k Ω K A))).symm)]
  dsimp only [x₅, x₄]
  rw [show x₃ = Work.AbsoluteKummer.H1π ↥H' (Work.SSGRoute.homCoind k Ω K X) c₁ from hx₃]
  simp only [Work.SSGRoute.E1aClean.levelChangeTransferD]
  rw [h1Transfer_H1π]
  refine e1cHensel_comp_val_eq_zero_of_unramified p k Ω K ζ hζ hζK A hA q hAq hp
    φ hφ hφint ?_ μ₀ ?_ R₂ ?_ c₂ ?_
  · exact valUnitsAddHom_unitsMap_gal k Ω K A hA q e θ φ hθ
  · intro x
    dsimp only [μ₀]
    refine (rep_ndrec_hom_apply_of_res e U (Rep.res e.symm Z₀)
      (res_comp_symm_self e U) χ₀ (Additive.ofMul x)).trans ?_
    dsimp only [χ₀]
    change (Rep.Hom.hom (θ ≫ NK.HassePrinciple.localUnitsValHom (K := k) (L := ↥K) q))
      (Additive.ofMul x) = _
    change (NK.HassePrinciple.localUnitsValHom (K := k) (L := ↥K) q).hom
      (Rep.Hom.hom θ (Additive.ofMul x)) = _
    rw [hθ]
    rfl
  · intro r
    rw [show (p : ℤ) • r = p • r from Nat.cast_smul_eq_nsmul ℤ p r]
    exact Work.SSGRoute.E1aClean.dualMod_p_smul_eq_zero p (TensorProduct (ZMod p) E T) r
  · intro g hg
    dsimp only [c₂]
    rw [Work.SSGRoute.PT.z1Transfer_coe, Work.SSGRoute.PT.cochainTransfer_apply]
    change (c₁ : ↥H' → Work.SSGRoute.homCoind k Ω K X)
        ((IntermediateField.fixingSubgroupEquiv (decompField k Ω A)).symm g) = 0
    have hval : (c₁ : ↥H' → Work.SSGRoute.homCoind k Ω K X)
        ((IntermediateField.fixingSubgroupEquiv (decompField k Ω A)).symm g)
        = Φd (b (AlgEquiv.restrictScalars k g)) := by
      rw [show (c₁ : ↥H' → Work.SSGRoute.homCoind k Ω K X)
            ((IntermediateField.fixingSubgroupEquiv (decompField k Ω A)).symm g)
          = Φd (b (((IntermediateField.fixingSubgroupEquiv (decompField k Ω A)).symm g)
              : Ω ≃ₐ[k] Ω)) from rfl]
      rw [fixingSubgroupEquiv_symm_coe_eq_restrictScalars' (K := K) A g]
    rw [hval]
    rw [hInertia _ hg, map_zero]

end Work.SSGRoute.E1aClean.LeadPhiUnr

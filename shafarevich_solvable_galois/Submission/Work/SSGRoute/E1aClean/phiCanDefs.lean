import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.E1aClean.finPlaceDict
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The definable finite-place dictionary chain `Φcan`

Per the lead's ruling `_lead_design/ssg_natwit_0820.md` §(c) FIN.  See the header of
`E1aClean/finPlaceDict.lean` for the design; this file contains the chain itself and, below it, the
statements of the three clauses (`naturality`, `square`, `unramified`) that constitute
`LeadNatWit.FinPlaceDict`.
-/

namespace Work.SSGRoute.E1aClean

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct

-- the `Γ`-action on `homCoind` is not a global instance (see `ext_h1_bridge.lean`)
attribute [local instance 10000] Work.SSGRoute.homCoind.instDistribMulActionAlgEquiv

noncomputable section

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- Restricting a representation along `e.toMonoidHom` and then along `e.symm.toMonoidHom` gives it
back. -/
theorem res_comp_symm_self {k : Type} [Semiring k] {G G' : Type} [Group G] [Group G']
    (e : G ≃* G') (M : Rep k G') :
    Rep.res e.symm.toMonoidHom (Rep.res e.toMonoidHom M) = M := by
  have hcomp : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id G' := by
    ext x
    simp
  show Rep.of (X := M.V) ((M.ρ.comp e.toMonoidHom).comp e.symm.toMonoidHom) = M
  rw [MonoidHom.comp_assoc, hcomp, MonoidHom.comp_id]

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  [NumberField K]
variable (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
variable (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
variable (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)

/-- **The definable finite-place dictionary chain** of the lead's ruling §(c) FIN. -/
noncomputable def phiCan
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
          (add_zero 1))) :
    ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
      [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E],
      Work.SSGRoute.H1loc p k Ω K E (SSGRoute.decomp k A) ≃+ localExt p k Ω K T A q E := by
  intro E _ _ _ _ _
  classical
  -- ## the datum instances
  haveI hGal : IsGalois k Ω := IsAlgClosure.isGalois k Ω
  haveI hAlg : IsAlgClosure ↥(decompField k Ω A) Ω := decompField_isAlgClosure_via k Ω K A rfl
  haveI hFd : FiniteDimensional ↥(decompField k Ω A) ↥(henselOverDecomp k Ω K A) :=
    henselOverDecomp_finiteDimensional k Ω K A
  haveI hGl : IsGalois ↥(decompField k Ω A) ↥(henselOverDecomp k Ω K A) :=
    henselOverDecomp_isGalois k Ω K A
  haveI hChar : CharZero ↥(decompField k Ω A) := inferInstance
  set H' : Subgroup (Ω ≃ₐ[k] Ω) := (decompField k Ω A).fixingSubgroup with hH'def
  have hfix : H' = SSGRoute.decomp k A := decompField_fixingSubgroup_via k Ω K A rfl
  -- ## the coefficient representations
  haveI hTfin : Finite T := Work.SSGRoute.ExtChain.e1aFiniteT p k Ω K ζ T hT
  haveI hDfin : Finite (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)) :=
    Work.SSGRoute.PT.finite_dualMod_tensor p E T
  let X : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) :=
    SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))
  haveI hXfin : Module.Finite ℤ X.V := by
    change Module.Finite ℤ (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))
    exact Module.Finite.of_finite
  let XD : Rep.{0} SSGRoute.PTExt.Coeff ↥(SSGRoute.PTExt.decompK (k := k)
      (NK.GlobalCFT.Place.ofFinite q)) :=
    Rep.res (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype X
  let R₂ : Rep.{0} SSGRoute.PTExt.Coeff (↥(henselOverDecomp k Ω K A) ≃ₐ[↥(decompField k Ω A)]
      ↥(henselOverDecomp k Ω K A)) := Rep.res e.symm.toMonoidHom XD
  haveI hR₂fin : Module.Finite ℤ R₂.V := hXfin
  haveI hXf : Finite (X : Type) := by
    change Finite (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))
    exact hDfin
  -- ## the coefficient transport
  let Φd : E ≃+ Work.SSGRoute.homCoind k Ω K X :=
    Work.SSGRoute.ExtChain.e1aCoeffNat p k Ω K ζ hζ hζK T hT E
  have hEfin : Finite E := inferInstance
  letI hGammaE : DistribMulAction (Ω ≃ₐ[k] Ω) E := DistribMulAction.compHom E (SSGRoute.res k K)
  have hΦ : Work.GroupCohomology.IsEquivariant H'
      (Φd.toAddMonoidHom : E →+ Work.SSGRoute.homCoind k Ω K X) :=
    fun h' e => Work.SSGRoute.ExtChain.e1aCoeffNat_equivariant p k Ω K ζ hζ hζK T hT E
      (h' : Ω ≃ₐ[k] Ω) e
  have hΨ : Work.GroupCohomology.IsEquivariant H'
      (Φd.symm.toAddMonoidHom : Work.SSGRoute.homCoind k Ω K X →+ E) :=
    fun h' n => Work.SSGRoute.ExtChain.e1aCoeffNat_symm_equivariant p k Ω K ζ hζ hζK T hT E
      (h' : Ω ≃ₐ[k] Ω) n
  -- ## the chain
  refine (h1locSubgroupEqEquiv p E hfix.symm).trans ?_
  refine (Work.SSGRoute.H1locEquivH1 p k Ω K E H' (fun h m => rfl)).trans ?_
  refine (Work.SSGRoute.H1Equiv.h1AddEquiv Φd hΦ hΨ).trans ?_
  refine (levelChangeTransferD p k Ω K A X
    (levelTwoGroupHom k Ω K A hA q hAq e) hφres).trans ?_
  refine (Work.SSGRoute.ExtChain.E1cGeneric.e1cEquiv (k := ↥(decompField k Ω A))
    (Ω := Ω) (K := henselOverDecomp k Ω K A) R₂).symm.trans ?_
  have hY : Rep.res e.symm.toMonoidHom (Rep.res e.toMonoidHom
      (SSGRoute.PTExt.unitsK ↥(decompField k Ω A) ↥(henselOverDecomp k Ω K A)))
      = SSGRoute.PTExt.unitsK ↥(decompField k Ω A) ↥(henselOverDecomp k Ω K A) :=
    res_comp_symm_self e _
  refine (Eq.mp (congrArg (fun S => CategoryTheory.Abelian.Ext R₂
      (SSGRoute.PTExt.unitsK ↥(decompField k Ω A) ↥(henselOverDecomp k Ω K A)) 1 ≃+
      CategoryTheory.Abelian.Ext R₂ S 1) hY.symm) (AddEquiv.refl _)).trans ?_
  refine (extResEquivExplicit e XD (Rep.res e.toMonoidHom
    (SSGRoute.PTExt.unitsK ↥(decompField k Ω A) ↥(henselOverDecomp k Ω K A)))).trans ?_
  exact AddEquiv.ofBijective
    ((CategoryTheory.Abelian.Ext.mk₀ θ).postcomp XD (add_zero 1)) (hpush E)


/-- **Factor 1 of `phiCan`, named** (`E`-indexed, additive: `phiCan` untouched).  The bridge
`H1loc(D_A,E) ≃+ H¹(↥((k^h).fixingSubgroup), E)` — `phiCan`'s first two steps.  The subgroup action that
the *type* needs is the binder `[DistribMulAction (Ω ≃ₐ[k] Ω) E]` (a call site passes
`DistribMulAction.compHom E (SSGRoute.res k K)`), and `hcomp` records the action law that the body's
`letI` made definitional — callers supply `hcomp := fun _ _ => rfl`. -/
noncomputable def phiCanBridge (E : Type) [AddCommGroup E] [Module (ZMod p) E]
    [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    [DistribMulAction (Ω ≃ₐ[k] Ω) E]
    (hcomp : ∀ (g : Ω ≃ₐ[k] Ω) (m : E), g • m = SSGRoute.res k K g • m)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (hAq : ∀ x : NumberField.RingOfIntegers ↥K,
      x ∈ q.asIdeal ↔ A.valuation (((x : ↥K) : Ω)) < 1) :
    Work.SSGRoute.H1loc p k Ω K E (SSGRoute.decomp k A) ≃+
      Work.AbsoluteKummer.H1 ↥((decompField k Ω A).fixingSubgroup) E :=
  (h1locSubgroupEqEquiv p E (decompField_fixingSubgroup_via k Ω K A rfl).symm).trans
    (Work.SSGRoute.H1locEquivH1 p k Ω K E _ (fun h m => hcomp (h : Ω ≃ₐ[k] Ω) m))

attribute [local instance 10000] Rep.hV2 Rep.hV1 Submodule.module

/-- **Factor 2 of `phiCan`, named** (`E`-indexed, additive: `phiCan` untouched).  The coefficient
transport at the decomposition subgroup, at the same `Φd = e1aCoeffNat … E` that `globalDictionaryCanon`
uses.  `hcomp` records the action law the body's `letI` made definitional (callers pass
`fun _ _ => rfl`), and the two equivariances use it in *opposite* directions. -/
noncomputable def phiCanCoeff
    (A : ValuationSubring Ω)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    [DistribMulAction (Ω ≃ₐ[k] Ω) E]
    (hcomp : ∀ (g : Ω ≃ₐ[k] Ω) (m : E), g • m = SSGRoute.res k K g • m) :
    Work.AbsoluteKummer.H1 ↥((decompField k Ω A).fixingSubgroup) E ≃+
      Work.AbsoluteKummer.H1 ↥((decompField k Ω A).fixingSubgroup)
        (Work.SSGRoute.homCoind k Ω K
          (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)))) := by
  classical
  let X : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) :=
    SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))
  let Φd : E ≃+ Work.SSGRoute.homCoind k Ω K X :=
    Work.SSGRoute.ExtChain.e1aCoeffNat p k Ω K ζ hζ hζK T hT E
  have hΦ : Work.GroupCohomology.IsEquivariant ↥((decompField k Ω A).fixingSubgroup)
      Φd.toAddMonoidHom :=
    fun h e => by
      show Φd ((h : Ω ≃ₐ[k] Ω) • e) = (h : Ω ≃ₐ[k] Ω) • Φd e
      rw [hcomp (h : Ω ≃ₐ[k] Ω) e]
      exact Work.SSGRoute.ExtChain.e1aCoeffNat_equivariant p k Ω K ζ hζ hζK T hT E
        (h : Ω ≃ₐ[k] Ω) e
  have hΨ : Work.GroupCohomology.IsEquivariant ↥((decompField k Ω A).fixingSubgroup)
      Φd.symm.toAddMonoidHom :=
    fun h n => by
      show Φd.symm ((h : Ω ≃ₐ[k] Ω) • n) = (h : Ω ≃ₐ[k] Ω) • Φd.symm n
      rw [hcomp (h : Ω ≃ₐ[k] Ω) (Φd.symm n)]
      exact Work.SSGRoute.ExtChain.e1aCoeffNat_symm_equivariant p k Ω K ζ hζ hζK T hT E
        (h : Ω ≃ₐ[k] Ω) n
  exact Work.SSGRoute.H1Equiv.h1AddEquiv Φd hΦ hΨ

end

end Work.SSGRoute.E1aClean

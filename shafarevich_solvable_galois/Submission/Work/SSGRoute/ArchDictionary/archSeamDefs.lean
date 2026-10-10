import Mathlib.GroupTheory.Nilpotent
import Mathlib.RepresentationTheory.Coinduced
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.ArchDictionary.archPhiP2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Seam definitions for the complex place, `p = 2` (lead design archp2_1008)

COPY-READY module: install verbatim as
`Submission/Work/SSGRoute/ArchDictionary/archSeamDefs.lean` (sorry-free, axiom-clean).

* `seamUnits` — `Ωˣ → K_wˣ`, `φ` followed by a choice of `ℂ ≃ K_w` extending the completion map;
* `seamCoeffLoc` — the LOCAL coefficient identification, the seam-push of the GLOBAL opaque
  `ExtChain.e1aCoeffNat` (NOT `localCoeffP2`: see `_lead_design/archp2_1008/ARCHP2_PLAN.md` §2);
* `archPhiOf` — `acH1Equiv ≫ cycTransfer ≫ mapH1 Ψ ≫ (NatH1.eOf)⁻¹` for an arbitrary equivariant
  coefficient equivalence `Ψ` (L4446's `archPhiDef` with the coefficient a parameter);
* `isEquivariant_symm`.
-/

namespace Work.SSGRoute.ArchDictionary.ArchSeamP2

open CategoryTheory CategoryTheory.Limits SSGRoute.PTExt Work.SSGRoute.ArchDictionary

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]

/-- **The seam on units** `Ωˣ → K_wˣ`: `φ` followed by (a choice of) `ℂ ≃ K_w` extending the
completion map on `K`.  Its values on `μ₂` do not depend on the choice. -/
noncomputable def seamUnits (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (φ : Ω →+* ℂ)
    (hlink : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x)) (w : NK.GlobalCFT.Place ↥K)
    (hw : w = NK.GlobalCFT.Place.ofInfinite
      (NumberField.InfinitePlace.mk (φ.comp (algebraMap ↥K Ω))))
    (hne : decompK (k := k) w ≠ ⊥) :
    Ωˣ →* (NK.GlobalCFT.Place.localField ↥K w)ˣ :=
  Units.map ((Classical.choose (unitsToLocalUnitsHom_eq_embedding 2 k Ω K c hc2 hc1 φ hlink w hw
    hne)).symm.toRingHom.comp φ).toMonoidHom

/-- `seamUnits` extends the completion map `Kˣ → K_wˣ` (PROVED). -/
theorem seamUnits_on_K (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (φ : Ω →+* ℂ)
    (hlink : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x)) (w : NK.GlobalCFT.Place ↥K)
    (hw : w = NK.GlobalCFT.Place.ofInfinite
      (NumberField.InfinitePlace.mk (φ.comp (algebraMap ↥K Ω))))
    (hne : decompK (k := k) w ≠ ⊥) (x : (↥K)ˣ) :
    seamUnits c hc2 hc1 φ hlink w hw hne (Units.map (algebraMap ↥K Ω).toMonoidHom x)
      = NK.HassePrinciple.unitsToLocalUnitsHom w x := by
  have he := Classical.choose_spec (unitsToLocalUnitsHom_eq_embedding 2 k Ω K c hc2 hc1 φ hlink
    w hw hne)
  set e := Classical.choose (unitsToLocalUnitsHom_eq_embedding 2 k Ω K c hc2 hc1 φ hlink w hw hne)
  apply Units.ext
  show e.symm (φ (algebraMap ↥K Ω (x : ↥K))) = _
  rw [← he x, RingEquiv.symm_apply_apply]

/-- **The local coefficient identification, seam-push of the global `e1aCoeffNat`.**
`Ψ_loc e := seamUnits ∘ e1aCoeffNat e : E'.V → K_wˣ`. -/
noncomputable def seamCoeffLoc (T : Type) [AddCommGroup T] [Module (ZMod 2) T]
    [DistribMulAction (K ≃ₐ[k] K) T] [SMulCommClass (K ≃ₐ[k] K) (ZMod 2) T]
    (hζ : IsPrimitiveRoot (-1 : Ω) 2) (hζK : (-1 : Ω) ∈ K)
    (hT : SSGRoute.IsCyclotomicDual 2 (T := T) (SSGRoute.res k K) (-1 : Ω))
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (φ : Ω →+* ℂ)
    (hlink : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x)) (w : NK.GlobalCFT.Place ↥K)
    (hw : w = NK.GlobalCFT.Place.ofInfinite
      (NumberField.InfinitePlace.mk (φ.comp (algebraMap ↥K Ω))))
    (hne : decompK (k := k) w ≠ ⊥)
    (E : Type) [AddCommGroup E] [Module (ZMod 2) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod 2) E] [Finite E] :
    E →+ ((Eprime 2 k Ω K T E).V →ₗ[Coeff] (localUnitsK (k := k) w).V) :=
  ((Work.SSGRoute.linAddEquiv (Eprime 2 k Ω K T E).V
      (Additive (NK.GlobalCFT.Place.localField ↥K w)ˣ)).symm.toAddMonoidHom).comp
    ((AddMonoidHom.compHom
        (MonoidHom.toAdditive (seamUnits c hc2 hc1 φ hlink w hw hne))).comp
      (Work.SSGRoute.ExtChain.e1aCoeffNat 2 k Ω K (-1) hζ hζK T hT E).toAddMonoidHom)

/-- **The canonical composite with an arbitrary equivariant coefficient identification**
(L4446's `archPhiDef`, with `localCoeffP2` replaced by the parameter `Ψ`). -/
noncomputable def archPhiOf (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1)
    (φ : Ω →+* ℂ) (hlink : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
    (w : NK.GlobalCFT.Place ↥K)
    (hw : w = NK.GlobalCFT.Place.ofInfinite
      (NumberField.InfinitePlace.mk (φ.comp (algebraMap ↥K Ω))))
    (hne : decompK (k := k) w ≠ ⊥)
    (E : Type) [AddCommGroup E] [DistribMulAction (K ≃ₐ[k] K) E]
    (M : Rep.{0} Coeff ↥(decompK (k := k) w))
    (Ψ : E ≃+ (M.V →ₗ[Coeff] (localUnitsK (k := k) w).V))
    (hΦ : @Work.GroupCohomology.IsEquivariant ↥(decompK (k := k) w) E
      (M.V →ₗ[Coeff] (localUnitsK (k := k) w).V) _ _ _ (dcAct K E w)
      (Work.SSGRoute.homRepDistribMulAction M (localUnitsK (k := k) w)) Ψ.toAddMonoidHom)
    (hΨ : @Work.GroupCohomology.IsEquivariant ↥(decompK (k := k) w)
      (M.V →ₗ[Coeff] (localUnitsK (k := k) w).V) E _ _ _
      (Work.SSGRoute.homRepDistribMulAction M (localUnitsK (k := k) w)) (dcAct K E w)
      Ψ.symm.toAddMonoidHom) :
    Ac (K := K) (E := E) c ≃+ Abelian.Ext M (localUnitsK (k := k) w) 1 := by
  have hdiv := localUnitsK_divisible_of_decompK_ne_bot (k := k) (Ω := Ω) (K := K) φ w hw hne
  let eD : Abelian.Ext M (localUnitsK (k := k) w) 1 ≃+
      Work.SSGRoute.homH1 ↥(decompK (k := k) w) M (localUnitsK (k := k) w) :=
    NatH1.eOf (N := localUnitsK (k := k) w)
      (moduleInjective_coeff_of_divisible _
        (show ∀ (n : ℕ), 0 < n → ∀ y : (localUnitsK (k := k) w).V,
          ∃ x : (localUnitsK (k := k) w).V, n • x = y from hdiv))
      (fun M => Classical.choose (homRepFree_coind_iso _ M.V _))
      (fun M => Classical.choose_spec (homRepFree_coind_iso _ M.V _)) M
  let coeHom : @Work.GroupCohomology.H1 ↥(decompK (k := k) w) E _ _ (dcAct K E w) →+
      Work.SSGRoute.homH1 ↥(decompK (k := k) w) M (localUnitsK (k := k) w) :=
    @Work.GroupCohomology.mapH1 ↥(decompK (k := k) w) E
      (M.V →ₗ[Coeff] (localUnitsK (k := k) w).V) _ _ _ (dcAct K E w)
      (Work.SSGRoute.homRepDistribMulAction M (localUnitsK (k := k) w)) Ψ.toAddMonoidHom hΦ
  let coeHomInv : Work.SSGRoute.homH1 ↥(decompK (k := k) w) M (localUnitsK (k := k) w) →+
      @Work.GroupCohomology.H1 ↥(decompK (k := k) w) E _ _ (dcAct K E w) :=
    @Work.GroupCohomology.mapH1 ↥(decompK (k := k) w)
      (M.V →ₗ[Coeff] (localUnitsK (k := k) w).V) E _ _ _
      (Work.SSGRoute.homRepDistribMulAction M (localUnitsK (k := k) w)) (dcAct K E w)
      Ψ.symm.toAddMonoidHom hΨ
  have hcoe : Ψ.symm.toAddMonoidHom.comp Ψ.toAddMonoidHom = AddMonoidHom.id E :=
    AddMonoidHom.ext fun x => Ψ.symm_apply_apply x
  have hcoe' : Ψ.toAddMonoidHom.comp Ψ.symm.toAddMonoidHom = AddMonoidHom.id _ :=
    AddMonoidHom.ext fun y => Ψ.apply_symm_apply y
  have hleft : ∀ x, coeHomInv (coeHom x) = x := by
    intro x
    change (coeHomInv.comp coeHom) x = x
    simp only [coeHomInv, coeHom]
    rw [← Work.GroupCohomology.mapH1_comp]
    simp only [hcoe, Work.GroupCohomology.mapH1_id]
    rfl
  have hright : ∀ y, coeHom (coeHomInv y) = y := by
    intro y
    change (coeHom.comp coeHomInv) y = y
    simp only [coeHomInv, coeHom]
    rw [← Work.GroupCohomology.mapH1_comp]
    simp only [hcoe', Work.GroupCohomology.mapH1_id]
    rfl
  let coeff := AddEquiv.ofBijective coeHom
      ⟨fun x y hxy => (hleft x).symm.trans ((congrArg coeHomInv hxy).trans (hleft y)),
       fun y => ⟨coeHomInv y, hright y⟩⟩
  exact (acH1Equiv K c E).trans
    ((cycTransfer (k := k) (Ω := Ω) (K := K) c hc2 hc1 φ hlink w hw hne E).trans
      (coeff.trans eD.symm))

/-- The inverse of an equivariant additive equivalence is equivariant (PROVED). -/
theorem isEquivariant_symm {G A B : Type} [Group G] [AddCommGroup A] [AddCommGroup B]
    [DistribMulAction G A] [DistribMulAction G B] (Ψ : A ≃+ B)
    (h : Work.GroupCohomology.IsEquivariant G Ψ.toAddMonoidHom) :
    Work.GroupCohomology.IsEquivariant G Ψ.symm.toAddMonoidHom := by
  intro g y
  apply Ψ.injective
  have := h g (Ψ.symm y)
  simp only [AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, AddEquiv.apply_symm_apply]
    at this ⊢
  rw [this]

#print axioms seamUnits_on_K
#print axioms seamCoeffLoc
#print axioms archPhiOf
#print axioms isEquivariant_symm

end Work.SSGRoute.ArchDictionary.ArchSeamP2

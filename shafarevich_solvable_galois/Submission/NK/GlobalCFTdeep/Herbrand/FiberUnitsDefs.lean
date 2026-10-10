import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Submission.NK.GlobalCFTdeep.Herbrand.fiberIdelesRep_iso_coind
import Submission.NK.GlobalCFTdeep.Herbrand.herbrandEq_localUnitsRep_ofFinite
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The local units of a completion as a module over the decomposition group

For a place `w` of `L` and its decomposition group `D_w = {σ | σ • w = w}`, the group `𝒪_wˣ` of
local units is stable under the action of `D_w` on `L_wˣ` (a special case of
`NK.HassePrinciple.localUnitsEquiv_mem`).  This file records

* `NK.GlobalCFTdeep.localUnitSubRep w` — `𝒪_wˣ` as a `ℤ[D_w]`-module;
* `NK.GlobalCFTdeep.valLog`, `...localValLinear` — the valuation logarithm `v : L_wˣ → ℤ` at a
  finite place of `L`, whose kernel is `𝒪_wˣ` and which is surjective;
* `NK.GlobalCFTdeep.valLog_localAction` — the valuation logarithm is invariant under local
  automorphisms, i.e. the action of `D_w` on `ℤ` is trivial.

The short exact sequence `0 ⟶ 𝒪_wˣ ⟶ L_wˣ ⟶ ℤ ⟶ 0` of `ℤ[D_w]`-modules built from these maps
lives in `Submission/Work/GlobalCFTdeep/Herbrand/FiberUnitsLocal.lean`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFTdeep

open NK.GlobalCFT

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-! ## The valuation logarithm on the units of a completion -/

/-- The logarithm of the valuation, as a homomorphism on the units of a complete discretely
valued field. -/
noncomputable def valLog (F : Type*) [Field F] [Valued F (WithZero (Multiplicative ℤ))] :
    Fˣ →* Multiplicative ℤ :=
  Commons.NumberTheory.NumberField.Completion.unitsValLog F

@[simp] theorem valLog_apply (F : Type*) [Field F] [Valued F (WithZero (Multiplicative ℤ))]
    (u : Fˣ) :
    valLog F u = Commons.NumberTheory.NumberField.Completion.unitsValLog F u := rfl

theorem valLog_eq_one_iff (F : Type*) [Field F] [Valued F (WithZero (Multiplicative ℤ))]
    (u : Fˣ) : valLog F u = 1 ↔ Valued.v (u : F) = 1 :=
  Commons.NumberTheory.NumberField.Completion.unitsValLog_eq_one_iff u

/-- **The valuation logarithm at a finite place**, as a `ℤ`-linear map on the units of the
completion.  Its kernel is the group of local units (`localValLinear_eq_zero_iff`) and it is
surjective (`localValLinear_surjective`). -/
noncomputable def localValLinear (q : HeightOneSpectrum (𝓞 L)) :
    Additive ((Place.localField L (Place.ofFinite q))ˣ) →ₗ[ℤ] ℤ where
  toFun a := Multiplicative.toAdd
    (valLog (HeightOneSpectrum.adicCompletion L q) (Additive.toMul a))
  map_add' a b := by
    show Multiplicative.toAdd (valLog (HeightOneSpectrum.adicCompletion L q)
      (Additive.toMul (a + b))) =
      Multiplicative.toAdd (valLog (HeightOneSpectrum.adicCompletion L q) (Additive.toMul a)) +
        Multiplicative.toAdd (valLog (HeightOneSpectrum.adicCompletion L q) (Additive.toMul b))
    rw [toMul_add, map_mul, toAdd_mul]
  map_smul' n a := by
    show Multiplicative.toAdd (valLog (HeightOneSpectrum.adicCompletion L q)
      (Additive.toMul (n • a))) =
      n • Multiplicative.toAdd (valLog (HeightOneSpectrum.adicCompletion L q) (Additive.toMul a))
    rw [toMul_zsmul, map_zpow, toAdd_zpow]

theorem localValLinear_apply (q : HeightOneSpectrum (𝓞 L))
    (u : (Place.localField L (Place.ofFinite q))ˣ) :
    localValLinear q (Additive.ofMul u) =
      Multiplicative.toAdd (valLog (HeightOneSpectrum.adicCompletion L q) u) := rfl

/-- **The kernel of the valuation logarithm is the group of local units.** -/
theorem localValLinear_eq_zero_iff (q : HeightOneSpectrum (𝓞 L))
    (u : (Place.localField L (Place.ofFinite q))ˣ) :
    localValLinear q (Additive.ofMul u) = 0 ↔ u ∈ Place.localUnits L (Place.ofFinite q) := by
  show Multiplicative.toAdd (valLog (HeightOneSpectrum.adicCompletion L q) u) = 0 ↔ _
  rw [Place.mem_localUnits_ofFinite_iff_valued_eq_one]
  have key : ∀ y : Multiplicative ℤ, Multiplicative.toAdd y = 0 ↔ y = 1 := by
    intro y
    rw [show (1 : Multiplicative ℤ) = Multiplicative.ofAdd (0 : ℤ) from rfl]
    exact Multiplicative.toAdd.injective.eq_iff
  rw [key, valLog_apply]
  exact Commons.NumberTheory.NumberField.Completion.unitsValLog_eq_one_iff u

theorem localValLinear_surjective (q : HeightOneSpectrum (𝓞 L)) :
    Function.Surjective (localValLinear q) := by
  intro z
  have hs : Function.Surjective (valLog (HeightOneSpectrum.adicCompletion L q)) :=
    Commons.NumberTheory.NumberField.Completion.unitsValLog_adicCompletion_surjective L q
  obtain ⟨u, hu⟩ := hs (Multiplicative.ofAdd z)
  refine ⟨Additive.ofMul u, ?_⟩
  show Multiplicative.toAdd (valLog (HeightOneSpectrum.adicCompletion L q) u) = z
  rw [hu]; simp

/-- **The valuation logarithm is invariant under the local action of the decomposition group**:
the transported local automorphism of `L_w` preserves the valuation. -/
theorem valLog_localAction (Q : HeightOneSpectrum (𝓞 K)) (q : HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) (σ : L ≃ₐ[K] L)
    (h : σ • Place.ofFinite q = Place.ofFinite q)
    (u : (Place.localField L (Place.ofFinite q))ˣ) :
    valLog (HeightOneSpectrum.adicCompletion L q)
        (Units.map (NK.GlobalCFT.Inclusion.Place.localAction σ (Place.ofFinite q) h).toMonoidHom
          u) =
      valLog (HeightOneSpectrum.adicCompletion L q) u := by
  letI : Algebra (HeightOneSpectrum.adicCompletion K Q)
      (HeightOneSpectrum.adicCompletion L q) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  have hmem : σ ∈ Commons.NumberTheory.NumberField.Completion.decompositionSubgroup (K := K) q := by
    rw [Commons.NumberTheory.NumberField.Completion.mem_decompositionSubgroup,
      NK.GlobalCFT.Inclusion.globalCFT_placeSmul_eq_smulHeightOneSpectrum]
    exact Place.ofFinite_inj.mp ((Place.smul_ofFinite σ q).trans h)
  have h1 : NK.GlobalCFT.Inclusion.Place.localAction σ (Place.ofFinite q) h
      = (decompositionSubgroupIsoLocalGalois Q q hq
          ⟨σ, by
            rw [decompositionSubgroup_eq_commons (K := K) (L := L) q]
            exact hmem⟩).toRingEquiv := by
    rw [decompositionSubgroupIsoLocalGalois_apply]
    exact localAction_eq_decompositionToAdicCompletion (K := K) (L := L) q σ h
  rw [h1]
  show Commons.NumberTheory.NumberField.Completion.unitsValLog
      (HeightOneSpectrum.adicCompletion L q)
      ((decompositionSubgroupIsoLocalGalois Q q hq
          ⟨σ, by
            rw [decompositionSubgroup_eq_commons (K := K) (L := L) q]
            exact hmem⟩) •
        (u : (HeightOneSpectrum.adicCompletion L q)ˣ)) =
    Commons.NumberTheory.NumberField.Completion.unitsValLog
      (HeightOneSpectrum.adicCompletion L q) u
  rw [AlgEquiv.smul_units_def]
  exact Commons.NumberTheory.NumberField.Completion.unitsValLog_smul Q q hq _ u

/-! ## The local units as a module over the decomposition group -/

/-- Transport of units along an equivalence of groups. -/
theorem units_map_symm_map {A B : Type*} [Monoid A] [Monoid B] (f : A ≃* B) (u : Aˣ) :
    Units.map f.symm.toMonoidHom (Units.map f.toMonoidHom u) = u := by
  ext
  simp

/-- **The local units are stable under the decomposition group.**  This is
`NK.HassePrinciple.localUnitsEquiv_mem` for the transport of the local action used in
`NK.GlobalCFTdeep.decompositionUnitsAction`. -/
theorem mem_localUnits_smul_decomposition (w : Place L)
    (σ : decompositionSubgroup (K := K) (L := L) w) (u : (Place.localField L w)ˣ) :
    Units.map (NK.GlobalCFT.Inclusion.Place.localAction σ.1 w σ.2).toMonoidHom u
        ∈ Place.localUnits L w ↔
      u ∈ Place.localUnits L w := by
  have h : Units.map (NK.GlobalCFT.Inclusion.Place.localAction σ.1 w σ.2).toMonoidHom u
      = NK.HassePrinciple.localUnitsEquiv (K := K) w ⟨σ.1, σ.2⟩ u :=
    (localUnitsEquiv_apply_eq (K := K) w ⟨σ.1, σ.2⟩ u).symm
  rw [h]
  exact NK.HassePrinciple.localUnitsEquiv_mem (K := K) w ⟨σ.1, σ.2⟩ u

/-- **The action of the decomposition group on the local units**, as a `MulDistribMulAction` on
the subgroup `𝒪_wˣ ≤ L_wˣ`. -/
noncomputable instance instMulDistribMulActionLocalUnitsSubtype (w : Place L) :
    MulDistribMulAction (decompositionSubgroup (K := K) (L := L) w) ↥(Place.localUnits L w) :=
  letI : MulDistribMulAction (decompositionSubgroup (K := K) (L := L) w)
      ((Place.localField L w)ˣ) := decompositionUnitsAction (K := K) (L := L) w
  stableMulDistribMulAction (decompositionSubgroup (K := K) (L := L) w)
    (Place.localUnits L w)
    (fun σ u hu => (mem_localUnits_smul_decomposition (K := K) (L := L) w σ u).2 hu)

/-- **The local units `𝒪_wˣ` of `L_w` as a `ℤ[D_w]`-module.** -/
noncomputable def localUnitSubRep (w : Place L) :
    Rep ℤ (decompositionSubgroup (K := K) (L := L) w) :=
  Rep.ofMulDistribMulAction (decompositionSubgroup (K := K) (L := L) w)
    ↥(Place.localUnits L w)

theorem localUnitSubRep_ρ_apply (w : Place L)
    (σ : decompositionSubgroup (K := K) (L := L) w)
    (u : (localUnitSubRep (K := K) (L := L) w).V) :
    (localUnitSubRep (K := K) (L := L) w).ρ σ u =
      Additive.ofMul (σ • (Additive.toMul u : ↥(Place.localUnits L w))) := rfl

@[simp] theorem coe_smul_localUnitSubRep (w : Place L)
    (σ : decompositionSubgroup (K := K) (L := L) w) (u : ↥(Place.localUnits L w)) :
    ((σ • u : ↥(Place.localUnits L w)) : (Place.localField L w)ˣ) =
      Units.map (NK.GlobalCFT.Inclusion.Place.localAction σ.1 w σ.2).toMonoidHom
        (u : (Place.localField L w)ˣ) := rfl

theorem localUnitsRep_ρ_apply (w : Place L)
    (σ : decompositionSubgroup (K := K) (L := L) w)
    (a : (localUnitsRep (K := K) (L := L) w).V) :
    (localUnitsRep (K := K) (L := L) w).ρ σ a =
      Additive.ofMul
        (Units.map (NK.GlobalCFT.Inclusion.Place.localAction σ.1 w σ.2).toMonoidHom
          (Additive.toMul a)) := by
  letI : MulDistribMulAction (decompositionSubgroup (K := K) (L := L) w)
      ((Place.localField L w)ˣ) := decompositionUnitsAction (K := K) (L := L) w
  rfl

end NK.GlobalCFTdeep

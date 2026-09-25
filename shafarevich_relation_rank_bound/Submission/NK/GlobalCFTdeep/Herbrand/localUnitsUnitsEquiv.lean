/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.NK.GlobalCFTdeep.Shared
import Submission.NK.NumberTheory.NumberField.Completion.H2_units_ringOfIntegers_unramified

/-!
# The local units `𝒪_qˣ` as the units of `𝒪_q`

For a finite place `q` of a number field `L`, an element of `Place.localUnits L (Place.ofFinite q)`
is a unit `u` of the local field `L_q` with `u ∈ 𝒪_q` and `u⁻¹ ∈ 𝒪_q`, i.e. it *is* a unit of the
ring `𝒪_q` of integers of `L_q`.  This file records that identification as a `MulEquiv`

* `NK.GlobalCFTdeep.Herbrand.localUnitsUnitsEquiv q : ↥(Place.localUnits L (Place.ofFinite q)) ≃*
  (↥(q.adicCompletionIntegers L))ˣ`.

Since the left-hand side is the module of the `ℤ[D_q]`-representation
`NK.GlobalCFTdeep.localUnitSubRep` and the right-hand side is the module of the local
representation `Commons.NumberTheory.NumberField.Completion.adicIntegersUnitsRep` of the local
Galois group, this is the bridge that lets the unramified computations of
`Submission/Work/NumberTheory/NumberField/Completion/H2_units_ringOfIntegers_unramified.lean` be
transported to `localUnitSubRep`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open scoped NumberField
open NumberField IsDedekindDomain
open CategoryTheory

noncomputable section

namespace NK.GlobalCFTdeep.Herbrand

open NK.GlobalCFT

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- **The local units `𝒪_qˣ` are the units of `𝒪_q`.**  An element of `Place.localUnits L
(Place.ofFinite q)` is a unit of `L_q` whose value and inverse value lie in the ring of integers,
which is exactly a unit of that ring. -/
noncomputable def localUnitsUnitsEquiv (q : HeightOneSpectrum (𝓞 L)) :
    ↥(Place.localUnits L (Place.ofFinite q)) ≃* (↥(q.adicCompletionIntegers L))ˣ :=
  Submonoid.unitsEquivUnitsType
    ((q.adicCompletionIntegers L).toSubring.toSubsemiring.toSubmonoid)

/-- The underlying element of `L_q` is unchanged by `localUnitsUnitsEquiv`. -/
@[simp] theorem coe_localUnitsUnitsEquiv (q : HeightOneSpectrum (𝓞 L))
    (u : ↥(Place.localUnits L (Place.ofFinite q))) :
    (((localUnitsUnitsEquiv q u : (↥(q.adicCompletionIntegers L))ˣ) :
        ↥(q.adicCompletionIntegers L)) : q.adicCompletion L)
      = ((u : (q.adicCompletion L)ˣ) : q.adicCompletion L) := rfl

/-- **The identification `localUnitsUnitsEquiv` is equivariant** for the action of the
decomposition group on the local units and the local Galois action on the units of `𝒪_q`.

Both actions act on the underlying element of `L_q` by the *same* ring automorphism: the local
action of `σ` is `decompositionToAdicCompletion` (`localAction_eq_decompositionToAdicCompletion`),
which is also `decompositionSubgroupIsoLocalGalois σ`. -/
theorem localUnitsUnitsEquiv_rep (Q : HeightOneSpectrum (𝓞 K)) (q : HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (σ : decompositionSubgroup (K := K) (L := L) (Place.ofFinite q))
    (u : ↥(Place.localUnits L (Place.ofFinite q))) :
    localUnitsUnitsEquiv q
        (Additive.toMul
          ((localUnitSubRep (K := K) (L := L) (Place.ofFinite q)).ρ σ (Additive.ofMul u)))
      = Additive.toMul
          ((Commons.NumberTheory.NumberField.Completion.adicIntegersUnitsRep Q q hq)
            (decompositionSubgroupIsoLocalGalois Q q hq σ)
            (Additive.ofMul (localUnitsUnitsEquiv q u))) := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  letI : MulDistribMulAction ↥(decompositionSubgroup (K := K) (L := L) (Place.ofFinite q))
      ↥(Place.localUnits L (Place.ofFinite q)) :=
    instMulDistribMulActionLocalUnitsSubtype (K := K) (L := L) (Place.ofFinite q)
  letI : MulDistribMulAction (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)
      (↥(q.adicCompletionIntegers L))ˣ :=
    Commons.NumberTheory.NumberField.Completion.adicIntegersUnitsUnitsAction Q q hq
  -- the local action and the local Galois action are the same ring automorphism
  have hring : NK.GlobalCFT.Inclusion.Place.localAction σ.1 (Place.ofFinite q) σ.2
      = (decompositionSubgroupIsoLocalGalois Q q hq σ).toRingEquiv := by
    rw [NK.GlobalCFTdeep.localAction_eq_decompositionToAdicCompletion (K := K) (L := L)
        q σ.1 σ.2,
      NK.GlobalCFTdeep.decompositionSubgroupIsoLocalGalois_apply (K := K) (L := L) Q q hq σ]
  -- the two sides are equal on the underlying element of `L_q`
  have hR : (((((decompositionSubgroupIsoLocalGalois Q q hq σ) •
        (localUnitsUnitsEquiv q u) : (↥(q.adicCompletionIntegers L))ˣ)) :
        ↥(q.adicCompletionIntegers L)) : q.adicCompletion L)
      = (decompositionSubgroupIsoLocalGalois Q q hq σ)
          (((u : (q.adicCompletion L)ˣ) : q.adicCompletion L)) := by
    have h2 := Commons.NumberTheory.NumberField.Completion.adicIntegersUnitsRep_apply_coe
      Q q hq (decompositionSubgroupIsoLocalGalois Q q hq σ) (localUnitsUnitsEquiv q u)
    rw [show Additive.toMul
          ((Commons.NumberTheory.NumberField.Completion.adicIntegersUnitsRep Q q hq)
            (decompositionSubgroupIsoLocalGalois Q q hq σ)
            (Additive.ofMul (localUnitsUnitsEquiv q u)))
        = (decompositionSubgroupIsoLocalGalois Q q hq σ) • (localUnitsUnitsEquiv q u)
      from rfl] at h2
    rw [h2, coe_localUnitsUnitsEquiv]
  -- the goal is the corresponding statement about the `•`-actions
  show localUnitsUnitsEquiv q (σ • u) =
    (decompositionSubgroupIsoLocalGalois Q q hq σ) • (localUnitsUnitsEquiv q u)
  apply Units.ext
  apply Subtype.ext
  rw [coe_localUnitsUnitsEquiv, NK.GlobalCFTdeep.coe_smul_localUnitSubRep]
  rw [show ((Units.map (NK.GlobalCFT.Inclusion.Place.localAction σ.1 (Place.ofFinite q)
        σ.2).toMonoidHom) ((u : (q.adicCompletion L)ˣ)) : q.adicCompletion L)
      = NK.GlobalCFT.Inclusion.Place.localAction σ.1 (Place.ofFinite q) σ.2
          (((u : (q.adicCompletion L)ˣ) : q.adicCompletion L)) from rfl]
  rw [hR, hring]
  rfl

end NK.GlobalCFTdeep.Herbrand

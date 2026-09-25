/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.NK.GlobalCFTdeep.Herbrand.SIdeles

/-!
# The rank of the group of `T`-units: vocabulary

Let `L` be a number field and `T` a set of places of `L`.  The `T`-units
`NK.GlobalCFTdeep.TUnits T ⊆ Lˣ` are the units which are local units outside `T`, i.e. the
elements of `Lˣ` whose `q`-adic valuation vanishes at every finite place `q ∉ T`.

This file collects the vocabulary used to compute the rank of `TUnits T` (Dirichlet's `S`-unit
theorem for a finite `T` containing all infinite places):

* `SSet T` — the finite places lying in `T`;
* `expUnit q a` — the `q`-adic valuation of a global unit `a`, in additive coordinates;
* `mem_TUnits_iff_expUnit` — membership in `TUnits T` as vanishing of these valuations;
* `tUnitsVal T : Additive (TUnits T) →ₗ[ℤ] (SSet T → ℤ)` — the valuation map;
* `globalUnits L` — the units of `𝓞 L`, as a subgroup of `Lˣ`, and `unitsToTUnits T`;
* `unitsToTUnits_injective`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField RestrictedProduct nonZeroDivisors
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFTdeep

open NK.GlobalCFT

variable {L : Type} [Field L] [NumberField L]

/-- The finite places of `L` which lie in `T`. -/
def SSet (T : Set (Place L)) : Set (HeightOneSpectrum (𝓞 L)) := {q | Place.ofFinite q ∈ T}

@[simp] theorem mem_SSet {T : Set (Place L)} {q : HeightOneSpectrum (𝓞 L)} :
    q ∈ SSet T ↔ Place.ofFinite q ∈ T := Iff.rfl

/-- The `q`-adic valuation of a global unit, in additive coordinates: the integer `n` with
`q.valuation L (a : L) = exp (-n)`. -/
noncomputable def expUnit (q : HeightOneSpectrum (𝓞 L)) (a : Lˣ) : ℤ :=
  - WithZero.log (q.valuation L (a : L))

theorem expUnit_mul (q : HeightOneSpectrum (𝓞 L)) (a b : Lˣ) :
    expUnit q (a * b) = expUnit q a + expUnit q b := by
  rw [expUnit, expUnit, expUnit, Units.val_mul, map_mul]
  rw [WithZero.log_mul ((Valuation.ne_zero_iff _).mpr (Units.ne_zero a))
    ((Valuation.ne_zero_iff _).mpr (Units.ne_zero b))]
  ring

@[simp] theorem expUnit_one (q : HeightOneSpectrum (𝓞 L)) : expUnit q (1 : Lˣ) = 0 := by
  rw [expUnit, Units.val_one, map_one, WithZero.log_one, neg_zero]

@[simp] theorem expUnit_inv (q : HeightOneSpectrum (𝓞 L)) (a : Lˣ) :
    expUnit q a⁻¹ = - expUnit q a := by
  rw [expUnit, expUnit, Units.val_inv_eq_inv_val, map_inv₀, WithZero.log_inv]

theorem expUnit_zpow (q : HeightOneSpectrum (𝓞 L)) (a : Lˣ) (n : ℤ) :
    expUnit q (a ^ n) = n * expUnit q a := by
  rw [expUnit, expUnit, Units.val_zpow_eq_zpow_val, map_zpow₀, WithZero.log_zpow]
  simp

theorem expUnit_eq_zero_iff (q : HeightOneSpectrum (𝓞 L)) (a : Lˣ) :
    expUnit q a = 0 ↔ q.valuation L (a : L) = 1 := by
  have ha : q.valuation L (a : L) ≠ 0 := (Valuation.ne_zero_iff _).mpr (Units.ne_zero a)
  rw [expUnit, neg_eq_zero, ← WithZero.exp_eq_one, WithZero.exp_log ha]

/-- The value of the principal idèle of a global unit at a finite place, in the local field. -/
theorem valued_principalIdele (q : HeightOneSpectrum (𝓞 L)) (a : Lˣ) :
    Valued.v (((Units.map (algebraMap L (Place.localField L (Place.ofFinite q))) a :
      (Place.localField L (Place.ofFinite q))ˣ)) : Place.localField L (Place.ofFinite q))
      = q.valuation L (a : L) := by
  rw [Units.coe_map]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' q (a : L)

theorem expUnit_eq_zero_iff_mem_localUnits (q : HeightOneSpectrum (𝓞 L)) (a : Lˣ) :
    expUnit q a = 0 ↔
      Units.map (algebraMap L (Place.localField L (Place.ofFinite q))) a ∈
        Place.localUnits L (Place.ofFinite q) := by
  rw [expUnit_eq_zero_iff, Place.mem_localUnits_ofFinite_iff_valued_eq_one]
  exact iff_of_eq (congrArg (fun z => z = 1) (valued_principalIdele q a)).symm

/-- Membership in the `T`-units, as a condition on the `q`-adic valuations at the finite places
outside `T`. -/
theorem mem_TUnits_iff_valuation (T : Set (Place L)) {a : Lˣ} :
    a ∈ TUnits T ↔ ∀ q : HeightOneSpectrum (𝓞 L), Place.ofFinite q ∉ T →
      q.valuation L (a : L) = 1 := by
  rw [TUnits, Subgroup.mem_comap]
  constructor
  · intro h q hq
    have h2 := h (Place.ofFinite q) hq
    rw [Idele.principalIdele_apply] at h2
    exact (expUnit_eq_zero_iff q a).mp ((expUnit_eq_zero_iff_mem_localUnits q a).mpr h2)
  · intro h w hw
    match w with
    | Sum.inl _ => exact Place.mem_localUnits_ofInfinite
    | Sum.inr q =>
        rw [Idele.principalIdele_apply]
        exact (expUnit_eq_zero_iff_mem_localUnits q a).mp ((expUnit_eq_zero_iff q a).mpr (h q hw))

/-- Membership in the `T`-units, as vanishing of the `q`-adic valuations outside `T`. -/
theorem mem_TUnits_iff_expUnit (T : Set (Place L)) {a : Lˣ} :
    a ∈ TUnits T ↔ ∀ q : HeightOneSpectrum (𝓞 L), Place.ofFinite q ∉ T → expUnit q a = 0 := by
  rw [mem_TUnits_iff_valuation]
  exact forall_congr' fun q => imp_congr_right fun _ => (expUnit_eq_zero_iff q a).symm


/-- The `q`-adic valuation as an additive homomorphism on the units of `L`. -/
noncomputable def expUnitAddHom (q : HeightOneSpectrum (𝓞 L)) : Additive Lˣ →+ ℤ where
  toFun x := expUnit q (Additive.toMul x)
  map_zero' := by
    have h : Additive.toMul (0 : Additive Lˣ) = 1 := rfl
    rw [h, expUnit_one]
  map_add' x y := by
    have h : Additive.toMul (x + y) = Additive.toMul x * Additive.toMul y := rfl
    rw [h, expUnit_mul]

@[simp] theorem expUnitAddHom_apply (q : HeightOneSpectrum (𝓞 L)) (x : Additive Lˣ) :
    expUnitAddHom q x = expUnit q (Additive.toMul x) := rfl

/-- Powers in `Lˣ` are integer multiples in `Additive Lˣ`. -/
@[simp] theorem ofMul_zpow (a : Lˣ) (n : ℤ) :
    Additive.ofMul (a ^ n) = n • Additive.ofMul a := rfl

/-- Multiplication of `T`-units is addition in `Additive (TUnits T)`. -/
@[simp] theorem ofMul_mul (T : Set (Place L)) (a b : TUnits T) :
    Additive.ofMul (a * b) = Additive.ofMul a + Additive.ofMul b := rfl

/-- The valuation map on `T`-units, one coordinate per finite place in `T`. -/
noncomputable def tUnitsValHom (T : Set (Place L)) (q : SSet T) :
    Additive (TUnits T) →+ ℤ where
  toFun x := expUnit q.1 ((Additive.toMul x : TUnits T) : Lˣ)
  map_zero' := by
    have h : ((Additive.toMul (0 : Additive (TUnits T)) : TUnits T) : Lˣ) = 1 := rfl
    rw [h, expUnit_one]
  map_add' x y := by
    have h : ((Additive.toMul (x + y) : TUnits T) : Lˣ) =
        ((Additive.toMul x : TUnits T) : Lˣ) * ((Additive.toMul y : TUnits T) : Lˣ) := rfl
    rw [h, expUnit_mul]

/-- The valuation map `Additive (TUnits T) →ₗ[ℤ] (SSet T → ℤ)`. -/
noncomputable def tUnitsVal (T : Set (Place L)) :
    Additive (TUnits T) →ₗ[ℤ] (SSet T → ℤ) :=
  LinearMap.pi fun q : SSet T => (tUnitsValHom T q).toIntLinearMap

@[simp] theorem tUnitsVal_apply (T : Set (Place L)) (x : Additive (TUnits T)) (q : SSet T) :
    tUnitsVal T x q = expUnit q.1 ((Additive.toMul x : TUnits T) : Lˣ) := rfl

/-- The units of `𝓞 L`, regarded as a subgroup of `Lˣ`. -/
noncomputable def globalUnits (L : Type) [Field L] [NumberField L] : Subgroup Lˣ :=
  (Units.map (algebraMap (𝓞 L) L).toMonoidHom).range

theorem globalUnits_le_TUnits (T : Set (Place L)) : globalUnits L ≤ TUnits T := by
  intro a ha
  rw [mem_TUnits_iff_expUnit]
  intro q _
  obtain ⟨u, rfl⟩ := ha
  rw [expUnit_eq_zero_iff]
  rw [show ((Units.map (algebraMap (𝓞 L) L).toMonoidHom u : Lˣ) : L) =
    algebraMap (𝓞 L) L (u : 𝓞 L) from rfl]
  rw [HeightOneSpectrum.valuation_eq_one_iff_notMem]
  intro hmem
  exact q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem q.asIdeal hmem (Units.isUnit u))

/-- The inclusion of the units of `𝓞 L` into the `T`-units. -/
noncomputable def unitsToTUnitsHom (T : Set (Place L)) : (𝓞 L)ˣ →* TUnits T :=
  (Subgroup.inclusion (globalUnits_le_TUnits T)).comp
    (MonoidHom.rangeRestrict (Units.map (algebraMap (𝓞 L) L).toMonoidHom))

/-- The inclusion of the units of `𝓞 L` into the `T`-units, as a `ℤ`-linear map. -/
noncomputable def unitsToTUnits (T : Set (Place L)) :
    Additive ((𝓞 L)ˣ) →ₗ[ℤ] Additive (TUnits T) :=
  (MonoidHom.toAdditive (unitsToTUnitsHom T)).toIntLinearMap

theorem unitsToTUnits_apply (T : Set (Place L)) (u : Additive ((𝓞 L)ˣ)) :
    unitsToTUnits T u = unitsToTUnitsHom T (Additive.toMul u) := rfl

theorem unitsToTUnitsHom_apply (T : Set (Place L)) (u : (𝓞 L)ˣ) :
    ((unitsToTUnitsHom T u : TUnits T) : Lˣ) = Units.map (algebraMap (𝓞 L) L).toMonoidHom u :=
  rfl

theorem unitsToTUnits_injective (T : Set (Place L)) :
    Function.Injective (unitsToTUnits T) := by
  intro x y hxy
  have h2 : unitsToTUnitsHom T (Additive.toMul x) = unitsToTUnitsHom T (Additive.toMul y) :=
    congrArg (fun z => Additive.toMul z) hxy
  have h3 : ((unitsToTUnitsHom T (Additive.toMul x) : TUnits T) : Lˣ) =
      ((unitsToTUnitsHom T (Additive.toMul y) : TUnits T) : Lˣ) := congrArg _ h2
  rw [unitsToTUnitsHom_apply, unitsToTUnitsHom_apply] at h3
  have h4 : ((Additive.toMul x : (𝓞 L)ˣ) : L) = ((Additive.toMul y : (𝓞 L)ˣ) : L) := by
    have := congrArg (fun u : Lˣ => (u : L)) h3
    simpa using this
  have h5 : Additive.toMul x = Additive.toMul y :=
    Units.ext (IsFractionRing.injective (𝓞 L) L h4)
  simpa using h5

end NK.GlobalCFTdeep

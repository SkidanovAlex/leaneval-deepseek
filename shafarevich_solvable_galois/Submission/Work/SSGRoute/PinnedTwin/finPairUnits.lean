import Mathlib
import Submission.Work.SSGRoute.ZDataTwo.Mu2FiniteForm
import Submission.Work.SSGRoute.NodeS37.p16Shim
import Submission.Work.HilbertSymbolGeneral.hilbertSymbol_comm
import Submission.Work.SSGRoute.NodeS37.henselUnitSquare
import Submission.Commons.NumberTheory.NumberField.val_algebraMap_adicCompletion_eq
import Submission.Commons.RingTheory.Henselian.adicCompletionIntegers_henselianLocalRing
import Submission.Commons.NumberTheory.NumberField.Completion.finite_adicCompletionIntegers_quotient_maximalIdeal_pow
import Submission.Work.SSGRoute.PinnedTwin.exists_sq_add_sq_eq_neg_one
import Submission.Work.SSGRoute.PinnedTwin.isSquare_mul_of_not_isSquare
import Submission.Work.SSGRoute.PinnedTwin.isSquare_unitGroup_iff_isSquare_residue
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The local Hilbert symbol of two units at a non-dyadic place is trivial

`Work.SSGRoute.PinnedTwin.finPairUnits`: for a number field `K`, a finite place `P` with
`2` a unit in the ring of integers of the completion, and `α β : Kˣ` with `v_P(α) = v_P(β) = 1`
(both `P`-adic units), the local Hilbert pairing `finPair P α β` vanishes.

The mathematical content is the standard local fact that at a non-dyadic place two units have
trivial Hilbert symbol.  Through the norm-form description of the canonical `2`-adic Hilbert symbol
(`Work.HilbertSymbolGeneral.hilbertSymbol_eq_one_iff_form`) the task reduces to a purely local
statement in the completion `F = K_P`: every unit of `F` is represented by the norm form
`X² - b Y²` of an unramified quadratic extension.  That is
`Work.SSGRoute.PinnedTwin.exists_sq_sub_mul_sq_eq_of_val_one` below, proved by a case analysis on
the square classes of the unit group `𝒪_Fˣ = F^×/1 + 𝔪`: a unit is a square iff its residue is a
square (Hensel), and the residue-field square classes are controlled by Euler's criterion.

## Contents

* `toAdd_eq_zero_iff_zmodTwo`, `isSquare_unit_iff_isSquare_val`, `isSquare_mul_of_sq` — elementary;
* `unit_pow_card_div_two_dichotomy`, `pow_card_div_two_eq_neg_one`,
  `isSquare_mul_inv_of_not_isSquare` — Euler's criterion on the unit group of a finite field;
* `finite_residueField`, `residueChar_ne_two` — the residue field of the completion is finite with
  odd characteristic;
* `exists_sq_sub_mul_sq_eq_of_val_one` — the local norm-form statement;
* `finPairUnits` — the target.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Work.SSGRoute.PinnedTwin

open IsDedekindDomain

variable {K : Type} [Field K] [NumberField K]

/-! ## Elementary helpers -/

/-- The zero test in the two-element group `Multiplicative (ZMod 2)`. -/
lemma toAdd_eq_zero_iff_zmodTwo (x : Multiplicative (ZMod 2)) :
    Multiplicative.toAdd x = 0 ↔ x = 1 := by
  fin_cases x <;> decide

/-- For a unit of a field, being a square as a unit and as an element agree. -/
lemma isSquare_unit_iff_isSquare_val {F : Type} [Field F] (x : Fˣ) :
    IsSquare x ↔ IsSquare (x : F) := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨(y : F), by rw [← Units.val_mul, hy]⟩
  · rintro ⟨s, hs⟩
    have hs0 : s ≠ 0 := fun h => x.ne_zero (by rw [h, mul_zero] at hs; exact hs)
    exact ⟨Units.mk0 s hs0, Units.ext (by rw [Units.val_mul, Units.val_mk0]; exact hs)⟩

/-- A product of squares is a square. -/
lemma isSquare_mul_of_sq {F : Type} [Field F] {x y : F} (hx : IsSquare x) (hy : IsSquare y) :
    IsSquare (x * y) := by
  obtain ⟨s, rfl⟩ := hx
  obtain ⟨t, rfl⟩ := hy
  exact ⟨s * t, by ring⟩

/-- A product of squares is a square, in a unit group. -/
lemma isSquare_unit_mul_of_sq {F : Type} [Field F] {x y : Fˣ} (hx : IsSquare x) (hy : IsSquare y) :
    IsSquare (x * y) := by
  obtain ⟨s, rfl⟩ := hx
  obtain ⟨t, rfl⟩ := hy
  exact ⟨s * t, by rw [mul_mul_mul_comm]⟩

/-! ## Euler's criterion for the units of a finite field -/

/-- The Euler dichotomy for the units of a finite field of odd characteristic. -/
lemma unit_pow_card_div_two_dichotomy {κ : Type} [Field κ] [Fintype κ]
    (h2 : ringChar κ ≠ 2) (r : κˣ) :
    r ^ (Fintype.card κ / 2) = 1 ∨ r ^ (Fintype.card κ / 2) = -1 := by
  rcases FiniteField.pow_dichotomy h2 r.ne_zero with h | h
  · left
    ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact h
  · right
    ext
    rw [Units.val_pow_eq_pow_val]
    simpa using h

/-- A non-square unit of a finite field of odd characteristic has `(q-1)/2`-th power `-1`. -/
lemma pow_card_div_two_eq_neg_one {κ : Type} [Field κ] [Fintype κ] (h2 : ringChar κ ≠ 2)
    {r : κˣ} (hr : ¬ IsSquare r) : r ^ (Fintype.card κ / 2) = -1 := by
  rcases unit_pow_card_div_two_dichotomy h2 r with h | h
  · exact absurd ((FiniteField.unit_isSquare_iff h2 r).mpr h) hr
  · exact h

/-- The quotient of two non-square units of a finite field of odd characteristic is a square. -/
lemma isSquare_mul_inv_of_not_isSquare {κ : Type} [Field κ] [Fintype κ] (h2 : ringChar κ ≠ 2)
    {r s : κˣ} (hr : ¬ IsSquare r) (hs : ¬ IsSquare s) : IsSquare (r * s⁻¹) := by
  refine (FiniteField.unit_isSquare_iff h2 (r * s⁻¹)).mpr ?_
  rw [mul_pow, inv_pow, pow_card_div_two_eq_neg_one h2 hr,
    pow_card_div_two_eq_neg_one h2 hs]
  simp

/-! ## The completion's residue field -/

/-- The residue field of the ring of integers of a completion at a finite place is finite. -/
lemma finite_residueField (P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Finite (IsLocalRing.ResidueField (P.adicCompletionIntegers K)) := by
  have h :=
    Commons.NumberTheory.NumberField.Completion.finite_adicCompletionIntegers_quotient_maximalIdeal_pow
      K P 1
  rw [pow_one] at h
  exact h

/-- If `2` is a unit of the integers of the completion, the residue field has odd characteristic. -/
lemma residueChar_ne_two (P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (h2 : IsUnit (2 : P.adicCompletionIntegers K)) :
    ringChar (IsLocalRing.ResidueField (P.adicCompletionIntegers K)) ≠ 2 := by
  intro h
  have hc : CharP (IsLocalRing.ResidueField (P.adicCompletionIntegers K)) 2 := ringChar.of_eq h
  have hz : ((2 : ℕ) : IsLocalRing.ResidueField (P.adicCompletionIntegers K)) = 0 :=
    (CharP.cast_eq_zero_iff _ 2 2).mpr (dvd_refl 2)
  have hres0 : IsLocalRing.residue (P.adicCompletionIntegers K) (2 :
      P.adicCompletionIntegers K) = 0 := by
    show IsLocalRing.residue _ ((2 : ℕ) : P.adicCompletionIntegers K) = 0
    rw [map_natCast]
    exact hz
  have hne := (IsLocalRing.residue_ne_zero_iff_isUnit
    (R := P.adicCompletionIntegers K) (2 : P.adicCompletionIntegers K)).mpr h2
  rw [hres0] at hne
  exact hne rfl

/-! ## The local norm form on units -/

/-- The element of the integers of the completion attached to an element of valuation `1`. -/
noncomputable def toA (P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (c : P.adicCompletion K)
    (hc : Valued.v (R := P.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) c = 1) :
    P.adicCompletionIntegers K :=
  ⟨c, by
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
    exact le_of_eq hc⟩

lemma toA_coe (P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (c : P.adicCompletion K)
    (hc : Valued.v (R := P.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) c = 1) :
    ((toA P c hc : P.adicCompletionIntegers K) : P.adicCompletion K) = c := rfl

/-- The unit group element of the completion's integers attached to an element of valuation `1`. -/
noncomputable def toUnitGroup (P : IsDedekindDomain.HeightOneSpectrum
    (NumberField.RingOfIntegers K)) (c : P.adicCompletion K)
    (hc : Valued.v (R := P.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) c = 1) :
    (P.adicCompletionIntegers K).unitGroup :=
  ⟨Units.mk0 c ((Valuation.ne_zero_iff (Valued.v (R := P.adicCompletion K))).mp
      (by rw [hc]; exact one_ne_zero)), by
    show Units.mk0 c _ ∈ (Valued.v (R := P.adicCompletion K)
      (Γ₀ := WithZero (Multiplicative ℤ))).valuationSubring.unitGroup
    rw [Valuation.mem_unitGroup_iff]
    exact hc⟩

lemma toUnitGroup_coe (P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (c : P.adicCompletion K)
    (hc : Valued.v (R := P.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) c = 1) :
    (((toUnitGroup P c hc : (P.adicCompletionIntegers K).unitGroup) : (P.adicCompletion K)ˣ) :
      P.adicCompletion K) = c := rfl

/-- The residue of the unit attached to an element of valuation `1`, in terms of the attached
element of the integers. -/
lemma toUnitGroup_residue (P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (c : P.adicCompletion K)
    (hc : Valued.v (R := P.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) c = 1) :
    ((P.adicCompletionIntegers K).unitGroupToResidueFieldUnits (toUnitGroup P c hc) :
      IsLocalRing.ResidueField (P.adicCompletionIntegers K)) =
      IsLocalRing.residue (P.adicCompletionIntegers K) (toA P c hc) := by
  rw [ValuationSubring.coe_unitGroupToResidueFieldUnits_apply]
  congr 1

/-- The residue of the element of the integers attached to a unit-group element. -/
lemma residue_unitGroupMulEquiv (P : IsDedekindDomain.HeightOneSpectrum
    (NumberField.RingOfIntegers K)) (u : (P.adicCompletionIntegers K).unitGroup) :
    IsLocalRing.residue (P.adicCompletionIntegers K)
        (((P.adicCompletionIntegers K).unitGroupMulEquiv u : (P.adicCompletionIntegers K)ˣ) :
          P.adicCompletionIntegers K) =
      ((P.adicCompletionIntegers K).unitGroupToResidueFieldUnits u :
        IsLocalRing.ResidueField (P.adicCompletionIntegers K)) :=
  (ValuationSubring.coe_unitGroupToResidueFieldUnits_apply (P.adicCompletionIntegers K) u).symm

/-- **The norm form of an unramified quadratic extension represents every unit.**

Let `P` be a finite place of a number field `K` at which `2` is a unit of the completion's integers,
and let `a`, `b` be elements of the completion `F = K_P` with `v a = v b = 1` (i.e. units).  Then
`a` is represented by the norm form `X ^ 2 - b * Y ^ 2` of `F(√b)`.

The proof is the classical square-class computation of a non-dyadic local field: a unit of `F` is a
square exactly when its residue is a square
(`Work.SSGRoute.PinnedTwin.isSquare_unitGroup_iff_isSquare_residue`), so with `a = b t ^ 2` (the
ratio of two non-squares is a square, by Euler's criterion) the equation becomes
`X ^ 2 = b (1 + Y ^ 2)`; choosing `Y` whose residue satisfies that `1 + Ȳ ^ 2` lies in the opposite
square class — which exists by `exists_sq_add_sq_eq_neg_one` — the right hand side has square
residue and Hensel's lemma produces `X`. -/
theorem exists_sq_sub_mul_sq_eq_of_val_one
    (P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (h2 : IsUnit (2 : P.adicCompletionIntegers K))
    (a b : P.adicCompletion K)
    (ha : Valued.v (R := P.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) a = 1)
    (hb : Valued.v (R := P.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) b = 1) :
    ∃ x y : P.adicCompletion K, x ^ 2 - b * y ^ 2 = a := by
  haveI hHens : HenselianLocalRing (P.adicCompletionIntegers K) :=
    Commons.RingTheory.Henselian.adicCompletionIntegers_henselianLocalRing
      (R := NumberField.RingOfIntegers K) (K := K) P
  haveI hFinite : Finite (IsLocalRing.ResidueField (P.adicCompletionIntegers K)) :=
    finite_residueField (K := K) P
  haveI hFin : Fintype (IsLocalRing.ResidueField (P.adicCompletionIntegers K)) :=
    Fintype.ofFinite _
  have hk2 := residueChar_ne_two (K := K) P h2
  have hb0 : b ≠ 0 := (Valuation.ne_zero_iff (Valued.v (R := P.adicCompletion K))).mp
    (by rw [hb]; exact one_ne_zero)
  -- Case 1: `b` is a square.
  by_cases hbsq : IsSquare b
  · obtain ⟨s, hs⟩ := hbsq
    have hs0 : s ≠ 0 := fun h => hb0 (by rw [hs, h, mul_zero])
    refine ⟨(a + 1) / 2, (a - 1) / (2 * s), ?_⟩
    rw [hs]
    field_simp
    ring
  -- Case 2: `a` is a square.
  by_cases hasq : IsSquare a
  · obtain ⟨s, hs⟩ := hasq
    exact ⟨s, 0, by rw [hs]; ring⟩
  -- Case 3: both are non-squares.
  have hra : ¬ IsSquare ((P.adicCompletionIntegers K).unitGroupToResidueFieldUnits
      (toUnitGroup P a ha)) := by
    intro hsq
    refine hasq ?_
    have h1 := (isSquare_unitGroup_iff_isSquare_residue (K := K) P h2
      (toUnitGroup P a ha)).mpr hsq
    rwa [toUnitGroup_coe] at h1
  have hrb : ¬ IsSquare ((P.adicCompletionIntegers K).unitGroupToResidueFieldUnits
      (toUnitGroup P b hb)) := by
    intro hsq
    refine hbsq ?_
    have h1 := (isSquare_unitGroup_iff_isSquare_residue (K := K) P h2
      (toUnitGroup P b hb)).mpr hsq
    rwa [toUnitGroup_coe] at h1
  -- the ratio `a / b` is a square
  have hratio : IsSquare (a * b⁻¹) := by
    have h1 : IsSquare ((P.adicCompletionIntegers K).unitGroupToResidueFieldUnits
        (toUnitGroup P a ha * (toUnitGroup P b hb)⁻¹)) := by
      rw [map_mul, map_inv]
      exact isSquare_mul_inv_of_not_isSquare hk2 hra hrb
    have h2' := (isSquare_unitGroup_iff_isSquare_residue (K := K) P h2
      (toUnitGroup P a ha * (toUnitGroup P b hb)⁻¹)).mpr h1
    rw [show (((toUnitGroup P a ha * (toUnitGroup P b hb)⁻¹ :
        (P.adicCompletionIntegers K).unitGroup) : (P.adicCompletion K)ˣ) : P.adicCompletion K)
        = a * b⁻¹ from by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Units.val_inv_eq_inv_val,
        toUnitGroup_coe, toUnitGroup_coe]] at h2'
    exact h2'
  obtain ⟨t, ht⟩ := hratio
  have haeq : a = b * (t * t) := by
    have h := congrArg (fun z : P.adicCompletion K => z * b) ht
    rw [mul_assoc, inv_mul_cancel₀ hb0, mul_one] at h
    rw [h]; ring
  -- Case 3a: `-1` is a square.
  by_cases hneg : IsSquare (-1 : P.adicCompletion K)
  · obtain ⟨i, hi⟩ := hneg
    refine ⟨0, t * i, ?_⟩
    rw [haeq]
    rw [show (0 : P.adicCompletion K) ^ 2 - b * (t * i) ^ 2 =
      -(b * (t * t) * (i * i)) by ring, ← hi]
    ring
  -- Case 3b: `-1` is not a square.
  · have hnegv : Valued.v (R := P.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
        (-1 : P.adicCompletion K) = 1 := by
      have h1 := (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.integers K P).isUnit_iff_valuation_eq_one.mp
        (show IsUnit (-1 : P.adicCompletionIntegers K) from isUnit_one.neg)
      simp only [map_neg, map_one] at h1
      exact h1
    -- `-1` is a non-square in the residue field
    have hnegκ : ¬ IsSquare (-1 : IsLocalRing.ResidueField (P.adicCompletionIntegers K)) := by
      intro hsq
      refine hneg ?_
      have hres : IsLocalRing.residue (P.adicCompletionIntegers K) (toA P (-1) hnegv) = -1 := by
        have : toA P (-1) hnegv = (-1 : P.adicCompletionIntegers K) := by
          refine Subtype.ext ?_
          rw [toA_coe]
          simp
        rw [this]
        simp
      have h1 : IsSquare (((toUnitGroup P (-1) hnegv :
          (P.adicCompletionIntegers K).unitGroup) : (P.adicCompletion K)ˣ) :
          P.adicCompletion K) := by
        refine (isSquare_unitGroup_iff_isSquare_residue (K := K) P h2
          (toUnitGroup P (-1) hnegv)).mpr ?_
        rw [isSquare_unit_iff_isSquare_val]
        rw [toUnitGroup_residue, hres]
        exact hsq
      rwa [toUnitGroup_coe] at h1
    -- the residue of `b` is a non-square
    have hrbnsq : ¬ IsSquare (((P.adicCompletionIntegers K).unitGroupToResidueFieldUnits
        (toUnitGroup P b hb) : IsLocalRing.ResidueField (P.adicCompletionIntegers K))) := by
      intro hsq
      exact hrb ((isSquare_unit_iff_isSquare_val _).mpr hsq)
    -- the two-squares input in the residue field
    obtain ⟨u, v, huv⟩ :=
      exists_sq_add_sq_eq_neg_one (κ := IsLocalRing.ResidueField (P.adicCompletionIntegers K)) hk2
    have hu0 : u ≠ 0 := by
      rintro rfl
      refine hnegκ ?_
      rw [zero_pow (by norm_num : 2 ≠ 0), zero_add] at huv
      exact ⟨v, by rw [pow_two] at huv; exact huv.symm⟩
    have hv0 : v ≠ 0 := by
      rintro rfl
      refine hnegκ ?_
      rw [zero_pow (by norm_num : 2 ≠ 0), add_zero] at huv
      exact ⟨u, by rw [pow_two] at huv; exact huv.symm⟩
    have huinv0 : u⁻¹ ≠ 0 := inv_ne_zero hu0
    have hyne : v * u⁻¹ ≠ 0 := mul_ne_zero hv0 huinv0
    -- the square class of `b * (1 + (v/u)^2)`
    have hkey : (1 : IsLocalRing.ResidueField (P.adicCompletionIntegers K)) + (v * u⁻¹) ^ 2
        = -(u⁻¹) ^ 2 := by
      have hu2 : u ^ 2 ≠ 0 := pow_ne_zero 2 hu0
      field_simp
      rw [huv]
    have hBsq : IsSquare (((P.adicCompletionIntegers K).unitGroupToResidueFieldUnits
        (toUnitGroup P b hb) : IsLocalRing.ResidueField (P.adicCompletionIntegers K)) *
        ((1 : IsLocalRing.ResidueField (P.adicCompletionIntegers K)) + (v * u⁻¹) ^ 2)) := by
      rw [hkey]
      have h1 : IsSquare (((-1 : IsLocalRing.ResidueField (P.adicCompletionIntegers K)) *
          ((P.adicCompletionIntegers K).unitGroupToResidueFieldUnits
            (toUnitGroup P b hb) : IsLocalRing.ResidueField (P.adicCompletionIntegers K)))) :=
        isSquare_mul_of_not_isSquare hk2 hnegκ hrbnsq
      have h2' : IsSquare (((-1 : IsLocalRing.ResidueField (P.adicCompletionIntegers K)) *
          ((P.adicCompletionIntegers K).unitGroupToResidueFieldUnits
            (toUnitGroup P b hb) : IsLocalRing.ResidueField (P.adicCompletionIntegers K))) *
          ((u⁻¹) * (u⁻¹))) :=
        isSquare_mul_of_sq h1 ⟨u⁻¹, rfl⟩
      simpa only [pow_two, mul_neg, neg_mul, mul_assoc, one_mul] using h2'
    -- lift `v / u` to a unit of the completion's integers
    obtain ⟨w, hw⟩ := ValuationSubring.surjective_unitGroupToResidueFieldUnits
      (P.adicCompletionIntegers K) (Units.mk0 (v * u⁻¹) hyne)
    have hwval : ((P.adicCompletionIntegers K).unitGroupToResidueFieldUnits w :
        IsLocalRing.ResidueField (P.adicCompletionIntegers K)) = v * u⁻¹ := by
      rw [hw]
      rfl
    set Yc : P.adicCompletionIntegers K :=
      (((P.adicCompletionIntegers K).unitGroupMulEquiv w : (P.adicCompletionIntegers K)ˣ) :
        P.adicCompletionIntegers K) with hYc
    have hYcres : IsLocalRing.residue (P.adicCompletionIntegers K) Yc = v * u⁻¹ := by
      rw [hYc, residue_unitGroupMulEquiv, hwval]
    have hYc2u : IsUnit (1 + Yc * Yc : P.adicCompletionIntegers K) := by
      rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_add, map_one, map_mul, hYcres]
      rw [show v * u⁻¹ * (v * u⁻¹) = (v * u⁻¹) ^ 2 from (pow_two _).symm, hkey]
      exact neg_ne_zero.mpr (pow_ne_zero 2 huinv0)
    -- `b * (1 + Y^2)` has square residue, hence is a square in `F`
    have hY2v : Valued.v (R := P.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
        (1 + (Yc : P.adicCompletion K) ^ 2) = 1 := by
      have h1 := (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.integers K P).isUnit_iff_valuation_eq_one.mp hYc2u
      rw [pow_two]
      exact h1
    have hZv : Valued.v (R := P.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
        (b * (1 + (Yc : P.adicCompletion K) ^ 2)) = 1 := by
      rw [map_mul, hb, hY2v, one_mul]
    have hZsq : IsSquare (b * (1 + (Yc : P.adicCompletion K) ^ 2)) := by
      refine (isSquare_unitGroup_iff_isSquare_residue (K := K) P h2
        (toUnitGroup P _ hZv)).mpr ?_
      rw [isSquare_unit_iff_isSquare_val, toUnitGroup_residue]
      have hzeq : toA P (b * (1 + (Yc : P.adicCompletion K) ^ 2)) hZv
          = toA P b hb * (1 + Yc * Yc) := by
        refine Subtype.ext ?_
        show b * (1 + (Yc : P.adicCompletion K) ^ 2) =
          ((toA P b hb : P.adicCompletionIntegers K) : P.adicCompletion K) *
            ((1 + Yc * Yc : P.adicCompletionIntegers K) : P.adicCompletion K)
        rw [toA_coe]
        push_cast
        ring
      rw [hzeq, map_mul]
      rw [show IsLocalRing.residue (P.adicCompletionIntegers K) (toA P b hb)
          = ((P.adicCompletionIntegers K).unitGroupToResidueFieldUnits
              (toUnitGroup P b hb) : IsLocalRing.ResidueField (P.adicCompletionIntegers K)) from
        (toUnitGroup_residue P b hb).symm]
      rw [show IsLocalRing.residue (P.adicCompletionIntegers K) (1 + Yc * Yc)
          = 1 + (v * u⁻¹) ^ 2 from by rw [map_add, map_one, map_mul, pow_two, hYcres]]
      simpa only [pow_two] using hBsq
    obtain ⟨X, hX⟩ := hZsq
    refine ⟨t * X, t * (Yc : P.adicCompletion K), ?_⟩
    rw [haeq]
    rw [show (t * X) ^ 2 - b * (t * (Yc : P.adicCompletion K)) ^ 2 =
        t ^ 2 * (X * X) - b * t ^ 2 * ((Yc : P.adicCompletion K) * (Yc : P.adicCompletion K))
        by ring, ← hX]
    ring


/-- **The local Hilbert symbol of two `P`-adic units is trivial.** -/
theorem finPairUnits {K : Type} [Field K] [NumberField K]
    (P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (h2 : IsUnit (2 : P.adicCompletionIntegers K)) (α β : Kˣ)
    (hα : P.valuation K (α : K) = 1) (hβ : P.valuation K (β : K) = 1) :
    Work.SSGRoute.ZDataTwo.finPair (k := K) P α β = 0 := by
  have hA : Valued.v (R := P.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
      (algebraMap K (P.adicCompletion K) (α : K)) = 1 := by
    rw [Commons.NumberTheory.NumberField.val_algebraMap_adicCompletion_eq]
    exact hα
  have hB : Valued.v (R := P.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
      (algebraMap K (P.adicCompletion K) (β : K)) = 1 := by
    rw [Commons.NumberTheory.NumberField.val_algebraMap_adicCompletion_eq]
    exact hβ
  obtain ⟨x, y, hxy⟩ :=
    exists_sq_sub_mul_sq_eq_of_val_one (K := K) P h2 _ _ hA hB
  rw [Work.SSGRoute.ZDataTwo.finPair, toAdd_eq_zero_iff_zmodTwo,
    Work.HilbertSymbolGeneral.hilbertSymbol_eq_one_iff_form]
  exact ⟨x, y, hxy⟩

end Work.SSGRoute.PinnedTwin

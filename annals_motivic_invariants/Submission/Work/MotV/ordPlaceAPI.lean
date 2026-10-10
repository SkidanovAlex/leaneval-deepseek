/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotV

# The API of the order of vanishing at a rational place of `N(E)`

This file proves `Work.MotV.ordPlaceAPI`: at every rational place `S` of the function field
`N(E)` of a Weierstrass curve, the order of vanishing `ordOfPlace E S hS`

* is multiplicative,
* inverts on `f⁻¹`,
* is nonnegative exactly on the place `S`,
* satisfies the ultrametric inequality,
* and takes values divisible by `5` on fifth-power-valued elements.

The proof goes through the normal form `f = u·π^n` (`u` a unit of the discrete valuation
ring `↥S`, `π` a uniformiser, `n : ℤ`) for `f ≠ 0`, established in
`ordPlace_unit_zpow'` / `ordPlace_exists_unit_zpow'`; see `Submission/Work/MotV/ordPlaceCommon.lean`
for the definitional layer (`avNat`, `ordPlace`).

## Main results

* `ordPlaceAPI`
* `ordPlace_mul`, `ordPlace_inv`, `ordPlace_nonneg_iff'`, `ordPlace_add`, `ordPlace_fifth`

## Tags

elliptic curve, function field, place, discrete valuation ring, order of vanishing
-/

import Mathlib
import Submission.Work.MotV.PlaceDefs
import Submission.Work.MotV.Defs
import Submission.Work.MotV.ordPlaceCommon
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open WeierstrassCurve WeierstrassCurve.Affine
open scoped WithZero Classical

namespace Work.MotV

noncomputable section

set_option autoImplicit false

variable {N : Type*} [Field N]

/-! ## §1 Elementary coercions -/

/-- The inverse of a unit of a subalgebra, in the ambient ring. -/
lemma coe_inv_of_units_subalgebra {R A : Type*} [CommSemiring R] [Field A] [Algebra R A]
    (S : Subalgebra R A) (u : Units ↥S) :
    (((u⁻¹ : Units ↥S) : ↥S) : A) = (((u : Units ↥S) : ↥S) : A)⁻¹ := by
  have h1 : (((u⁻¹ : Units ↥S) : ↥S) : A) * (((u : Units ↥S) : ↥S) : A) = 1 := by
    have := congrArg (fun x : ↥S => (x : A)) (Units.inv_mul u)
    simpa only [Subalgebra.coe_mul, Subalgebra.coe_one] using this
  exact eq_inv_of_mul_eq_one_left h1

/-- A unit of a subalgebra is a nonzero element of the ambient ring. -/
lemma units_coe_ne_zero {R A : Type*} [CommSemiring R] [Field A] [Algebra R A]
    (S : Subalgebra R A) (u : Units ↥S) : (((u : Units ↥S) : ↥S) : A) ≠ 0 :=
  fun h => Units.ne_zero u (by
    apply Subtype.val_injective
    rw [Subalgebra.coe_zero]
    exact h)

/-- A nonzero element of the ambient ring, viewed in the subalgebra, is nonzero. -/
lemma subtype_ne_zero_of_ne_zero {R A : Type*} [CommSemiring R] [Field A] [Algebra R A]
    (S : Subalgebra R A) {f : A} (hfS : f ∈ S) (hf : f ≠ 0) : (⟨f, hfS⟩ : ↥S) ≠ 0 :=
  fun h => hf (by
    have := congrArg (fun x : ↥S => (x : A)) h
    simpa using this)

/-- The product of two units of a subalgebra, in the ambient ring. -/
lemma coe_units_mul {R A : Type*} [CommSemiring R] [Field A] [Algebra R A]
    (S : Subalgebra R A) (u v : Units ↥S) :
    (((u * v : Units ↥S) : ↥S) : A) =
      (((u : Units ↥S) : ↥S) : A) * (((v : Units ↥S) : ↥S) : A) := by
  rw [Units.val_mul, Subalgebra.coe_mul]

/-- The inverse of a negative integral power. -/
lemma inv_zpow_neg {G : Type*} [DivisionMonoid G] (a : G) (k : ℕ) :
    (a ^ (-(k : ℤ)))⁻¹ = a ^ k := by
  rw [zpow_neg, inv_inv, zpow_natCast]

/-- The value of `avNat` on a power of an irreducible element. -/
lemma avNat_pow_irreducible {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {π : R} (hπ : Irreducible π) (m : ℕ) : avNat (π ^ m) = m := by
  rw [avNat_def, hπ.addVal_pow]
  exact WithTop.untopD_coe 0 m

/-- `max (exp a) (exp b) = exp (max a b)` in `ℤᵐ⁰`. -/
lemma exp_max_int (a b : ℤ) :
    max (WithZero.exp a) (WithZero.exp b) = WithZero.exp (max a b) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (WithZero.exp_le_exp.mpr h)]
  · rw [max_eq_left h, max_eq_left (WithZero.exp_le_exp.mpr h)]

/-! ## §2 The sum of two monomials -/

/-- The sum of two monomials `u π^a`, `v π^b` factors as `π^(min a b)` times an element of `S`. -/
lemma add_decomp (E : WeierstrassCurve N) (S : Subalgebra N (MotC2.Func E))
    [IsDiscreteValuationRing ↥S] {π : ↥S} (hπ : Irreducible π)
    (u v : Units ↥S) (a b : ℤ)
    (hne : ((u : ↥S) : MotC2.Func E) * ((π : ↥S) : MotC2.Func E) ^ a +
        ((v : ↥S) : MotC2.Func E) * ((π : ↥S) : MotC2.Func E) ^ b ≠ 0) :
    ∃ z : ↥S, z ≠ 0 ∧
      ((u : ↥S) : MotC2.Func E) * ((π : ↥S) : MotC2.Func E) ^ a +
        ((v : ↥S) : MotC2.Func E) * ((π : ↥S) : MotC2.Func E) ^ b =
      ((π : ↥S) : MotC2.Func E) ^ (min a b) * (z : MotC2.Func E) := by
  set P : MotC2.Func E := ((π : ↥S) : MotC2.Func E) with hPdef
  have hP : P ≠ 0 := by
    rw [hPdef]
    intro h
    exact hπ.ne_zero (Subtype.val_injective (by simpa using h))
  set c : ℤ := min a b with hc
  set m : ℕ := (a - c).toNat with hmdef
  set n : ℕ := (b - c).toNat with hndef
  have hm : c + (m : ℤ) = a := by
    have h : (m : ℤ) = a - c := Int.toNat_of_nonneg (by rw [hc]; omega)
    omega
  have hn : c + (n : ℤ) = b := by
    have h : (n : ℤ) = b - c := Int.toNat_of_nonneg (by rw [hc]; omega)
    omega
  have hf : ((u : ↥S) : MotC2.Func E) * P ^ a =
      P ^ c * (((u : ↥S) : MotC2.Func E) * P ^ m) := by
    rw [← hm, zpow_add₀ hP, zpow_natCast]
    first | refl_ring1 | ring
  have hg : ((v : ↥S) : MotC2.Func E) * P ^ b =
      P ^ c * (((v : ↥S) : MotC2.Func E) * P ^ n) := by
    rw [← hn, zpow_add₀ hP, zpow_natCast]
    first | refl_ring1 | ring
  have hz : ((u * π ^ m + v * π ^ n : ↥S) : MotC2.Func E) =
      ((u : ↥S) : MotC2.Func E) * P ^ m + ((v : ↥S) : MotC2.Func E) * P ^ n := by
    rw [Subalgebra.coe_add, Subalgebra.coe_mul, Subalgebra.coe_mul,
      Subalgebra.coe_pow, Subalgebra.coe_pow, ← hPdef]
  have hsum : ((u : ↥S) : MotC2.Func E) * P ^ a + ((v : ↥S) : MotC2.Func E) * P ^ b =
      P ^ c * ((u * π ^ m + v * π ^ n : ↥S) : MotC2.Func E) := by
    rw [hf, hg, hz]
    first | refl_ring1 | ring
  refine ⟨u * π ^ m + v * π ^ n, ?_, ?_⟩
  · intro h0
    apply hne
    rw [hsum, h0]
    simp
  · rw [hsum]

/-! ## §3 The value group -/

/-- `valZFun` is `f ↦ exp (-ord_P f)`, with value `0` at `0`. -/
def valZFun (E : WeierstrassCurve N) (S : Subalgebra N (MotC2.Func E))
    [IsDiscreteValuationRing ↥S] (hS : MotC2.IsRatPlace E S) (f : MotC2.Func E) : ℤᵐ⁰ :=
  if f = 0 then 0 else WithZero.exp (-(ordPlace E S hS f))

lemma valZFun_zero (E : WeierstrassCurve N) (S : Subalgebra N (MotC2.Func E))
    [IsDiscreteValuationRing ↥S] (hS : MotC2.IsRatPlace E S) : valZFun E S hS 0 = 0 := by
  rw [valZFun]
  exact dif_pos rfl

lemma valZFun_apply (E : WeierstrassCurve N) (S : Subalgebra N (MotC2.Func E))
    [IsDiscreteValuationRing ↥S] (hS : MotC2.IsRatPlace E S) {f : MotC2.Func E}
    (hf : f ≠ 0) : valZFun E S hS f = WithZero.exp (-(ordPlace E S hS f)) := by
  rw [valZFun]
  exact dif_neg hf

lemma valZFun_ne_zero (E : WeierstrassCurve N) (S : Subalgebra N (MotC2.Func E))
    [IsDiscreteValuationRing ↥S] (hS : MotC2.IsRatPlace E S) {f : MotC2.Func E}
    (hf : f ≠ 0) : valZFun E S hS f ≠ 0 := by
  rw [valZFun_apply E S hS hf]
  exact WithZero.exp_ne_zero

lemma valZFun_one (E : WeierstrassCurve N) (S : Subalgebra N (MotC2.Func E))
    [IsDiscreteValuationRing ↥S] (hS : MotC2.IsRatPlace E S) : valZFun E S hS 1 = 1 := by
  rw [valZFun_apply E S hS one_ne_zero, ordPlace_one E S hS, neg_zero, WithZero.exp_zero]

/-- The order of a constant. -/
lemma ordPlace_algebraMap {E : WeierstrassCurve N} {S : Subalgebra N (MotC2.Func E)}
    [IsDiscreteValuationRing ↥S] (hS : MotC2.IsRatPlace E S) (c : N) :
    ordPlace E S hS (algebraMap N (MotC2.Func E) c) = 0 := by
  by_cases hc : c = 0
  · subst hc
    rw [map_zero, ordPlace_zero]
  · have hmem : algebraMap N (MotC2.Func E) c ∈ S := S.algebraMap_mem c
    rw [ordPlace_eq_of_mem E S hS _ hmem]
    have hunit : IsUnit (⟨algebraMap N (MotC2.Func E) c, hmem⟩ : ↥S) := by
      refine isUnit_iff_exists_inv.mpr
        ⟨⟨algebraMap N (MotC2.Func E) c⁻¹, S.algebraMap_mem c⁻¹⟩, ?_⟩
      apply Subtype.ext
      simp only [Subalgebra.coe_mul, Subalgebra.coe_one]
      rw [← map_mul, mul_inv_cancel₀ hc, map_one]
    have h2 : avNat (⟨algebraMap N (MotC2.Func E) c, hmem⟩ : ↥S) = 0 := by
      rw [← IsUnit.unit_spec hunit]
      exact avNat_eq_zero_of_unit hunit.unit
    rw [h2]
    norm_num

lemma valZFun_trivOn_apply (E : WeierstrassCurve N) (S : Subalgebra N (MotC2.Func E))
    [IsDiscreteValuationRing ↥S] (hS : MotC2.IsRatPlace E S) (c : N) (hc : c ≠ 0) :
    valZFun E S hS (algebraMap N (MotC2.Func E) c) = 1 := by
  have hne : algebraMap N (MotC2.Func E) c ≠ 0 := by
    intro h
    have h' : algebraMap N (MotC2.Func E) (c * c⁻¹) = 0 := by
      rw [map_mul, h, zero_mul]
    rw [mul_inv_cancel₀ hc, map_one] at h'
    exact one_ne_zero h'
  rw [valZFun_apply E S hS hne, ordPlace_algebraMap hS c, neg_zero, WithZero.exp_zero]

/-! ## §4 The uniformiser normal form -/

/-- At a rational place, `u·π^n` has order `n`. -/
lemma ordPlace_unit_zpow' {E : WeierstrassCurve N} {S : Subalgebra N (MotC2.Func E)}
    [IsDiscreteValuationRing ↥S] (hS : MotC2.IsRatPlace E S) {π : ↥S} (hπ : Irreducible π)
    (u : Units ↥S) (n : ℤ) :
    ordPlace E S hS (((u : ↥S) : MotC2.Func E) * ((π : ↥S) : MotC2.Func E) ^ n) = n := by
  set P : MotC2.Func E := ((π : ↥S) : MotC2.Func E) with hPdef
  have hπ0 : π ≠ 0 := hπ.ne_zero
  have hP : P ≠ 0 := by
    rw [hPdef]
    intro h
    exact hπ0 (Subtype.val_injective (by simpa using h))
  by_cases hn : 0 ≤ n
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = (m : ℤ) :=
      ⟨n.toNat, (Int.toNat_of_nonneg hn).symm⟩
    rw [zpow_natCast]
    have hcoe : (((u * π ^ m : ↥S)) : MotC2.Func E) = ((u : ↥S) : MotC2.Func E) * P ^ m := by
      rw [Subalgebra.coe_mul, Subalgebra.coe_pow, ← hPdef]
    have hsub : (⟨((u : ↥S) : MotC2.Func E) * P ^ m, hcoe ▸ (u * π ^ m).2⟩ : ↥S)
        = u * π ^ m := Subtype.ext hcoe.symm
    rw [ordPlace_eq_of_mem E S hS _ (hcoe ▸ (u * π ^ m).2), hsub,
      avNat_mul (Units.ne_zero u) (pow_ne_zero m hπ0), avNat_eq_zero_of_unit u, zero_add,
      avNat_pow_irreducible hπ m]
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, n = -(k : ℤ) := by
      refine ⟨(-n).toNat, ?_⟩
      have h := Int.toNat_of_nonneg (show (0 : ℤ) ≤ -n by omega)
      omega
    subst hk
    have hk1 : 1 ≤ k := by omega
    have hx0 : ((u : ↥S) : MotC2.Func E) * P ^ (-(k : ℤ)) ≠ 0 :=
      mul_ne_zero (units_coe_ne_zero S u) (zpow_ne_zero _ hP)
    have hxy : (((u⁻¹ * π ^ k : ↥S)) : MotC2.Func E) =
        (((u : ↥S) : MotC2.Func E) * P ^ (-(k : ℤ)))⁻¹ := by
      rw [Subalgebra.coe_mul, Subalgebra.coe_pow, ← hPdef, mul_inv,
        ← coe_inv_of_units_subalgebra S u, inv_zpow_neg]
    have hxnotmem : ((u : ↥S) : MotC2.Func E) * P ^ (-(k : ℤ)) ∉ S := by
      intro hx
      have hxinv : (((u : ↥S) : MotC2.Func E) * P ^ (-(k : ℤ)))⁻¹ ∈ S :=
        hxy ▸ (u⁻¹ * π ^ k).2
      have hmul : (⟨((u : ↥S) : MotC2.Func E) * P ^ (-(k : ℤ)), hx⟩ : ↥S) *
          ⟨(((u : ↥S) : MotC2.Func E) * P ^ (-(k : ℤ)))⁻¹, hxinv⟩ = 1 := by
        apply Subtype.ext
        simp only [Subalgebra.coe_mul, Subalgebra.coe_one]
        exact mul_inv_cancel₀ hx0
      have hsum0 : avNat (⟨((u : ↥S) : MotC2.Func E) * P ^ (-(k : ℤ)), hx⟩ : ↥S) +
          avNat (⟨(((u : ↥S) : MotC2.Func E) * P ^ (-(k : ℤ)))⁻¹, hxinv⟩ : ↥S) = 0 := by
        rw [← avNat_mul
              (x := (⟨((u : ↥S) : MotC2.Func E) * P ^ (-(k : ℤ)), hx⟩ : ↥S))
              (y := (⟨(((u : ↥S) : MotC2.Func E) * P ^ (-(k : ℤ)))⁻¹, hxinv⟩ : ↥S))
              (subtype_ne_zero_of_ne_zero S hx hx0)
              (subtype_ne_zero_of_ne_zero S hxinv (inv_ne_zero hx0)), hmul, avNat_one]
      have h2 : avNat (⟨(((u : ↥S) : MotC2.Func E) * P ^ (-(k : ℤ)))⁻¹, hxinv⟩ : ↥S) = k := by
        rw [show (⟨(((u : ↥S) : MotC2.Func E) * P ^ (-(k : ℤ)))⁻¹, hxinv⟩ : ↥S) = u⁻¹ * π ^ k
              from Subtype.ext hxy.symm]
        rw [avNat_mul (Units.ne_zero u⁻¹) (pow_ne_zero k hπ0), avNat_eq_zero_of_unit u⁻¹,
          zero_add, avNat_pow_irreducible hπ k]
      omega
    rw [ordPlace_eq_of_notMem E S hS _ hxnotmem]
    have hsub : (⟨(((u : ↥S) : MotC2.Func E) * P ^ (-(k : ℤ)))⁻¹,
        inv_mem_of_notMem hS hxnotmem⟩ : ↥S) = u⁻¹ * π ^ k := Subtype.ext hxy.symm
    rw [hsub, avNat_mul (Units.ne_zero u⁻¹) (pow_ne_zero k hπ0), avNat_eq_zero_of_unit u⁻¹,
      zero_add, avNat_pow_irreducible hπ k]

/-- Every nonzero element of the function field is a unit times a power of a uniformiser. -/
lemma ordPlace_exists_unit_zpow' {E : WeierstrassCurve N} {S : Subalgebra N (MotC2.Func E)}
    [IsDiscreteValuationRing ↥S] (hS : MotC2.IsRatPlace E S) {π : ↥S} (hπ : Irreducible π)
    (f : MotC2.Func E) (hf : f ≠ 0) :
    ∃ (u : Units ↥S) (n : ℤ), f = ((u : ↥S) : MotC2.Func E) *
      ((π : ↥S) : MotC2.Func E) ^ n := by
  by_cases hfS : f ∈ S
  · obtain ⟨m, u, hu⟩ :=
      IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (subtype_ne_zero_of_ne_zero S hfS hf) hπ
    refine ⟨u, (m : ℤ), ?_⟩
    rw [zpow_natCast]
    have h2 : ((⟨f, hfS⟩ : ↥S) : MotC2.Func E) =
        ((u : ↥S) : MotC2.Func E) * ((π : ↥S) : MotC2.Func E) ^ m := by
      rw [hu, Subalgebra.coe_mul, Subalgebra.coe_pow]
    exact h2
  · have hfinv : f⁻¹ ∈ S := (MotC2.mem_or_inv_mem_of_isRatPlace hS f).resolve_left hfS
    obtain ⟨m, u, hu⟩ :=
      IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
        (subtype_ne_zero_of_ne_zero S hfinv (inv_ne_zero hf)) hπ
    refine ⟨u⁻¹, -((m : ℤ)), ?_⟩
    have h2 : f⁻¹ = ((u : ↥S) : MotC2.Func E) * ((π : ↥S) : MotC2.Func E) ^ m := by
      have h3 : ((⟨f⁻¹, hfinv⟩ : ↥S) : MotC2.Func E) =
          ((u : ↥S) : MotC2.Func E) * ((π : ↥S) : MotC2.Func E) ^ m := by
        rw [hu, Subalgebra.coe_mul, Subalgebra.coe_pow]
      exact h3
    have h3 : ((((π : ↥S) : MotC2.Func E) ^ m)⁻¹) =
        ((π : ↥S) : MotC2.Func E) ^ (-(m : ℤ)) := by
      rw [zpow_neg, zpow_natCast]
    rw [← inv_inv f, h2, mul_inv, coe_inv_of_units_subalgebra S u, h3]

/-- The order of a power of the uniformiser. -/
lemma ordPlace_zpow {E : WeierstrassCurve N} {S : Subalgebra N (MotC2.Func E)}
    [IsDiscreteValuationRing ↥S] (hS : MotC2.IsRatPlace E S) {π : ↥S} (hπ : Irreducible π)
    (n : ℤ) : ordPlace E S hS (((π : ↥S) : MotC2.Func E) ^ n) = n := by
  have h := ordPlace_unit_zpow' (E := E) (S := S) hS hπ (1 : Units ↥S) n
  simpa using h

/-! ## §5 Multiplicativity, inverse, sign criterion, ultrametric inequality -/

lemma ordPlace_mul_of {E : WeierstrassCurve N} {S : Subalgebra N (MotC2.Func E)}
    [IsDiscreteValuationRing ↥S] (hS : MotC2.IsRatPlace E S) {π : ↥S} (hπ : Irreducible π)
    (f g : MotC2.Func E) (hf : f ≠ 0) (hg : g ≠ 0) :
    ordPlace E S hS (f * g) = ordPlace E S hS f + ordPlace E S hS g := by
  obtain ⟨u, a, hfa⟩ := ordPlace_exists_unit_zpow' hS hπ f hf
  obtain ⟨v, b, hgb⟩ := ordPlace_exists_unit_zpow' hS hπ g hg
  set P : MotC2.Func E := ((π : ↥S) : MotC2.Func E) with hPdef
  have hP : P ≠ 0 := by
    rw [hPdef]
    intro h
    exact hπ.ne_zero (Subtype.val_injective (by simpa using h))
  have hmul : (((u : ↥S) : MotC2.Func E) * P ^ a) * (((v : ↥S) : MotC2.Func E) * P ^ b) =
      (((u * v : Units ↥S) : ↥S) : MotC2.Func E) * P ^ (a + b) := by
    rw [coe_units_mul S u v, zpow_add₀ hP]
    first | refl_ring1 | ring
  rw [hfa, hgb, hmul, ordPlace_unit_zpow' hS hπ (u * v) (a + b),
    ordPlace_unit_zpow' hS hπ u a, ordPlace_unit_zpow' hS hπ v b]

theorem ordPlace_mul {E : WeierstrassCurve N} {S : Subalgebra N (MotC2.Func E)}
    [IsDiscreteValuationRing ↥S] (hS : MotC2.IsRatPlace E S)
    (f g : MotC2.Func E) (hf : f ≠ 0) (hg : g ≠ 0) :
    ordPlace E S hS (f * g) = ordPlace E S hS f + ordPlace E S hS g := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible ↥S
  exact ordPlace_mul_of hS hπ f g hf hg

lemma ordPlace_inv_of {E : WeierstrassCurve N} {S : Subalgebra N (MotC2.Func E)}
    [IsDiscreteValuationRing ↥S] (hS : MotC2.IsRatPlace E S) {π : ↥S} (hπ : Irreducible π)
    (f : MotC2.Func E) (hf : f ≠ 0) :
    ordPlace E S hS f⁻¹ = - ordPlace E S hS f := by
  obtain ⟨u, a, hfa⟩ := ordPlace_exists_unit_zpow' hS hπ f hf
  have hx : ((((u : ↥S) : MotC2.Func E) * ((π : ↥S) : MotC2.Func E) ^ a)⁻¹) =
      (((u⁻¹ : Units ↥S) : ↥S) : MotC2.Func E) * ((π : ↥S) : MotC2.Func E) ^ (-a) := by
    rw [mul_inv, coe_inv_of_units_subalgebra S u, ← zpow_neg]
  rw [hfa, hx, ordPlace_unit_zpow' hS hπ u⁻¹ (-a), ordPlace_unit_zpow' hS hπ u a]

theorem ordPlace_inv {E : WeierstrassCurve N} {S : Subalgebra N (MotC2.Func E)}
    [IsDiscreteValuationRing ↥S] (hS : MotC2.IsRatPlace E S)
    (f : MotC2.Func E) (hf : f ≠ 0) :
    ordPlace E S hS f⁻¹ = - ordPlace E S hS f := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible ↥S
  exact ordPlace_inv_of hS hπ f hf

/-- The sign criterion. -/
theorem ordPlace_nonneg_iff' {E : WeierstrassCurve N} {S : Subalgebra N (MotC2.Func E)}
    [IsDiscreteValuationRing ↥S] (hS : MotC2.IsRatPlace E S) (f : MotC2.Func E) :
    0 ≤ ordPlace E S hS f ↔ f ∈ S := by
  by_cases hf : f ∈ S
  · exact iff_of_true (by rw [ordPlace_eq_of_mem E S hS f hf]; exact Int.natCast_nonneg _) hf
  · have hf0 : f ≠ 0 := fun h => hf (h ▸ S.zero_mem)
    have hfinv : f⁻¹ ∈ S := inv_mem_of_notMem hS hf
    have hne : (⟨f⁻¹, hfinv⟩ : ↥S) ≠ 0 :=
      subtype_ne_zero_of_ne_zero S hfinv (inv_ne_zero hf0)
    rw [ordPlace_eq_of_notMem E S hS f hf]
    constructor
    · intro h
      have hnu : ¬ IsUnit (⟨f⁻¹, hfinv⟩ : ↥S) := by
        rintro ⟨v, hv⟩
        have hcoe : ((v : ↥S) : MotC2.Func E) = f⁻¹ := by rw [hv]
        have hfv : f = (((v⁻¹ : Units ↥S) : ↥S) : MotC2.Func E) := by
          rw [coe_inv_of_units_subalgebra S v, hcoe, inv_inv]
        exact hf (hfv.symm ▸ Subtype.property ((v⁻¹ : Units ↥S) : ↥S))
      have := (one_le_avNat_iff hne).mpr hnu
      omega
    · intro h; exact absurd h hf

/-- The ultrametric inequality. -/
lemma ordPlace_add_of {E : WeierstrassCurve N} {S : Subalgebra N (MotC2.Func E)}
    [IsDiscreteValuationRing ↥S] (hS : MotC2.IsRatPlace E S) {π : ↥S} (hπ : Irreducible π)
    (f g : MotC2.Func E) (hfg : f + g ≠ 0) :
    min (ordPlace E S hS f) (ordPlace E S hS g) ≤ ordPlace E S hS (f + g) := by
  by_cases hf : f = 0
  · subst hf
    rw [ordPlace_zero, zero_add]
    exact min_le_right _ _
  by_cases hg : g = 0
  · subst hg
    rw [ordPlace_zero, add_zero]
    exact min_le_left _ _
  obtain ⟨u, a, hfa⟩ := ordPlace_exists_unit_zpow' hS hπ f hf
  obtain ⟨v, b, hgb⟩ := ordPlace_exists_unit_zpow' hS hπ g hg
  have hne : ((u : ↥S) : MotC2.Func E) * ((π : ↥S) : MotC2.Func E) ^ a +
      ((v : ↥S) : MotC2.Func E) * ((π : ↥S) : MotC2.Func E) ^ b ≠ 0 := by
    rw [← hfa, ← hgb]; exact hfg
  obtain ⟨z, hz0, hz⟩ := add_decomp E S hπ u v a b hne
  have hP : ((π : ↥S) : MotC2.Func E) ≠ 0 := by
    intro h
    exact hπ.ne_zero (Subtype.val_injective (by simpa using h))
  have hzfun : (z : MotC2.Func E) ≠ 0 := fun h => hz0 (Subtype.val_injective h)
  have hsum : f + g = ((π : ↥S) : MotC2.Func E) ^ (min a b) * (z : MotC2.Func E) := by
    rw [hfa, hgb]; exact hz
  rw [hsum,
    ordPlace_mul_of hS hπ (((π : ↥S) : MotC2.Func E) ^ (min a b)) (z : MotC2.Func E)
      (zpow_ne_zero _ hP) hzfun,
    ordPlace_zpow hS hπ (min a b)]
  rw [hfa, hgb, ordPlace_unit_zpow' hS hπ u a, ordPlace_unit_zpow' hS hπ v b]
  have hz0' : 0 ≤ ordPlace E S hS (z : MotC2.Func E) :=
    (ordPlace_nonneg_iff' hS _).mpr z.2
  linarith

theorem ordPlace_add {E : WeierstrassCurve N} {S : Subalgebra N (MotC2.Func E)}
    [IsDiscreteValuationRing ↥S] (hS : MotC2.IsRatPlace E S)
    (f g : MotC2.Func E) (hfg : f + g ≠ 0) :
    min (ordPlace E S hS f) (ordPlace E S hS g) ≤ ordPlace E S hS (f + g) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible ↥S
  exact ordPlace_add_of hS hπ f g hfg

/-! ## §6 The place valuation and the fifth-power divisibility -/

/-- The place valuation `f ↦ exp (-ord_P f)` of the function field at a rational place. -/
def valZ (E : WeierstrassCurve N) (S : Subalgebra N (MotC2.Func E))
    [IsDiscreteValuationRing ↥S] (hS : MotC2.IsRatPlace E S) : Valuation (MotC2.Func E) ℤᵐ⁰ where
  toFun := valZFun E S hS
  map_zero' := valZFun_zero E S hS
  map_one' := valZFun_one E S hS
  map_mul' f g := by
    rcases eq_or_ne f 0 with rfl | hf
    · rw [zero_mul, valZFun_zero, zero_mul]
    rcases eq_or_ne g 0 with rfl | hg
    · rw [mul_zero, valZFun_zero, mul_zero]
    rw [valZFun_apply E S hS (mul_ne_zero hf hg), valZFun_apply E S hS hf,
      valZFun_apply E S hS hg, ordPlace_mul hS f g hf hg, neg_add, WithZero.exp_add]
  map_add_le_max' f g := by
    rcases eq_or_ne f 0 with rfl | hf
    · rw [zero_add, valZFun_zero]
      exact le_max_right _ _
    rcases eq_or_ne g 0 with rfl | hg
    · rw [add_zero, valZFun_zero]
      exact le_max_left _ _
    rcases eq_or_ne (f + g) 0 with hfg | hfg
    · rw [hfg, valZFun_zero]
      exact zero_le
    rw [valZFun_apply E S hS hfg, valZFun_apply E S hS hf, valZFun_apply E S hS hg,
      exp_max_int (-(ordPlace E S hS f)) (-(ordPlace E S hS g))]
    refine WithZero.exp_le_exp.mpr ?_
    have h := ordPlace_add hS f g hfg
    simp only [max_neg_neg]
    linarith

/-- The place valuation is trivial on the constants. -/
lemma valZ_trivOn (E : WeierstrassCurve N) (S : Subalgebra N (MotC2.Func E))
    [IsDiscreteValuationRing ↥S] (hS : MotC2.IsRatPlace E S) :
    TrivOn N (valZ E S hS) :=
  fun c hc => valZFun_trivOn_apply E S hS c hc

/-- Fifth-power-valued elements have order divisible by five. -/
theorem ordPlace_fifth {E : WeierstrassCurve N} {S : Subalgebra N (MotC2.Func E)}
    [IsDiscreteValuationRing ↥S] (hS : MotC2.IsRatPlace E S) (g : MotC2.Func E)
    (hg : FifthPowerValued N g) : 5 ∣ ordPlace E S hS g := by
  by_cases hg0 : g = 0
  · subst hg0; rw [ordPlace_zero]; exact dvd_zero 5
  obtain ⟨u, hu⟩ := hg (valZ E S hS) (valZ_trivOn E S hS)
  have hgne : valZ E S hS g ≠ 0 := valZFun_ne_zero E S hS hg0
  have hu0 : u ≠ 0 := by
    intro h
    apply hgne
    rw [hu, h, show valZ E S hS (0 : MotC2.Func E) = 0 from valZFun_zero E S hS]
    exact zero_pow (by norm_num : 5 ≠ 0)
  have hu' : valZFun E S hS g = (valZFun E S hS u) ^ 5 := hu
  have key : WithZero.exp (-(ordPlace E S hS g)) =
      WithZero.exp ((5 : ℕ) • (-(ordPlace E S hS u))) := by
    rw [valZFun_apply E S hS hg0, valZFun_apply E S hS hu0, ← WithZero.exp_nsmul] at hu'
    exact hu'
  have h2 := WithZero.exp_inj.mp key
  rw [nsmul_eq_mul] at h2
  exact ⟨ordPlace E S hS u, by omega⟩

/-! ## §7 The API -/

theorem ordPlaceAPI {N : Type*} [Field N] (E : WeierstrassCurve N)
    (S : Subalgebra N (Work.MotC2.Func E)) (hS : Work.MotC2.IsRatPlace E S) :
    (∀ f g : Work.MotC2.Func E, f ≠ 0 → g ≠ 0 →
        Work.MotV.ordOfPlace E S hS (f * g) =
          Work.MotV.ordOfPlace E S hS f + Work.MotV.ordOfPlace E S hS g) ∧
    (∀ f : Work.MotC2.Func E, f ≠ 0 →
        Work.MotV.ordOfPlace E S hS f⁻¹ = - Work.MotV.ordOfPlace E S hS f) ∧
    (∀ f : Work.MotC2.Func E, 0 ≤ Work.MotV.ordOfPlace E S hS f ↔ f ∈ S) ∧
    (∀ f g : Work.MotC2.Func E, f + g ≠ 0 → min (Work.MotV.ordOfPlace E S hS f)
        (Work.MotV.ordOfPlace E S hS g) ≤ Work.MotV.ordOfPlace E S hS (f + g)) ∧
    (∀ g : Work.MotC2.Func E, Work.MotV.FifthPowerValued N g →
      5 ∣ Work.MotV.ordOfPlace E S hS g) := by
  letI : IsDiscreteValuationRing ↥S := hS.1.choose
  simp only [ordOfPlace_eq_ordPlace]
  exact ⟨ordPlace_mul hS, ordPlace_inv hS, ordPlace_nonneg_iff' hS, ordPlace_add hS,
    ordPlace_fifth hS⟩

end

end Work.MotV

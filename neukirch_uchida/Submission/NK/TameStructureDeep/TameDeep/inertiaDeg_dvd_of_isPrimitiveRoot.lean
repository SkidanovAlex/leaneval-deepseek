/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The inertia degree is divisible by `m` if the completion contains `μ_{q ^ m - 1}`

Let `K ⊆ L` be number fields, `𝔭` a finite prime of `K`, `q` a prime of `L` above `𝔭`, and let
`N = #κ(𝔭)` be the cardinality of the residue field of the `𝔭`-adic completion of `K`.  If the
`q`-adic completion `L_q` contains a primitive `(N ^ m - 1)`-st root of unity (`m > 0`), then
`m ∣ f`, where `f = [κ(q) : κ(𝔭)]` is the inertia degree.

The proof is the classical reduction to the residue field: `N ^ m - 1` is prime to the residue
characteristic `p` (because `p ∣ N`), so a primitive `(N ^ m - 1)`-st root of unity `ζ ∈ L_q` is a
*unit* of the ring of integers `q.adicCompletionIntegers L` whose *residue* `ζ̄` is again a primitive
`(N ^ m - 1)`-st root of unity.  As `ζ̄` lies in the multiplicative group of the finite field
`κ(q)`, whose order is `#κ(q) - 1 = N ^ f - 1`, we get `N ^ m - 1 ∣ N ^ f - 1`, and the elementary
fact that `N` has multiplicative order exactly `m` modulo `N ^ m - 1` turns this into `m ∣ f`.
-/
import Mathlib
import Submission.NK.TameStructureDeep.TameDeepImports

namespace NK.TameStructureDeep.TameDeep

open IsDedekindDomain

set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

/-- **The elementary arithmetic step.**  If `2 ≤ N`, `0 < m` and `N ^ m - 1 ∣ N ^ f - 1`, then
`m ∣ f`.

Indeed `N` has multiplicative order exactly `m` in `ZMod (N ^ m - 1)`
(`NK.TameStructureDeep.Degree.orderOf_natCast_zmod_pow_sub_one`), while the divisibility
`N ^ m - 1 ∣ N ^ f - 1` says precisely that `N ^ f ≡ 1` modulo `N ^ m - 1`. -/
lemma dvd_of_pow_sub_one_dvd_pow_sub_one {N m f : ℕ} (hN : 2 ≤ N) (hm : 0 < m)
    (h : N ^ m - 1 ∣ N ^ f - 1) : m ∣ f := by
  have hNf1 : 1 ≤ N ^ f := Nat.one_le_pow f N (by omega)
  have hmod : (1 : ℕ) ≡ N ^ f [MOD N ^ m - 1] := (Nat.modEq_iff_dvd' hNf1).mpr h
  have hcast : ((N ^ f : ℕ) : ZMod (N ^ m - 1)) = 1 := by
    have hh := (ZMod.natCast_eq_natCast_iff (1 : ℕ) (N ^ f) (N ^ m - 1)).mpr hmod
    simpa using hh.symm
  have hpow : ((N : ZMod (N ^ m - 1))) ^ f = 1 := by
    rw [← Nat.cast_pow]
    exact hcast
  have hord := NK.TameStructureDeep.Degree.orderOf_natCast_zmod_pow_sub_one (q := N) (m := m)
    hN (Nat.pos_iff_ne_zero.mp hm)
  have hdvd : orderOf ((N : ZMod (N ^ m - 1))) ∣ f := orderOf_dvd_iff_pow_eq_one.mpr hpow
  rwa [hord] at hdvd

/-- **`IsPrimitiveRoot` transfers backwards along an injective monoid hom.**

If the image of `x` under an injective monoid hom is a primitive `k`-th root of unity, so is `x`:
`x ^ k = 1` follows by injectivity, and if `x ^ l = 1` then `(f x) ^ l = 1`, whence `k ∣ l`. -/
lemma isPrimitiveRoot_of_injective_apply {M N F : Type*} [CommMonoid M] [CommMonoid N]
    [FunLike F M N] [MonoidHomClass F M N] (f : F) (hf : Function.Injective f) {x : M} {k : ℕ}
    (h : IsPrimitiveRoot (f x) k) : IsPrimitiveRoot x k :=
  ⟨hf (by rw [map_pow, h.pow_eq_one, map_one]),
    fun l hl => h.dvd_of_pow_eq_one l (by rw [← map_pow, hl, map_one])⟩

theorem inertiaDeg_dvd_of_isPrimitiveRoot {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver 𝔭.asIdeal)
    {m : ℕ} (hm : 0 < m) {ζ : q.adicCompletion L}
    (hζ : IsPrimitiveRoot ζ
      ((Nat.card (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K))) ^ m - 1)) :
    m ∣ q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) := by
  classical
  -- abbreviations for the residue cardinality of `𝔭` and the inertia degree of `q`
  set N : ℕ := Nat.card (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) with hNdef
  set f : ℕ := q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) with hfdef
  -- finiteness of the two residue fields
  haveI hfinK : Finite (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) :=
    Commons.NumberTheory.NumberField.Completion.finite_residueField_adicCompletion K 𝔭
  haveI hftK : Fintype (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) := Fintype.ofFinite _
  haveI hfinL : Finite (IsLocalRing.ResidueField (q.adicCompletionIntegers L)) :=
    Commons.NumberTheory.NumberField.Completion.finite_residueField_adicCompletion L q
  haveI hftL : Fintype (IsLocalRing.ResidueField (q.adicCompletionIntegers L)) := Fintype.ofFinite _
  -- `N ≥ 2`, as the residue field is a nontrivial finite field
  have hN2 : 2 ≤ N := by
    rw [hNdef, Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  -- the residue field of the completion of `L` at `q` has `N ^ f` elements
  have hcardL : Nat.card (IsLocalRing.ResidueField (q.adicCompletionIntegers L)) = N ^ f := by
    rw [hNdef, hfdef]
    exact Commons.NumberTheory.NumberField.Completion.natCard_residueField_adicCompletion_eq_pow_inertiaDeg
      K L 𝔭 q hq
  have hn : N ^ m - 1 ≠ 0 := by
    have h2 : 1 < N ^ m := one_lt_pow' (by omega : 1 < N) hm.ne'
    have h1 : 1 ≤ N ^ m := le_of_lt h2
    omega
  have hζ' : IsPrimitiveRoot ζ (N ^ m - 1) := by simpa [hNdef] using hζ
  -- ## Step 1: `ζ` lies in the ring of integers of `L_q`
  have hmem : ζ ∈ (q.adicCompletionIntegers L : ValuationSubring (q.adicCompletion L)) := by
    rcases ValuationSubring.mem_or_inv_mem (q.adicCompletionIntegers L) ζ with h | h
    · exact h
    · -- `ζ⁻¹ ∈ 𝒪`, hence `ζ = (ζ⁻¹) ^ (N ^ m - 2)` is integral as well
      have hζ0 : ζ ≠ 0 := hζ'.ne_zero hn
      have hζinvpow : (ζ⁻¹) ^ (N ^ m - 1) = 1 := by rw [inv_pow, hζ'.pow_eq_one, inv_one]
      have hge : 1 ≤ N ^ m - 1 := Nat.one_le_iff_ne_zero.mpr hn
      have hsucc : (ζ⁻¹) ^ (N ^ m - 1) = (ζ⁻¹) ^ (N ^ m - 1 - 1) * ζ⁻¹ := by
        rw [← pow_succ, Nat.sub_add_cancel hge]
      have hone : ζ = (ζ⁻¹) ^ (N ^ m - 1 - 1) := by
        symm
        calc (ζ⁻¹) ^ (N ^ m - 1 - 1)
            = (ζ⁻¹) ^ (N ^ m - 1 - 1) * ζ⁻¹ * ζ := by
              rw [mul_assoc, inv_mul_cancel₀ hζ0, mul_one]
          _ = (ζ⁻¹) ^ (N ^ m - 1) * ζ := by rw [← hsucc]
          _ = ζ := by rw [hζinvpow, one_mul]
      rw [hone]
      exact pow_mem h _
  set z : q.adicCompletionIntegers L := ⟨ζ, hmem⟩ with hzdef
  have hzprim : IsPrimitiveRoot z (N ^ m - 1) :=
    isPrimitiveRoot_of_injective_apply
      (f := ValuationSubring.subtype (q.adicCompletionIntegers L))
      (fun a b hab => Subtype.ext hab) (x := z)
      (by
        have : (ValuationSubring.subtype (q.adicCompletionIntegers L)) z = ζ := by
          rw [hzdef]
          rfl
        rw [this]
        exact hζ')
  -- ## Step 2: the order `N ^ m - 1` is a unit of the ring of integers
  have hnunit : IsUnit ((N ^ m - 1 : ℕ) : q.adicCompletionIntegers L) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_natCast]
    intro h0
    set κL := IsLocalRing.ResidueField (q.adicCompletionIntegers L) with hκL
    have hpprime : (ringChar κL).Prime := CharP.prime_ringChar κL
    haveI : Fact (ringChar κL).Prime := ⟨hpprime⟩
    -- the residue characteristic divides `N ^ f = #κ(q)`, hence divides `N`
    have hpdvdcard : ringChar κL ∣ N ^ f := by
      rw [← hcardL, Nat.card_eq_fintype_card]
      exact (prime_dvd_char_iff_dvd_card (ringChar κL)).mp (dvd_refl _)
    have hpdvdN : ringChar κL ∣ N := hpprime.dvd_of_dvd_pow hpdvdcard
    -- but `N ^ m ≡ 0`, so `ringChar κL` cannot divide `N ^ m - 1`
    have hpdvdn : ringChar κL ∣ N ^ m - 1 :=
      (CharP.cast_eq_zero_iff κL (ringChar κL) (N ^ m - 1)).mp h0
    have hpnd : ringChar κL ∣ N ^ m := hpdvdN.trans (dvd_pow_self _ hm.ne')
    have hone : ringChar κL ∣ 1 := by
      have hsub := Nat.dvd_sub hpnd hpdvdn
      rwa [Nat.sub_sub_self (Nat.one_le_pow m N (by omega))] at hsub
    exact hpprime.not_dvd_one hone
  -- ## Step 3: the residue of `ζ` is a primitive `(N ^ m - 1)`-st root of unity
  have hresprim : IsPrimitiveRoot
      (IsLocalRing.residue (q.adicCompletionIntegers L) z) (N ^ m - 1) :=
    NK.TameStructureDeep.Tame.isPrimitiveRoot_residue hnunit hzprim
  -- ## Step 4: consequently `N ^ m - 1` divides the order of the residue field's unit group
  have hres0 : IsLocalRing.residue (q.adicCompletionIntegers L) z ≠ 0 := hresprim.ne_zero hn
  set u : (IsLocalRing.ResidueField (q.adicCompletionIntegers L))ˣ :=
    Units.mk0 (IsLocalRing.residue (q.adicCompletionIntegers L) z) hres0 with hudef
  have huval : ((u : (IsLocalRing.ResidueField (q.adicCompletionIntegers L))ˣ) :
      IsLocalRing.ResidueField (q.adicCompletionIntegers L)) =
      IsLocalRing.residue (q.adicCompletionIntegers L) z := by
    rw [hudef]
    exact Units.val_mk0 hres0
  have huprim : IsPrimitiveRoot u (N ^ m - 1) := by
    have h : IsPrimitiveRoot
        (((u : (IsLocalRing.ResidueField (q.adicCompletionIntegers L))ˣ) :
          IsLocalRing.ResidueField (q.adicCompletionIntegers L))) (N ^ m - 1) := by
      rw [huval]
      exact hresprim
    exact IsPrimitiveRoot.coe_units_iff.mp h
  have horder : orderOf u = N ^ m - 1 := huprim.eq_orderOf.symm
  have hdvd : N ^ m - 1 ∣
      Nat.card (IsLocalRing.ResidueField (q.adicCompletionIntegers L)) - 1 := by
    have h := orderOf_dvd_natCard u
    rw [horder, Nat.card_units] at h
    exact h
  rw [hcardL] at hdvd
  -- ## Step 5: elementary arithmetic
  exact dvd_of_pow_sub_one_dvd_pow_sub_one hN2 hm hdvd

end NK.TameStructureDeep.TameDeep

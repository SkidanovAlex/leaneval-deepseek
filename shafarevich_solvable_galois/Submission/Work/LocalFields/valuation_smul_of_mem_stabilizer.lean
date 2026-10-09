/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The valuation at a prime is invariant under its decomposition group

Let `L/K` be a finite Galois extension of number fields and `w` a finite prime of `L`
(a nonzero prime ideal of `𝓞 L`).  The decomposition group `D_w = stabilizer Gal(L/K) w.asIdeal`
acts on `L` by `K`-algebra automorphisms, and the `w`-adic valuation `w.valuation L` is
invariant under this action:

`Work.LocalFields.valuation_smul_of_mem_stabilizer`.

The proof proceeds in three steps, each of independent interest.

* `Work.LocalFields.exists_exp_neg_of_ne_zero_of_le_one` and
  `Work.LocalFields.eq_of_forall_le_exp_neg` : an element of `ℤᵐ⁰ = WithZero (Multiplicative ℤ)`
  which is nonzero and `≤ 1` is of the form `exp (-n)` for a unique `n : ℕ`, so an element of
  `ℤᵐ⁰` in this range is determined by the set of `n` with `a ≤ exp (-n)`.

* `Work.LocalFields.intValuation_map_ringEquiv` : for a Dedekind domain `R`, a prime
  `w : HeightOneSpectrum R` and a ring automorphism `e` of `R` preserving `w`, the `w`-adic
  integer valuation is invariant: `w.intValuation (e a) = w.intValuation a`.  This is a
  consequence of `intValuation_le_pow_iff_mem` and the fact that `Ideal.map e` commutes with
  powers and preserves `w.asIdeal`.

* the reduction to `𝓞 L`: an element `x : L` is a fraction `a / s` of elements of `𝓞 L`
  (`IsLocalization.mk'`), and both the automorphism and the valuation are compatible with this
  description.
-/
import Mathlib
import Submission.Work.LocalFields.Basic
import Submission.Work.LocalFields.Decomposition
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.LocalFields

open scoped NumberField Pointwise Valued WithZero

/-! ## Elements of `ℤᵐ⁰` that are nonzero and dominated by `1`

The value group `ℤᵐ⁰ = WithZero (Multiplicative ℤ)` carries the operation `exp : ℤ → ℤᵐ⁰`.
An element `a` with `a ≠ 0` and `a ≤ 1` is `exp (-n)` for a unique natural number `n`, and the
set `{n | a ≤ exp (-n)}` is the initial segment `{n | n ≤ n₀}`.  Consequently this set determines
`a`.  We record both facts. -/

/-- A nonzero element of `ℤᵐ⁰` that is at most `1` is `exp (-n)` for some `n : ℕ`. -/
theorem exists_exp_neg_of_ne_zero_of_le_one {a : ℤᵐ⁰} (ha : a ≠ 0) (ha1 : a ≤ 1) :
    ∃ m : ℕ, a = WithZero.exp (-(m : ℤ)) := by
  have hk : a = WithZero.exp a.log := (WithZero.exp_log ha).symm
  have h0 : a.log ≤ 0 := by
    have h : WithZero.exp a.log ≤ WithZero.exp (0 : ℤ) := by
      rw [WithZero.exp_zero]; exact hk ▸ ha1
    exact WithZero.exp_le_exp.mp h
  refine ⟨(-a.log).toNat, ?_⟩
  calc a = WithZero.exp a.log := hk
    _ = WithZero.exp (-(↑((-a.log).toNat) : ℤ)) := by
          congr 1
          rw [Int.toNat_of_nonneg (show 0 ≤ -a.log by omega)]
          ring

/-- Two nonzero elements of `ℤᵐ⁰` that are at most `1` and induce the same "`≤ exp (-n)`"
sets for all `n : ℕ` are equal. -/
theorem eq_of_forall_le_exp_neg {a b : ℤᵐ⁰} (ha : a ≠ 0) (hb : b ≠ 0) (ha1 : a ≤ 1)
    (hb1 : b ≤ 1) (h : ∀ n : ℕ, a ≤ WithZero.exp (-(n : ℤ)) ↔ b ≤ WithZero.exp (-(n : ℤ))) :
    a = b := by
  obtain ⟨m, hm⟩ := exists_exp_neg_of_ne_zero_of_le_one ha ha1
  obtain ⟨m', hm'⟩ := exists_exp_neg_of_ne_zero_of_le_one hb hb1
  apply le_antisymm
  · have hb' : b ≤ WithZero.exp (-(m' : ℤ)) := le_of_eq hm'
    have h1 := (h m').mpr hb'
    rwa [← hm'] at h1
  · have ha' : a ≤ WithZero.exp (-(m : ℤ)) := le_of_eq hm
    have h1 := (h m).mp ha'
    rwa [← hm] at h1

/-! ## Invariance of the adic integer valuation under a prime-preserving automorphism -/

/-- For a bijective ring endomorphism `e` of `R` and an ideal `J`, membership of `e a` in
`Ideal.map e J` is membership of `a` in `J`. -/
theorem mem_map_ringEquiv {R : Type*} [CommRing R] (e : R ≃+* R) (J : Ideal R) (a : R) :
    e a ∈ Ideal.map (e : R →+* R) J ↔ a ∈ J := by
  constructor
  · intro h
    obtain ⟨x, hx, hxe⟩ :=
      (Ideal.mem_map_iff_of_surjective (f := (e : R →+* R)) e.surjective).mp h
    rwa [e.injective hxe] at hx
  · intro h
    exact (Ideal.mem_map_iff_of_surjective (f := (e : R →+* R)) e.surjective).mpr ⟨a, h, rfl⟩

/-- The `w`-adic integer valuation on a Dedekind domain is invariant under a ring automorphism
that preserves the prime `w`. -/
theorem intValuation_map_ringEquiv {R : Type*} [CommRing R] [IsDedekindDomain R]
    (w : IsDedekindDomain.HeightOneSpectrum R) (e : R ≃+* R)
    (he : Ideal.map (e : R →+* R) w.asIdeal = w.asIdeal) (a : R) :
    w.intValuation (e a) = w.intValuation a := by
  by_cases ha : a = 0
  · rw [ha, map_zero, map_zero]
  · have hea : e a ≠ 0 := fun h => ha (e.injective (by rw [h, map_zero]))
    refine eq_of_forall_le_exp_neg (w.intValuation_ne_zero _ hea) (w.intValuation_ne_zero _ ha)
      (w.intValuation_le_one _) (w.intValuation_le_one _) (fun n => ?_)
    rw [IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem,
        IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem]
    have hpow : Ideal.map (e : R →+* R) (w.asIdeal ^ n) = w.asIdeal ^ n := by
      rw [Ideal.map_pow, he]
    nth_rewrite 1 [← hpow]
    exact mem_map_ringEquiv e (w.asIdeal ^ n) a

/-! ## Compatibility of the Galois action on `𝓞 L` with `algebraMap` -/

/-- The Galois action on `𝓞 L` is compatible with the canonical inclusion `𝓞 L → L`. -/
theorem gal_algebraMap {K L : Type*} [Field K] [Field L] [Algebra K L] (σ : Gal(L/K))
    (b : 𝓞 L) :
    σ (algebraMap (𝓞 L) L b)
      = algebraMap (𝓞 L) L (MulSemiringAction.toRingEquiv Gal(L/K) (𝓞 L) σ b) := by
  rw [← NumberField.RingOfIntegers.coe_eq_algebraMap b,
      ← NumberField.RingOfIntegers.coe_eq_algebraMap
        (MulSemiringAction.toRingEquiv Gal(L/K) (𝓞 L) σ b)]
  simp only [MulSemiringAction.toRingEquiv_apply_apply]
  rfl

/-! ## The main theorem -/

theorem valuation_smul_of_mem_stabilizer {K L : Type*} [Field K] [Field L] [NumberField K]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (w : Work.LocalFields.FinitePrime L) (σ : Gal(L/K))
    (hσ : σ ∈ Work.LocalFields.decompositionGroup K w) (x : L) :
    w.valuation L (σ x) = w.valuation L x := by
  have hsmul : σ • w.asIdeal = w.asIdeal :=
    (Work.LocalFields.mem_decompositionGroup_iff σ).mp hσ
  let e : 𝓞 L ≃+* 𝓞 L := MulSemiringAction.toRingEquiv Gal(L/K) (𝓞 L) σ
  have he_ringhom : (e : 𝓞 L →+* 𝓞 L) = MulSemiringAction.toRingHom Gal(L/K) (𝓞 L) σ := by
    simp only [e]
    rfl
  have hmap : Ideal.map (e : 𝓞 L →+* 𝓞 L) w.asIdeal = w.asIdeal := by
    rw [he_ringhom, ← Ideal.pointwise_smul_def]
    exact hsmul
  have key : ∀ b : 𝓞 L, w.intValuation (e b) = w.intValuation b :=
    fun b => intValuation_map_ringEquiv w e hmap b
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.mk'_surjective (nonZeroDivisors (𝓞 L)) x
  have hs' : IsLocalization.mk' L a s = x := hs
  have hes0 : (e (s : 𝓞 L)) ∈ nonZeroDivisors (𝓞 L) := by
    rw [mem_nonZeroDivisors_iff_ne_zero]
    intro h
    exact (nonZeroDivisors.coe_ne_zero s) (e.injective (by rw [h, map_zero]))
  let es : nonZeroDivisors (𝓞 L) := ⟨e (s : 𝓞 L), hes0⟩
  have hes : (es : 𝓞 L) = e (s : 𝓞 L) := rfl
  have hσmk : σ (IsLocalization.mk' L a s) = IsLocalization.mk' L (e a) es := by
    have h1 : IsLocalization.mk' L a s * algebraMap (𝓞 L) L (s : 𝓞 L)
        = algebraMap (𝓞 L) L a := IsLocalization.mk'_spec L a s
    have h2 : σ (IsLocalization.mk' L a s) * algebraMap (𝓞 L) L (es : 𝓞 L)
        = algebraMap (𝓞 L) L (e a) := by
      have h2' := congrArg σ h1
      rw [map_mul] at h2'
      rwa [show σ (algebraMap (𝓞 L) L (s : 𝓞 L)) = algebraMap (𝓞 L) L (es : 𝓞 L) from by
              rw [hes]; exact gal_algebraMap σ (s : 𝓞 L),
           show σ (algebraMap (𝓞 L) L a) = algebraMap (𝓞 L) L (e a) from gal_algebraMap σ a]
        at h2'
    have h3 : IsLocalization.mk' L (e a) es * algebraMap (𝓞 L) L (es : 𝓞 L)
        = algebraMap (𝓞 L) L (e a) := IsLocalization.mk'_spec L (e a) es
    have hne : algebraMap (𝓞 L) L (es : 𝓞 L) ≠ 0 := by
      rw [← NumberField.RingOfIntegers.coe_eq_algebraMap]
      exact fun h => nonZeroDivisors.coe_ne_zero es (NumberField.RingOfIntegers.coe_injective h)
    exact mul_right_cancel₀ hne (by rw [h2, h3])
  calc w.valuation L (σ x)
      = w.valuation L (σ (IsLocalization.mk' L a s)) := by rw [← hs']
    _ = w.valuation L (IsLocalization.mk' L (e a) es) := by rw [hσmk]
    _ = w.intValuation (e a) / w.intValuation (es : 𝓞 L) :=
          IsDedekindDomain.HeightOneSpectrum.valuation_of_mk' w
    _ = w.intValuation a / w.intValuation (s : 𝓞 L) := by rw [key a, hes, key (s : 𝓞 L)]
    _ = w.valuation L (IsLocalization.mk' L a s) :=
          (IsDedekindDomain.HeightOneSpectrum.valuation_of_mk' w).symm
    _ = w.valuation L x := by rw [hs']

end Work.LocalFields

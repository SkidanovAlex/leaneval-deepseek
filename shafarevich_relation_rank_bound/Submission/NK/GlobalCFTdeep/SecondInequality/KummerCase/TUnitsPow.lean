/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
# `S`-units, their `p`-th powers, and the Kummer class `H₀ = ⟨a⟩ · U(S)^p`

Vocabulary and elementary lemmas shared by the Kummer case of the second inequality
(Milne, *Class Field Theory*, VII §6):

* `tUnitsPow p S` — the `p`-th powers of the `S`-units, as a subgroup of `Kˣ`;
* `kummerH0 p S u` — Milne's `H₀ = ⟨u⟩ · U(S)^p`;
* `mem_kummerH0_of_exists_pow_eq` (**Claim A**): an `S`-unit which is a `p`-th power in
  `L = K(a^{1/p})` lies in `H₀`.
-/
import Mathlib
import Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase.Defs
import Submission.NK.GlobalCFTdeep.SecondInequality.tUnits_index_powSubgroup
import Submission.NK.GlobalCFTdeep.Herbrand.SIdeles
import Submission.NK.GlobalCFTdeep.Herbrand.finrank_tUnits
import Submission.NK.GlobalCFT.Place
import Submission.NK.GlobalCFT.Idele

open scoped NumberField RestrictedProduct
open IntermediateField
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

namespace NK.GlobalCFTdeep.SecondInequality.KummerCase

open NK.GlobalCFT

section Basic

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]

/-- `[L : K] = p` for a cyclic extension of cardinality `p`. -/
theorem finrank_eq_prime {p : ℕ} (hcard : Nat.card (L ≃ₐ[K] L) = p) :
    Module.finrank K L = p := by
  rw [← IsGalois.card_aut_eq_finrank K L, hcard]

/-- `a` is not a `p`-th power in `K` when `L = K(a^{1/p})` has degree `p`. -/
theorem not_exists_pow_eq_of_adjoin {p : ℕ} (hp : p.Prime)
    (hcard : Nat.card (L ≃ₐ[K] L) = p) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {a : K} (ha : a ≠ 0) {α : L} (hα : α ^ p = algebraMap K L a)
    (hadj : IntermediateField.adjoin K {α} = ⊤) :
    ¬ ∃ c : K, c ^ p = a := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  rintro ⟨c, hc⟩
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hc
    exact ha hc.symm
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hα
    exact (map_ne_zero (algebraMap K L)).mpr ha hα.symm
  have hpow : (α / algebraMap K L c) ^ p = 1 := by
    rw [div_pow, hα, ← map_pow, hc, div_self ((map_ne_zero (algebraMap K L)).mpr ha)]
  have hζL : IsPrimitiveRoot (algebraMap K L ζ) p :=
    hζ.map_of_injective (algebraMap K L).injective
  obtain ⟨i, -, hi⟩ := hζL.eq_pow_of_pow_eq_one hpow
  have hαK : α ∈ (⊥ : IntermediateField K L) := by
    have heq : α = algebraMap K L c * algebraMap K L (ζ ^ i) := by
      rw [map_pow, hi]
      field_simp
      exact (div_self ((map_ne_zero (algebraMap K L)).mpr hc0)).symm
    rw [heq]
    exact mul_mem (IntermediateField.algebraMap_mem _ c)
      (IntermediateField.algebraMap_mem _ (ζ ^ i))
  have htopbot : (⊤ : IntermediateField K L) = ⊥ := by
    rw [← hadj]
    exact le_antisymm (IntermediateField.adjoin_simple_le_iff.mpr hαK) bot_le
  have hsurj : Function.Surjective (algebraMap K L) := by
    intro x
    exact IntermediateField.mem_bot.mp (htopbot ▸ (IntermediateField.mem_top : x ∈ (⊤ : IntermediateField K L)))
  have hfr : Module.finrank K L = 1 :=
    Algebra.finrank_eq_one_iff_bijective_algebraMap.mpr
      ⟨(algebraMap K L).injective, hsurj⟩
  have hp1 : p = 1 := by rw [← finrank_eq_prime hcard, hfr]
  exact hp.ne_one hp1

end Basic

section LocalUnits

variable {K : Type} [Field K] [NumberField K]

/-- The value group of a completion has no nontrivial `p`-th roots of unity. -/
theorem withZero_pow_eq_one {p : ℕ} (hp : p.Prime) {a : WithZero (Multiplicative ℤ)}
    (h : a ^ p = 1) : a = 1 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  cases a with
  | zero =>
    rw [zero_pow hp.ne_zero] at h
    exact absurd h.symm one_ne_zero
  | coe g =>
    have hg : g ^ p = 1 := WithZero.coe_inj.mp (by
      rw [WithZero.coe_pow, WithZero.coe_one]; exact h)
    have hg1 : g = 1 :=
      Commons.NumberTheory.NumberField.Completion.pow_right_injective_zint hp.ne_zero
        (a := g) (b := 1) (by rw [hg, one_pow])
    rw [hg1]
    exact WithZero.coe_one.symm

/-- A `p`-th power whose value is a local unit is a local unit. -/
theorem mem_localUnits_of_pow_mem {p : ℕ} (hp : p.Prime) {v : Place K}
    {x : (Place.localField K v)ˣ} (h : x ^ p ∈ Place.localUnits K v) :
    x ∈ Place.localUnits K v := by
  cases v with
  | inl w => exact Place.mem_localUnits_ofInfinite
  | inr q =>
      rw [Place.mem_localUnits_ofFinite_iff_valued_eq_one] at h ⊢
      have h2 : (Valued.v (x : q.adicCompletion K)) ^ p = 1 := by
        rw [← map_pow, ← Units.val_pow_eq_pow_val, h]
      exact withZero_pow_eq_one hp h2

/-- A `p`-th power which is an `S`-unit has a `p`-th root which is an `S`-unit. -/
theorem mem_TUnits_of_pow_mem {p : ℕ} (hp : p.Prime) (S : Set (Place K)) {x : Kˣ}
    (h : x ^ p ∈ NK.GlobalCFTdeep.TUnits (L := K) S) :
    x ∈ NK.GlobalCFTdeep.TUnits (L := K) S := by
  rw [NK.GlobalCFTdeep.mem_TUnits] at h ⊢
  intro w hw
  refine mem_localUnits_of_pow_mem (K := K) hp ?_
  simpa only [map_pow] using h w hw

end LocalUnits

section Gen

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- An element of `L` fixed by a generator of `Gal(L/K)` lies in `K`. -/
theorem mem_bot_of_zpowers_fixing (σ : L ≃ₐ[K] L) (hspan : Subgroup.zpowers σ = ⊤) {x : L}
    (hσx : σ x = x) : x ∈ (⊥ : IntermediateField K L) := by
  have hσE : σ ∈ (IntermediateField.adjoin K {x}).fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    induction hy using IntermediateField.adjoin_induction with
    | mem z hz => rw [Set.mem_singleton_iff] at hz; rw [hz]; exact hσx
    | algebraMap r => exact AlgEquiv.commutes σ r
    | add y z _ _ ihy ihz => rw [map_add, ihy, ihz]
    | inv y _ ihy => rw [map_inv₀, ihy]
    | mul y z _ _ ihy ihz => rw [map_mul, ihy, ihz]
  have hsub : Subgroup.zpowers σ ≤ (IntermediateField.adjoin K {x}).fixingSubgroup :=
    Subgroup.zpowers_le.mpr hσE
  have hfixeq : (IntermediateField.adjoin K {x}).fixingSubgroup = ⊤ := by
    rw [eq_top_iff]
    rw [← hspan]
    exact hsub
  have hbot : IntermediateField.adjoin K {x} = ⊥ := by
    rw [← IsGalois.fixedField_fixingSubgroup (F := K) (E := L)
      (K := IntermediateField.adjoin K {x}), hfixeq, IsGalois.fixedField_top]
  exact IntermediateField.adjoin_simple_le_iff.mp (hbot ▸ le_rfl)

end Gen

section ClaimA

/-- `U(S)^p`, the `p`-th powers of the `S`-units, as a subgroup of `Kˣ`. -/
noncomputable def tUnitsPow {K : Type} [Field K] [NumberField K] (p : ℕ) (S : Set (Place K)) :
    Subgroup (Kˣ) :=
  Subgroup.map (powMonoidHom p) (NK.GlobalCFTdeep.TUnits (L := K) S)

/-- Membership in `U(S)^p` as a subgroup of `Kˣ`. -/
theorem mem_tUnitsPow {K : Type} [Field K] [NumberField K] {p : ℕ} {S : Set (Place K)} {x : Kˣ} :
    x ∈ tUnitsPow (K := K) p S ↔ ∃ y ∈ NK.GlobalCFTdeep.TUnits (L := K) S, y ^ p = x := by
  constructor
  · intro h
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp h
    exact ⟨y, hy, by rwa [powMonoidHom_apply] at hyx⟩
  · rintro ⟨y, hy, hyx⟩
    exact Subgroup.mem_map.mpr ⟨y, hy, by rw [powMonoidHom_apply, hyx]⟩

/-- `H₀ = ⟨a⟩ · U(S)^p`. -/
noncomputable def kummerH0 {K : Type} [Field K] [NumberField K] (p : ℕ) (S : Set (Place K))
    (u : Kˣ) : Subgroup (Kˣ) :=
  Subgroup.closure {u} ⊔ tUnitsPow (K := K) p S

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]


/-- **Claim A (Milne, *CFT* VII §6).**  An `S`-unit which is a `p`-th power in `L` lies in
`⟨a⟩ · U(S)^p`. -/
theorem mem_kummerH0_of_exists_pow_eq {p : ℕ} (hp : p.Prime)
    (hcard : Nat.card (L ≃ₐ[K] L) = p) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {a : K} (ha : a ≠ 0) {α : L} (hα : α ^ p = algebraMap K L a)
    (hadj : IntermediateField.adjoin K {α} = ⊤)
    (S : Finset (NK.GlobalCFT.Place K))
    (haS : Units.mk0 a ha ∈ NK.GlobalCFTdeep.TUnits (L := K) (S : Set (Place K)))
    {b : K} (hb : b ≠ 0)
    (hbS : Units.mk0 b hb ∈ NK.GlobalCFTdeep.TUnits (L := K) (S : Set (Place K)))
    (hbl : ∃ β : L, β ^ p = algebraMap K L b) :
    Units.mk0 b hb ∈ kummerH0 (K := K) p (S : Set (Place K)) (Units.mk0 a ha) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := L ≃ₐ[K] L)
  have hspan : Subgroup.zpowers σ = ⊤ := (Subgroup.eq_top_iff' _).mpr hσ
  obtain ⟨β, hβ⟩ := hbl
  have haL : algebraMap K L a ≠ 0 := (map_ne_zero (algebraMap K L)).mpr ha
  have hbL : algebraMap K L b ≠ 0 := (map_ne_zero (algebraMap K L)).mpr hb
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hα
    exact haL hα.symm
  have hβ0 : β ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hβ
    exact hbL hβ.symm
  have hxpow : (σ α / α) ^ p = 1 := by
    rw [div_pow, ← map_pow, hα, AlgEquiv.commutes, div_self haL]
  have hxne : σ α / α ≠ 1 := by
    intro hcon
    have hfix : σ α = α := by
      rw [div_eq_one_iff_eq hα0] at hcon
      exact hcon
    have hσ1 : σ = 1 := by
      have hmem : σ ∈ (IntermediateField.adjoin K {α}).fixingSubgroup := by
        rw [IntermediateField.mem_fixingSubgroup_iff]
        intro y hy
        induction hy using IntermediateField.adjoin_induction with
        | mem z hz => rw [Set.mem_singleton_iff] at hz; rw [hz]; exact hfix
        | algebraMap r => exact AlgEquiv.commutes σ r
        | add y z _ _ ihy ihz => rw [map_add, ihy, ihz]
        | inv y _ ihy => rw [map_inv₀, ihy]
        | mul y z _ _ ihy ihz => rw [map_mul, ihy, ihz]
      rw [hadj, IntermediateField.fixingSubgroup_top] at hmem
      exact hmem
    have hcard1 : Nat.card (L ≃ₐ[K] L) = 1 := by
      have htop : (⊤ : Subgroup (L ≃ₐ[K] L)) = ⊥ := by
        rw [← hspan, Subgroup.zpowers_eq_bot]
        exact hσ1
      have h1 : (⊥ : Subgroup (L ≃ₐ[K] L)).index = 1 := by
        rw [← htop, Subgroup.index_top]
      rwa [Subgroup.index_bot] at h1
    rw [hcard] at hcard1
    exact hp.ne_one hcard1
  have hxprim : IsPrimitiveRoot (σ α / α) p := by
    haveI : Fact p.Prime := ⟨hp⟩
    rw [← orderOf_eq_prime hxpow hxne]
    exact IsPrimitiveRoot.orderOf _
  have hypow : (σ β / β) ^ p = 1 := by
    rw [div_pow, ← map_pow, hβ, AlgEquiv.commutes, div_self hbL]
  set z : L := σ α / α with hzdef
  have hσα0 : σ α ≠ 0 := fun h => hα0 (σ.injective (by rw [h, map_zero]))
  have hz0 : z ≠ 0 := by
    rw [hzdef]
    exact div_ne_zero hσα0 hα0
  have hxprim' : IsPrimitiveRoot z p := hxprim
  obtain ⟨i, -, hi⟩ := hxprim'.eq_pow_of_pow_eq_one hypow
  have hσx : σ (β * (α ^ i)⁻¹) = β * (α ^ i)⁻¹ := by
    have h1 : σ α = z * α := by rw [hzdef]; field_simp
    have hβ' : σ β = z ^ i * β := by
      rw [show z ^ i = σ β / β from hi]; field_simp
    have hα' : σ (α ^ i) = z ^ i * α ^ i := by rw [map_pow, h1, mul_pow]
    rw [map_mul, map_inv₀, hβ', hα', mul_inv]
    field_simp
  have hxbot : β * (α ^ i)⁻¹ ∈ (⊥ : IntermediateField K L) :=
    mem_bot_of_zpowers_fixing σ hspan hσx
  obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp hxbot
  have hβc : β = algebraMap K L c * α ^ i := by
    rw [hc, mul_assoc, inv_mul_cancel₀ (pow_ne_zero i hα0), mul_one]
  have hcb : c ^ p * a ^ i = b := by
    refine (algebraMap K L).injective ?_
    calc algebraMap K L (c ^ p * a ^ i)
        = (algebraMap K L c) ^ p * (algebraMap K L a) ^ i := by rw [map_mul, map_pow, map_pow]
      _ = (algebraMap K L c) ^ p * (α ^ i) ^ p := by
            rw [← hα, ← pow_mul, Nat.mul_comm, pow_mul]
      _ = (algebraMap K L c * α ^ i) ^ p := by rw [mul_pow]
      _ = β ^ p := by rw [← hβc]
      _ = algebraMap K L b := hβ
  have hc0 : c ≠ 0 := by
    intro h0
    have h2 := hc
    rw [h0, map_zero] at h2
    exact mul_ne_zero hβ0 (inv_ne_zero (pow_ne_zero i hα0)) h2.symm
  have hcS : Units.mk0 c hc0 ∈ NK.GlobalCFTdeep.TUnits (L := K) (S : Set (Place K)) := by
    refine mem_TUnits_of_pow_mem (K := K) hp _ ?_
    have hpowmem : (Units.mk0 c hc0) ^ p =
        (Units.mk0 b hb) * ((Units.mk0 a ha) ^ i)⁻¹ := by
      ext
      simp only [Units.val_pow_eq_pow_val, Units.val_mul, Units.val_inv_eq_inv_val,
        Units.val_mk0]
      rw [← hcb, mul_assoc, mul_inv_cancel₀ (pow_ne_zero i ha), mul_one]
    rw [hpowmem]
    exact mul_mem hbS (inv_mem (pow_mem haS i))
  have hb_eq : Units.mk0 b hb = (Units.mk0 c hc0) ^ p * (Units.mk0 a ha) ^ i := by
    ext
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0]
    rw [← hcb]
  have h1 : (Units.mk0 c hc0) ^ p ∈
      Subgroup.closure {Units.mk0 a ha} ⊔ Subgroup.map (powMonoidHom p)
        (NK.GlobalCFTdeep.TUnits (L := K) (S : Set (Place K))) :=
    Subgroup.mem_sup_right (mem_tUnitsPow.mpr ⟨Units.mk0 c hc0, hcS, rfl⟩)
  have h2 : (Units.mk0 a ha) ^ i ∈
      Subgroup.closure {Units.mk0 a ha} ⊔ Subgroup.map (powMonoidHom p)
        (NK.GlobalCFTdeep.TUnits (L := K) (S : Set (Place K))) :=
    Subgroup.mem_sup_left (Subgroup.pow_mem (Subgroup.closure {Units.mk0 a ha})
      (Subgroup.subset_closure rfl) i)
  rw [hb_eq]
  exact Subgroup.mul_mem _ h1 h2

end ClaimA



end NK.GlobalCFTdeep.SecondInequality.KummerCase

/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Kummer field `k(a^{1/p})` is Galois of degree `p` over `k`

Let `k` be a field containing a primitive `p`-th root of unity `ζ` (`p` a prime), let
`K'` be a separable closure of `k`, and let `a ∈ kˣ` be an element which is not a `p`-th
power.  Then the Kummer field

  `kummerField p a = k(α : α ^ p = a) ⊆ K'`

is a Galois extension of `k` of degree `p`.

The two mathematical inputs are:

* `p ≠ ringChar k`: a primitive `p`-th root of unity cannot exist in characteristic `p`,
  since in characteristic `p` one has `(ζ - 1) ^ p = ζ ^ p - 1 = 0`, forcing `ζ = 1`;
* the polynomial `X ^ p - a` is irreducible over `k` (Mathlib's
  `X_pow_sub_C_irreducible_of_prime`) and separable, has a root `α` in `K'`, and all its
  roots are of the form `ζ ^ i * α` with `ζ ^ i ∈ k`; hence every root lies in `k⟮α⟯` and
  `kummerField p a = k⟮α⟯`, whose `k`-dimension is `deg (minpoly k α) = p`.

Consequently `kummerField p a` is the splitting field of the separable polynomial
`X ^ p - a`, so it is Galois over `k`.
-/
import Mathlib
import Submission.NK.LocalAnabelian.Kummer.Defs

open Polynomial IntermediateField

namespace NK.LocalAnabelian.Kummer

/-- A field containing a primitive `p`-th root of unity has characteristic different from
`p`.  Indeed in characteristic `p` one has `(ζ - 1) ^ p = ζ ^ p - 1 ^ p = 0`, hence `ζ = 1`,
which contradicts `IsPrimitiveRoot.ne_one`. -/
theorem pow_ne_ringChar_of_isPrimitiveRoot {k : Type*} [Field k] (p : ℕ) (hp : p.Prime)
    {ζ : k} (hζ : IsPrimitiveRoot ζ p) : p ≠ ringChar k := by
  intro h
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP k p := by rw [h]; exact ringChar.charP k
  have h1 : (ζ - 1) ^ p = 0 := by rw [sub_pow_char, hζ.pow_eq_one, one_pow, sub_self]
  exact hζ.ne_one hp.one_lt (sub_eq_zero.mp ((pow_eq_zero_iff hp.ne_zero).mp h1))

/-- **The Kummer field of a non-`p`-th power is cyclic of degree `p`.**

For `p` prime, `ζ` a primitive `p`-th root of unity in `k`, `K'` a separable closure of `k`
and `a ∈ kˣ` which is not a `p`-th power, the Kummer field `k(a^{1/p}) ⊆ K'` is a Galois
extension of `k` of degree `p`. -/
theorem isGalois_kummerField_and_finrank {k K' : Type*} [Field k] [Field K']
    [Algebra k K'] [IsSepClosure k K']
    (p : ℕ) (hp : p.Prime) {ζ : k} (hζ : IsPrimitiveRoot ζ p)
    (a : kˣ) (ha : a ∉ powSubgroup p k) :
    IsGalois k (kummerField (K' := K') p a) ∧
      Module.finrank k (kummerField (K' := K') p a) = p := by
  haveI : IsSepClosed K' := IsSepClosure.sep_closed k
  let L : IntermediateField k K' := kummerField (K' := K') p a
  have hb0 : algebraMap k K' (a : k) ≠ 0 := by simp
  -- The characteristic is not `p`, so `X ^ p - a` is separable.
  have hchar : p ≠ ringChar k := pow_ne_ringChar_of_isPrimitiveRoot p hp hζ
  have hpk : (p : k) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime (R := k) hp hchar.symm
  have hsep : (X ^ p - C (a : k)).Separable := separable_X_pow_sub_C (a : k) hpk (by simp)
  -- A `p`-th root `α` of `a` in the separable closure `K'`.
  obtain ⟨α, hα⟩ := IsSepClosed.exists_aeval_eq_zero K' (X ^ p - C (a : k))
      (by rw [degree_X_pow_sub_C hp.pos]; exact Nat.cast_ne_zero.mpr hp.ne_zero) hsep
  rw [aeval_def, eval₂_sub, eval₂_pow, eval₂_C, eval₂_X, sub_eq_zero] at hα
  have hα0 : α ≠ 0 := by
    intro h; rw [h, zero_pow hp.ne_zero] at hα; exact hb0 hα.symm
  -- Every root of `X ^ p - a` is `ζ ^ i * α`, hence `kummerField p a = k⟮α⟯`.
  have hadjoin : L = k⟮α⟯ := by
    apply le_antisymm
    · rw [show L = kummerField (K' := K') p a from rfl, kummerField_le_iff]
      intro β hβ
      have hx : (β / α) ^ p = 1 := by
        rw [div_pow, hβ, hα, div_self hb0]
      have hmem : β / α ∈ nthRoots p (1 : K') := (mem_nthRoots hp.pos).mpr hx
      rw [(hζ.map_of_injective (RingHom.injective (algebraMap k K'))).nthRoots_eq
        (show (1 : K') ^ p = 1 by simp)] at hmem
      simp only [Multiset.mem_map, Multiset.mem_range] at hmem
      obtain ⟨i, hi, hβi⟩ := hmem
      rw [mul_one] at hβi
      have hβeq : β = algebraMap k K' (ζ ^ i) * α := by
        rw [map_pow, hβi, div_mul_cancel₀ β hα0]
      rw [hβeq]
      exact mul_mem (IntermediateField.algebraMap_mem _ (ζ ^ i)) (mem_adjoin_simple_self k α)
    · rw [adjoin_simple_le_iff]
      exact mem_kummerField_of_pow_eq hα
  -- `X ^ p - a` is irreducible over `k`, hence `minpoly k α = X ^ p - a`.
  have ha_ne : ∀ b : k, b ^ p ≠ (a : k) := by
    intro b hb
    have hb0' : b ≠ 0 := by
      rintro rfl
      rw [zero_pow hp.ne_zero] at hb
      exact Units.ne_zero a hb.symm
    refine ha ?_
    rw [powSubgroup, MonoidHom.mem_range]
    exact ⟨Units.mk0 b hb0', by rw [powMonoidHom_apply]; ext; simpa using hb⟩
  have hirr : Irreducible (X ^ p - C (a : k)) := X_pow_sub_C_irreducible_of_prime hp ha_ne
  have hroot : aeval α (X ^ p - C (a : k)) = 0 := by
    rw [aeval_def, eval₂_sub, eval₂_pow, eval₂_C, eval₂_X, sub_eq_zero]
    exact hα
  have hminpoly : minpoly k α = X ^ p - C (a : k) :=
    (minpoly.eq_of_irreducible_of_monic hirr hroot (monic_X_pow_sub_C _ hp.ne_zero)).symm
  have hint : IsIntegral k α := IsIntegral.of_pow hp.pos (by rw [hα]; exact isIntegral_algebraMap)
  have hfin : Module.finrank k L = p := by
    rw [hadjoin, adjoin.finrank hint, hminpoly, natDegree_X_pow_sub_C]
  -- The root set of `X ^ p - a` is exactly the generating set of the Kummer field.
  have hrootset : (X ^ p - C (a : k)).rootSet K' =
      {x : K' | x ^ p = algebraMap k K' (a : k)} := by
    ext x
    rw [mem_rootSet_of_ne (X_pow_sub_C_ne_zero hp.pos (a : k)), aeval_def, eval₂_sub, eval₂_pow,
      eval₂_C, eval₂_X, sub_eq_zero]
    simp
  -- `X ^ p - a` splits over `K'` (its roots are the `ζ ^ i * α`).
  have hsplitK' : ((X ^ p - C (a : k)).map (algebraMap k K')).Splits := by
    have hζ' : IsPrimitiveRoot ((algebraMap k K') ζ) p :=
      hζ.map_of_injective (RingHom.injective (algebraMap k K'))
    have := X_pow_sub_C_splits_of_isPrimitiveRoot hζ' hα
    simpa using this
  -- So the Kummer field is the splitting field of `X ^ p - a` over `k`.
  have hL : L = IntermediateField.adjoin k ((X ^ p - C (a : k)).rootSet K') := by
    rw [hrootset]
    rfl
  have hsplit : (X ^ p - C (a : k)).IsSplittingField k ↥L :=
    hL.symm ▸ IntermediateField.adjoin_rootSet_isSplittingField hsplitK'
  -- A splitting field of a separable polynomial is Galois.
  have hgal : IsGalois k (kummerField (K' := K') p a) := by
    haveI : (X ^ p - C (a : k)).IsSplittingField k ↥L := hsplit
    exact IsGalois.of_separable_splitting_field (p := X ^ p - C (a : k)) hsep
  exact ⟨hgal, hfin⟩

end NK.LocalAnabelian.Kummer

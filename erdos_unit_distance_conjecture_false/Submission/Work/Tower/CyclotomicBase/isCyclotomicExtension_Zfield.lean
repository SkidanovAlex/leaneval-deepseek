import Mathlib
import Submission.Work.Tower.CyclotomicBase.Defs

/-!
# The field fixed by the inertia subgroup of `rᵢ` is a cyclotomic field

Let `r : Fin ℓ → ℕ` be a family of primes and `D = ∏ᵢ rᵢ`.  The Galois group of `ℚ(ζ_D)` is
`(ℤ/D)ˣ`, and the inertia subgroup of the prime `rᵢ` is the subgroup `inertiaSub r i` of units
congruent to `1` modulo `m := D / rᵢ`.  The fixed field `Zfield r i` of this subgroup is
`ℚ(ζ_m)`; in particular it is a cyclotomic extension of `ℚ` cut out by the `m`-th roots of unity.

The proof identifies `Zfield r i` with `ℚ⟮ζ^(rᵢ)⟯ ⊆ ℚ(ζ_D)`, where `ζ` is a primitive `D`-th root
of unity (so that `ζ^(rᵢ)` is a primitive `m`-th root of unity):

* `ℚ⟮ζ^(rᵢ)⟯ ≤ Zfield r i` because `σ ∈ inertiaSub` acts as `x ↦ x ^ a` with `a ≡ 1 (mod m)` on
  every `m`-th root of unity (`galEquivZMod_apply_of_pow_eq`);
* the reverse inclusion follows from `[ℚ⟮ζ^(rᵢ)⟯ : ℚ] = φ(m) = [Zfield r i : ℚ]`, the latter being
  the index of `inertiaSub`, computed as `#((ℤ/m)ˣ)` via the surjectivity of `ZMod.unitsMap`.
-/

set_option linter.style.haveILetI false

open NumberField

namespace Work.Tower.CyclotomicBase

open scoped Classical

theorem isCyclotomicExtension_Zfield {ℓ : ℕ} (r : Fin ℓ → ℕ) (hr : ∀ i, Nat.Prime (r i))
    [NeZero (D r)] (i : Fin ℓ) :
    IsCyclotomicExtension {(D r) / (r i)} ℚ ↥(Zfield r i) := by
  haveI hcyc : IsCyclotomicExtension {D r} ℚ (Cyc r) := isCyclotomicExtension_cyc r
  haveI hgal : IsGalois ℚ (Cyc r) := IsCyclotomicExtension.isGalois {D r} ℚ (Cyc r)
  haveI hint : Algebra.IsIntegral ℚ (Cyc r) := IsCyclotomicExtension.integral {D r} ℚ (Cyc r)
  -- a primitive `D`-th root of unity and its `rᵢ`-th power, a primitive `m`-th root
  let ζ : Cyc r := IsCyclotomicExtension.zeta (D r) ℚ (Cyc r)
  have hζ : IsPrimitiveRoot ζ (D r) := IsCyclotomicExtension.zeta_spec (D r) ℚ (Cyc r)
  have hri0 : r i ≠ 0 := (hr i).ne_zero
  have hm : (D r) / (r i) ≠ 0 := by
    intro h
    have h1 := Nat.div_mul_cancel (r_dvd_D r i)
    rw [h, zero_mul] at h1
    exact NeZero.ne (D r) h1.symm
  haveI hmz : NeZero ((D r) / (r i)) := ⟨hm⟩
  have hζm : IsPrimitiveRoot (ζ ^ (r i)) ((D r) / (r i)) := hζ.pow_of_dvd hri0 (r_dvd_D r i)
  -- `ζ^(rᵢ)` is fixed by the inertia subgroup
  have hmem : ζ ^ (r i) ∈ Zfield r i := by
    rw [Zfield, IntermediateField.mem_fixedField_iff]
    intro f hf
    -- the exponent `a` attached to `f` is `1` modulo `m`
    have hv : (galEquiv r f).val.val ≡ 1 [MOD (D r) / (r i)] := by
      have h : (ZMod.unitsMap (div_r_dvd_D r i)) (galEquiv r f) = 1 := by
        simpa [inertiaSub, Subgroup.mem_comap] using hf
      have hcast : ((galEquiv r f : ZMod (D r)).cast : ZMod ((D r) / (r i))) = 1 := by
        rw [← ZMod.unitsMap_val (div_r_dvd_D r i) (galEquiv r f), h, Units.val_one]
      have h3 : ((galEquiv r f).val.val : ZMod ((D r) / (r i))) = 1 := by
        rw [← ZMod.cast_natCast (div_r_dvd_D r i) (galEquiv r f).val.val, ZMod.natCast_zmod_val]
        exact hcast
      exact (ZMod.natCast_eq_natCast_iff ((galEquiv r f).val.val) 1 ((D r) / (r i))).mp
        (by simpa using h3)
    have hbD : (ζ ^ (r i)) ^ (D r) = 1 := by
      rw [← pow_mul, Nat.mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    -- `f` acts on any `D`-th root of unity as `x ↦ x ^ a`
    have hact := IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq (D r) (Cyc r) f hbD
    have hof : IsOfFinOrder (ζ ^ (r i)) := hζm.isOfFinOrder hm
    have hmod : (galEquiv r f).val.val ≡ 1 [MOD orderOf (ζ ^ (r i))] :=
      Nat.ModEq.of_dvd (orderOf_dvd_of_pow_eq_one hζm.pow_eq_one) hv
    rw [hact]
    rw [show (IsCyclotomicExtension.Rat.galEquivZMod (D r) (Cyc r) f).val.val =
      (galEquiv r f).val.val from rfl]
    simpa using (IsOfFinOrder.pow_eq_pow_iff_modEq hof).mpr hmod
  -- `[Zfield r i : ℚ] = φ(m)`
  have hfrZ : Module.finrank ℚ ↥(Zfield r i) = ((D r) / (r i)).totient := by
    rw [IntermediateField.finrank_eq_fixingSubgroup_index (L := Zfield r i), fixingSubgroup_Zfield]
    have hidx : (Subgroup.comap (galEquiv r).toMonoidHom (inertiaSub r i)).index =
        (inertiaSub r i).index :=
      Subgroup.index_comap_of_surjective (inertiaSub r i) (galEquiv r).surjective
    rw [hidx, inertiaSub, Subgroup.index_ker]
    rw [show (ZMod.unitsMap (div_r_dvd_D r i)).range = ⊤ from
      MonoidHom.range_eq_top.mpr (ZMod.unitsMap_surjective (div_r_dvd_D r i)),
      Nat.card_congr (Subgroup.topEquiv (G := (ZMod ((D r) / (r i)))ˣ)).toEquiv,
      Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  -- `[ℚ⟮ζ^(rᵢ)⟯ : ℚ] = φ(m)`
  haveI hcycAd : IsCyclotomicExtension {(D r) / (r i)} ℚ
      ↥(IntermediateField.adjoin ℚ ({ζ ^ (r i)} : Set (Cyc r))) :=
    hζm.intermediateField_adjoin_isCyclotomicExtension ℚ
  have hfrA : Module.finrank ℚ ↥(IntermediateField.adjoin ℚ ({ζ ^ (r i)} : Set (Cyc r)))
      = ((D r) / (r i)).totient :=
    IsCyclotomicExtension.finrank _
      (Polynomial.cyclotomic.irreducible_rat (Nat.pos_of_ne_zero hm))
  -- hence the two fields coincide
  have hle : IntermediateField.adjoin ℚ ({ζ ^ (r i)} : Set (Cyc r)) ≤ Zfield r i := by
    rw [IntermediateField.adjoin_le_iff]
    rw [Set.singleton_subset_iff]
    exact hmem
  have heq : Zfield r i = IntermediateField.adjoin ℚ ({ζ ^ (r i)} : Set (Cyc r)) :=
    (IntermediateField.eq_of_le_of_finrank_le hle (by rw [hfrZ, hfrA])).symm
  exact IsCyclotomicExtension.equiv {(D r) / (r i)} ℚ
    ↥(IntermediateField.adjoin ℚ ({ζ ^ (r i)} : Set (Cyc r)))
    (IntermediateField.equivOfEq heq.symm)

end Work.Tower.CyclotomicBase

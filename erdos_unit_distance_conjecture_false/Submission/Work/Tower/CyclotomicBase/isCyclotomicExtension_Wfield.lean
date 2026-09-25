import Mathlib
import Submission.Work.Tower.CyclotomicBase.Defs
import Submission.Work.Tower.CyclotomicBase.Basic

/-!
# The field `Wᵢ = ℚ(ζ_{rᵢ})` is a cyclotomic extension of `ℚ`

Let `r : Fin ℓ → ℕ` be a family of primes and `D = ∏ᵢ rᵢ`.  The Galois group of `ℚ(ζ_D)` is
`(ℤ/D)ˣ`, and `Wfield r i` is the fixed field of the subgroup `otherSub r i` of units congruent
to `1` modulo `rᵢ`.  This field is `ℚ(ζ_{rᵢ})`; in particular it is a cyclotomic extension of `ℚ`
cut out by the `rᵢ`-th roots of unity.

The proof identifies `Wfield r i` with `ℚ⟮ζ^(D/rᵢ)⟯ ⊆ ℚ(ζ_D)`, where `ζ` is a primitive `D`-th
root of unity (so that `ζ^(D/rᵢ)` is a primitive `rᵢ`-th root of unity), mirroring the proof of
`isCyclotomicExtension_Zfield` with the roles of `rᵢ` and `D/rᵢ` exchanged:

* `ℚ⟮ζ^(D/rᵢ)⟯ ≤ Wfield r i` because `σ ∈ otherSub r i` acts as `x ↦ x ^ a` with
  `a ≡ 1 (mod rᵢ)` on every `rᵢ`-th root of unity (`galEquivZMod_apply_of_pow_eq`);
* the reverse inclusion follows from `[ℚ⟮ζ^(D/rᵢ)⟯ : ℚ] = φ(rᵢ) = [Wfield r i : ℚ]`, the latter
  being the index of `otherSub r i`, computed as `#((ℤ/rᵢ)ˣ)` via the surjectivity of
  `ZMod.unitsMap`.
-/

set_option linter.style.haveILetI false
set_option autoImplicit false

open NumberField

namespace Work.Tower.CyclotomicBase

open scoped Classical

theorem isCyclotomicExtension_Wfield {ℓ : ℕ} (r : Fin ℓ → ℕ) (hr : ∀ i, Nat.Prime (r i))
    [NeZero (D r)] (i : Fin ℓ) :
    IsCyclotomicExtension {r i} ℚ ↥(Wfield r i) := by
  haveI hcyc : IsCyclotomicExtension {D r} ℚ (Cyc r) := isCyclotomicExtension_cyc r
  haveI hgal : IsGalois ℚ (Cyc r) := IsCyclotomicExtension.isGalois {D r} ℚ (Cyc r)
  haveI hint : Algebra.IsIntegral ℚ (Cyc r) := IsCyclotomicExtension.integral {D r} ℚ (Cyc r)
  -- a primitive `D`-th root of unity and its `(D/rᵢ)`-th power, a primitive `rᵢ`-th root
  let ζ : Cyc r := IsCyclotomicExtension.zeta (D r) ℚ (Cyc r)
  have hζ : IsPrimitiveRoot ζ (D r) := IsCyclotomicExtension.zeta_spec (D r) ℚ (Cyc r)
  have hri0 : r i ≠ 0 := (hr i).ne_zero
  haveI hriz : NeZero (r i) := ⟨hri0⟩
  have hm : (D r) / (r i) ≠ 0 := by
    intro h
    have h1 := Nat.div_mul_cancel (r_dvd_D r i)
    rw [h, zero_mul] at h1
    exact NeZero.ne (D r) h1.symm
  have hζm : IsPrimitiveRoot (ζ ^ ((D r) / (r i))) (r i) := by
    have h1 := hζ.pow_of_dvd hm (div_r_dvd_D r i)
    rwa [Nat.div_div_self (r_dvd_D r i) (NeZero.ne (D r))] at h1
  -- `ζ^(D/rᵢ)` is fixed by the subgroup of units congruent to `1` modulo `rᵢ`
  have hmem : ζ ^ ((D r) / (r i)) ∈ Wfield r i := by
    rw [Wfield, IntermediateField.mem_fixedField_iff]
    intro f hf
    -- the exponent `a` attached to `f` is `1` modulo `rᵢ`
    have hv : (galEquiv r f).val.val ≡ 1 [MOD r i] := by
      have h : (ZMod.unitsMap (r_dvd_D r i)) (galEquiv r f) = 1 := by
        simpa [otherSub, Subgroup.mem_comap] using hf
      have hcast : ((galEquiv r f : ZMod (D r)).cast : ZMod (r i)) = 1 := by
        rw [← ZMod.unitsMap_val (r_dvd_D r i) (galEquiv r f), h, Units.val_one]
      have h3 : ((galEquiv r f).val.val : ZMod (r i)) = 1 := by
        rw [← ZMod.cast_natCast (r_dvd_D r i) (galEquiv r f).val.val, ZMod.natCast_zmod_val]
        exact hcast
      exact (ZMod.natCast_eq_natCast_iff ((galEquiv r f).val.val) 1 (r i)).mp
        (by simpa using h3)
    have hbD : (ζ ^ ((D r) / (r i))) ^ (D r) = 1 := by
      rw [← pow_mul, Nat.mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    -- `f` acts on any `D`-th root of unity as `x ↦ x ^ a`
    have hact := IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq (D r) (Cyc r) f hbD
    have hof : IsOfFinOrder (ζ ^ ((D r) / (r i))) := hζm.isOfFinOrder hri0
    have hmod : (galEquiv r f).val.val ≡ 1 [MOD orderOf (ζ ^ ((D r) / (r i)))] :=
      Nat.ModEq.of_dvd (orderOf_dvd_of_pow_eq_one hζm.pow_eq_one) hv
    rw [hact]
    rw [show (IsCyclotomicExtension.Rat.galEquivZMod (D r) (Cyc r) f).val.val =
      (galEquiv r f).val.val from rfl]
    simpa using (IsOfFinOrder.pow_eq_pow_iff_modEq hof).mpr hmod
  -- `[Wfield r i : ℚ] = φ(rᵢ)`
  have hfrW : Module.finrank ℚ ↥(Wfield r i) = (r i).totient := by
    rw [IntermediateField.finrank_eq_fixingSubgroup_index (L := Wfield r i), fixingSubgroup_Wfield]
    have hidx : (Subgroup.comap (galEquiv r).toMonoidHom (otherSub r i)).index =
        (otherSub r i).index :=
      Subgroup.index_comap_of_surjective (otherSub r i) (galEquiv r).surjective
    rw [hidx, otherSub, Subgroup.index_ker]
    rw [show (ZMod.unitsMap (r_dvd_D r i)).range = ⊤ from
      MonoidHom.range_eq_top.mpr (ZMod.unitsMap_surjective (r_dvd_D r i)),
      Nat.card_congr (Subgroup.topEquiv (G := (ZMod (r i))ˣ)).toEquiv,
      Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  -- `[ℚ⟮ζ^(D/rᵢ)⟯ : ℚ] = φ(rᵢ)`
  haveI hcycAd : IsCyclotomicExtension {r i} ℚ
      ↥(IntermediateField.adjoin ℚ ({ζ ^ ((D r) / (r i))} : Set (Cyc r))) :=
    hζm.intermediateField_adjoin_isCyclotomicExtension ℚ
  have hfrA : Module.finrank ℚ ↥(IntermediateField.adjoin ℚ ({ζ ^ ((D r) / (r i))} : Set (Cyc r)))
      = (r i).totient :=
    IsCyclotomicExtension.finrank _
      (Polynomial.cyclotomic.irreducible_rat (Nat.pos_of_ne_zero hri0))
  -- hence the two fields coincide
  have hle : IntermediateField.adjoin ℚ ({ζ ^ ((D r) / (r i))} : Set (Cyc r)) ≤ Wfield r i := by
    rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
    exact hmem
  have heq : Wfield r i = IntermediateField.adjoin ℚ ({ζ ^ ((D r) / (r i))} : Set (Cyc r)) :=
    (IntermediateField.eq_of_le_of_finrank_le hle (by rw [hfrW, hfrA])).symm
  exact IsCyclotomicExtension.equiv {r i} ℚ
    ↥(IntermediateField.adjoin ℚ ({ζ ^ ((D r) / (r i))} : Set (Cyc r)))
    (IntermediateField.equivOfEq heq.symm)

end Work.Tower.CyclotomicBase

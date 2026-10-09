import Mathlib
import Submission.NK.TameStructureDeep.Tame.units_mem_pow_of_residue_pow_eq_one
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.TameStructureDeep.Tame

theorem exists_rootOfUnity_unit_zpow {A : Type*} [CommRing A] [IsLocalRing A]
    [HenselianLocalRing A] [Finite (IsLocalRing.ResidueField A)] {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hunit : IsUnit (ℓ : A)) (hdiv : ℓ ∣ Nat.card (IsLocalRing.ResidueField A) - 1) :
    ∃ ω : Aˣ,
      (ω : A) ^ (Nat.card (IsLocalRing.ResidueField A) - 1) = 1 ∧
      IsPrimitiveRoot (IsLocalRing.residue A (ω : A))
        (Nat.card (IsLocalRing.ResidueField A) - 1) ∧
      ∀ u : Aˣ, ∃ (j : ℤ) (w : A), w ^ ℓ = (u : A) * ((ω ^ j : Aˣ) : A) := by
  classical
  haveI : Fintype (IsLocalRing.ResidueField A) := Fintype.ofFinite _
  set N := Nat.card (IsLocalRing.ResidueField A) - 1 with hN
  -- A generator of the cyclic group `kˣ`.
  obtain ⟨ωk, hωgen⟩ := IsCyclic.exists_generator (α := (IsLocalRing.ResidueField A)ˣ)
  have hωorder : orderOf (ωk : IsLocalRing.ResidueField A) = N := by
    rw [orderOf_units, orderOf_eq_card_of_forall_mem_zpowers hωgen, Nat.card_units, hN]
  have hωprim : IsPrimitiveRoot (ωk : IsLocalRing.ResidueField A) N :=
    IsPrimitiveRoot.iff_orderOf.mpr hωorder
  -- `N = #k - 1` is a unit of `A`.
  have h1k : 1 ≤ Nat.card (IsLocalRing.ResidueField A) := by
    rw [Nat.card_eq_fintype_card]
    exact le_of_lt Fintype.one_lt_card
  have hNunit : IsUnit (N : A) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
    simp only [map_natCast]
    have hcard0 : (Nat.card (IsLocalRing.ResidueField A) : IsLocalRing.ResidueField A) = 0 := by
      rw [Nat.card_eq_fintype_card]
      exact FiniteField.cast_card_eq_zero _
    rw [hN, Nat.cast_sub h1k, hcard0]
    simp
  -- Teichmüller lift of `ωk`.
  obtain ⟨ζ, hζpow, hζres⟩ :=
    Commons.RingTheory.Henselian.kummer_root_lift (R := A) N isUnit_one hNunit
      (ωk : IsLocalRing.ResidueField A) (by rw [map_one]; exact hωprim.pow_eq_one)
  have hζunit : IsUnit ζ := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, hζres]
    exact ωk.ne_zero
  have hmapω : Units.map (IsLocalRing.residue A).toMonoidHom hζunit.unit = ωk := by
    apply Units.ext
    simp [Units.coe_map, IsUnit.unit_spec, hζres]
  refine ⟨hζunit.unit, ?_, ?_, ?_⟩
  · rw [IsUnit.unit_spec]
    exact hζpow
  · rw [IsUnit.unit_spec, hζres]
    exact hωprim
  · intro u
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp
      (hωgen (Units.map (IsLocalRing.residue A).toMonoidHom u))
    have hmapu : Units.map (IsLocalRing.residue A).toMonoidHom
        (u * hζunit.unit ^ (-m)) = 1 := by
      rw [map_mul, map_zpow, hmapω, ← hm, ← zpow_add, add_neg_cancel, zpow_zero]
    have hres1 : IsLocalRing.residue A ((u * hζunit.unit ^ (-m) : Aˣ) : A) = 1 := by
      have hcoe : ((Units.map (IsLocalRing.residue A).toMonoidHom
          (u * hζunit.unit ^ (-m)) : (IsLocalRing.ResidueField A)ˣ) :
          IsLocalRing.ResidueField A) = 1 := by
        rw [hmapu]
        exact Units.val_one
      rw [Units.coe_map] at hcoe
      exact hcoe
    have hres : IsLocalRing.residue A ((u * hζunit.unit ^ (-m) : Aˣ) : A) ^
        ((Nat.card (IsLocalRing.ResidueField A) - 1) / ℓ) = 1 := by
      rw [hres1, one_pow]
    obtain ⟨w', hw'⟩ := MonoidHom.mem_range.mp
      (units_mem_pow_of_residue_pow_eq_one hℓ hunit hdiv (u * hζunit.unit ^ (-m)) hres)
    rw [powMonoidHom_apply] at hw'
    refine ⟨-m, (w' : A), ?_⟩
    rw [← Units.val_pow_eq_pow_val, hw']
    simp

end NK.TameStructureDeep.Tame

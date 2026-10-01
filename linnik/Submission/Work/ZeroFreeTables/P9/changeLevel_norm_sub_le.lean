import Mathlib

namespace Work.ZeroFreeTables.P9

open DirichletCharacter

/-- Every value of a Dirichlet character with values in `ℂ` has norm at most one:
it vanishes on non-units, and takes roots of unity on units. -/
lemma norm_apply_le_one_Dirichlet {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (a : ZMod N) : ‖χ a‖ ≤ 1 := by
  by_cases ha : IsUnit a
  · have hk : Fintype.card (ZMod N)ˣ ≠ 0 := Fintype.card_ne_zero
    have hpow : χ a ^ Fintype.card (ZMod N)ˣ = 1 := by
      rw [← ha.unit_spec, ← MulChar.pow_apply_coe χ _ ha.unit, MulChar.pow_card_eq_one,
        MulChar.one_apply_coe]
    rw [Complex.norm_eq_one_of_pow_eq_one hpow hk]
  · rw [MulChar.map_nonunit χ ha, norm_zero]
    norm_num

theorem changeLevel_norm_sub_le {N q : ℕ} [NeZero N] [NeZero q] (hNq : N ∣ q) (ψ : DirichletCharacter ℂ N) (n : ℕ) :
    ‖(DirichletCharacter.changeLevel hNq ψ) (n : ZMod q) - ψ (n : ZMod N)‖ ≤ (if Nat.Coprime n N ∧ ¬ Nat.Coprime n q then (1:ℝ) else 0) := by
  by_cases hq : Nat.Coprime n q
  · -- `n` is a unit modulo `q`, so `changeLevel` does not change its value
    have hcast : (DirichletCharacter.changeLevel hNq ψ) (n : ZMod q) = ψ (n : ZMod N) := by
      have h := DirichletCharacter.changeLevel_eq_cast_of_dvd' ψ hNq (a := (n : ℤ))
        (Nat.isCoprime_iff_coprime.mpr hq)
      simpa using h
    rw [hcast, sub_self, norm_zero]
    simp [hq]
  · -- `n` is not a unit modulo `q`, so `changeLevel ψ` vanishes at it
    have hnq : ¬ IsUnit (n : ZMod q) := fun h => hq ((ZMod.isUnit_iff_coprime n q).mp h)
    have hzero : (DirichletCharacter.changeLevel hNq ψ) (n : ZMod q) = 0 :=
      MulChar.map_nonunit _ hnq
    rw [hzero, zero_sub, norm_neg]
    by_cases hN : Nat.Coprime n N
    · rw [if_pos ⟨hN, hq⟩]
      exact norm_apply_le_one_Dirichlet ψ (n : ZMod N)
    · have hnN : ¬ IsUnit (n : ZMod N) := fun h => hN ((ZMod.isUnit_iff_coprime n N).mp h)
      rw [MulChar.map_nonunit ψ hnN]
      simp [hN]

end Work.ZeroFreeTables.P9

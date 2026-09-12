import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Pow

set_option linter.style.haveILetI false

namespace Commons.Data.ZMod

theorem even_val_iff_two_mul {t : ℕ} (z : ZMod (2 ^ t)) : Even z.val ↔ ∃ w : ZMod (2 ^ t), z = 2 * w := by
  haveI : NeZero (2 ^ t) := ⟨pow_ne_zero t (by norm_num : 2 ≠ 0)⟩
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨(k : ZMod (2 ^ t)), ?_⟩
    calc
      z = (z.val : ZMod (2 ^ t)) := (ZMod.natCast_zmod_val z).symm
      _ = (((k + k) : ℕ) : ZMod (2 ^ t)) := by rw [hk]
      _ = (k : ZMod (2 ^ t)) + (k : ZMod (2 ^ t)) := by rw [Nat.cast_add]
      _ = 2 * (k : ZMod (2 ^ t)) := by rw [← two_mul]
  · intro h
    by_cases ht0 : t = 0
    · subst t
      have hlt : z.val < 2 ^ 0 := ZMod.val_lt z
      norm_num at hlt
      rw [hlt]
      exact ⟨0, rfl⟩
    · have ht : 1 ≤ t := by omega
      have h2 : 2 ∣ 2 ^ t := by
        refine ⟨2 ^ (t - 1), ?_⟩
        calc
          2 ^ t = 2 ^ ((t - 1) + 1) := by rw [Nat.sub_add_cancel ht]
          _ = 2 ^ (t - 1) * 2 ^ 1 := by rw [pow_add]
          _ = 2 ^ (t - 1) * 2 := by rw [pow_one]
          _ = 2 * 2 ^ (t - 1) := by rw [mul_comm]
      let φ : ZMod (2 ^ t) →+* ZMod 2 := ZMod.castHom h2 (ZMod 2)
      have hφz : φ z = (z.val : ZMod 2) := by
        rw [ZMod.castHom_apply]
        exact ZMod.cast_eq_val z
      have hφ2 : φ (2 : ZMod (2 ^ t)) = 0 := by
        rw [show (2 : ZMod (2 ^ t)) = ((2 : ℕ) : ZMod (2 ^ t)) by rfl]
        rw [map_natCast]
        exact ZMod.natCast_self 2
      have hφ0 : φ z = 0 := by
        rcases h with ⟨w, hw⟩
        rw [hw]
        rw [map_mul, hφ2]
        simp
      have hz0 : (z.val : ZMod 2) = 0 := by
        rw [← hφz]
        exact hφ0
      exact ZMod.natCast_eq_zero_iff_even.mp hz0

end Commons.Data.ZMod
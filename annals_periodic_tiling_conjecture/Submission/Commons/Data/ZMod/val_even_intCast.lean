import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum.Basic

namespace Commons.Data.ZMod

theorem val_even_intCast {t : ℕ} (ht : 1 ≤ t) (x : ℤ) :
    Even ((x : ZMod (2 ^ t)).val) ↔ Even x := by
  let v : ℕ := (x : ZMod (2 ^ t)).val
  change Even v ↔ Even x
  have hv : (v : ℤ) = x % ((2 ^ t : ℕ) : ℤ) := by
    dsimp [v]
    exact ZMod.val_intCast x
  have h2dvd : (2 : ℤ) ∣ ((2 ^ t : ℕ) : ℤ) := by
    have hnat : 2 * 2 ^ (t - 1) = 2 ^ t := by
      rw [mul_comm, ← pow_succ, Nat.sub_add_cancel ht]
    refine ⟨(2 ^ (t - 1) : ℕ), ?_⟩
    exact_mod_cast hnat.symm
  have hlift : Even v ↔ (v : ℤ) % (2 : ℤ) = 0 := by
    rw [Nat.even_iff]
    constructor
    · intro h
      change (v : ℤ) % ↑(2 : ℕ) = 0
      rw [← Int.natCast_mod, h]
      norm_num
    · intro h
      change (v : ℤ) % ↑(2 : ℕ) = 0 at h
      rw [← Int.natCast_mod] at h
      exact_mod_cast h
  rw [hlift, Int.even_iff, hv]
  rw [← Int.emod_emod_of_dvd x h2dvd]

end Commons.Data.ZMod
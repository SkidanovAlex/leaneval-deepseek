import Mathlib

namespace Commons.NumberTheory.DirichletCharacter

/-- The element `p ^ (e - 1)` is nilpotent of square zero in `ZMod (p ^ e)` when `2 ≤ e`. -/
private lemma natCast_pow_sq_eq_zero (p e : ℕ) (he : 2 ≤ e) :
    (((p ^ (e - 1) : ℕ)) : ZMod (p ^ e)) * (((p ^ (e - 1) : ℕ)) : ZMod (p ^ e)) = 0 := by
  rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff, ← pow_add]
  exact pow_dvd_pow p (by omega)

/-- The key congruence: `(1 + p ^ (e - 1)) ^ k ≡ 1 + p ^ (e - 1) * k` in `ZMod (p ^ e)`
for `2 ≤ e`. -/
private lemma pow_one_add_eq (p e : ℕ) (he : 2 ≤ e) (k : ℕ) :
    (((1 + p ^ (e - 1) : ℕ)) : ZMod (p ^ e)) ^ k
      = ((1 + p ^ (e - 1) * k : ℕ) : ZMod (p ^ e)) := by
  set t : ZMod (p ^ e) := ((p ^ (e - 1) : ℕ) : ZMod (p ^ e)) with htdef
  have ht : t * t = 0 := by
    rw [htdef]
    exact natCast_pow_sq_eq_zero p e he
  have hpow : ∀ k : ℕ, (1 + t) ^ k = 1 + (k : ZMod (p ^ e)) * t := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ih]
      have hk : ((k + 1 : ℕ) : ZMod (p ^ e)) = (k : ZMod (p ^ e)) + 1 := by
        rw [Nat.cast_add, Nat.cast_one]
      rw [hk]
      linear_combination (k : ZMod (p ^ e)) * ht
  have h1 : (((1 + p ^ (e - 1) : ℕ)) : ZMod (p ^ e)) = 1 + t := by
    rw [Nat.cast_add, Nat.cast_one, htdef]
  rw [h1, hpow, htdef]
  push_cast
  ring

theorem primePowKernel_char_pow (p e : ℕ) (he : 2 ≤ e) (χ : DirichletCharacter ℂ (p^e)) (k : ℕ) :
    χ (((1 + (p : ℤ) ^ (e - 1) * (k : ℤ) : ℤ)) : ZMod (p ^ e))
      = (χ ((((1 + p ^ (e - 1) : ℕ)) : ZMod (p ^ e)))) ^ k := by
  have hmain : ((((1 + p ^ (e - 1) : ℕ)) : ZMod (p ^ e)) ^ k)
      = (((1 + (p : ℤ) ^ (e - 1) * (k : ℤ) : ℤ)) : ZMod (p ^ e)) := by
    rw [pow_one_add_eq p e he k]
    push_cast
    ring
  rw [← hmain, map_pow]

end Commons.NumberTheory.DirichletCharacter

import Mathlib
import Submission.Work.BMF.recursion.ShiftDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.recursion

/-- Since `k ≥ 1`, the modulus `p^k` is a multiple of `p`. -/
private lemma prime_dvd_prime_pow_int (p k : ℕ) (hk : 1 ≤ k) : (p : ℤ) ∣ (p : ℤ) ^ k := by
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  rw [hj, pow_succ]
  exact dvd_mul_left (p : ℤ) _

lemma shiftMod_zmod_ne (p k y m n : ℕ) (hp : p.Prime) (hk : 1 ≤ k)
    (h : ¬ (p : ℤ) ∣ ((m : ℤ) - (n : ℤ))) :
    (((Work.BMF.recursion.shiftMod p k y m : ℕ) : ZMod p)) ≠
      (((Work.BMF.recursion.shiftMod p k y n : ℕ) : ZMod p)) := by
  intro hc
  -- `p` divides `p^k`, so the congruence modulo `p^k` descends to one modulo `p`
  have hp1 : (p : ℤ) ∣ (p : ℤ) ^ k := prime_dvd_prime_pow_int p k hk
  have hm : (((shiftMod p k y m : ℕ) : ℤ)) ≡ ((m : ℤ) - (y : ℤ)) [ZMOD (p : ℤ)] :=
    (shiftMod_modEq p k y m hp).of_dvd hp1
  have hn : (((shiftMod p k y n : ℕ) : ℤ)) ≡ ((n : ℤ) - (y : ℤ)) [ZMOD (p : ℤ)] :=
    (shiftMod_modEq p k y n hp).of_dvd hp1
  -- equality in `ZMod p` is congruence modulo `p`
  have heq : (((shiftMod p k y m : ℕ) : ℤ)) ≡ (((shiftMod p k y n : ℕ) : ℤ)) [ZMOD (p : ℤ)] := by
    apply (ZMod.intCast_eq_intCast_iff _ _ p).mp
    simpa using hc
  have hchain : ((m : ℤ) - (y : ℤ)) ≡ ((n : ℤ) - (y : ℤ)) [ZMOD (p : ℤ)] :=
    hm.symm.trans (heq.trans hn)
  exact h (by convert hchain.symm.dvd using 1; ring)

end Work.BMF.recursion

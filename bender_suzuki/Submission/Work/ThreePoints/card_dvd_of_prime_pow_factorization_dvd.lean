import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThreePoints

theorem card_dvd_of_prime_pow_factorization_dvd {G : Type*} [Group G] [Finite G] {m : ℕ}
    (h : ∀ p : ℕ, p.Prime → p ∣ Nat.card G → p ^ (Nat.card G).factorization p ∣ m) :
    Nat.card G ∣ m := by
  rw [Nat.dvd_iff_prime_pow_dvd_dvd m (Nat.card G)]
  intro p k hp hpk
  have hd : Nat.card G ≠ 0 := (Nat.card_pos (α := G)).ne'
  have hle : k ≤ (Nat.card G).factorization p := (hp.pow_dvd_iff_le_factorization hd).mp hpk
  refine dvd_trans (pow_dvd_pow p hle) ?_
  rcases Nat.eq_zero_or_pos ((Nat.card G).factorization p) with h0 | hpos
  · rw [h0, pow_zero]; exact one_dvd m
  · exact h p hp ((hp.dvd_iff_one_le_factorization hd).mpr hpos)

end Work.ThreePoints

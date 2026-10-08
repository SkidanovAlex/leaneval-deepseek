import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PGroup.Symplectic

/-- If a prime `p` divides `κ ^ p - 1`, then `p ∣ κ - 1`.
This is Fermat's little theorem in the form `κ ^ p ≡ κ [MOD p]`. -/
theorem dvd_sub_one_of_dvd_pow_sub_one {p κ : ℕ} (hp : p.Prime) (h : p ∣ κ ^ p - 1) : p ∣ κ - 1 := by
  rcases Nat.eq_zero_or_pos κ with hκ | hκ
  · subst hκ; simp
  -- `h` says `κ ^ p` is congruent to `1` modulo `p`
  have h1 : 1 ≡ κ ^ p [MOD p] := (Nat.modEq_iff_dvd' (Nat.one_le_pow p κ hκ)).mpr h
  -- Fermat's little theorem: `κ ^ p ≡ κ [MOD p]`
  have h2 : κ ^ p ≡ κ [MOD p] := by
    rw [← Int.natCast_modEq_iff]
    push_cast
    exact Int.ModEq.pow_prime_eq_self hp (κ : ℤ)
  exact (h1.trans h2).dvd'

end Work.PGroup.Symplectic

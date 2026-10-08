import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.AppXIField.L0

theorem addHom_surjective_of_card_le {K V : Type} [AddCommGroup K] [Finite K]
    [AddCommGroup V] [Finite V] (f : K →+ V) (hf : Function.Injective f) {n : ℕ}
    (hn : n + 1 ≤ Nat.card K) (hV : Nat.card V ≤ 2 * n + 1) : Function.Surjective f := by
  -- The image of `f` is a subgroup of `V` isomorphic to `K`, so `Nat.card K ∣ Nat.card V`.
  have hdiv : Nat.card K ∣ Nat.card V := AddSubgroup.card_dvd_of_injective f hf
  have hle : Nat.card K ≤ Nat.card V := Nat.card_le_card_of_injective f hf
  have hKpos : 0 < Nat.card K := by omega
  have hlt : Nat.card V < 2 * Nat.card K := by omega
  -- Write `Nat.card V = Nat.card K * q`; then `q < 2`, and `q ≠ 0`, so `q = 1`.
  obtain ⟨q, hq⟩ := hdiv
  have hq2 : q < 2 := by
    have hmul : Nat.card K * q < Nat.card K * 2 := by
      rw [← hq, Nat.mul_comm (Nat.card K) 2]
      exact hlt
    exact Nat.lt_of_mul_lt_mul_left hmul
  have heq : Nat.card K = Nat.card V := by
    rcases Nat.eq_zero_or_pos q with h | h
    · rw [h, Nat.mul_zero] at hq
      omega
    · have hq1 : q = 1 := by omega
      rw [hq, hq1, Nat.mul_one]
  exact (hf.bijective_of_nat_card_le heq.ge).2

end Work.AppXIField.L0

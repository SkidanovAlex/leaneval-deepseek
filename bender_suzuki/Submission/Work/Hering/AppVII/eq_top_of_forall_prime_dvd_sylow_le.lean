import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Hering.AppVII

theorem eq_top_of_forall_prime_dvd_sylow_le {G : Type*} [Group G] [Finite G] (H : Subgroup G)
    (h : ∀ (r : ℕ), r.Prime → r ∣ Nat.card G → ∃ S : Sylow r G, (S : Subgroup G) ≤ H) :
    H = ⊤ := by
  -- `Nat.card G` is nonzero since `G` is a finite nonempty (group) type.
  have hn : Nat.card G ≠ 0 := Nat.card_pos.ne'
  -- It suffices to show `Nat.card G ∣ Nat.card H`: together with the always true
  -- `Nat.card H ∣ Nat.card G` this forces the two cardinals to be equal.
  have hdiv : Nat.card G ∣ Nat.card H := by
    -- A number divides another iff every prime power dividing the first divides the second.
    rw [Nat.dvd_iff_prime_pow_dvd_dvd]
    intro p k hp hpk
    rcases Nat.eq_zero_or_pos k with hk | hk
    · -- `p ^ 0 = 1` divides everything.
      subst hk
      exact one_dvd _
    · -- `p ^ k ∣ Nat.card G` with `k ≥ 1`, so `p ∣ Nat.card G` and there is a Sylow
      -- `p`-subgroup `S ≤ H`.
      have hpdvd : p ∣ Nat.card G :=
        dvd_trans (dvd_pow_self p (Nat.pos_iff_ne_zero.mp hk)) hpk
      obtain ⟨S, hSH⟩ := h p hp hpdvd
      have : Fact p.Prime := ⟨hp⟩
      -- `p ^ k ∣ Nat.card S`: the order of `S` is the full `p`-part of `Nat.card G`.
      have hkfact : k ≤ (Nat.card G).factorization p :=
        (Nat.Prime.pow_dvd_iff_le_factorization hp hn).mp hpk
      have h1 : p ^ k ∣ Nat.card (S : Subgroup G) := by
        rw [Sylow.card_eq_multiplicity S]
        exact pow_dvd_pow p hkfact
      -- `Nat.card S ∣ Nat.card H` because `S ≤ H`.
      have h2 : Nat.card (S : Subgroup G) ∣ Nat.card H := Subgroup.card_dvd_of_le hSH
      exact dvd_trans h1 h2
  have hdiv2 : Nat.card H ∣ Nat.card G := Subgroup.card_subgroup_dvd_card H
  -- Equal cardinals of `H` and `G` force `H = ⊤`.
  exact Subgroup.eq_top_of_card_eq H (Nat.dvd_antisymm hdiv2 hdiv)

end Work.Hering.AppVII

import Mathlib
import Submission.Work.Hall.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Hall subgroups pull back along quotients by a `π`-normal subgroup

If `N ◁ G` has `π`-number order and `H̄ ≤ G ⧸ N` is a Hall `π`-subgroup of the quotient,
then its full preimage `H̄.comap (mk' N)` is a Hall `π`-subgroup of `G`.

The index part is immediate: `mk' N` is surjective, so `index_comap_of_surjective` identifies
the index of the preimage with that of `H̄`.  For the order part we use
`|comap| = |N| · |H̄|`: if `H̄` has finite index this is Lagrange's theorem combined with
`card_mul_index` (in the quotient `G ⧸ N` and in `G`), and if `H̄` has infinite index then
`H̄` is trivial — a `π`-number of infinite index cannot have a prime divisor, because
`IsPiNat (¬π) 0` says that no prime lies in `π` — whence the preimage is `mk' N`'s kernel `N`.
-/

namespace Work.Hall.HallAPI

/-- A product of two `π`-numbers is a `π`-number. -/
private theorem isPiNat_mul {π : ℕ → Prop} {m n : ℕ}
    (hm : Work.Hall.IsPiNat π m) (hn : Work.Hall.IsPiNat π n) :
    Work.Hall.IsPiNat π (m * n) := by
  intro p hp hd
  rcases (Nat.Prime.dvd_mul hp).mp hd with h | h
  · exact hm p hp h
  · exact hn p hp h

theorem hall_isHall_comap_mk {G : Type*} [Group G] {π : ℕ → Prop} {N : Subgroup G} [N.Normal]
    (hN : Work.Hall.IsPiNat π (Nat.card N)) {Hbar : Subgroup (G ⧸ N)}
    (h : Work.Hall.IsHall π Hbar) :
    Work.Hall.IsHall π (Hbar.comap (QuotientGroup.mk' N)) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · by_cases h0 : Hbar.index = 0
    · -- `H̄` has infinite index, so it is trivial and the preimage is `N` itself
      have hcard1 : Nat.card Hbar = 1 := by
        refine Nat.eq_one_iff_not_exists_prime_dvd.mpr fun p hp hpd => ?_
        exact (h2 p hp (by rw [h0]; exact dvd_zero p)) (h1 p hp hpd)
      have hHbar : Hbar = ⊥ := Subgroup.card_eq_one.mp hcard1
      rw [hHbar, MonoidHom.comap_bot, QuotientGroup.ker_mk']
      exact hN
    · -- `H̄` has finite index: `|comap| · [G : H̄] = |G| = |N| · (|H̄| · [G : H̄])`
      have hidx : (Hbar.comap (QuotientGroup.mk' N)).index = Hbar.index :=
        Subgroup.index_comap_of_surjective Hbar (QuotientGroup.mk'_surjective N)
      have e1 : Nat.card (Hbar.comap (QuotientGroup.mk' N)) * Hbar.index = Nat.card G := by
        rw [← hidx, Subgroup.card_mul_index]
      have e2 : Nat.card N * (Nat.card Hbar * Hbar.index) = Nat.card G := by
        rw [Subgroup.card_mul_index Hbar]
        exact Subgroup.card_mul_index N
      have hcard : Nat.card (Hbar.comap (QuotientGroup.mk' N))
          = Nat.card N * Nat.card Hbar := by
        refine Nat.mul_right_cancel (Nat.pos_of_ne_zero h0) ?_
        rw [Nat.mul_assoc]
        exact e1.trans e2.symm
      rw [hcard]
      exact isPiNat_mul hN h1
  · rw [Subgroup.index_comap_of_surjective Hbar (QuotientGroup.mk'_surjective N)]
    exact h2

end Work.Hall.HallAPI

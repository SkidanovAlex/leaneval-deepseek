import Mathlib
import Submission.Work.PGroup.Symplectic.card_eq_pow_even_of_nondegenerate_alt
import Submission.Work.PGroup.Symplectic.sq_card_quotient_center_of_class_two

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `|H / Z(H)|` is an even power of `p`

Let `H` be a finite group whose derived subgroup `⁅⊤,⊤⁆` is central of prime order `p`
(`p` odd) and such that every `p`-th power in `H` is central.  Then `|H / Z(H)| = p ^ (2 * k)`
for some `k`.

The group `H / Z(H)` is abelian (the derived subgroup is central) and has exponent dividing `p`
(every `p`-th power is central), hence is an elementary abelian `p`-group: its order is a power
of `p`.  On the other hand, by the commutator pairing it is a symplectic space over `𝔽_p`, so its
order is a perfect square (`sq_card_quotient_center_of_class_two`).  A number which is both a power
of the prime `p` and a perfect square is an even power of `p`, which is the claim.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped commutatorElement

noncomputable section

namespace Work.PGroup.Symplectic

theorem card_quotient_center_pow_even {H : Type*} [Group H] [Finite H] {p : ℕ}
    (hp : p.Prime) (hodd : p ≠ 2)
    (hclass : ⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆ ≤ Subgroup.center H)
    (hder : Nat.card (⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆ : Subgroup H) = p)
    (helem : ∀ x : H, x ^ p ∈ Subgroup.center H) :
    ∃ k : ℕ, Nat.card (H ⧸ Subgroup.center H) = p ^ (2 * k) := by
  classical
  -- Every element of `H / Z(H)` has order dividing `p`.
  have hExp : ∀ a : H ⧸ Subgroup.center H, a ^ p = 1 := by
    intro a
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center H) a
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact helem x
  haveI : Fact p.Prime := ⟨hp⟩
  -- Hence `H / Z(H)` is a `p`-group, so its cardinality is a power of `p`.
  have hIspg : IsPGroup p (H ⧸ Subgroup.center H) :=
    fun a => ⟨1, by rw [pow_one]; exact hExp a⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hIspg
  -- On the other hand its cardinality is a perfect square.
  obtain ⟨r, hr⟩ := sq_card_quotient_center_of_class_two hp hodd hclass hder helem
  -- A perfect square which is a power of the prime `p` is an even power of `p`.
  have hrsq : r ^ 2 = p ^ m := by rw [← hr, hm]
  have hdvd : r ∣ p ^ m := by rw [← hrsq]; exact dvd_pow_self r (by norm_num)
  obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  exact ⟨k, by rw [hr, hk]; ring_nf⟩

end Work.PGroup.Symplectic

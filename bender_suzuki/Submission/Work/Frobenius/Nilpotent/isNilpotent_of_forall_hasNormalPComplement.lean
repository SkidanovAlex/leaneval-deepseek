/-
`Work.Frobenius.Nilpotent.isNilpotent_of_forall_hasNormalPComplement`

If a finite group `G` has a normal `p`-complement for every prime `p` dividing `|G|`, then `G` is
nilpotent.

The proof is the classical "product of quotient" argument: for each prime `p ∣ |G|` choose a normal
`p`-complement `N_p` (so `G ⧸ N_p` is a `p`-group, hence nilpotent).  The diagonal map
`G →* ∏_{p ∈ primeFactors |G|} G ⧸ N_p`, `g ↦ (g N_p)_p`, is injective: its kernel is
`⋂_p N_p`, and a nontrivial element `x` has an element of prime order `q` dividing `orderOf x`;
then `q ∈ primeFactors |G|` while `N_q` is a `q'`-group, so `x ∉ N_q`.  Hence `G` embeds in a
finite product of nilpotent groups, so `G` is nilpotent (subgroups of nilpotent groups are
nilpotent).
-/
import Mathlib
import Submission.Work.NPC.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

namespace Work.Frobenius.Nilpotent

open Classical

theorem isNilpotent_of_forall_hasNormalPComplement {G : Type*} [Group G] [Finite G]
    (h : ∀ p : ℕ, p.Prime → p ∣ Nat.card G → Work.NPC.HasNormalPComplement p G) :
    Group.IsNilpotent G := by
  classical
  -- Index the normal `p`-complements by the primes dividing `|G|`.
  let ι := (Nat.card G).primeFactors
  let N : ι → Subgroup G := fun p =>
    Classical.choose (h p.val (Nat.prime_of_mem_primeFactors p.2) (Nat.dvd_of_mem_primeFactors p.2))
  have hN : ∀ p : ι, Work.NPC.IsNormalPComplement p.val (N p) := fun p =>
    Classical.choose_spec (h p.val (Nat.prime_of_mem_primeFactors p.2) (Nat.dvd_of_mem_primeFactors p.2))
  haveI hNnorm : ∀ p : ι, (N p).Normal := fun p => (hN p).normal
  haveI hprime : ∀ p : ι, Fact p.val.Prime := fun p => ⟨Nat.prime_of_mem_primeFactors p.2⟩
  -- Each quotient by a normal `p`-complement is a `p`-group, hence nilpotent.
  haveI hpgrp : ∀ p : ι, Group.IsNilpotent (G ⧸ (N p)) := fun p =>
    IsPGroup.isNilpotent (hN p).isPGroup_quotient
  haveI hpi : Group.IsNilpotent (∀ p : ι, G ⧸ (N p)) := inferInstance
  -- The diagonal map into the product of the quotients.
  let φ : G →* (∀ p : ι, G ⧸ (N p)) :=
    { toFun := fun g p => QuotientGroup.mk' (N p) g
      map_one' := by ext p; simp
      map_mul' := by intro a b; ext p; simp }
  -- `φ` is injective: its kernel is `⋂_p N_p = ⊥`.
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    by_contra hx1
    -- A nontrivial element has an element of prime order `q`.
    have hord : orderOf x ≠ 1 := fun hh => hx1 (orderOf_eq_one_iff.mp hh)
    obtain ⟨q, hqprime, hqdvd⟩ := Nat.exists_prime_and_dvd hord
    have hqmem : q ∈ (Nat.card G).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hqprime, hqdvd.trans (orderOf_dvd_natCard x),
        Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩⟩
    have hqidx : φ x ⟨q, hqmem⟩ = 1 := by
      have := congrFun (show φ x = 1 from hx) ⟨q, hqmem⟩
      simpa using this
    -- `x` lies in the `q`-complement, contradicting that it is a `q'`-group.
    have hxN : x ∈ N ⟨q, hqmem⟩ :=
      (QuotientGroup.eq_one_iff (N := N ⟨q, hqmem⟩) x).mp hqidx
    have hdvd : q ∣ Nat.card (N ⟨q, hqmem⟩) :=
      hqdvd.trans (Subgroup.orderOf_dvd_natCard (N ⟨q, hqmem⟩) hxN)
    have hcop : q.Coprime (Nat.card (N ⟨q, hqmem⟩)) := (hN ⟨q, hqmem⟩).coprime_card.symm
    exact (hqprime.coprime_iff_not_dvd.mp hcop) hdvd
  -- `G` is isomorphic to its image, a subgroup of a nilpotent group.
  let e : G ≃* φ.range := MonoidHom.ofInjective hinj
  exact Group.nilpotent_of_mulEquiv e.symm

end Work.Frobenius.Nilpotent

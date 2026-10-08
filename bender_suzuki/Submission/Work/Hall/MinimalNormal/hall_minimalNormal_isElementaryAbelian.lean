import Mathlib
import Submission.Work.Hall.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Minimal normal subgroups of solvable groups are elementary abelian

Let `G` be a finite group, `N ◁ G` a minimal normal subgroup and suppose that `N` is solvable.
Then `N` is elementary abelian: it is abelian of exponent some prime `p`.

This is a standard ingredient in the proof of P. Hall's theorems (and of the Feit–Thompson
odd order theorem).  The proof has two steps.

* `N` is abelian.  Suppose not, so that `⁅N, N⁆ ≠ ⊥`.  The commutator subgroup `⁅N, N⁆` is
  normal in `G` and contained in `N`, so by minimality of `N` we get `N ≤ ⁅N, N⁆`, i.e.
  `⁅N, N⁆ = N`.  But a nontrivial solvable group is not perfect
  (`Group.IsSolvable.commutator_lt_top_of_nontrivial`), a contradiction.

* `N` has exponent a prime `p`.  Since `N` is nontrivial and finite, some prime `p` divides
  `|N|`; by Cauchy's theorem there is `y ∈ N` of order `p`.  The set `K = {x ∈ N | x ^ p = 1}`
  is a subgroup of `G` (here commutativity of `N` is used), it is normal in `G` because
  conjugation is an automorphism of `N`, and it is nontrivial because `y ∈ K`.  Minimality of
  `N` gives `N ≤ K`: every element of `N` has `p`-th power `1`.
-/

namespace Work.Hall.MinimalNormal

set_option linter.style.haveILetI false

open Classical
open scoped Pointwise

/-- A minimal normal subgroup of a group which is solvable is abelian. -/
theorem isMulCommutative_of_isMinimalNormal_of_isSolvable {G : Type*} [Group G]
    {N : Subgroup G} (hN : Work.Hall.IsMinimalNormal N) (h : Group.IsSolvable N) :
    IsMulCommutative ↥N := by
  obtain ⟨hNnorm, hNne, hNmin⟩ := hN
  haveI : Nontrivial ↥N := (Subgroup.nontrivial_iff_ne_bot N).mpr hNne
  haveI : Group.IsSolvable ↥N := h
  by_contra hnc
  have hbot : ⁅N, N⁆ ≠ ⊥ := fun hb => hnc ((Subgroup.commutator_self_eq_bot_iff).mp hb)
  have hnorm : (⁅N, N⁆ : Subgroup G).Normal := Subgroup.commutator_normal N N
  have hle : ⁅N, N⁆ ≤ N := Subgroup.commutator_le_self N
  have hge : N ≤ ⁅N, N⁆ := hNmin ⁅N, N⁆ hnorm hle hbot
  have hmapTop : Subgroup.map N.subtype (⊤ : Subgroup ↥N) = N := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hcommut : Subgroup.map N.subtype (commutator ↥N) = ⁅N, N⁆ := by
    change Subgroup.map N.subtype ⁅(⊤ : Subgroup ↥N), ⊤⁆ = ⁅N, N⁆
    rw [Subgroup.map_commutator, hmapTop]
  have hlt : ⁅N, N⁆ < N := by
    have hstrict := Group.IsSolvable.commutator_lt_top_of_nontrivial ↥N
    have := Subgroup.map_subtype_lt_map_subtype.mpr hstrict
    rwa [hcommut, hmapTop] at this
  exact absurd (le_antisymm hle hge) (ne_of_lt hlt)

theorem hall_minimalNormal_isElementaryAbelian {G : Type*} [Group G] [Finite G] {N : Subgroup G}
    (hN : Work.Hall.IsMinimalNormal N) (h : Group.IsSolvable N) :
    ∃ p : ℕ, p.Prime ∧ Work.Hall.IsElementaryAbelian p N := by
  obtain ⟨hNnorm, hNne, hNmin⟩ := hN
  haveI : Nontrivial ↥N := (Subgroup.nontrivial_iff_ne_bot N).mpr hNne
  have hcomm : IsMulCommutative ↥N :=
    isMulCommutative_of_isMinimalNormal_of_isSolvable ⟨hNnorm, hNne, hNmin⟩ h
  -- some prime divides `|N|`
  have hcard : Nat.card ↥N ≠ 1 := by
    intro hc
    have hsub : Subsingleton ↥N := (Nat.card_eq_one_iff_unique.mp hc).1
    obtain ⟨a, b, hab⟩ := exists_pair_ne ↥N
    exact hab (Subsingleton.elim a b)
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hcard
  haveI : Fact p.Prime := ⟨hp⟩
  -- Cauchy: an element of order `p`
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥N) p hpdvd
  have hypow : (y : G) ^ p = 1 := by
    have h1 : y ^ p = 1 := by rw [← orderOf_dvd_iff_pow_eq_one, hy]
    exact congrArg Subtype.val h1
  have hyne : (y : G) ≠ 1 := by
    intro h1
    have hy1 : y = 1 := Subtype.ext h1
    have : orderOf y = 1 := orderOf_eq_one_iff.mpr hy1
    rw [hy] at this
    exact hp.ne_one this
  -- the subgroup of elements of `N` whose `p`-th power is trivial
  let K : Subgroup G :=
    { carrier := {z : G | z ∈ N ∧ z ^ p = 1}
      one_mem' := ⟨N.one_mem, one_pow p⟩
      mul_mem' := by
        rintro a b ⟨ha, hap⟩ ⟨hb, hbp⟩
        refine ⟨N.mul_mem ha hb, ?_⟩
        have hc : a * b = b * a :=
          congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : ↥N) ⟨b, hb⟩)
        rw [Commute.mul_pow hc, hap, hbp, one_mul]
      inv_mem' := by
        rintro a ⟨ha, hap⟩
        refine ⟨N.inv_mem ha, ?_⟩
        rw [inv_pow, hap, inv_one] }
  have hKnormal : K.Normal := by
    refine ⟨fun a ha g => ?_⟩
    obtain ⟨haN, hap⟩ := ha
    refine ⟨hNnorm.conj_mem a haN g, ?_⟩
    rw [conj_pow, hap, mul_one, mul_inv_cancel]
  have hKne : K ≠ ⊥ := by
    intro hbot
    have : (y : G) ∈ (⊥ : Subgroup G) := hbot ▸ (show (y : G) ∈ K from ⟨y.2, hypow⟩)
    exact hyne (Subgroup.mem_bot.mp this)
  have hNK : N ≤ K := hNmin K hKnormal (by rintro z ⟨hz, _⟩; exact hz) hKne
  refine ⟨p, hp, hcomm, fun a => ?_⟩
  have hmem : (a : G) ∈ K := hNK a.2
  have hpow : (a : G) ^ p = 1 := hmem.2
  exact Subtype.ext hpow

end Work.Hall.MinimalNormal

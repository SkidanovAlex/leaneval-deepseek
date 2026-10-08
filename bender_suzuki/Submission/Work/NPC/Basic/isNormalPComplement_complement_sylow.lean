import Mathlib
import Submission.Work.NPC.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

namespace Work.NPC.Basic

theorem isNormalPComplement_complement_sylow {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {N : Subgroup G} (h : Work.NPC.IsNormalPComplement p N)
    (P : Sylow p G) : N.IsComplement' (P : Subgroup G) := by
  have hp : p.Prime := Fact.out
  haveI : N.Normal := h.normal
  haveI : Finite (G ⧸ N) := (finite_iff_subgroup_quotient N).mp ‹Finite G› |>.2
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp h.isPGroup_quotient
  -- The order of the quotient G ⧸ N is a power of p.
  have hcardG : Nat.card G = p ^ m * Nat.card N := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N, hm]
  -- Hence m is the multiplicity of p in |G|.
  have hfacle : Nat.factorization (Nat.card G) p = m := by
    rw [hcardG, Nat.factorization_mul (pow_ne_zero m hp.ne_zero) Nat.card_pos.ne']
    have hzero : Nat.factorization (Nat.card N) p = 0 := by
      rw [Nat.factorization_eq_zero_of_not_dvd]
      rw [← hp.coprime_iff_not_dvd]
      exact h.coprime_card.symm
    simp only [Finsupp.coe_add, Pi.add_apply, Nat.factorization_pow_self hp, hzero, add_zero]
  -- A Sylow p-subgroup has order p ^ m.
  have hP : Nat.card (P : Subgroup G) = p ^ m := by
    rw [P.card_eq_multiplicity, hfacle]
  have hPN : Nat.card N * Nat.card (P : Subgroup G) = Nat.card G := by
    rw [hP, Subgroup.card_eq_card_quotient_mul_card_subgroup N, hm]
    exact Nat.mul_comm _ _
  have hcop : Nat.Coprime (Nat.card N) (Nat.card (P : Subgroup G)) := by
    rw [hP]
    exact h.coprime_card.pow_right m
  exact Subgroup.isComplement'_of_card_mul_and_disjoint hPN
    (Subgroup.disjoint_of_coprime_natCard hcop)

end Work.NPC.Basic

/-
Area A9: a self-contained proof of **Frobenius' normal `p`-complement theorem**.

If every non-identity `p`-subgroup `Q ≤ G` has `N_G(Q)/C_G(Q)` a `p`-group (Frobenius' condition),
then `G` has a normal `p`-complement.  The proof here is by strong induction on `|G|` and avoids the
transfer criterion `P* = P'`:

* Frobenius' condition is inherited by every subgroup `A ≤ G` (`hasFrobeniusCondition_subgroup`),
  so the induction hypothesis applies to any proper subgroup.
* Take `Q ∈ Syl_p(G)`.  Frobenius' condition makes `Q` conjugacy-closed in `G`
  (`conjugacyClosed_sylow_of_hasFrobeniusCondition`), hence the focal subgroup of `Q` is `⁅Q,Q⁆`
  (`Work.NPC.focalSubgroup_eq_commutator_of_conjugacyClosed`).
* The kernel `A := (Q.transferFocal).ker` of the transfer is therefore a *proper* normal subgroup
  with `G ⧸ A ≃* Q ⧸ Q.focalSubgroupOf` a `p`-group (nontrivial because `Q` is a nontrivial
  `p`-group, so `⁅Q,Q⁆ ≠ Q`).
* By induction `A` has a normal `p`-complement `N`; it is unique, hence normal in `G`, and `G ⧸ N`
  is an extension of the `p`-groups `A ⧸ N` and `G ⧸ A`, hence a `p`-group.
-/
import Mathlib
import Submission.Work.NPC.Defs
import Submission.Work.NPC.Engine
import Submission.Work.NPC.Fusion
import Submission.Work.NPC.Complement
import Submission.Work.NPC.Basic.isNormalPComplement_unique
import Submission.Work.NPC.Basic.hasNormalPComplement_of_coprime
import Submission.Work.NPC.Basic.isNormalPComplement_map_of_quotient
import Submission.Work.NPC.Frobenius.conjugacyClosed_sylow_of_hasFrobeniusCondition
import Submission.Work.NPC.Frobenius.hasFrobeniusCondition_subgroup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

open scoped Pointwise commutatorElement

universe u

namespace Work.NPC.Frobenius

variable {p : ℕ} [Fact p.Prime]

/-- `⁅Q, Q⁆ ≠ Q` for a non-identity `p`-subgroup `Q`: a nontrivial `p`-group is solvable, hence not
perfect. -/
theorem commutator_ne_self_of_isPGroup {G : Type*} [Group G] [Finite G]
    {Q : Subgroup G} (hQ : IsPGroup p Q) (hQne : Q ≠ ⊥) :
    ⁅Q, Q⁆ ≠ Q := by
  intro heq
  haveI hnt : Nontrivial ↥Q := (Subgroup.nontrivial_iff_ne_bot Q).mpr hQne
  haveI hnil : Group.IsNilpotent ↥Q := IsPGroup.isNilpotent hQ
  haveI hsol : Group.IsSolvable ↥Q := IsNilpotent.to_isSolvable
  have hlt : _root_.commutator ↥Q < ⊤ :=
    Group.IsSolvable.commutator_lt_top_of_nontrivial (G := ↥Q)
  have htop : Subgroup.map Q.subtype (⊤ : Subgroup ↥Q) = Q := by
    rw [Subgroup.map_top, Subgroup.range_subtype]
  have hmap : Subgroup.map Q.subtype (_root_.commutator ↥Q) =
      Subgroup.map Q.subtype (⊤ : Subgroup ↥Q) := by
    rw [Subgroup.map_subtype_commutator, heq, htop]
  exact hlt.ne (Subgroup.map_subtype_inj.mp hmap)

/-- Strong-induction form of Frobenius' normal `p`-complement theorem. -/
theorem frobenius_npc_of_card_le : ∀ (n : ℕ), ∀ (G : Type u) [Group G] [Finite G],
    Nat.card G ≤ n → Work.NPC.HasFrobeniusCondition p G → Work.NPC.HasNormalPComplement p G := by
  intro n
  induction n with
  | zero =>
    intro G _ _ hle _
    exact absurd (Nat.eq_zero_of_le_zero hle) Nat.card_pos.ne'
  | succ n ih =>
    intro G _ _ hle h
    obtain ⟨Q⟩ := Sylow.nonempty (p := p) (G := G)
    by_cases hQ : (Q : Subgroup G) = ⊥
    · -- `p ∤ |G|`: the whole group is its own normal `p`-complement
      have hcard : Nat.card G = (Q : Subgroup G).index := by
        rw [← Subgroup.card_mul_index (Q : Subgroup G), hQ]
        simp
      refine Work.NPC.Basic.hasNormalPComplement_of_coprime
        ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr ?_).symm
      rw [hcard]
      exact Q.not_dvd_index
    · -- main step: the transfer kernel is a proper normal subgroup with `p`-group quotient
      have hcc := conjugacyClosed_sylow_of_hasFrobeniusCondition Q h
      have hfoc : (Q : Subgroup G).focalSubgroup = ⁅(Q : Subgroup G), (Q : Subgroup G)⁆ :=
        Work.NPC.focalSubgroup_eq_commutator_of_conjugacyClosed hcc
      have hQ'ne : ⁅(Q : Subgroup G), (Q : Subgroup G)⁆ ≠ (Q : Subgroup G) :=
        commutator_ne_self_of_isPGroup Q.isPGroup' hQ
      haveI : ((Q : Subgroup G).transferFocal.ker).Normal :=
        MonoidHom.normal_ker _
      -- `A ≠ ⊤`
      have hAne : (Q : Subgroup G).transferFocal.ker ≠ ⊤ := by
        intro htop
        have h1 : (Q : Subgroup G).transferFocal.ker ⊓ (Q : Subgroup G) =
            (Q : Subgroup G) := by
          rw [htop, top_inf_eq]
        rw [Subgroup.ker_transferFocal_inf_eq_focalSubgroup, hfoc] at h1
        exact hQ'ne h1
      have hx : ∃ x : G, x ∉ (Q : Subgroup G).transferFocal.ker := by
        simpa [Subgroup.eq_top_iff'] using hAne
      obtain ⟨x, hx⟩ := hx
      have hlt : Nat.card ↥((Q : Subgroup G).transferFocal.ker) < Nat.card G :=
        Finite.card_subtype_lt hx
      -- the quotient is a `p`-group
      have hquot : IsPGroup p (G ⧸ (Q : Subgroup G).transferFocal.ker) :=
        IsPGroup.of_equiv (IsPGroup.to_quotient Q.isPGroup' (Q : Subgroup G).focalSubgroupOf)
          (Subgroup.transferFocal.quotientKerMulEquivQuotientFocalSubroupOf Q).symm
      -- the induction hypothesis
      have hHPA : Work.NPC.HasFrobeniusCondition p ↥((Q : Subgroup G).transferFocal.ker) :=
        hasFrobeniusCondition_subgroup _ h
      obtain ⟨N, hN⟩ := ih ↥((Q : Subgroup G).transferFocal.ker)
        (Nat.lt_succ_iff.mp (lt_of_lt_of_le hlt hle)) hHPA
      exact ⟨N.map ((Q : Subgroup G).transferFocal.ker).subtype,
        Work.NPC.Basic.isNormalPComplement_map_of_quotient hN hquot⟩

/-- **Frobenius' normal `p`-complement theorem**: if `N_G(Q)/C_G(Q)` is a `p`-group for every
non-identity `p`-subgroup `Q ≤ G`, then `G` has a normal `p`-complement. -/
theorem frobenius_npc_via_induction {G : Type u} [Group G] [Finite G]
    (h : Work.NPC.HasFrobeniusCondition p G) : Work.NPC.HasNormalPComplement p G :=
  frobenius_npc_of_card_le (Nat.card G) G le_rfl h

end Work.NPC.Frobenius

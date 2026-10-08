/-
Area A9 (normal `p`-complement theorems): complements of Sylow subgroups.

A normal `p`-complement is exactly a normal subgroup which is a complement of a Sylow
`p`-subgroup (`hasNormalPComplement_iff_exists_complement_sylow`), and it is unique
(`Work.NPC.normalPComplement`).
-/
import Submission.Work.NPC.Defs
import Submission.Work.NPC.Basic.isNormalPComplement_complement_sylow
import Submission.Work.NPC.Basic.isNormalPComplement_unique

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

noncomputable section

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open scoped Pointwise commutatorElement

namespace Work.NPC

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- If a normal subgroup `N` is a complement of a Sylow `p`-subgroup `P`, then `N` is a normal
`p`-complement: `|N| = [G : P]` is coprime to `p`, and `G ⧸ N ≃* P` is a `p`-group. -/
theorem isNormalPComplement_of_isComplement'_sylow {N : Subgroup G} (hN : N.Normal)
    (P : Sylow p G) (h : N.IsComplement' (P : Subgroup G)) : IsNormalPComplement p N := by
  haveI := hN
  refine ⟨hN, ?_, ?_⟩
  · have hcard : Nat.card ↥N = (P : Subgroup G).index := h.index_eq_card.symm
    rw [hcard]
    exact ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr P.not_dvd_index).symm
  · exact IsPGroup.of_equiv P.isPGroup' h.symm.QuotientMulEquiv.symm

/-- `G` has a normal `p`-complement if and only if some normal subgroup is a complement of a fixed
Sylow `p`-subgroup `P`. -/
theorem hasNormalPComplement_iff_exists_complement_sylow (P : Sylow p G) :
    HasNormalPComplement p G ↔ ∃ N : Subgroup G, N.Normal ∧ N.IsComplement' (P : Subgroup G) := by
  constructor
  · rintro ⟨N, hN⟩
    exact ⟨N, hN.normal, Basic.isNormalPComplement_complement_sylow hN P⟩
  · rintro ⟨N, hN, h⟩
    exact ⟨N, isNormalPComplement_of_isComplement'_sylow hN P h⟩

/-- The **normal `p`-complement** of `G`, chosen from a proof that one exists.  It is unique by
`Work.NPC.Basic.isNormalPComplement_unique`. -/
noncomputable def normalPComplement {G : Type*} [Group G] {p : ℕ}
    (h : HasNormalPComplement p G) : Subgroup G :=
  Classical.choose h

theorem normalPComplement_spec {G : Type*} [Group G] {p : ℕ}
    (h : HasNormalPComplement p G) : IsNormalPComplement p (normalPComplement h) :=
  Classical.choose_spec h

theorem normalPComplement_normal {G : Type*} [Group G] {p : ℕ}
    (h : HasNormalPComplement p G) : (normalPComplement h).Normal :=
  (normalPComplement_spec h).normal

theorem normalPComplement_coprime_card {G : Type*} [Group G] {p : ℕ}
    (h : HasNormalPComplement p G) : (Nat.card (normalPComplement h)).Coprime p :=
  (normalPComplement_spec h).coprime_card

theorem normalPComplement_isPGroup_quotient {G : Type*} [Group G] {p : ℕ}
    (h : HasNormalPComplement p G) [hn : (normalPComplement h).Normal] :
    IsPGroup p (G ⧸ normalPComplement h) := by
  haveI := hn
  exact (normalPComplement_spec h).isPGroup_quotient

/-- Every normal `p`-complement of `G` is the chosen one. -/
theorem eq_normalPComplement {G : Type*} [Group G] [Finite G] {p : ℕ}
    {h : HasNormalPComplement p G} {N : Subgroup G} (hN : IsNormalPComplement p N) :
    N = normalPComplement h :=
  Basic.isNormalPComplement_unique hN (normalPComplement_spec h)

end Work.NPC

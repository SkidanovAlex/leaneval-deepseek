import Mathlib
import Submission.Work.CORE3.Defs

-- The two local instances introduced below are `Prop`-valued (`Fact q.Prime` and
-- `Subgroup.Normal`), which trips the style linter `haveILetI`; `haveI`/`letI` is exactly
-- what is wanted here (the instances must be available to typeclass search).
set_option linter.style.haveILetI false

namespace Work.CORE3

/-- Hall components of a normal Hall subgroup are "all or nothing": if `I ≤ F` is a normal Hall
subgroup of the finite group `F` and `Q ≤ F` is a `q`-group for a prime `q`, then `Q ≤ I` or
`Q ⊓ I = ⊥`. -/
theorem isPGroup_le_or_inf_eq_bot_of_isHallIn {G : Type*} [Group G] [Finite G]
    {F I Q : Subgroup G} {q : ℕ} (hq : q.Prime) (hHall : Work.GW2.IsHallIn I F)
    (hIn : (I.subgroupOf F).Normal) (hQF : Q ≤ F) (hQq : IsPGroup q Q) :
    Q ≤ I ∨ Q ⊓ I = ⊥ := by
  -- Work in the ambient group `F` (a finite group), where `I.subgroupOf F` is normal.
  letI : Fact q.Prime := ⟨hq⟩
  have hIF : I ≤ F := hHall.1
  haveI : (I.subgroupOf F).Normal := hIn
  -- `Q`, transported into `F`, is again a `q`-group.
  have hQ' : IsPGroup q ↥(Q.subgroupOf F) :=
    hQq.of_equiv (Subgroup.subgroupOfEquivOfLe hQF).symm
  -- The Hall condition of `I` in `F`, transported to `I.subgroupOf F ≤ F`.
  have hcard : Nat.card ↥(I.subgroupOf F) = Nat.card ↥I :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hIF).toEquiv
  have hcop : (Nat.card ↥(I.subgroupOf F)).Coprime (I.subgroupOf F).index := by
    rw [hcard]
    exact hHall.2
  -- Mathlib's "all or nothing" for a `q`-group against a normal Hall subgroup.
  rcases IsPGroup.le_or_disjoint_of_coprime (H := I.subgroupOf F) hQ' hcop with h | h
  · left
    intro x hx
    have hxF : x ∈ F := hQF hx
    have hmem : (⟨x, hxF⟩ : ↥F) ∈ Q.subgroupOf F := by
      rw [Subgroup.mem_subgroupOf]; exact hx
    have hthis := h hmem
    rw [Subgroup.mem_subgroupOf] at hthis
    exact hthis
  · right
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hxF : x ∈ F := hQF hx.1
    have hxI : (⟨x, hxF⟩ : ↥F) ∈ I.subgroupOf F := by
      rw [Subgroup.mem_subgroupOf]; exact hx.2
    have hxQ : (⟨x, hxF⟩ : ↥F) ∈ Q.subgroupOf F := by
      rw [Subgroup.mem_subgroupOf]; exact hx.1
    have hd := Subgroup.disjoint_def.mp h hxI hxQ
    simpa using congrArg Subtype.val hd

end Work.CORE3

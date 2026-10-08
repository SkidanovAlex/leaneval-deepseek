import Mathlib
import Submission.Work.SmallRank.Regular.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

namespace Work.SmallRank.Regular

/-- A nontrivial finite `p`-group is not perfect: its commutator subgroup is proper.

Indeed a `p`-group is nilpotent (`IsPGroup.isNilpotent`), hence solvable
(`IsNilpotent.to_isSolvable`), and a nontrivial solvable group has a strictly smaller
commutator subgroup (`Group.IsSolvable.commutator_lt_top_of_nontrivial`).  Mathlib's
`commutator G` is definitionally `⁅⊤, ⊤⁆`, which is exactly `Work.SmallRank.commutator G`. -/
theorem commutator_ne_top {p : ℕ} (hp : p.Prime) {G : Type*} [Group G] [Finite G]
    (hG : IsPGroup p G) [Nontrivial G] :
    Work.SmallRank.commutator G ≠ ⊤ := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Group.IsNilpotent G := hG.isNilpotent
  haveI : Group.IsSolvable G := IsNilpotent.to_isSolvable
  exact (Group.IsSolvable.commutator_lt_top_of_nontrivial G).ne

end Work.SmallRank.Regular

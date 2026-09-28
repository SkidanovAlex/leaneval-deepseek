import Mathlib

set_option linter.style.haveILetI false

namespace Work.RatHurewicz

/-- The image of a finitely generated group under a homomorphism into a commutative torsion
group is finite.

Indeed `f.range` is finitely generated (as a quotient of `G`), commutative (being a subgroup of
the commutative group `H`) and torsion, hence finite by the structure theory of finitely generated
abelian groups (`CommGroup.finite_of_fg_isMulTorsion`). -/
theorem finiteRangeOfFg {G H : Type*} [Group G] [Group H] (hG : Group.FG G)
    (hcomm : ∀ a b : H, a * b = b * a) (htors : ∀ h : H, ∃ n : ℕ, 0 < n ∧ h ^ n = 1)
    (f : G →* H) : (Set.range f).Finite := by
  -- use the commutativity hypothesis to upgrade `H` to a commutative group
  letI : CommGroup H := { ‹Group H› with mul_comm := hcomm }
  -- `f.range` is a quotient of the finitely generated group `G`
  haveI hFG : Group.FG G := hG
  -- `f.range` is torsion
  have hK : IsMulTorsion f.range := by
    intro k
    rw [isOfFinOrder_iff_pow_eq_one]
    obtain ⟨n, hnpos, hn⟩ := htors (k : H)
    exact ⟨n, hnpos, Subtype.ext (by simpa using hn)⟩
  -- a finitely generated torsion abelian group is finite
  haveI : Finite f.range := CommGroup.finite_of_fg_isMulTorsion f.range hK
  exact Set.toFinite (f.range : Set H)

end Work.RatHurewicz

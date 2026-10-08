import Mathlib
import Submission.Work.PGroup.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The center of an extraspecial group is its derived subgroup

An extraspecial `p`-group `E` (FT §2) is a *special* `p`-group that is non-abelian and whose
center has order `p`.  By definition a special group is either elementary abelian, or a
non-abelian `p`-group whose center, derived subgroup and Frattini subgroup coincide.

Since `E` is extraspecial it is not commutative, so the elementary abelian branch of
`IsSpecial` is impossible (`IsElementaryAbelian p E` entails `IsMulCommutative E`), and the
non-abelian branch applies, giving `Z(E) = ⁅E, E⁆` immediately.

This is the "`Z(E) = E'`" half of the standard structure theory of extraspecial groups; it is
recorded as a separate lemma because later arguments use it without wanting the additional
`Z(E) = Φ(E)` information.
-/

namespace Work.PGroup

theorem center_eq_commutator_of_isExtraspecial {G : Type*} [Group G] {p : ℕ} (E : Subgroup G)
    (hE : Work.PGroup.IsExtraspecial p E) : Work.PGroup.centerIn E = ⁅E, E⁆ := by
  obtain ⟨hnc, hs, -⟩ := hE
  rcases hs with hea | ⟨-, -, hcenter, -, -⟩
  · exact absurd hea.1 hnc
  · exact hcenter

end Work.PGroup

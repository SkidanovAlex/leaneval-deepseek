import Mathlib
import Submission.Work.ZassenhausTwoGroup.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausTwoGroup

/-- A non-trivial subgroup of odd order is not a `2`-group.

If `Q₁` were a `2`-group then, for a non-trivial element `g ∈ Q₁`, `2` would divide `orderOf g`
(`IsPGroup.dvd_orderOf`).  On the other hand `orderOf g ∣ Nat.card Q₁` (`orderOf_dvd_natCard`)
and `Nat.card Q₁` is odd, so `orderOf g` is odd — contradiction. -/
theorem not_isPGroup_two_of_odd {G : Type} [Group G] {Q₁ : Subgroup G}
    (h : Odd (Nat.card Q₁)) (hne : Q₁ ≠ ⊥) : ¬ IsPGroup 2 Q₁ := by
  intro hQ
  obtain ⟨g, hg⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have h2 : 2 ∣ orderOf g := hQ.dvd_orderOf hg
  have hodd : Odd (orderOf g) := h.of_dvd_nat (orderOf_dvd_natCard g)
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)

end Work.ZassenhausTwoGroup

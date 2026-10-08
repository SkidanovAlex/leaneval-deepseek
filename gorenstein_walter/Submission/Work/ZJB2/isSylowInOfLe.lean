import Mathlib
import Submission.Work.ZJB2.Defs

namespace Work.ZJB2

open Work.ZJB

/-- **G3.** A Sylow `p`-subgroup of `G` contained in `M` is a Sylow `p`-subgroup of `M`.

Membership `S ≤ M` is the only hypothesis needed: `S` is a `p`-group, and it is maximal
among the `p`-subgroups of `M` because it is already maximal among all `p`-subgroups of `G`. -/
theorem isSylowInOfLe (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Finite G] :
    Work.ZJB.IsSylowInOfLeProp p G := by
  intro S M hSM
  exact ⟨hSM, S.isPGroup', fun Q hSQ _ hQ => S.is_maximal' hQ hSQ⟩

end Work.ZJB2

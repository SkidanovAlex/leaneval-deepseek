import Mathlib
import Submission.NK.LocalAnabelian.Basic

/-!
# The residue characteristic is detected by the tower-rank predicate

If a group `G` detects the residue characteristic `p` through the unbounded
`ℓ`-tower rank predicate, then any prime `q` that *is* an unbounded tower rank
for a group `H ≃* G` must equal `p`.

This is the "one direction" form of `residueCharDetectedBy_unique`: rather than
assuming that `H` detects `q`, we only assume that `H` *has* unbounded `q`-tower
rank, which is what the local-anabelian argument actually provides.
-/

namespace NK.LocalAnabelian.ResidueChar

open NK.LocalAnabelian

/-- If `G` detects the residue characteristic `p` (in the sense of
`ResidueCharDetectedBy`) and `H ≃* G` has unbounded `q`-tower rank for a prime
`q`, then `p = q`. -/
theorem residueCharDetectedBy_of_unique {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    {p q : ℕ} (hG : ResidueCharDetectedBy p G) (hq : q.Prime) (h : HasUnboundedTowerRank q H) :
    p = q := by
  have hqG : HasUnboundedTowerRank q G := hasUnboundedTowerRank_congr e.symm h
  exact ((hG q hq).mp hqG).symm

end NK.LocalAnabelian.ResidueChar

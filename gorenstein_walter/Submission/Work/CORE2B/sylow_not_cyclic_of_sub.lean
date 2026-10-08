import Mathlib
import Submission.Work.CORE2B.Defs

namespace Work.CORE2B

/-- If `G` has a non-cyclic `p`-subgroup `V`, then no Sylow `p`-subgroup of `G` is cyclic.

Indeed if `P` were a cyclic Sylow `p`-subgroup, then every Sylow `p`-subgroup is isomorphic to
`P` (they are all conjugate), hence cyclic; and `V` lies in some Sylow `p`-subgroup `Q`, so `V`,
being a subgroup of the cyclic group `Q`, would be cyclic — contradiction. -/
theorem sylow_not_cyclic_of_sub {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (V : Subgroup G) (hV : IsPGroup p ↥V) (hnc : ¬ IsCyclic ↥V) (P : Sylow p G) :
    ¬ IsCyclic P := by
  intro hPcyc
  -- `V` is contained in some Sylow `p`-subgroup `Q`.
  obtain ⟨Q, hVQ⟩ := hV.exists_le_sylow
  -- `Q` is conjugate to `P`, hence cyclic.
  have hQcyc : IsCyclic ↥Q := (Sylow.equiv P Q).isCyclic.mp hPcyc
  -- A subgroup of the cyclic group `Q` is cyclic, so `V` is cyclic.
  exact hnc (@Subgroup.isCyclic_of_le G _ V Q hVQ hQcyc)

end Work.CORE2B

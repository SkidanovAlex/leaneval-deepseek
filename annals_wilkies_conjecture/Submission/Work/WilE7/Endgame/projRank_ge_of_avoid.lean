import Mathlib
import Submission.Work.WilE7.Endgame.E2_rank_strata

namespace Work.WilE7.Endgame
open Classical Filter Topology
open WilkiesDesign WilkiesDesign.E
open Work.WilE7.MainDesign

theorem projRank_ge_of_avoid {n m K : ℕ} (T : WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    (b : Set (Fin n → ℝ))
    (hdisj : ∀ r : ℕ, r < K → Disjoint b (WilkiesDesign.E.projFirst n (m + 1) ''
      (Work.WilE7.MainDesign.absPt '' {z : Fin (0 + (n + (m + 1))) → ℝ |
        z ∈ T.X.set ∧ Work.WilE7.MainDesign.projRank T z = r})))
    {z : Fin (0 + (n + (m + 1))) → ℝ} (hz : z ∈ T.X.set)
    (hzb : WilkiesDesign.E.projFirst n (m + 1) (Work.WilE7.MainDesign.absPt z) ∈ b) :
    K ≤ Work.WilE7.MainDesign.projRank T z := by
  by_contra hK
  rw [not_le] at hK
  have hd := hdisj (Work.WilE7.MainDesign.projRank T z) hK
  refine (Set.disjoint_left.mp hd) hzb ?_
  exact ⟨Work.WilE7.MainDesign.absPt z, ⟨z, ⟨hz, rfl⟩, rfl⟩, rfl⟩

end Work.WilE7.Endgame

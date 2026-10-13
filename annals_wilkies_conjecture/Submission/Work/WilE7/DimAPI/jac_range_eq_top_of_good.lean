import Mathlib
import Submission.Work.WilE7.MainDesignDefs

namespace Work.WilE7.DimAPI

theorem jac_range_eq_top_of_good {p q : ℕ} (S : WilkiesDesign.E.Stratum p q) (hS : S.Good)
    {z : Fin (p + q) → ℝ} (hz : z ∈ S.X.set) :
    (Work.WilE7.MainDesign.jac S z).range = ⊤ := by sorry

end Work.WilE7.DimAPI

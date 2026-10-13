import Mathlib
import Submission.Work.WilE9.Defs
import Submission.Work.WilE2.Degree

namespace Work.WilE9.EaD

/-- The symbolic derivative does not raise the total degree.

`eaD c i` is by definition `Work.WilE2.ESys.d (ESys.ofChain c) i`, and the degree bound for
that operator is `Work.WilE2.ESys.d_totalDegree_le`: `∂ᵢ Q = Q_{xᵢ} + ∑ⱼ aⱼᵢ Eⱼ Q_{Eⱼ}`, whose
first summand loses a degree (`pderiv`) and whose second summand combines the factor `Eⱼ`
(which restores exactly the degree lost by `Q_{Eⱼ}`) with the scalar `aⱼᵢ`. -/
theorem eaD_totalDegree_le {N r : ℕ} (c : WilkiesDesign.E.EAChain N r) (i : Fin N)
    (Q : WilkiesDesign.E.EAPoly N r) :
    (WilkiesDesign.E.eaD c i Q).totalDegree ≤ Q.totalDegree := by
  have h := Work.WilE2.ESys.d_totalDegree_le (Work.WilE2.ESys.ofChain c) i Q
  rwa [show Work.WilE2.ESys.d (Work.WilE2.ESys.ofChain c) i Q = WilkiesDesign.E.eaD c i Q
        from rfl] at h

end Work.WilE9.EaD

import Mathlib
import Submission.Work.Fitting.Defs
import Submission.Work.Fitting.pPrimePCore_characteristic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Fitting

/-- Each term of the upper `p`-series of a finite group is characteristic: the series is
built by alternately taking `O_{p'}` and `O_p` of the successive quotients, both of which
are characteristic, and pulling back along the (characteristic) quotient map. -/
theorem pCoreSeries_characteristic (p : ℕ) (G : Type*) [Group G] [Finite G] (n : ℕ) :
    (Work.Fitting.pCoreSeries p G n).Characteristic := by
  induction n with
  | zero =>
      rw [pCoreSeries_zero]
      exact Subgroup.botCharacteristic
  | succ n ih =>
      rw [pCoreSeries_succ]
      exact characteristic_comap_quotient ih _
        (piCore_characteristic (fun q => if Even n then q ≠ p else q = p) (G ⧸ pCoreSeries p G n))

end Work.Fitting

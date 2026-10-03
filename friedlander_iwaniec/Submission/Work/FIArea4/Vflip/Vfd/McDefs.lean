import Mathlib
import Submission.Work.FIArea4.Vflip.Vfd.FarSepDefs
import Submission.Work.FIArea4.Vflip.Vfd.farGadgets
import Submission.Work.FIArea4.A4varbounds

/-!
# The per-`(m,c)` bracket of the machine-checked far bound

This module fixes the expression `mcInner` that appears as the inner bracket of the target
`Work.FIArea4.Vflip.Vfd.farInner_mc_bound`: it is exactly the output of the dyadic sum estimate
`dyadic_far_sum` applied to the window `Qmin = SR/(5HcD) < q' < Qmax = 8RS/(cD)` of the flipped
modulus, with the three pieces `A = R'S`, `B = sqrt(R'S)(R'S)^{ε/4}`,
`Cc = (R'S^{3/4} + S R'^{3/4})(R'S)^{ε/4}`, `R' = cR c R`.
-/

namespace Work.FIArea4.Vflip.Vfd

open Finset
open scoped BigOperators

noncomputable section

/-- The per-`(m,c)` inner bracket of `farInner_mc_bound`. -/
def mcInner (D R S m c : ℕ) (H ε : ℝ) : ℝ :=
  (m * ((S:ℝ)*(R:ℝ)/(5*H*(c:ℝ)*(D:ℝ))))^(-(1:ℝ)/2) * ((cR c R:ℝ)*(S:ℝ))
    + ((R:ℝ)*(S:ℝ))^(ε/4)
      * ( m * (16*(R:ℝ)*(S:ℝ)/((c:ℝ)*(D:ℝ))) * Real.sqrt ((cR c R:ℝ)*(S:ℝ))
          + (Real.log (160*H)+1)
            * ( (cR c R:ℝ)*((S:ℝ)^((3:ℝ)/4)) + (S:ℝ)*((cR c R:ℝ)^((3:ℝ)/4)) ) )

end

end Work.FIArea4.Vflip.Vfd

import Mathlib
import Submission.Work.RPA3.A3Defs
import Submission.Work.RPA3.TubularDefs
import Submission.Work.RPA3.Symp
import Submission.Work.RPA3.contDiff_thetaP
import Submission.Work.RPA3.theta_columns_independent
import Submission.Work.RPA3.thetaP_hasFDerivAt_equiv
import Submission.Work.RPA3.exists_local_chart
import Submission.Work.RPA3.theta_injective
import Submission.Work.RPA3.thetaP_locDiffeo_zero

namespace Work.RPA3

/-- D2, existence of the tubular data.  Assemble `TubularData L` from the pieces: take
ε := min ε₁ ε₂ where ε₁ is the radius of `theta_columns_independent` and ε₂ that of
`theta_injective`; the injectivity field is the conclusion of `theta_injective` (whose hypothesis at
ξ = 0 is `thetaP_locDiffeo_zero`), restricted to the radius ε ≤ ε₂; the chart field is
`exists_local_chart` applied with the local-diffeo property `thetaP_hasFDerivAt_equiv` fed by
`theta_columns_independent` (whose column-independence holds for ‖ξ‖ < ε₁) and the smoothness
`contDiff_thetaP`. -/
theorem tubularData_exists (L : Work.RPA3.LagFamilyAll) : Nonempty (Work.RPA3.TubularData L) := by
  -- radius `ε₁` and column-independence on `|x| ≤ X₀+1` for `‖ξ‖ < ε₁`
  obtain ⟨ε₁, hε₁pos, hind⟩ := theta_columns_independent L
  -- injectivity radius `ε₂ ≤ ε₁`, with the local-diffeo hypothesis at `ξ = 0`
  obtain ⟨ε₂, hε₂pos, hε₂le, hinj⟩ :=
    theta_injective L ε₁ hε₁pos (thetaP_locDiffeo_zero L)
  refine ⟨{ ε := min ε₁ ε₂
            εpos := lt_min hε₁pos hε₂pos
            inj := ?_
            chart := ?_ }⟩
  · -- the injectivity field, using `‖ξ‖ < min ε₁ ε₂ ⟹ ‖ξ‖ < ε₂`
    intro τ hτ x t x' t' ξ ξ' ht ht' hξ hξ' k heq
    exact hinj τ hτ x t x' t' ξ ξ' ht ht'
      (lt_of_lt_of_le hξ (min_le_right _ _)) (lt_of_lt_of_le hξ' (min_le_right _ _)) k heq
  · -- the local-chart field, using `‖ξ‖ < min ε₁ ε₂ ⟹ ‖ξ‖ < ε₁`
    intro w hτ hx hξ
    exact exists_local_chart L ε₁ (contDiff_thetaP L)
      (fun w hwτ hwx hwξ => thetaP_hasFDerivAt_equiv L ε₁ hind w hwτ hwx hwξ)
      w hτ hx (lt_of_lt_of_le hξ (min_le_left _ _))

end Work.RPA3

import Mathlib
import Submission.Work.RHContract.LandauDefs

namespace Work.RHContract.B

/-- If `N` is analytic at `0` with `N 0 = 0`, then `N s / s` has a removable singularity at `0`:
it agrees off `0` with the analytic function `dslope N 0`, whose value at `0` is `deriv N 0`. -/
theorem div_removable_analyticAt (N : ℂ → ℂ) (hN : AnalyticAt ℂ N 0) (hN0 : N 0 = 0)
    (hN' : deriv N 0 ≠ 0) :
    ∃ A : ℂ → ℂ, AnalyticAt ℂ A 0 ∧
      Filter.EventuallyEq (nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ) A (fun s : ℂ => N s / s) := by
  rcases hN with ⟨p, hp⟩
  refine ⟨dslope N 0, (HasFPowerSeriesAt.has_fpower_series_dslope_fslope hp).analyticAt, ?_⟩
  filter_upwards [dslope_eventuallyEq_slope_nhdsNE (a := (0 : ℂ)) N] with s hs
  rw [hs]
  rw [slope_def_field, hN0]
  simp

end Work.RHContract.B

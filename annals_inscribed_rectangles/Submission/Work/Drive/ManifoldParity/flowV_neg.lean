import Mathlib
import Submission.Work.Drive.ManifoldParity.InterSetFlowDefs

namespace Work.Drive.ManifoldParity

/-- **The flow of `-V` is the time-reversal of the flow of `V`.**  Both sides are integral curves of
the (Lipschitz) field `-V` through `x`, so they agree by uniqueness of integral curves. -/
theorem flowV_neg {V : Work.Drive.Amb 4 → Work.Drive.Amb 4} (hV : ContDiff ℝ Ctop V)
    (hVs : HasCompactSupport V) (hV' : ContDiff ℝ Ctop (-V)) (hVs' : HasCompactSupport (-V))
    (s : ℝ) (x : Work.Drive.Amb 4) :
    flowV (-V) hV' hVs' s x = flowV V hV hVs (-s) x := by
  obtain ⟨L, hL⟩ :=
    Work.Drive.exists_lipschitzWith_of_contDiff_hasCompactSupport (f := -V) hV' hVs'
  have h1 : ∀ t, HasDerivAt (fun u : ℝ => Work.Drive.flowV (-V) hV' hVs' u x)
      ((-V) ((fun u : ℝ => Work.Drive.flowV (-V) hV' hVs' u x) t)) t :=
    Work.Drive.flowV_deriv (-V) hV' hVs' x
  have h2 : ∀ t, HasDerivAt (fun u : ℝ => Work.Drive.flowV V hV hVs (-u) x)
      ((-V) ((fun u : ℝ => Work.Drive.flowV V hV hVs (-u) x) t)) t := by
    intro t
    have h := (Work.Drive.flowV_deriv V hV hVs x (-t)).scomp t (hasDerivAt_neg' t)
    simpa [Function.comp_def, Pi.neg_apply] using h
  have heq := Work.Drive.integralCurve_unique hL h1 h2 (t₀ := 0)
    (by simp [Work.Drive.flowV_zero])
  exact congrFun heq s

end Work.Drive.ManifoldParity

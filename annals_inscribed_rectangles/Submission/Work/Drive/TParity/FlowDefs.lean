import Mathlib
import Submission.Work.Drive.TParity.Basic
import Submission.Work.Drive.exists_global_integralCurve
import Submission.Work.Drive.integralCurve_unique
import Submission.Work.Drive.flowField_basic

/-!
# The global flow of a compactly supported smooth field on `ℝ⁹`

This is the nine-box analogue of `Work.Drive.ManifoldParity.flowV`
(`Submission/Work/Drive/ManifoldParity/InterSetFlowDefs.lean`), which is stated only for
`Amb 4 = ℝ⁵`.  Everything else in the flow argument (`FlowSetup`, `FlowChart`, `FlowCover`,
`even_ncard_boundary`) is already generic in the dimension.
-/

namespace Work.Drive.TParity

open scoped Manifold ContDiff Topology
open Set Manifold

noncomputable section

/-- The global flow of a compactly supported smooth field `V : ℝ⁹ → ℝ⁹`, as a function of the time
and the initial point. -/
noncomputable def flowV8 (V : Amb 8 → Amb 8) (hV : ContDiff ℝ Ctop V)
    (hVs : HasCompactSupport V) : ℝ → Amb 8 → Amb 8 :=
  fun t x => (Classical.choose (Work.Drive.exists_global_integralCurve hV hVs x)) t

theorem flowV8_zero (V : Amb 8 → Amb 8) (hV : ContDiff ℝ Ctop V) (hVs : HasCompactSupport V)
    (x : Amb 8) : flowV8 V hV hVs 0 x = x :=
  (Classical.choose_spec (Work.Drive.exists_global_integralCurve hV hVs x)).1

theorem flowV8_deriv (V : Amb 8 → Amb 8) (hV : ContDiff ℝ Ctop V) (hVs : HasCompactSupport V)
    (x : Amb 8) : ∀ t, HasDerivAt (fun s => flowV8 V hV hVs s x) (V (flowV8 V hV hVs t x)) t :=
  (Classical.choose_spec (Work.Drive.exists_global_integralCurve hV hVs x)).2

/-- **The flow property**: the integral curves of `V` through the same point agree, so the global
flow is an action of `ℝ`. -/
theorem flowV8_add (V : Amb 8 → Amb 8) (hV : ContDiff ℝ Ctop V) (hVs : HasCompactSupport V)
    (s t : ℝ) (x : Amb 8) :
    flowV8 V hV hVs (s + t) x = flowV8 V hV hVs s (flowV8 V hV hVs t x) := by
  obtain ⟨L, hL⟩ := Work.Drive.exists_lipschitzWith_of_contDiff_hasCompactSupport hV hVs
  have h1 : ∀ u : ℝ, HasDerivAt (fun v : ℝ => flowV8 V hV hVs (v + t) x)
      (V ((fun v : ℝ => flowV8 V hV hVs (v + t) x) u)) u := by
    intro u
    have h := (flowV8_deriv V hV hVs x (u + t)).comp_add_const u
    simpa using h
  have h2 : ∀ u : ℝ, HasDerivAt (fun v : ℝ => flowV8 V hV hVs v (flowV8 V hV hVs t x))
      (V ((fun v : ℝ => flowV8 V hV hVs v (flowV8 V hV hVs t x)) u)) u := fun u =>
    flowV8_deriv V hV hVs (flowV8 V hV hVs t x) u
  have heq : (fun u : ℝ => flowV8 V hV hVs (u + t) x) =
      (fun u : ℝ => flowV8 V hV hVs u (flowV8 V hV hVs t x)) :=
    Work.Drive.integralCurve_unique hL h1 h2 (by rw [zero_add, flowV8_zero])
  have := congrFun heq s
  simpa [zero_add] using this

/-- **The flow of `-V` is the time-reversal of the flow of `V`.** -/
theorem flowV8_neg {V : Amb 8 → Amb 8} (hV : ContDiff ℝ Ctop V) (hVs : HasCompactSupport V)
    (hV' : ContDiff ℝ Ctop (-V)) (hVs' : HasCompactSupport (-V))
    (s : ℝ) (x : Amb 8) :
    flowV8 (-V) hV' hVs' s x = flowV8 V hV hVs (-s) x := by
  obtain ⟨L, hL⟩ :=
    Work.Drive.exists_lipschitzWith_of_contDiff_hasCompactSupport (f := -V) hV' hVs'
  have h1 : ∀ t, HasDerivAt (fun u : ℝ => flowV8 (-V) hV' hVs' u x)
      ((-V) ((fun u : ℝ => flowV8 (-V) hV' hVs' u x) t)) t :=
    flowV8_deriv (-V) hV' hVs' x
  have h2 : ∀ t, HasDerivAt (fun u : ℝ => flowV8 V hV hVs (-u) x)
      ((-V) ((fun u : ℝ => flowV8 V hV hVs (-u) x) t)) t := by
    intro t
    have h := (flowV8_deriv V hV hVs x (-t)).scomp t (hasDerivAt_neg' t)
    simpa [Function.comp_def, Pi.neg_apply] using h
  have heq := Work.Drive.integralCurve_unique hL h1 h2 (t₀ := 0)
    (by simp [flowV8_zero])
  exact congrFun heq s

end

end Work.Drive.TParity

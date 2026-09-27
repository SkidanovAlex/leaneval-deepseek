import Mathlib
import Submission.Work.Drive.BoxParityDefs
import Submission.Work.Drive.exists_global_integralCurve
import Submission.Work.Drive.integralCurve_unique
import Submission.Work.Drive.flowField_basic

/-!
# The global flow of a compactly supported smooth field on `Amb m = ℝ^{m+1}`

This is the dimension-generic version of `Work.Drive.flowV`
(`Submission/Work/Drive/ManifoldParity/InterSetFlowDefs.lean`), which was stated for `m = 4`.
It is the flow used by the intrinsic mod-2 parity argument for sets `K ⊆ ℝ^{m+1}` that are locally
graphs of smooth curves over coordinate axes.
-/

namespace Work.Drive

open scoped ContDiff Topology
open Set

noncomputable section

/-- The global flow of a smooth compactly supported field `V` on `Amb m = ℝ^{m+1}`. -/
noncomputable def flowGen {m : ℕ} (V : Amb m → Amb m) (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hVs : HasCompactSupport V) : ℝ → Amb m → Amb m :=
  fun t x => (Classical.choose (exists_global_integralCurve hV hVs x)) t

theorem flowGen_zero {m : ℕ} (V : Amb m → Amb m) (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hVs : HasCompactSupport V) (x : Amb m) : flowGen V hV hVs 0 x = x :=
  (Classical.choose_spec (exists_global_integralCurve hV hVs x)).1

theorem flowGen_deriv {m : ℕ} (V : Amb m → Amb m) (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hVs : HasCompactSupport V) (x : Amb m) :
    ∀ t, HasDerivAt (fun s => flowGen V hV hVs s x) (V (flowGen V hV hVs t x)) t :=
  (Classical.choose_spec (exists_global_integralCurve hV hVs x)).2

/-- Linearity of the flow in time: the integral curves through a common point agree. -/
theorem flowGen_add {m : ℕ} (V : Amb m → Amb m) (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hVs : HasCompactSupport V) (s t : ℝ) (x : Amb m) :
    flowGen V hV hVs (s + t) x = flowGen V hV hVs s (flowGen V hV hVs t x) := by
  obtain ⟨L, hL⟩ := exists_lipschitzWith_of_contDiff_hasCompactSupport hV hVs
  have h1 : ∀ u : ℝ, HasDerivAt (fun v : ℝ => flowGen V hV hVs (v + t) x)
      (V ((fun v : ℝ => flowGen V hV hVs (v + t) x) u)) u := by
    intro u
    have h := (flowGen_deriv V hV hVs x (u + t)).comp_add_const u
    simpa using h
  have h2 : ∀ u : ℝ, HasDerivAt (fun v : ℝ => flowGen V hV hVs v (flowGen V hV hVs t x))
      (V ((fun v : ℝ => flowGen V hV hVs v (flowGen V hV hVs t x)) u)) u := fun u =>
    flowGen_deriv V hV hVs (flowGen V hV hVs t x) u
  have heq : (fun u : ℝ => flowGen V hV hVs (u + t) x) =
      (fun u : ℝ => flowGen V hV hVs u (flowGen V hV hVs t x)) :=
    integralCurve_unique hL h1 h2 (by rw [zero_add, flowGen_zero])
  have := congrFun heq s
  simpa [zero_add] using this

/-- The flow of `-V` is the time-reversal of the flow of `V`. -/
theorem flowGen_neg {m : ℕ} (V : Amb m → Amb m) (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hVs : HasCompactSupport V) (hV' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (-V))
    (hVs' : HasCompactSupport (-V)) (s : ℝ) (x : Amb m) :
    flowGen (-V) hV' hVs' s x = flowGen V hV hVs (-s) x := by
  obtain ⟨L, hL⟩ := exists_lipschitzWith_of_contDiff_hasCompactSupport (f := -V) hV' hVs'
  have h1 : ∀ t, HasDerivAt (fun u : ℝ => flowGen (-V) hV' hVs' u x)
      ((-V) ((fun u : ℝ => flowGen (-V) hV' hVs' u x) t)) t :=
    flowGen_deriv (-V) hV' hVs' x
  have h2 : ∀ t, HasDerivAt (fun u : ℝ => flowGen V hV hVs (-u) x)
      ((-V) ((fun u : ℝ => flowGen V hV hVs (-u) x) t)) t := by
    intro t
    have h := (flowGen_deriv V hV hVs x (-t)).scomp t (hasDerivAt_neg' t)
    simpa [Function.comp_def, Pi.neg_apply] using h
  have heq := integralCurve_unique hL h1 h2 (t₀ := 0) (by simp [flowGen_zero])
  exact congrFun heq s

end

end Work.Drive

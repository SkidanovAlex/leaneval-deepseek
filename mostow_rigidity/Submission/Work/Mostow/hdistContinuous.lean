import Mathlib
import Submission.Work.Mostow.Hyper

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open Submission.Mostow.Hyper

/-- The cosh-kernel `cc u v = cosh (hdist u v)` is at least `1`. -/
lemma one_le_cc_hdistContinuous {n : ℕ} (u v : E n) : 1 ≤ cc u v := by
  have h1 : inner ℝ u v ≤ ‖u‖ * ‖v‖ := real_inner_le_norm u v
  have hnn : 0 ≤ 1 + ‖u‖ * ‖v‖ := by positivity
  have ht : 0 ≤ tpart u * tpart v := le_of_lt (mul_pos (tpart_pos u) (tpart_pos v))
  have hb : (1 + ‖u‖ * ‖v‖)^2 ≤ (tpart u * tpart v)^2 := by
    rw [mul_pow, sq_tpart, sq_tpart]
    nlinarith [sq_nonneg (‖u‖ - ‖v‖)]
  have h2 : 1 + ‖u‖ * ‖v‖ ≤ tpart u * tpart v := by
    have := Real.sqrt_le_sqrt hb
    rwa [Real.sqrt_sq hnn, Real.sqrt_sq ht] at this
  simp only [cc]
  linarith

/-- The hyperbolic distance `hdist u v = arcosh (tpart u * tpart v - ⟪u, v⟫)` is continuous. -/
theorem hdistContinuous (n : ℕ) : Continuous (fun p : E n × E n => hdist p.1 p.2) := by
  have h : (fun p : E n × E n => hdist p.1 p.2) = fun p => Real.arcosh (cc p.1 p.2) := by
    funext p; exact hdist_eq_cc p.1 p.2
  rw [h]
  have htpart : Continuous (fun u : E n => tpart u) :=
    Real.continuous_sqrt.comp (by fun_prop)
  have hcont : Continuous (fun p : E n × E n => cc p.1 p.2) := by
    simp only [cc]
    exact ((htpart.comp continuous_fst).mul (htpart.comp continuous_snd)).sub continuous_inner
  have := ContinuousOn.comp_continuous (g := Real.arcosh)
    (f := fun p : E n × E n => cc p.1 p.2) (s := Set.Ici 1)
    Real.continuousOn_arcosh hcont (fun p => one_le_cc_hdistContinuous p.1 p.2)
  simpa [Function.comp_def] using this

end Work.Mostow

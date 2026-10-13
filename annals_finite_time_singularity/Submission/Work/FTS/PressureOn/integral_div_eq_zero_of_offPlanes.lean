/-
# The divergence theorem off the two coordinate planes

`Work.FTS.PressureOn.integral_div_eq_zero_of_offPlanes`: a continuous compactly supported field
`W : ℝ³ → ℝ³` which is differentiable (with derivative `fderiv ℝ W x`) at every point *off the
two planes* `x 0 = 0`, `x 2 = 0`, and whose divergence is integrable, has vanishing divergence
integral.

This is the `ψ ≡ 1` case of `integral_div_mul_of_differentiable_off_planes`, and it is the
"Weyl/Liouville" input of the pressure reconstruction: the exceptional set is a union of two
planes, hence null but *not* countable, so Mathlib's
`MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable` does not apply directly.  The
work is done by `Work.FTS.PressureOn.integral_trace_eq_zero_of_diff_off_planes` (imported through
`integral_div_mul_of_differentiable_off_planes`), which cuts `ℝ³` into the four boxes delimited by
the two planes and matches the face integrals pairwise; here we only have to transport `W` to the
coordinate space `Fin 3 → ℝ` and back.

The hypotheses of the sibling `integral_div_eq_zero_of_hasFDerivAt` are stronger (differentiability
everywhere); this lemma is what the pressure reconstruction actually has at its disposal, since
the pointwise vorticity equation is only available on `Uax = {x 2 ≠ 0 ∧ x 0² + x 1² ≠ 0}`.
-/
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PressureOn.Defs
import Submission.Work.FTS.PressureOn.integral_div_eq_zero_of_hasFDerivAt
import Submission.Work.FTS.PressureOn.integral_div_mul_of_differentiable_off_planes

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn

theorem integral_div_eq_zero_of_offPlanes {W : R3 → R3}
    (hWcont : Continuous W) (hWcs : HasCompactSupport W)
    (hWdiff : ∀ x, x 0 ≠ 0 → x 2 ≠ 0 → HasFDerivAt W (fderiv ℝ W x) x)
    (hWint : MeasureTheory.Integrable (fun x => FiniteTimeSingularity.div W x)) :
    ∫ x, FiniteTimeSingularity.div W x = 0 := by
  -- a ball containing the support, off which `W` and its divergence vanish
  obtain ⟨R, hRpos, hR⟩ := exists_norm_supp_bound W hWcs
  -- transport to the coordinate space `Fin 3 → ℝ`
  have hHcont : Continuous (transport W) := continuous_transport W hWcont
  have hHdiff : ∀ x : Fin 3 → ℝ, x 0 ≠ 0 → x 2 ≠ 0 →
      HasFDerivAt (transport W) (fderivTransport W x) x := by
    intro x hx0 hx2
    refine hasFDerivAt_transport ?_
    exact hWdiff (toLpCLM x) (by simpa using hx0) (by simpa using hx2)
  have hHint : MeasureTheory.Integrable
      (fun x : Fin 3 → ℝ => ∑ i, fderivTransport W x (Pi.single i (1 : ℝ)) i) := by
    refine (integrable_div_transport W hWint).congr ?_
    filter_upwards with x
    exact (sum_fderivTransport W x).symm
  have hHsupp : ∀ x : Fin 3 → ℝ, R ≤ ‖x‖ → transport W x = 0 := by
    intro x hx
    have h1 : R ≤ ‖toLpCLM x‖ := le_trans hx (norm_le_norm_toLp x)
    change WithLp.ofLp (W (toLpCLM x)) = 0
    rw [(hR (toLpCLM x) h1).1]
    exact WithLp.ofLp_zero 2
  have hH'supp : ∀ x : Fin 3 → ℝ, R ≤ ‖x‖ →
      (∑ i, fderivTransport W x (Pi.single i (1 : ℝ)) i) = 0 := by
    intro x hx
    have h1 : R ≤ ‖toLpCLM x‖ := le_trans hx (norm_le_norm_toLp x)
    rw [sum_fderivTransport]
    exact (hR (toLpCLM x) h1).2
  -- the divergence theorem on the coordinate space, off the two planes
  have hcore := integral_trace_eq_zero_of_diff_off_planes (transport W) (fderivTransport W)
    hHcont hHdiff hHint R hRpos hHsupp hH'supp
  -- transport back to `ℝ³`
  have hEq : (∫ x : Fin 3 → ℝ, FiniteTimeSingularity.div W (toLpCLM x))
      = ∫ x : Fin 3 → ℝ, ∑ i, fderivTransport W x (Pi.single i (1 : ℝ)) i :=
    MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun x => (sum_fderivTransport W x).symm)
  rw [← integral_div_transport W, hEq]
  exact hcore

end Work.FTS.PressureOn

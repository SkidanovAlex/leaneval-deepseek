import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixR.LatGreen.HeatIntegral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The truncated time-integral of the heat kernel is at most the Green's function

`∫₀^ε heatK3 s x ds ≤ 1/(4π‖x‖)` for every `ε > 0` and `x ≠ 0`.

This is immediate from `HeatIntegral`, which identifies the *full* time integral
`∫_{s>0} heatK3 s x ds = 1/(4π‖x‖)` with the fundamental solution of `−Δ` on `ℝ³`:
the truncated integral is the integral of a nonnegative kernel over a subset of `(0, ∞)`,
so it is dominated by the full one (`MeasureTheory.setIntegral_mono_set`).  Integrability of
the heat kernel on `(0, ∞)` is read off from `HeatIntegral` itself: were it non-integrable, the
Bochner integral would vanish (`MeasureTheory.integral_undef`), contradicting the positivity of
`1/(4π‖x‖)`.
-/

namespace Work.BoseFixR.LatGreen

/-- The heat kernel of `ℝ³` is integrable in time on `(0, ∞)`, at every `x ≠ 0`.  (This is
extracted from `HeatIntegral`: a nonnegative function whose Bochner integral is a *nonzero*
real is necessarily integrable.) -/
theorem integrableOn_heatK3_Ioi {x : EuclideanSpace ℝ (Fin 3)} (hx : x ≠ 0) :
    MeasureTheory.IntegrableOn (fun t : ℝ => heatK3 t x) (Set.Ioi (0 : ℝ)) := by
  by_contra h
  have h0 : ∫ t in Set.Ioi (0 : ℝ), heatK3 t x = 0 := MeasureTheory.integral_undef h
  have hH := HeatIntegral (x := x) hx
  rw [h0] at hH
  have hpos : 0 < 1 / (4 * Real.pi * ‖x‖) := by
    have hx' : 0 < ‖x‖ := norm_pos_iff.mpr hx
    positivity
  linarith

theorem heatK3_ioc_integral_le_green {ε : ℝ} (hε : 0 < ε)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ≠ 0) :
    ∫ s in Set.Ioc 0 ε, Work.BoseFixR.LatGreen.heatK3 s x
      ≤ 1 / (4 * Real.pi * ‖x‖) := by
  rw [← HeatIntegral (x := x) hx]
  refine MeasureTheory.setIntegral_mono_set (integrableOn_heatK3_Ioi hx) ?_ ?_
  · show ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      (0 : ℝ) ≤ heatK3 t x
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    exact Filter.Eventually.of_forall fun t ht => heatK3_nonneg ht x
  · exact Filter.Eventually.of_forall fun t ht => ht.1

end Work.BoseFixR.LatGreen

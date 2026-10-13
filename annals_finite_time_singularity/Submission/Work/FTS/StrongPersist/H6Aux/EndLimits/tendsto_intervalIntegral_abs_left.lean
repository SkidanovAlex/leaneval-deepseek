import Mathlib.MeasureTheory.Integral.DominatedConvergence

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Aux.EndLimits

/-- The primitive `r ↦ ∫_0^r |f|` of an `L¹` function on `(0,L)` tends to `0` as `r → 0` from
the right.  This is the absolute continuity of the Lebesgue integral, in the form of the
continuity of the integral as a function of its upper endpoint together with the fact that
`Icc 0 L` is a neighbourhood of `0` inside `Ioi 0`. -/
theorem tendsto_intervalIntegral_abs_left {L : ℝ} (hL : 0 < L) {f : ℝ → ℝ}
    (hf : MeasureTheory.IntegrableOn f (Set.Ioo (0:ℝ) L)) :
    Filter.Tendsto (fun r : ℝ => ∫ x in (0:ℝ)..r, |f x|)
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) := by
  -- `|f|` is interval integrable on `0..L`, so its primitive is continuous there.
  have hInt : IntervalIntegrable (fun x : ℝ => |f x|) MeasureTheory.volume (0:ℝ) L :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (le_of_lt hL)).2 hf.abs
  have hprim : ContinuousWithinAt (fun r : ℝ => ∫ x in (0:ℝ)..r, |f x|)
      (Set.Icc (0:ℝ) L) (0:ℝ) :=
    intervalIntegral.continuousWithinAt_primitive (MeasureTheory.measure_singleton 0)
      (by simpa [max_eq_right (le_of_lt hL)] using hInt)
  -- `Icc 0 L` is a neighbourhood of `0` relative to `Ioi 0`.
  have hsub : nhdsWithin (0:ℝ) (Set.Ioi 0) ≤ nhdsWithin (0:ℝ) (Set.Icc (0:ℝ) L) := by
    rw [nhdsWithin_le_iff, mem_nhdsWithin]
    exact ⟨Set.Iio L, isOpen_Iio, hL, fun x hx => ⟨le_of_lt hx.2, le_of_lt hx.1⟩⟩
  simpa using hprim.mono_left hsub

end Work.FTS.StrongPersist.H6Aux.EndLimits

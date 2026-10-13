import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Aux.EndLimits

/-- The absolute continuity of the integral: as `t → L⁻` the integral of `|f|` over `(t, L)`
tends to zero, for `f` integrable on `(0, L)`. -/
theorem tendsto_intervalIntegral_abs_right {L : ℝ} (hL : 0 < L) {f : ℝ → ℝ}
    (hf : MeasureTheory.IntegrableOn f (Set.Ioo (0:ℝ) L)) :
    Filter.Tendsto (fun t : ℝ => ∫ x in t..L, |f x|)
      (nhdsWithin L (Set.Iio L)) (nhds 0) := by
  -- extend `|f|` to a globally integrable function `F` by killing it off `(0, L)`
  set F : ℝ → ℝ := (Set.Ioo (0:ℝ) L).indicator (fun x => |f x|) with hFdef
  have hFint : MeasureTheory.Integrable F := by
    rw [hFdef]
    exact (MeasureTheory.integrable_indicator_iff measurableSet_Ioo).mpr hf.abs
  -- the measure of `(t, L)` tends to `0` as `t → L⁻`
  have hmeas : Filter.Tendsto (fun t : ℝ => MeasureTheory.volume (Set.Ioc t L))
      (nhdsWithin L (Set.Iio L)) (nhds 0) := by
    have hfun : (fun t : ℝ => MeasureTheory.volume (Set.Ioc t L)) =
        fun t : ℝ => ENNReal.ofReal (L - t) := by
      funext t
      rw [Real.volume_Ioc]
    rw [hfun]
    have hcont : Filter.Tendsto (fun t : ℝ => L - t) (nhdsWithin L (Set.Iio L))
        (nhds (L - L)) :=
      tendsto_nhdsWithin_of_tendsto_nhds
        (tendsto_const_nhds.sub Filter.tendsto_id)
    have h := ENNReal.tendsto_ofReal hcont
    simpa using h
  -- absolute continuity of the integral
  have hmain : Filter.Tendsto (fun t : ℝ => ∫ x in Set.Ioc t L, F x)
      (nhdsWithin L (Set.Iio L)) (nhds 0) :=
    hFint.tendsto_setIntegral_nhds_zero (s := fun t : ℝ => Set.Ioc t L) hmeas
  -- identify the two functions eventually (for `t` close to `L`, hence `t ∈ (0, L)`)
  refine Filter.Tendsto.congr' ?_ hmain
  filter_upwards [self_mem_nhdsWithin,
    eventually_nhdsWithin_of_eventually_nhds
      (Filter.eventually_iff.mpr (IsOpen.mem_nhds isOpen_Ioi hL))] with t ht hpos
  have h1 : (∫ x in t..L, |f x|) = ∫ x in Set.Ioo t L, |f x| := by
    rw [intervalIntegral.integral_of_le ht.le, MeasureTheory.integral_Ioc_eq_integral_Ioo]
  rw [MeasureTheory.integral_Ioc_eq_integral_Ioo, h1]
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun x hx => by
    simp only [hFdef,
      Set.indicator_of_mem (show x ∈ Set.Ioo (0:ℝ) L from ⟨lt_trans hpos hx.1, hx.2⟩)])

end Work.FTS.StrongPersist.H6Aux.EndLimits

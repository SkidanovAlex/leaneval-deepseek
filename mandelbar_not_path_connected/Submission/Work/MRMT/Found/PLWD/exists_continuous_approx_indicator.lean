import Mathlib
import Submission.Work.MRMT.Found.PLWD.Defs
import Submission.Work.MRMT.Found.eLpNorm_le_of_support_measure

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open MeasureTheory Filter Topology Function
open scoped ENNReal Topology

namespace Work.MRMT.Found.PLWD

/-- A compact subset of the open ball of radius `R` around the origin is contained in an open ball
of radius strictly smaller than `R`. -/
theorem exists_lt_isCompact_subset_ball {K : Set ℂ} {R : ℝ} (hR : 0 < R)
    (hK : IsCompact K) (hKR : K ⊆ Metric.ball 0 R) :
    ∃ r : ℝ, r < R ∧ K ⊆ Metric.ball 0 r := by
  by_cases hne : K.Nonempty
  · obtain ⟨x₀, hx₀K, hmax⟩ := hK.exists_isMaxOn hne continuous_norm.continuousOn
    have hx₀R : ‖x₀‖ < R := by
      have h := hKR hx₀K
      rwa [Metric.mem_ball, dist_zero_right] at h
    refine ⟨(‖x₀‖ + R) / 2, by linarith, fun x hx => ?_⟩
    rw [Metric.mem_ball, dist_zero_right]
    have h : ‖x‖ ≤ ‖x₀‖ := hmax hx
    linarith
  · refine ⟨R / 2, by linarith, fun x hx => ?_⟩
    exact absurd ⟨x, hx⟩ hne

theorem exists_continuous_approx_indicator {R : ℝ} (hR : 0 < R) {s : Set ℂ}
    (hsm : MeasurableSet s) (hsR : s ⊆ Metric.ball 0 R)
    (hfin : (MeasureTheory.volume : MeasureTheory.Measure ℂ) s < ⊤) (c : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (f : ℂ → ℂ) (r : ℝ), Continuous f ∧ r < R ∧
      Function.support f ⊆ Metric.closedBall 0 r ∧
      MeasureTheory.eLpNorm (fun z => f z - s.indicator (fun _ => c) z) 2
        (MeasureTheory.volume : MeasureTheory.Measure ℂ) ≤ ENNReal.ofReal ε := by
  -- A small real `δ` such that `‖c‖ * √δ ≤ ε/2`.
  set δ : ℝ := (ε / (2 * (‖c‖ + 1))) ^ 2 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  have hδnz : ENNReal.ofReal δ ≠ 0 := (ENNReal.ofReal_pos.mpr hδpos).ne'
  -- Inner approximation of `s` by a compact set.
  obtain ⟨K, hKs, hKc, hKsdiff⟩ := hsm.exists_isCompact_sdiff_lt hfin.ne hδnz
  have hKR : K ⊆ Metric.ball 0 R := hKs.trans hsR
  -- A radius `r < R` with `K ⊆ ball 0 r`.
  obtain ⟨r, hrR, hKr⟩ := exists_lt_isCompact_subset_ball hR hKc hKR
  have hε2pos : 0 < ε / 2 := by linarith
  have hε2nz : ENNReal.ofReal (ε / 2) ≠ 0 := (ENNReal.ofReal_pos.mpr hε2pos).ne'
  -- Urysohn-type `L²` approximation of the indicator of `K` by a continuous function supported
  -- in `ball 0 r`.
  obtain ⟨f, hfcont, hfclose, -, hfsupp, -⟩ :=
    MeasureTheory.exists_continuous_eLpNorm_sub_le_of_closed
      (μ := (MeasureTheory.volume : MeasureTheory.Measure ℂ)) (p := 2) (by norm_num)
      hKc.isClosed Metric.isOpen_ball hKr hKc.measure_lt_top.ne c hε2nz
  -- The real estimate.
  have hsqrt : Real.sqrt δ = ε / (2 * (‖c‖ + 1)) := by
    rw [hδdef, Real.sqrt_sq (by positivity)]
  have hkey : ‖c‖ * (ε / (2 * (‖c‖ + 1))) ≤ ε / 2 := by
    have hpos : (0 : ℝ) < 2 * (‖c‖ + 1) := by positivity
    rw [← mul_div_assoc, div_le_iff₀ hpos]
    nlinarith [norm_nonneg c, hε]
  -- The difference of the two indicators is the (small) indicator of `s \ K`.
  have hfun2 : (fun z => K.indicator (fun _ => c) z - s.indicator (fun _ => c) z)
      = fun z => (s \ K).indicator (fun _ => -c) z := by
    funext z
    by_cases hzK : z ∈ K
    · rw [Set.indicator_of_mem hzK (fun _ => c), Set.indicator_of_mem (hKs hzK) (fun _ => c),
        Set.indicator_of_notMem (fun h => h.2 hzK) (fun _ => -c)]
      simp
    · by_cases hzS : z ∈ s
      · rw [Set.indicator_of_notMem hzK (fun _ => c), Set.indicator_of_mem hzS (fun _ => c),
          Set.indicator_of_mem (show z ∈ s \ K from ⟨hzS, hzK⟩) (fun _ => -c)]
        simp
      · rw [Set.indicator_of_notMem hzK (fun _ => c), Set.indicator_of_notMem hzS (fun _ => c),
          Set.indicator_of_notMem (fun h => hzS h.1) (fun _ => -c)]
        simp
  have hbound2 : MeasureTheory.eLpNorm
      (fun z => K.indicator (fun _ => c) z - s.indicator (fun _ => c) z) 2
        (MeasureTheory.volume : MeasureTheory.Measure ℂ) ≤ ENNReal.ofReal (ε / 2) := by
    rw [hfun2]
    have hlep := eLpNorm_le_of_support_measure
      (f := fun z => (s \ K).indicator (fun _ => -c) z) (S := s \ K)
      (M := ‖c‖) (V := δ) (norm_nonneg c) (le_of_lt hδpos)
      ((Measurable.indicator measurable_const (hsm.diff hKc.measurableSet)).aestronglyMeasurable)
      ((hsm.diff hKc.measurableSet).nullMeasurableSet)
      (fun z hz => Set.indicator_of_notMem hz _)
      (by
        intro z
        by_cases hz : z ∈ s \ K
        · rw [Set.indicator_of_mem hz]; simp
        · rw [Set.indicator_of_notMem hz]; simp)
      (le_of_lt hKsdiff)
    refine hlep.trans ?_
    rw [hsqrt]
    exact (ENNReal.ofReal_le_ofReal_iff hε2pos.le).mpr hkey
  refine ⟨f, r, hfcont, hrR, hfsupp.trans Metric.ball_subset_closedBall, ?_⟩
  have heq : (fun z => f z - s.indicator (fun _ => c) z)
      = (fun z => (f z - K.indicator (fun _ => c) z)
          + (K.indicator (fun _ => c) z - s.indicator (fun _ => c) z)) := by
    funext z; ring
  rw [heq]
  calc MeasureTheory.eLpNorm
        ((fun z => f z - K.indicator (fun _ => c) z)
          + (fun z => K.indicator (fun _ => c) z - s.indicator (fun _ => c) z)) 2
          (MeasureTheory.volume : MeasureTheory.Measure ℂ)
      ≤ MeasureTheory.eLpNorm (fun z => f z - K.indicator (fun _ => c) z) 2
            (MeasureTheory.volume : MeasureTheory.Measure ℂ)
        + MeasureTheory.eLpNorm
            (fun z => K.indicator (fun _ => c) z - s.indicator (fun _ => c) z) 2
            (MeasureTheory.volume : MeasureTheory.Measure ℂ) :=
          MeasureTheory.eLpNorm_add_le (by norm_num)
    _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := add_le_add hfclose hbound2
    _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add hε2pos.le hε2pos.le]
        congr 1
        ring

end Work.MRMT.Found.PLWD

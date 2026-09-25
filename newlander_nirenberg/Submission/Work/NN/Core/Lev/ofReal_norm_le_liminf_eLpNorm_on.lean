import Mathlib
import Submission.Work.NN.Core.CnPert
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.NN.Core.ofReal_norm_le_liminf_eLpNorm

namespace Work.NN.Core.Lev

open scoped ENNReal
open MeasureTheory Filter

set_option linter.unusedVariables false in
theorem ofReal_norm_le_liminf_eLpNorm_on {n : ℕ} (hn : 0 < n) {u : Work.NN.Core.Cn n → ℂ}
    {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j)
    (hu : ContinuousOn u (Work.CR.Flat.polydisc 0 ρ))
    {c : Work.NN.Core.Cn n} (hc : c ∈ Work.CR.Flat.polydisc 0 ρ) {r : ℝ} (hr : 0 < r)
    (hball : Metric.ball c r ⊆ Work.CR.Flat.polydisc 0 ρ)
    {E : ℕ → ℝ} (hE : ∀ j, 1 ≤ E j)
    (hEtop : Filter.Tendsto E Filter.atTop Filter.atTop) :
    ENNReal.ofReal ‖u c‖ ≤ Filter.liminf
      (fun j => MeasureTheory.eLpNorm u (ENNReal.ofReal (E j))
        (MeasureTheory.volume.restrict (Metric.ball c r))) Filter.atTop := by
  -- `u` is continuous at `c`, since `c` is an interior point of the polydisc.
  have hcontAt : ContinuousAt u c :=
    hu.continuousAt ((Work.CR.Flat.isOpen_polydisc (0 : Work.NN.Core.Cn n) ρ).mem_nhds hc)
  -- Every `b < ‖u c‖` is eventually below the `L^{E j}` seminorm on the ball.
  have key : ∀ b : ℝ, 0 ≤ b → b < ‖u c‖ →
      ∀ᶠ j in Filter.atTop, ENNReal.ofReal b ≤ MeasureTheory.eLpNorm u (ENNReal.ofReal (E j))
        (MeasureTheory.volume.restrict (Metric.ball c r)) := by
    intro b hb0 hbc
    set b0 : ℝ := (b + ‖u c‖) / 2 with hb0def
    have hbb0 : b < b0 := by rw [hb0def]; linarith
    have hb0a : b0 < ‖u c‖ := by rw [hb0def]; linarith
    have hb0pos : 0 < b0 := lt_of_le_of_lt hb0 hbb0
    obtain ⟨s, hspos, hs⟩ := Work.NN.Core.exists_ball_norm_le_of_continuousAt hcontAt hb0a
    set s' : ℝ := min s r with hs'def
    have hs'pos : 0 < s' := lt_min hspos hr
    have hs'le_r : s' ≤ r := min_le_right _ _
    have hbound : ∀ x ∈ Metric.ball c s', b0 ≤ ‖u x‖ := fun x hx =>
      hs x (Metric.ball_subset_ball (min_le_left _ _) hx)
    -- The lower bound on the small ball, from the general measure-theoretic lemma.
    have hsmall : ∀ j, ENNReal.ofReal b0
          * (MeasureTheory.volume (Metric.ball c s')) ^ (1 / E j)
        ≤ MeasureTheory.eLpNorm u (ENNReal.ofReal (E j))
            (MeasureTheory.volume.restrict (Metric.ball c s')) := by
      intro j
      have hbd : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Metric.ball c s')), b0 ≤ ‖u x‖ := by
        rw [ae_restrict_iff' Metric.isOpen_ball.measurableSet]
        exact Filter.Eventually.of_forall fun x hx => hbound x hx
      have hmeas : AEStronglyMeasurable u (MeasureTheory.volume.restrict (Metric.ball c s')) := by
        have hsub : Metric.ball c s' ⊆ Work.CR.Flat.polydisc 0 ρ := fun x hx =>
          hball (Metric.ball_subset_ball hs'le_r hx)
        exact (hu.mono hsub).aestronglyMeasurable Metric.isOpen_ball.measurableSet
      have hh := Work.NN.Core.ofReal_mul_rpow_measure_le_eLpNorm hmeas hb0pos.le hbd (hE j)
      rwa [Measure.restrict_apply_univ] at hh
    -- Enlarge the ball to the given one.
    have hbig : ∀ j, MeasureTheory.eLpNorm u (ENNReal.ofReal (E j))
            (MeasureTheory.volume.restrict (Metric.ball c s'))
        ≤ MeasureTheory.eLpNorm u (ENNReal.ofReal (E j))
            (MeasureTheory.volume.restrict (Metric.ball c r)) := by
      intro j
      exact MeasureTheory.eLpNorm_mono_measure _
        (Measure.restrict_mono (Metric.ball_subset_ball hs'le_r) le_rfl)
    have hchain : ∀ j, ENNReal.ofReal b0
          * (MeasureTheory.volume (Metric.ball c s')) ^ (1 / E j)
        ≤ MeasureTheory.eLpNorm u (ENNReal.ofReal (E j))
            (MeasureTheory.volume.restrict (Metric.ball c r)) :=
      fun j => (hsmall j).trans (hbig j)
    have hvolpos : 0 < MeasureTheory.volume (Metric.ball c s') :=
      Metric.measure_ball_pos (MeasureTheory.volume : MeasureTheory.Measure (Work.NN.Core.Cn n)) c hs'pos
    have hlim := Work.NN.Core.eventually_ofReal_le_ofReal_mul_rpow_inv MeasureTheory.volume hvolpos
      hEtop hE hbb0 hb0pos
    filter_upwards [hlim] with j hj
    exact hj.trans (hchain j)
  -- Hence `ofReal b ≤ liminf` for every `b < ‖u c‖`.
  have key2 : ∀ b : ℝ, 0 ≤ b → b < ‖u c‖ →
      ENNReal.ofReal b ≤ Filter.liminf
        (fun j => MeasureTheory.eLpNorm u (ENNReal.ofReal (E j))
          (MeasureTheory.volume.restrict (Metric.ball c r))) Filter.atTop :=
    fun b hb0 hbc => Filter.le_liminf_of_le (by isBoundedDefault) (key b hb0 hbc)
  -- `ofReal ‖u c‖` is the supremum of `ofReal b` over `b < ‖u c‖`.
  refine le_of_forall_lt fun c' hc' => ?_
  have hc'top : c' ≠ ⊤ := ne_top_of_lt hc'
  have hc'lt : c'.toReal < ‖u c‖ := (ENNReal.lt_ofReal_iff_toReal_lt hc'top).mp hc'
  set b : ℝ := (c'.toReal + ‖u c‖) / 2 with hbdef
  have hb0 : 0 ≤ b := by
    rw [hbdef]; linarith [ENNReal.toReal_nonneg (a := c'), norm_nonneg (u c)]
  have hbc : b < ‖u c‖ := by rw [hbdef]; linarith
  have hc'b : c' < ENNReal.ofReal b := by
    rw [ENNReal.lt_ofReal_iff_toReal_lt hc'top, hbdef]; linarith
  exact lt_of_lt_of_le hc'b (key2 b hb0 hbc)

end Work.NN.Core.Lev

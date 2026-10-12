import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open MeasureTheory Filter

set_option linter.unusedVariables false

namespace Work.BoseRowsL.Tails

/-- If `f` is integrable on `ℝ³` and `c N → ∞`, then the integral of `f` over the tail region
`{p | c N < ‖p‖}` tends to `0`.

This is the standard dominated-convergence statement for the tails of an integrable function;
no monotonicity of `c` is needed, because the tails are eventually *decreasing* pointwise. -/
theorem tendsto_tail_setIntegral (f : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hf : MeasureTheory.Integrable f) (hf0 : ∀ᵐ p : EuclideanSpace ℝ (Fin 3), 0 ≤ f p)
    {c : ℕ → ℝ} (hc : Filter.Tendsto c Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun N : ℕ => ∫ p in {p : EuclideanSpace ℝ (Fin 3) | c N < ‖p‖}, f p)
      Filter.atTop (nhds 0) := by
  have hmeas : ∀ N : ℕ, MeasurableSet {p : EuclideanSpace ℝ (Fin 3) | c N < ‖p‖} :=
    fun N => measurableSet_lt measurable_const continuous_norm.measurable
  -- Rewrite the restricted integrals as integrals of the corresponding indicators.
  have hrewrite : ∀ N : ℕ,
      (∫ p in {p : EuclideanSpace ℝ (Fin 3) | c N < ‖p‖}, f p)
        = ∫ p, Set.indicator {p : EuclideanSpace ℝ (Fin 3) | c N < ‖p‖} f p :=
    fun N => (MeasureTheory.integral_indicator (hmeas N)).symm
  rw [funext hrewrite]
  -- Each indicator vanishes eventually, pointwise (no a.e. statement needed here).
  have hlim : ∀ᵐ p : EuclideanSpace ℝ (Fin 3) ∂(volume : Measure (EuclideanSpace ℝ (Fin 3))),
      Filter.Tendsto
        (fun N : ℕ => Set.indicator {p : EuclideanSpace ℝ (Fin 3) | c N < ‖p‖} f p)
        Filter.atTop (nhds 0) := by
    refine Filter.Eventually.of_forall (fun p => ?_)
    have hev : (fun _ : ℕ => (0 : ℝ)) =ᶠ[Filter.atTop]
        (fun N : ℕ => Set.indicator {p : EuclideanSpace ℝ (Fin 3) | c N < ‖p‖} f p) := by
      filter_upwards [hc.eventually (Filter.eventually_gt_atTop ‖p‖)] with N hN
      exact (Set.indicator_of_notMem
        (by simp only [Set.mem_ofPred_eq, not_lt]; exact hN.le) f).symm
    exact Filter.Tendsto.congr' hev tendsto_const_nhds
  -- Dominated convergence with dominating function `‖f‖`.
  have hmain : Filter.Tendsto
      (fun N : ℕ => ∫ p, Set.indicator {p : EuclideanSpace ℝ (Fin 3) | c N < ‖p‖} f p)
      Filter.atTop (nhds (∫ p, (0 : ℝ))) :=
    MeasureTheory.tendsto_integral_of_dominated_convergence
      (μ := (volume : Measure (EuclideanSpace ℝ (Fin 3))))
      (F := fun N p => Set.indicator {p : EuclideanSpace ℝ (Fin 3) | c N < ‖p‖} f p)
      (f := fun _ => (0 : ℝ))
      (fun p => ‖f p‖)
      (fun N => hf.aestronglyMeasurable.indicator (hmeas N))
      hf.norm
      (fun N => Filter.Eventually.of_forall (fun p => norm_indicator_le_norm_self _ _))
      hlim
  simpa using hmain

end Work.BoseRowsL.Tails

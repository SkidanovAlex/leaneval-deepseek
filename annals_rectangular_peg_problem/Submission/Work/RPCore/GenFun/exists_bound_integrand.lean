import Mathlib

open MeasureTheory

namespace Work.RPCore.GenFun

/-- On the compact set `[0,1] × closedBall y₀ 1` the integrand
`(t,x) ↦ ‖B (t • fderiv ℝ b (t • x) x + b (t • x))‖` is continuous, hence bounded by a
constant; the constant function is interval-integrable on `[0,1]`. -/
theorem exists_bound_integrand {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (B : E →L[ℝ] E →L[ℝ] ℝ) (b : E → E) (hb : ContDiff ℝ 3 b)
    (y₀ : E) :
    ∃ bound : ℝ → ℝ, IntervalIntegrable bound volume (0 : ℝ) 1 ∧
      ∀ t ∈ Set.uIoc (0 : ℝ) 1, ∀ x ∈ Metric.closedBall y₀ 1,
        ‖B (t • fderiv ℝ b (t • x) x + b (t • x))‖ ≤ bound t := by
  -- `fderiv ℝ b` is continuous because `b` is `C³`.
  have hfd : Continuous (fderiv ℝ b) := hb.continuous_fderiv (by norm_num)
  have hcomp : Continuous (fun p : ℝ × E => p.1 • p.2) := continuous_fst.smul continuous_snd
  -- the `fderiv ℝ b (t • x)` factor applied to `x` is continuous in `(t, x)`
  have hder : Continuous (fun p : ℝ × E => (fderiv ℝ b (p.1 • p.2)) p.2) :=
    (hfd.comp hcomp).clm_apply continuous_snd
  -- the argument of `B` is continuous in `(t, x)`
  have harg : Continuous (fun p : ℝ × E =>
      p.1 • (fderiv ℝ b (p.1 • p.2)) p.2 + b (p.1 • p.2)) :=
    (continuous_fst.smul hder).add (hb.continuous.comp hcomp)
  -- hence so is the whole integrand
  have hcont : Continuous (fun p : ℝ × E =>
      B (p.1 • (fderiv ℝ b (p.1 • p.2)) p.2 + b (p.1 • p.2))) :=
    B.continuous.comp harg
  -- it is bounded on the compact product `[0,1] × closedBall y₀ 1`
  have hK : IsCompact (Set.Icc (0:ℝ) 1 ×ˢ Metric.closedBall y₀ 1) :=
    isCompact_Icc.prod (isCompact_closedBall y₀ 1)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨fun _ => C, intervalIntegrable_const, ?_⟩
  intro t ht x hx
  have ht' : t ∈ Set.Icc (0:ℝ) 1 := by
    have : t ∈ Set.Ioc (0:ℝ) 1 := by
      simpa [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] using ht
    exact Set.Ioc_subset_Icc_self this
  exact hC (t, x) (Set.mem_prod.mpr ⟨ht', hx⟩)

end Work.RPCore.GenFun

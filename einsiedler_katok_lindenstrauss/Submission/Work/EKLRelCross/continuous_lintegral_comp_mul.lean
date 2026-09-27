import Mathlib
import Submission.Work.EKLRelCross.exists_compact_nhds_comp_mul_support

set_option linter.style.haveILetI false

namespace Work.EKLRelCross

open MeasureTheory Topology Filter
open scoped ENNReal

/-- **Continuity of a left translate of a compactly supported `ℝ≥0∞`-valued function under the
`lintegral`.**  If `σ` is a measure finite on compact sets on a second countable locally compact
topological group `G` and `F : G → ℝ≥0∞` is continuous, bounded by `1` and compactly supported,
then `w ↦ ∫⁻ x, F (w * x) ∂σ` is continuous. -/
theorem continuous_lintegral_comp_mul {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G]
    [SecondCountableTopology G]
    (σ : MeasureTheory.Measure G) (hσ : MeasureTheory.IsFiniteMeasureOnCompacts σ)
    (F : G → ENNReal) (hF : Continuous F) (hF1 : ∀ x, F x ≤ 1) (hFs : HasCompactSupport F) :
    Continuous (fun w : G => ∫⁻ x, F (w * x) ∂σ) := by
  classical
  haveI : IsFiniteMeasureOnCompacts σ := hσ
  rw [continuous_iff_continuousAt]
  intro w₀
  -- A compact set `B` containing the support of `w ↦ F (w * x)` for all `w` near `w₀`.
  obtain ⟨B, U, hBcomp, hU, hBU⟩ := exists_compact_nhds_comp_mul_support F hFs w₀
  -- Dominated convergence along the neighbourhood filter of `w₀`.
  refine MeasureTheory.tendsto_lintegral_filter_of_dominated_convergence
    (μ := σ) (l := 𝓝 w₀) (F := fun w x => F (w * x)) (f := fun x => F (w₀ * x))
    (B.indicator (1 : G → ENNReal)) ?_ ?_ ?_ ?_
  · -- Measurability of the integrands.
    filter_upwards with w
    exact (hF.comp (continuous_const.mul continuous_id)).measurable
  · -- Domination by the indicator of `B` for `w` near `w₀`.
    filter_upwards [hU] with w hw
    refine Filter.Eventually.of_forall (fun x => ?_)
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx]
      exact hF1 (w * x)
    · rw [Set.indicator_of_notMem hx]
      exact le_of_eq (by_contra fun h => hx (hBU w hw x h))
  · -- The dominating function has finite integral.
    exact ne_of_lt (lt_of_le_of_lt (lintegral_indicator_one_le B)
      (IsFiniteMeasureOnCompacts.lt_top_of_isCompact hBcomp))
  · -- Pointwise (indeed everywhere) convergence of the integrands.
    refine Filter.Eventually.of_forall (fun x => ?_)
    have hcont : Continuous (fun w : G => F (w * x)) :=
      hF.comp (continuous_id.mul continuous_const)
    exact hcont.continuousAt

end Work.EKLRelCross

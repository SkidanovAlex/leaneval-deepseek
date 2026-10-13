/-
# The `L₁₂` zero-mode identity: measure-theoretic helpers for the assembly

Two elementary limit facts for `L¹`-functions on `(0,∞)`:
`∫_{(0,ε]} g → 0` as `ε → 0⁺`, and `∫_{(ε,ρ]} g → ∫_{(ε,∞)} g` as `ρ → ∞`.
Both are proved by dominated convergence on the indicator functions, which avoids any
measurability hypothesis on `g` beyond integrability on `(0,∞)`.
-/
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Submission.Work.FTS.Apriori.ZeroMode.L12_ZMDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Apriori.ZeroMode

set_option autoImplicit false

/-- The indicator of a measurable set of an `L¹`-function is integrable. -/
theorem zm_integrable_indicator {g : ℝ → ℝ} {s : Set ℝ} (hs : MeasurableSet s)
    (hg : IntegrableOn g s) : Integrable (s.indicator g) :=
  (integrable_indicator_iff hs).mpr hg

/-- The set integrals of an `L¹`-function over `(0,ε]` tend to `0` as `ε → 0⁺`. -/
theorem zm_tendsto_Ioc_zero {g : ℝ → ℝ} (hg : IntegrableOn g (Set.Ioi 0)) :
    Tendsto (fun ε : ℝ => ∫ r in Set.Ioc (0:ℝ) ε, g r) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hgi : Integrable ((Set.Ioi (0:ℝ)).indicator g) :=
    zm_integrable_indicator measurableSet_Ioi hg
  have hfam : ∀ ε : ℝ, (∫ r in Set.Ioc (0:ℝ) ε, g r)
      = ∫ r : ℝ, (Set.Ioc (0:ℝ) ε).indicator g r :=
    fun ε => (integral_indicator measurableSet_Ioc).symm
  have hgoal : Tendsto (fun ε : ℝ => ∫ r : ℝ, (Set.Ioc (0:ℝ) ε).indicator g r)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have h := tendsto_integral_filter_of_dominated_convergence
      (μ := volume) (l := 𝓝[>] (0:ℝ))
      (F := fun ε : ℝ => fun r : ℝ => (Set.Ioc (0:ℝ) ε).indicator g r)
      (f := fun _ : ℝ => (0:ℝ))
      (fun a => ‖(Set.Ioi (0:ℝ)).indicator g a‖) ?_ ?_ hgi.norm ?_
    · simpa using h
    · filter_upwards with ε
      refine AEStronglyMeasurable.congr
        (show AEStronglyMeasurable ((Set.Ioc (0:ℝ) ε).indicator ((Set.Ioi (0:ℝ)).indicator g)) volume from
          AEStronglyMeasurable.indicator hgi.aestronglyMeasurable measurableSet_Ioc) ?_
      filter_upwards with r
      by_cases hr : r ∈ Set.Ioc (0:ℝ) ε
      · rw [Set.indicator_of_mem hr, Set.indicator_of_mem hr,
          Set.indicator_of_mem (show r ∈ Set.Ioi (0:ℝ) from hr.1)]
      · rw [Set.indicator_of_notMem hr, Set.indicator_of_notMem hr]
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      filter_upwards with r
      by_cases hr : r ∈ Set.Ioc (0:ℝ) ε
      · rw [Set.indicator_of_mem hr,
          Set.indicator_of_mem (show r ∈ Set.Ioi (0:ℝ) from hr.1)]
      · rw [Set.indicator_of_notMem hr]
        simp
    · filter_upwards with r
      by_cases hr : 0 < r
      · refine tendsto_const_nhds.congr' ?_
        filter_upwards [Ioo_mem_nhdsGT hr] with ε hε
        rw [Set.indicator_of_notMem]
        exact fun h => absurd h.2 (not_le.mpr hε.2)
      · refine tendsto_const_nhds.congr' ?_
        filter_upwards with ε
        rw [Set.indicator_of_notMem]
        exact fun h => absurd h.1 (not_lt.mpr (not_lt.mp hr))
  exact hgoal.congr' (Filter.Eventually.of_forall fun ε => (hfam ε).symm)

/-- The set integrals of an `L¹`-function over `(ε,ρ]` tend to the integral over `(ε,∞)`,
as `ρ → ∞`. -/
theorem zm_tendsto_Ioc_atTop {g : ℝ → ℝ} {ε : ℝ} (hg : IntegrableOn g (Set.Ioi ε)) :
    Tendsto (fun ρ : ℝ => ∫ r in Set.Ioc ε ρ, g r) atTop
      (𝓝 (∫ r in Set.Ioi ε, g r)) := by
  have hgi : Integrable ((Set.Ioi ε).indicator g) := zm_integrable_indicator measurableSet_Ioi hg
  have hfam : ∀ ρ : ℝ, (∫ r in Set.Ioc ε ρ, g r)
      = ∫ r : ℝ, (Set.Ioc ε ρ).indicator g r :=
    fun ρ => (integral_indicator measurableSet_Ioc).symm
  have hgoal : Tendsto (fun ρ : ℝ => ∫ r : ℝ, (Set.Ioc ε ρ).indicator g r) atTop
      (𝓝 (∫ r in Set.Ioi ε, g r)) := by
    have hpt : (∫ r in Set.Ioi ε, g r) = ∫ r : ℝ, (Set.Ioi ε).indicator g r :=
      (integral_indicator measurableSet_Ioi).symm
    rw [hpt]
    refine tendsto_integral_filter_of_dominated_convergence
      (μ := volume) (l := atTop)
      (F := fun ρ : ℝ => fun r : ℝ => (Set.Ioc ε ρ).indicator g r)
      (f := fun r : ℝ => (Set.Ioi ε).indicator g r)
      (fun a => ‖(Set.Ioi ε).indicator g a‖) ?_ ?_ hgi.norm ?_
    · filter_upwards with ρ
      refine AEStronglyMeasurable.congr
        (show AEStronglyMeasurable ((Set.Ioc ε ρ).indicator ((Set.Ioi ε).indicator g)) volume from
          AEStronglyMeasurable.indicator hgi.aestronglyMeasurable measurableSet_Ioc) ?_
      filter_upwards with r
      by_cases hr : r ∈ Set.Ioc ε ρ
      · rw [Set.indicator_of_mem hr, Set.indicator_of_mem hr,
          Set.indicator_of_mem (show r ∈ Set.Ioi ε from hr.1)]
      · rw [Set.indicator_of_notMem hr, Set.indicator_of_notMem hr]
    · filter_upwards [Ioi_mem_atTop ε] with ρ hρ
      filter_upwards with r
      by_cases hr : r ∈ Set.Ioc ε ρ
      · rw [Set.indicator_of_mem hr,
          Set.indicator_of_mem (show r ∈ Set.Ioi ε from hr.1)]
      · rw [Set.indicator_of_notMem hr]
        simp
    · filter_upwards with r
      by_cases hr : ε < r
      · refine Tendsto.congr' ?_ tendsto_const_nhds
        filter_upwards [Ioi_mem_atTop r] with ρ hρ
        rw [Set.indicator_of_mem (show r ∈ Set.Ioi ε from hr),
          Set.indicator_of_mem (show r ∈ Set.Ioc ε ρ from ⟨hr, le_of_lt hρ⟩)]
      · refine Tendsto.congr' ?_ tendsto_const_nhds
        filter_upwards with ρ
        rw [Set.indicator_of_notMem
            (show r ∉ Set.Ioi ε from fun h => absurd h (not_lt.mpr (not_lt.mp hr))),
          Set.indicator_of_notMem
            (show r ∉ Set.Ioc ε ρ from fun h => absurd h.1 (not_lt.mpr (not_lt.mp hr)))]
  exact hgoal.congr' (Filter.Eventually.of_forall fun ρ => (hfam ρ).symm)

end Work.FTS.Apriori.ZeroMode

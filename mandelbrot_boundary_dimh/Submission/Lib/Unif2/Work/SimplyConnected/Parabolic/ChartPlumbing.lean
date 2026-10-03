import Mathlib
import Submission.Lib.Unif2.Work.SimplyConnected.Parabolic.Defs
import Submission.Lib.Unif2.Holomorphic
import Submission.Lib.Unif2.Commons.Analysis.Complex.Analytic.deriv_ne_zero_of_injOn

/-!
# Chart bookkeeping for holomorphic functions on a Riemann surface

The elementary transfers used to run planar arguments in a chart of a complex one-manifold:
a chart ball contained in an open set, the analyticity and injectivity of the chart
representation `ψ ∘ chart.symm` on such a ball, and the non-vanishing of its derivative.

All statements are phrased with an arbitrary centre `a` of the ball (in the coordinates of the
chart), so that they can be used both at the preferred chart's own point and at a nearby point.
-/

namespace Work.SimplyConnected.Parabolic

open scoped Topology Manifold ContDiff
open Filter Metric Set

set_option maxHeartbeats 800000

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **Chart balls inside an open set.**  Every point of an open set `U` has a chart ball around it
whose `chart.symm`-image lies in `U`, and which lies in the chart's target (so that `chart.symm` is
the honest inverse there). -/
theorem exists_chart_ball_subset {U : Set X} (hU : IsOpen U) {z : X} (hz : z ∈ U) :
    ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball ((chartAt ℂ z) z) ρ ⊆ (chartAt ℂ z).target ∧
      (chartAt ℂ z).symm '' Metric.ball ((chartAt ℂ z) z) ρ ⊆ U := by
  have hsrc : z ∈ (chartAt ℂ z).source := mem_chart_source ℂ z
  have hmem : (chartAt ℂ z) z ∈ (chartAt ℂ z).target := (chartAt ℂ z).map_source hsrc
  obtain ⟨ρ₁, hρ₁, hρ₁tgt⟩ := Metric.mem_nhds_iff.mp ((chartAt ℂ z).open_target.mem_nhds hmem)
  have hz' : (chartAt ℂ z).symm ((chartAt ℂ z) z) ∈ U := by
    rw [(chartAt ℂ z).left_inv hsrc]; exact hz
  obtain ⟨ρ₂, hρ₂, hρ₂U⟩ := Metric.mem_nhds_iff.mp
    (((chartAt ℂ z).continuousAt_symm hmem).preimage_mem_nhds (hU.mem_nhds hz'))
  exact ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂,
    fun w hw => hρ₁tgt (Metric.ball_subset_ball (min_le_left _ _) hw),
    fun w hw => by
      obtain ⟨u, hu, rfl⟩ := hw
      exact hρ₂U (Metric.ball_subset_ball (min_le_right _ _) hu)⟩

/-- On a chart ball (of the chart at `z`) all of whose points lie in `U ∩ (chartAt ℂ z).source`,
with `U ⊆ Ω`, the chart representation of a function holomorphic on `Ω` is analytic. -/
theorem analyticAt_comp_chartAt_symm {Ω U : Set X} {ψ : X → ℂ}
    (hψ : ∀ x ∈ Ω, Submission.HolomorphicOnXAt ψ x) (hUΩ : U ⊆ Ω)
    {z : X} {a : ℂ} {ρ : ℝ}
    (hsub : (chartAt ℂ z).symm '' Metric.ball a ρ ⊆ U ∩ (chartAt ℂ z).source)
    (htgt : Metric.ball a ρ ⊆ (chartAt ℂ z).target) :
    ∀ w ∈ Metric.ball a ρ, AnalyticAt ℂ (ψ ∘ (chartAt ℂ z).symm) w := by
  intro w hw
  have hw' : (chartAt ℂ z).symm w ∈ Ω ∩ (chartAt ℂ z).source :=
    ⟨hUΩ (hsub ⟨w, hw, rfl⟩).1, (hsub ⟨w, hw, rfl⟩).2⟩
  have h := (Submission.HolomorphicOnXAt_iff_chart (X := X) (f := ψ)
    (x := (chartAt ℂ z).symm w) (y := z) hw'.2).mp (hψ _ hw'.1)
  rwa [(chartAt ℂ z).right_inv (htgt hw)] at h

/-- The chart representation of an injective function is injective on a chart ball inside `Ω`. -/
theorem injOn_comp_chartAt_symm {Ω U : Set X} {ψ : X → ℂ} (hinj : Set.InjOn ψ Ω) (hUΩ : U ⊆ Ω)
    {z : X} {a : ℂ} {ρ : ℝ}
    (hsub : (chartAt ℂ z).symm '' Metric.ball a ρ ⊆ U ∩ (chartAt ℂ z).source)
    (htgt : Metric.ball a ρ ⊆ (chartAt ℂ z).target) :
    Set.InjOn (ψ ∘ (chartAt ℂ z).symm) (Metric.ball a ρ) := by
  intro w₁ hw₁ w₂ hw₂ heq
  have h1 := hsub ⟨w₁, hw₁, rfl⟩
  have h2 := hsub ⟨w₂, hw₂, rfl⟩
  have h3 : (chartAt ℂ z).symm w₁ = (chartAt ℂ z).symm w₂ :=
    hinj (hUΩ h1.1) (hUΩ h2.1) heq
  calc w₁ = (chartAt ℂ z) ((chartAt ℂ z).symm w₁) := ((chartAt ℂ z).right_inv (htgt hw₁)).symm
    _ = (chartAt ℂ z) ((chartAt ℂ z).symm w₂) := by rw [h3]
    _ = w₂ := (chartAt ℂ z).right_inv (htgt hw₂)

/-- The derivative of a chart representation is non-zero where it is injective. -/
theorem deriv_comp_chartAt_symm_ne_zero {ψ : X → ℂ} {z y : X} {ρ : ℝ} (hρ : 0 < ρ)
    (han : ∀ w ∈ Metric.ball ((chartAt ℂ z) y) ρ, AnalyticAt ℂ (ψ ∘ (chartAt ℂ z).symm) w)
    (hinj : Set.InjOn (ψ ∘ (chartAt ℂ z).symm) (Metric.ball ((chartAt ℂ z) y) ρ)) :
    deriv (ψ ∘ (chartAt ℂ z).symm) ((chartAt ℂ z) y) ≠ 0 :=
  Commons.Analysis.Complex.Analytic.deriv_ne_zero_of_injOn hρ
    (han _ (Metric.mem_ball_self hρ)) hinj

end Work.SimplyConnected.Parabolic

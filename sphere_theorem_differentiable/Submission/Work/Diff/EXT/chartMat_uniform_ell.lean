import Mathlib
import Submission.Work.Diff.EXT.splice_defs
import Submission.Work.Diff.EXT.LocalExtDefs
import Submission.Work.Diff.EXT.sum_chartMatFun_eq_inner
import Submission.Work.Diff.EXT.uniform_posDef_of_continuous_v2
import Submission.Work.Diff.EXT.continuousAt_chartMatFun_centre
import Submission.Work.Diff.EXT.chartMatFun_centre_posDef_tfree

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT

/-- **Uniform positive definiteness of the chart matrix of a fixed smooth metric, near the chart
centre.**  The three inputs are the continuity of the entries at the centre
(`Work.Diff.EXT.continuousAt_chartMatFun_centre`), the positive definiteness at the centre
(`Work.Diff.EXT.chartMatFun_centre_posDef_tfree`) and the purely finite-dimensional
`Work.Diff.EXT.uniform_posDef_of_continuous_v2`; all three are proved without `T2Space M` and
without `I.Boundaryless`, which is what working with the explicit metric family `G : ℝ → SMet I M`
requires. -/
theorem chartMatFun_posDef_nhds
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (g : Submission.Diff.SMet I M) (x₀ : M) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ U : Set E, IsOpen U ∧ (extChartAt I x₀) x₀ ∈ U ∧
      ∀ y ∈ U, ∀ v : Fin (Module.finrank ℝ E) → ℝ,
        δ * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j, v i * v j * chartMatFun g x₀ y i j :=
  uniform_posDef_of_continuous_v2 (X := E) (n := Module.finrank ℝ E)
    (fun y : E => chartMatFun g x₀ y) (y₀ := (extChartAt I x₀) x₀)
    (fun i j => continuousAt_chartMatFun_centre g x₀ i j)
    (fun v hv => chartMatFun_centre_posDef_tfree g x₀ v hv)

/-- **The chart matrix is uniformly positive definite, on a bounded chart neighbourhood, uniformly
on the slab.**  Under the a priori chart bounds `ChartBounds G (T/2) T` and the two-sided lower
bound `a • (G 0).inner ≤ (G t).inner` on `[T/2,T)`, every chart centre `x₀` has a bounded open
neighbourhood `U` of `(extChartAt I x₀) x₀` on which the chart matrices `chartMat G x₀ t y` keep
their spatial `C^k` bounds and are uniformly positive definite, i.e.
`ε * ∑ vᵢ² ≤ ∑ vᵢ vⱼ (chartMat G x₀ t y)ᵢⱼ` for all `t ∈ [T/2,T)` and `y ∈ U`.

Availability: `Submission.ChartBounds.exists_chartGram_bounds` gives, for the instance metric
`⟨(G 0).toRiemannianMetric⟩`, a compact subset `K` of the chart and constants `0 < λ ≤ Λ` with
`λ‖a‖² ≤ chartGram x₀ p a a ≤ Λ‖a‖²` for `p ∈ K`; `Submission.Geodesic.frameVector_sum` /
`frameVector_smul` turn the quadratic form of the chart matrix into `chartGram` of the combination
`∑ vᵢ bBᵢ`, and a basis comparison (`‖∑ vᵢ bBᵢ‖ ≥ c ‖v‖` for some `c > 0`) finishes. -/
theorem chartMat_uniform_ell
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (G : ℝ → Submission.Diff.SMet I M) (T : ℝ) (hT : 0 < T)
    (hflow : Submission.Diff.IsRicciFlow G T)
    (hb : Work.Diff.EXT.ChartBounds G (T / 2) T)
    (hnd : ∃ a : ℝ, 0 < a ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ (x : M) (u : TangentSpace I x),
        a * (G 0).inner x u u ≤ (G t).inner x u u) :
    ∀ x₀ : M, ∃ U : Set E, IsOpen U ∧ (extChartAt I x₀) x₀ ∈ U ∧ Bornology.IsBounded U ∧
      (∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ y ∈ U,
        ‖iteratedFDeriv ℝ k (fun y' : E ↦ Work.Diff.EXT.chartMat G x₀ t y') y‖ ≤ C) ∧
      (∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ y ∈ U,
        ∀ v : Fin (Module.finrank ℝ E) → ℝ,
        ε * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j, v i * v j * Work.Diff.EXT.chartMat G x₀ t y i j) := by
  intro x₀
  obtain ⟨a, ha_pos, ha_le⟩ := hnd
  obtain ⟨Ucb, hUcb_open, hUcb_mem, hUcb_bnd⟩ := hb x₀
  obtain ⟨δ, hδ_pos, V, hV_open, hV_mem, hV_pos⟩ := chartMatFun_posDef_nhds (G 0) x₀
  refine ⟨Ucb ∩ V ∩ Metric.ball ((extChartAt I x₀) x₀) 1, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hUcb_open.inter hV_open).inter Metric.isOpen_ball
  · exact ⟨⟨hUcb_mem, hV_mem⟩, by rw [Metric.mem_ball]; simp⟩
  · exact (Metric.isBounded_ball (x := (extChartAt I x₀) x₀) (r := 1)).subset
      (fun y hy => hy.2)
  · intro k
    obtain ⟨C, hC0, hC⟩ := hUcb_bnd k
    exact ⟨C, hC0, fun t ht y hy => hC t ht y hy.1.1⟩
  · refine ⟨a * δ, mul_pos ha_pos hδ_pos, fun t ht y hy v => ?_⟩
    have hyV : y ∈ V := hy.1.2
    have hpos0 : δ * ∑ i, (v i) ^ 2
        ≤ ∑ i, ∑ j, v i * v j * chartMat G x₀ 0 y i j := by
      change δ * ∑ i, (v i) ^ 2
        ≤ ∑ i, ∑ j, v i * v j * chartMatFun (G 0) x₀ y i j
      exact hV_pos y hyV v
    let w : TangentSpace I ((extChartAt I x₀).symm y) :=
      ∑ i, v i • Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y) (bB i)
    have h1 : (∑ i, ∑ j, v i * v j * chartMat G x₀ t y i j)
        = (G t).inner ((extChartAt I x₀).symm y) w w := by
      rw [show (∑ i, ∑ j, v i * v j * chartMat G x₀ t y i j)
            = (∑ i, ∑ j, v i * v j * chartMatFun (G t) x₀ y i j) from rfl]
      rw [sum_chartMatFun_eq_inner (G t) x₀ y v]
    have h0 : (∑ i, ∑ j, v i * v j * chartMat G x₀ 0 y i j)
        = (G 0).inner ((extChartAt I x₀).symm y) w w := by
      rw [show (∑ i, ∑ j, v i * v j * chartMat G x₀ 0 y i j)
            = (∑ i, ∑ j, v i * v j * chartMatFun (G 0) x₀ y i j) from rfl]
      rw [sum_chartMatFun_eq_inner (G 0) x₀ y v]
    calc (a * δ) * ∑ i, (v i) ^ 2
        = a * (δ * ∑ i, (v i) ^ 2) := by ring
      _ ≤ a * (∑ i, ∑ j, v i * v j * chartMat G x₀ 0 y i j) :=
            mul_le_mul_of_nonneg_left hpos0 (le_of_lt ha_pos)
      _ = a * (G 0).inner ((extChartAt I x₀).symm y) w w := by rw [h0]
      _ ≤ (G t).inner ((extChartAt I x₀).symm y) w w :=
            ha_le t ht ((extChartAt I x₀).symm y) w
      _ = ∑ i, ∑ j, v i * v j * chartMat G x₀ t y i j := h1.symm

end Work.Diff.EXT

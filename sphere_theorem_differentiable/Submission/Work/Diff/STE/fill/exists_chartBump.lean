import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.fill

theorem exists_chartBump
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless]
    (x₀ : M) {σ : ℝ} (hσ : 0 < σ) (hσ4 : 2 * σ ≤ 1 / 4)
    (htarget : ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ 2 * σ →
      (Module.finBasis ℝ E).equivFun.symm
        ((Module.finBasis ℝ E).equivFun ((extChartAt I x₀) x₀) + z)
        ∈ (extChartAt I x₀).target) :
    ∃ χ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) χ ∧
      (∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ σ → χ z = 1) ∧
      (∀ z ∈ tsupport χ, (Module.finBasis ℝ E).equivFun.symm
        ((Module.finBasis ℝ E).equivFun ((extChartAt I x₀) x₀) + z)
        ∈ (extChartAt I x₀).target) ∧
      Function.support χ ⊆ Set.pi Set.univ (fun _ : Fin (Module.finrank ℝ E) =>
        Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) := by
  classical
  -- The bump function is the standard `ContDiffBump` at `0` with inner radius `σ` and outer
  -- radius `2σ`.  Its support is the open ball of radius `2σ` and its topological support the
  -- closed ball of radius `2σ`; since `2σ ≤ 1/4` everything it carries lies in the cube
  -- `(-1/2, 1/2)^n`, and `htarget` applies on the closed ball of radius `2σ`.
  let φ : ContDiffBump (0 : Fin (Module.finrank ℝ E) → ℝ) :=
    ⟨σ, 2 * σ, hσ, by linarith⟩
  have hrIn : φ.rIn = σ := rfl
  have hrOut : φ.rOut = 2 * σ := rfl
  refine ⟨⇑φ, ?_, ?_, ?_, ?_⟩
  · simpa using φ.contDiff (n := ⊤)
  · intro z hz
    apply φ.one_of_mem_closedBall
    rw [Metric.mem_closedBall, dist_zero_right, hrIn]
    exact hz
  · intro z hz
    apply htarget
    have hz' : z ∈ Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * σ) := by
      rw [← hrOut, ← φ.tsupport_eq]
      exact hz
    rwa [Metric.mem_closedBall, dist_zero_right] at hz'
  · intro z hz
    rw [Set.mem_pi]
    intro i _
    have hz' : z ∈ Metric.ball (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * σ) := by
      rw [← hrOut, ← φ.support_eq]
      exact hz
    rw [Metric.mem_ball, dist_zero_right] at hz'
    rw [Set.mem_Ioo]
    have h1 : |z i| ≤ ‖z‖ := norm_le_pi_norm z i
    have h2 : |z i| < 1 / 2 := by linarith
    exact abs_lt.mp h2

end Work.Diff.STE.fill

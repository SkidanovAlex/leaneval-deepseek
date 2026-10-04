/-
# Non-degeneracy of the chart matrix of the background metric just beyond the `2σ`-ball

`Work.Diff.STE.B3.Mf D g₀.inner j z` is the chart matrix of the background metric `g₀` in the
`g₀`-orthonormal frame `D.e j ·`, read at the point `D.pt j z` with flat coordinate `z`:

`Mf D g₀.inner j z a b = g₀.inner (pt j z) (e j a (pt j z)) (e j b (pt j z))`.

On the closed ball `‖z‖ ≤ 2 σ j` the frame is `g₀`-orthonormal by construction (`B3Data.heON`), so
`Mf` is the *identity* matrix there and its determinant is `1`.  The determinant is also continuous
at every `z` whose affine flat image lies in the chart target, because there `Mf` is the chart
matrix `D.matChart j g₀.inner a b` of the metric — which is smooth on the chart target
(`Work.Diff.STE.B3.matChart_metric_contDiffOn`) — composed with the affine `flatToE`.

Hence `{z | det (Mf z) ≠ 0}` is an open set containing the compact closed `2σ`-ball, and the usual
thickening argument produces a `δ > 0` with `det (Mf z) ≠ 0` for all `‖z‖ ≤ 2 σ j + δ`.

Note that no positivity/positive-definiteness input is needed: the non-degeneracy on the
`2σ`-ball is *exact* (the matrix is `1` there), and it is propagated outward by continuity alone.
-/
import Mathlib
import Submission.Work.Diff.STE.B3.TransportDefs
import Submission.Work.Diff.STE.B3.matChart_metric_contDiffOn

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3

open scoped Manifold ContDiff Bundle Topology BigOperators Matrix
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

theorem det_Mf_metric_ne_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z : Fin (Module.finrank ℝ E) → ℝ,
      ‖z‖ ≤ 2 * D.σ j + δ →
      (Matrix.of (Work.Diff.STE.B3.Mf (I := I) (M := M) D g₀.inner j z)).det ≠ 0 := by
  classical
  -- (1) On the closed `2σ`-ball the frame `e j ·` is `g₀`-orthonormal, so `Mf` is the identity
  -- matrix and its determinant is `1`.
  have hone : ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ 2 * D.σ j →
      (Matrix.of (Work.Diff.STE.B3.Mf (I := I) (M := M) D g₀.inner j z)).det = 1 := by
    intro z hz
    have hON := D.heON j z hz
    have hmat : Matrix.of (Work.Diff.STE.B3.Mf (I := I) (M := M) D g₀.inner j z) = 1 := by
      ext a b
      rw [Matrix.one_apply]
      simp only [Matrix.of_apply, Work.Diff.STE.B3.Mf, Work.Diff.STE.B3Data.mat,
        Work.Diff.STE.B3Data.pt]
      exact hON a b
    rw [hmat, Matrix.det_one]
  -- (2) `z ↦ det (Mf z)` is continuous at every `z` whose flat image lies in the chart target:
  -- there `Mf` is the smooth chart matrix of the metric composed with the affine `flatToE`.
  have hcont : ∀ z : Fin (Module.finrank ℝ E) → ℝ,
      Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target →
      ContinuousAt
        (fun z' => (Matrix.of (Work.Diff.STE.B3.Mf (I := I) (M := M) D g₀.inner j z')).det)
        z := by
    intro z hz
    have hentry : ∀ a b : Fin (Module.finrank ℝ E), ContinuousAt (fun z' => D.matChart j g₀.inner a b
        (Work.Diff.STE.flatToE (I := I) (D.x₀ j) z')) z := fun a b =>
      ((Work.Diff.STE.B3.matChart_metric_contDiffOn D j a b).continuousOn.continuousAt
        ((isOpen_extChartAt_target (I := I) (D.x₀ j)).mem_nhds hz)).comp
        ((Work.Diff.STE.B3.flatToE_contDiff (I := I) (D.x₀ j)).continuous.continuousAt)
    have hmat : ContinuousAt (fun z' => Matrix.of (fun a b => D.matChart j g₀.inner a b
        (Work.Diff.STE.flatToE (I := I) (D.x₀ j) z'))) z := by
      show ContinuousAt (fun z' : Fin (Module.finrank ℝ E) → ℝ => fun a b =>
        D.matChart j g₀.inner a b (Work.Diff.STE.flatToE (I := I) (D.x₀ j) z')) z
      rw [continuousAt_pi]
      intro a
      rw [continuousAt_pi]
      intro b
      exact hentry a b
    have hdet : Continuous
        (fun A : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ => A.det) :=
      Continuous.matrix_det continuous_id
    exact hdet.continuousAt.comp hmat
  -- (3) The determinant does not vanish on the compact closed `2σ`-ball.
  have hK : IsCompact (Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j)) :=
    isCompact_closedBall _ _
  have hKsub : Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j) ⊆
      {z | (Matrix.of (Work.Diff.STE.B3.Mf (I := I) (M := M) D g₀.inner j z)).det ≠ 0} := by
    intro z hz
    have hzn : ‖z‖ ≤ 2 * D.σ j := by
      rwa [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hz
    change (Matrix.of (Work.Diff.STE.B3.Mf (I := I) (M := M) D g₀.inner j z)).det ≠ 0
    rw [hone z hzn]
    exact one_ne_zero
  -- (4) The set where the determinant does not vanish is open (on the chart target) and contains
  -- the closed `2σ`-ball, hence contains a thickening of it.
  have hVopen : IsOpen (Work.Diff.STE.flatToE (I := I) (D.x₀ j) ⁻¹'
        (extChartAt I (D.x₀ j)).target ∩
      {z | (Matrix.of (Work.Diff.STE.B3.Mf (I := I) (M := M) D g₀.inner j z)).det ≠ 0}) := by
    rw [isOpen_iff_mem_nhds]
    rintro z ⟨hzU, hzF⟩
    exact Filter.inter_mem
      (((isOpen_extChartAt_target (I := I) (D.x₀ j)).preimage
        ((Work.Diff.STE.B3.flatToE_contDiff (I := I) (D.x₀ j)).continuous)).mem_nhds hzU)
      ((hcont z hzU).preimage_mem_nhds (isOpen_ne.mem_nhds hzF))
  have hKsubV : Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j) ⊆
      (Work.Diff.STE.flatToE (I := I) (D.x₀ j) ⁻¹' (extChartAt I (D.x₀ j)).target ∩
        {z | (Matrix.of (Work.Diff.STE.B3.Mf (I := I) (M := M) D g₀.inner j z)).det ≠ 0}) := by
    intro z hz
    have hzn : ‖z‖ ≤ 2 * D.σ j := by
      rwa [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hz
    exact ⟨D.htarget j z hzn, hKsub hz⟩
  obtain ⟨δ₁, hδ₁pos, hδ₁sub⟩ := hK.exists_thickening_subset_open hVopen hKsubV
  -- (5) Convert the thickening estimate into a radial one and halve `δ`.
  refine ⟨δ₁ / 2, by linarith, ?_⟩
  intro z hz
  by_cases hzs : ‖z‖ ≤ 2 * D.σ j
  · exact (hKsubV (by rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]; exact hzs)).2
  · rw [not_le] at hzs
    have hzpos : 0 < ‖z‖ := lt_trans (by linarith [D.hσ j]) hzs
    have hmem : z ∈ Metric.thickening δ₁
        (Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j)) := by
      rw [Metric.mem_thickening_iff]
      refine ⟨(2 * D.σ j / ‖z‖) • z, ?_, ?_⟩
      · rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs,
          abs_of_pos (div_pos (by linarith [D.hσ j]) hzpos)]
        exact le_of_eq (div_mul_cancel₀ (2 * D.σ j) hzpos.ne')
      · rw [dist_eq_norm]
        have h1 : z - (2 * D.σ j / ‖z‖) • z = (1 - 2 * D.σ j / ‖z‖) • z := by
          rw [sub_smul, one_smul]
        have h1pos : 0 < 1 - 2 * D.σ j / ‖z‖ := by
          rw [sub_pos, div_lt_one hzpos]; linarith [D.hσ j]
        rw [h1, norm_smul, Real.norm_eq_abs, abs_of_pos h1pos, sub_mul, one_mul,
          div_mul_cancel₀ _ hzpos.ne']
        linarith
    exact (hδ₁sub hmem).2

end Work.Diff.STE.B3

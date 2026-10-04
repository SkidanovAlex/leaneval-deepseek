import Mathlib
import Submission.Work.Diff.STE.B3.Data
import Submission.Work.Diff.STE.B3.TransportDefs
import Submission.Work.Diff.STE.B3.transport_Mf_second
import Submission.Work.Diff.STE.B3.transport_deTurck_general
import Submission.Work.Diff.EXT.local_ext_of_chart_bounds_v2

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3

open scoped Manifold ContDiff Bundle Topology BigOperators Matrix
open Bundle ContDiff Set Filter

set_option maxHeartbeats 1000000

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-- Elementary bound for the cross terms of a quadratic form: the double sum of `|ξ p| * |ξ q|`
is at most `n` times the sum of the squares. -/
private lemma tmw_sum_abs_le {n : ℕ} (ξ : Fin n → ℝ) :
    (∑ p, ∑ q, |ξ p| * |ξ q|) ≤ (n : ℝ) * ∑ i, (ξ i) ^ 2 := by
  have h1 : ∀ p q : Fin n, |ξ p| * |ξ q| ≤ ((ξ p) ^ 2 + (ξ q) ^ 2) / 2 := by
    intro p q
    have h2 : 0 ≤ (|ξ p| - |ξ q|) ^ 2 := sq_nonneg _
    rw [sub_sq, sq_abs, sq_abs] at h2
    linarith
  have hsum : (∑ p, ∑ q, ((ξ p) ^ 2 + (ξ q) ^ 2) / 2) = (n : ℝ) * ∑ i, (ξ i) ^ 2 := by
    conv_lhs => enter [2, i]; rw [← Finset.sum_div]
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.mul_sum]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← Finset.mul_sum]
    ring
  calc (∑ p, ∑ q, |ξ p| * |ξ q|) ≤ ∑ p, ∑ q, ((ξ p) ^ 2 + (ξ q) ^ 2) / 2 :=
        Finset.sum_le_sum (fun p _ => Finset.sum_le_sum (fun q _ => h1 p q))
    _ = (n : ℝ) * ∑ i, (ξ i) ^ 2 := hsum

/-- Membership in a closed ball of `Fin n → ℝ`, radially. -/
private lemma tmw_mem_closedBall_iff {n : ℕ} (r : ℝ) (z : Fin n → ℝ) :
    z ∈ Metric.closedBall (0 : Fin n → ℝ) r ↔ ‖z‖ ≤ r := by
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]

/-- **Continuity of the determinant of the frame matrix** at a point of the chart target, from the
local smoothness of the entries of the frame matrix and the Leibniz formula for the determinant. -/
private lemma tmw_det_continuousAt (D : B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    {z : Fin (Module.finrank ℝ E) → ℝ}
    (hzt : flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target) :
    ContinuousAt (fun y : Fin (Module.finrank ℝ E) → ℝ =>
      (Matrix.of (Ff (I := I) (M := M) D j y)).det) z :=
  (tmNom_det_ContDiffAt (X := fun y : Fin (Module.finrank ℝ E) → ℝ =>
      Matrix.of (Ff (I := I) (M := M) D j y))
    (fun p q => Ff_contDiffAt (I := I) (M := M) D j p q hzt)).continuousAt

/-- **The regularity window of a chart.**  On a ball strictly larger than the `2σ j`-ball, the flat
coordinate still lies in the chart target and the frame matrix is still invertible. -/
private lemma tmw_region (D : B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z : Fin (Module.finrank ℝ E) → ℝ,
      ‖z‖ ≤ 2 * D.σ j + δ →
      (flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target ∧
        (Matrix.of (Ff (I := I) (M := M) D j z)).det ≠ 0) := by
  classical
  have hK : IsCompact (Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j)) :=
    isCompact_closedBall _ _
  have hVopen : IsOpen (flatToE (I := I) (D.x₀ j) ⁻¹' (extChartAt I (D.x₀ j)).target ∩
      {z : Fin (Module.finrank ℝ E) → ℝ |
        (Matrix.of (Ff (I := I) (M := M) D j z)).det ≠ 0}) := by
    rw [isOpen_iff_mem_nhds]
    rintro z ⟨hzt, hzd⟩
    exact Filter.inter_mem
      ((isOpen_flatToE_preimage_target (I := I) (M := M) D j).mem_nhds hzt)
      ((tmw_det_continuousAt (I := I) (M := M) D j hzt).eventually_ne hzd)
  have hKsub : Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j) ⊆
      flatToE (I := I) (D.x₀ j) ⁻¹' (extChartAt I (D.x₀ j)).target ∩
      {z : Fin (Module.finrank ℝ E) → ℝ |
        (Matrix.of (Ff (I := I) (M := M) D j z)).det ≠ 0} := by
    intro z hz
    have hz' : ‖z‖ ≤ 2 * D.σ j := (tmw_mem_closedBall_iff (2 * D.σ j) z).mp hz
    exact ⟨D.htarget j z hz', det_Ff_ne_zero (I := I) (M := M) D j hz'⟩
  obtain ⟨δ₁, hδ₁pos, hδ₁sub⟩ := hK.exists_thickening_subset_open hVopen hKsub
  refine ⟨δ₁ / 2, by linarith, fun z hz => ?_⟩
  exact hδ₁sub (closedBall_add_subset_thickening (k := Module.finrank ℝ E)
    (by linarith [D.hσ j]) hδ₁pos
    ((tmw_mem_closedBall_iff (2 * D.σ j + δ₁ / 2) z).mpr hz))

theorem tmw_bgwin
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) :
    ∃ (δ m0 M0 : ℝ), 0 < δ ∧ 0 < m0 ∧ 0 < M0 ∧
      (∀ (j : ι₀) (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ 2 * D.σ j + δ →
        Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target ∧
          (Matrix.of (Work.Diff.STE.B3.Ff (I := I) (M := M) D j z)).det ≠ 0) ∧
      (∀ (j : ι₀) (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ 2 * D.σ j + δ →
        ∀ ξ : Fin (Module.finrank ℝ E) → ℝ,
        m0 * ∑ i, (ξ i) ^ 2
          ≤ ∑ a, ∑ b, Work.Diff.EXT.chartMatFun (I := I) g₀ (D.x₀ j)
              (Work.Diff.STE.flatToE (I := I) (D.x₀ j) z) a b * ξ a * ξ b) ∧
      (∀ (j : ι₀) (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ 2 * D.σ j + δ →
        ∀ ξ : Fin (Module.finrank ℝ E) → ℝ,
        (∑ a, ∑ b, Work.Diff.EXT.chartMatFun (I := I) g₀ (D.x₀ j)
              (Work.Diff.STE.flatToE (I := I) (D.x₀ j) z) a b * ξ a * ξ b)
          ≤ M0 * ∑ i, (ξ i) ^ 2) := by
  classical
  -- ## The per-chart window, with uniform two-sided bounds for the background chart matrix
  have hper : ∀ j : ι₀, ∃ (δj mj Mj : ℝ), 0 < δj ∧ 0 < mj ∧ 0 < Mj ∧
      (∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ 2 * D.σ j + δj →
        (Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target ∧
          (Matrix.of (Work.Diff.STE.B3.Ff (I := I) (M := M) D j z)).det ≠ 0)) ∧
      (∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ 2 * D.σ j + δj →
        ∀ ξ : Fin (Module.finrank ℝ E) → ℝ,
        mj * ∑ i, (ξ i) ^ 2
          ≤ ∑ a, ∑ b, Work.Diff.EXT.chartMatFun (I := I) g₀ (D.x₀ j)
              (Work.Diff.STE.flatToE (I := I) (D.x₀ j) z) a b * ξ a * ξ b) ∧
      (∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ 2 * D.σ j + δj →
        ∀ ξ : Fin (Module.finrank ℝ E) → ℝ,
        (∑ a, ∑ b, Work.Diff.EXT.chartMatFun (I := I) g₀ (D.x₀ j)
              (Work.Diff.STE.flatToE (I := I) (D.x₀ j) z) a b * ξ a * ξ b)
          ≤ Mj * ∑ i, (ξ i) ^ 2) := by
    intro j
    classical
    obtain ⟨δj, hδjpos, hregion⟩ := tmw_region (I := I) (M := M) D j
    let A : (Fin (Module.finrank ℝ E) → ℝ) →
        Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
      fun z p q => Work.Diff.EXT.chartMatFun (I := I) g₀ (D.x₀ j)
        (Work.Diff.STE.flatToE (I := I) (D.x₀ j) z) p q
    have hK₂ : IsCompact (Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ)
        (2 * D.σ j + δj)) := isCompact_closedBall _ _
    -- continuity of the entries of the chart matrix
    have hAcont : ∀ p q : Fin (Module.finrank ℝ E),
        ContinuousOn (fun z : Fin (Module.finrank ℝ E) → ℝ => A z p q)
          (Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j + δj)) := by
      intro p q z hz
      have hzf : Work.Diff.STE.flatToE (I := I) (D.x₀ j) z
          ∈ (extChartAt I (D.x₀ j)).target :=
        (hregion z ((tmw_mem_closedBall_iff (2 * D.σ j + δj) z).mp hz)).1
      have hcd : ContDiffAt ℝ ∞ (fun y : Fin (Module.finrank ℝ E) → ℝ =>
          Work.Diff.EXT.chartMatFun (I := I) g₀ (D.x₀ j)
            (Work.Diff.STE.flatToE (I := I) (D.x₀ j) y)) z :=
        (Work.Diff.EXT.contDiffAt_chartMatFun (I := I) (M := M) g₀ (D.x₀ j) hzf).fun_comp z
          ((Work.Diff.STE.contDiff_flatToE (I := I) (x₀ := D.x₀ j)).contDiffAt)
      exact (((contDiffAt_pi.mp (contDiffAt_pi.mp hcd p)) q).continuousAt).continuousWithinAt
    -- positive definiteness of the chart matrix, at every point of the enlarged ball
    have hpos : ∀ z ∈ Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j + δj),
        ∀ ξ : Fin (Module.finrank ℝ E) → ℝ, ξ ≠ 0 →
        0 < ∑ p, ∑ q, A z p q * ξ p * ξ q := by
      intro z hz ξ hξ
      have hzf : Work.Diff.STE.flatToE (I := I) (D.x₀ j) z
          ∈ (extChartAt I (D.x₀ j)).target :=
        (hregion z ((tmw_mem_closedBall_iff (2 * D.σ j + δj) z).mp hz)).1
      have h := Work.Diff.EXT.chartMatFun_posDef_target (I := I) (M := M) g₀ (D.x₀ j) hzf hξ
      have h2 : (∑ p, ∑ q, A z p q * ξ p * ξ q)
          = ∑ i, ∑ l, ξ i * ξ l * Work.Diff.EXT.chartMatFun (I := I) g₀ (D.x₀ j)
              (Work.Diff.STE.flatToE (I := I) (D.x₀ j) z) i l := by
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun l _ => ?_))
        have hAij : A z i l = Work.Diff.EXT.chartMatFun (I := I) g₀ (D.x₀ j)
            (Work.Diff.STE.flatToE (I := I) (D.x₀ j) z) i l := rfl
        rw [hAij]
        ring
      rw [h2]
      exact h
    -- compactness: uniform lower bound for the quadratic form, and bound on the entries
    obtain ⟨c, C, hcpos, hCnn, hlow, hCbound⟩ :=
      Work.Diff.STE.B3.quadForm_bounds
        (Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j + δj)) hK₂ A hAcont hpos
    -- the upper bound for the quadratic form, from the bound on the entries
    have hup : ∀ z ∈ Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j + δj),
        ∀ ξ : Fin (Module.finrank ℝ E) → ℝ,
        (∑ p, ∑ q, A z p q * ξ p * ξ q)
          ≤ (C * (Module.finrank ℝ E : ℝ)) * ∑ i, (ξ i) ^ 2 := by
      intro z hz ξ
      calc (∑ p, ∑ q, A z p q * ξ p * ξ q)
          ≤ ∑ p, ∑ q, |A z p q * ξ p * ξ q| :=
            Finset.sum_le_sum (fun p _ => Finset.sum_le_sum (fun q _ => le_abs_self _))
        _ = ∑ p, ∑ q, |A z p q| * |ξ p| * |ξ q| := by
            refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
            rw [abs_mul, abs_mul]
        _ ≤ ∑ p, ∑ q, C * (|ξ p| * |ξ q|) := by
            refine Finset.sum_le_sum (fun p _ => Finset.sum_le_sum (fun q _ => ?_))
            have h1 : |A z p q| ≤ C := hCbound z hz p q
            have h2 : 0 ≤ |ξ p| * |ξ q| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
            calc |A z p q| * |ξ p| * |ξ q| = |A z p q| * (|ξ p| * |ξ q|) := by ring
              _ ≤ C * (|ξ p| * |ξ q|) := mul_le_mul_of_nonneg_right h1 h2
        _ = C * (∑ p, ∑ q, |ξ p| * |ξ q|) := by
            simp only [Finset.mul_sum]
        _ ≤ C * ((Module.finrank ℝ E : ℝ) * ∑ i, (ξ i) ^ 2) :=
            mul_le_mul_of_nonneg_left (tmw_sum_abs_le ξ) hCnn
        _ = (C * (Module.finrank ℝ E : ℝ)) * ∑ i, (ξ i) ^ 2 := by ring
    refine ⟨δj, c, max (C * (Module.finrank ℝ E : ℝ)) 1, hδjpos, hcpos,
      lt_max_of_lt_right zero_lt_one, hregion, ?_, ?_⟩
    · intro z hz ξ
      exact hlow z ((tmw_mem_closedBall_iff (2 * D.σ j + δj) z).mpr hz) ξ
    · intro z hz ξ
      have h := hup z ((tmw_mem_closedBall_iff (2 * D.σ j + δj) z).mpr hz) ξ
      exact le_trans h (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Finset.sum_nonneg (fun i _ => sq_nonneg _)))
  choose δj mj Mj hprop using hper
  have hδj : ∀ j : ι₀, 0 < δj j := fun j => (hprop j).1
  have hmj : ∀ j : ι₀, 0 < mj j := fun j => (hprop j).2.1
  -- ## Combining the finitely many charts
  by_cases hne : Nonempty ι₀
  · haveI := hne
    obtain ⟨j₁, _, hminδ⟩ :=
      Finset.exists_max_image (Finset.univ : Finset ι₀) (fun j => - δj j) Finset.univ_nonempty
    obtain ⟨j₂, _, hminm⟩ :=
      Finset.exists_max_image (Finset.univ : Finset ι₀) (fun j => - mj j) Finset.univ_nonempty
    obtain ⟨j₃, _, hmaxM⟩ :=
      Finset.exists_max_image (Finset.univ : Finset ι₀) Mj Finset.univ_nonempty
    have hδle : ∀ j : ι₀, δj j₁ ≤ δj j := fun j => by
      have := hminδ j (Finset.mem_univ j); linarith
    have hmle : ∀ j : ι₀, mj j₂ ≤ mj j := fun j => by
      have := hminm j (Finset.mem_univ j); linarith
    have hMle : ∀ j : ι₀, Mj j ≤ Mj j₃ := fun j => hmaxM j (Finset.mem_univ j)
    refine ⟨δj j₁, mj j₂, max (Mj j₃) 1, hδj j₁, hmj j₂, lt_max_of_lt_right zero_lt_one,
      ?_, ?_, ?_⟩
    · intro j z hz
      obtain ⟨-, -, -, hreg, -, -⟩ := hprop j
      exact hreg z (by linarith [hδle j, hz])
    · intro j z hz ξ
      obtain ⟨-, -, -, -, hl, -⟩ := hprop j
      have h := hl z (by linarith [hδle j, hz]) ξ
      have h2 : mj j₂ * ∑ i, (ξ i) ^ 2 ≤ mj j * ∑ i, (ξ i) ^ 2 :=
        mul_le_mul_of_nonneg_right (hmle j) (Finset.sum_nonneg (fun i _ => sq_nonneg _))
      linarith
    · intro j z hz ξ
      obtain ⟨-, -, -, -, -, hu⟩ := hprop j
      have h := hu z (by linarith [hδle j, hz]) ξ
      exact le_trans h (mul_le_mul_of_nonneg_right (le_trans (hMle j) (le_max_left _ _))
        (Finset.sum_nonneg (fun i _ => sq_nonneg _)))
  · refine ⟨1, 1, 1, one_pos, one_pos, one_pos, ?_, ?_, ?_⟩
    · intro j; exact (hne ⟨j⟩).elim
    · intro j; exact (hne ⟨j⟩).elim
    · intro j; exact (hne ⟨j⟩).elim

end Work.Diff.STE.B3

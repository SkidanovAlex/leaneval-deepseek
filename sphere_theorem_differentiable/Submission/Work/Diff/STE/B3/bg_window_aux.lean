import Mathlib
import Submission.Work.Diff.STE.B3.CoeffDefs
import Submission.Work.Diff.STE.Lead.Gal.gardADefs
import Submission.Work.Diff.STE.D.BasePos.smet_uniform_upper
import Submission.Work.Diff.EXT.ConnCov.gram_lower_of_hmet
import Submission.Work.Diff.EXT.basis_coeff_norm_equiv
import Submission.Work.Diff.EXT.chartMatFun_centre_posDef_tfree

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The uniform ellipticity window of the background metric `g₀` on the Layer B3 charts

For the Layer B3 data `D` (a finite chart atlas with radii `σ j ≤ 1/8`) this file produces the
window data used by the transport: a single `δ > 0` such that

* the whole flat ball of radius `2 σ j + δ` of every chart still maps into the chart target
  (`Work.Diff.STE.Lead.Gal.gardTargetDelta`),
* on that enlarged ball the chart matrix of the background metric `g₀` is uniformly elliptic:
  `mlo * |ξ|² ≤ ∑_{ab} (chartMatFun g₀ (x₀ j) (flatToE (x₀ j) z))_{ab} ξ_a ξ_b ≤ Mhi * |ξ|²`.

The quadratic bounds are the compactness statement for the (continuous, pointwise positive
definite) chart Gram matrix: `Work.Diff.EXT.ConnCov.gram_lower_of_compact_metric` gives the lower
bound `c ‖a‖² ≤ g₀(v_a, v_a)` on each compact flat ball, and
`Work.Diff.STE.D.BasePos.smet_uniform_upper` the upper bound `g₀(v_a,v_a) ≤ C ‖a‖²`.  Rewriting the
metric pairing of the frame vector of `a = ∑ᵢ ξᵢ bBᵢ` as the quadratic form of the chart matrix
(`Work.Diff.EXT.sum_chartMatFun_eq_inner`, `Work.Diff.EXT.frameVector_sum_tfree`) and comparing
`‖a‖²` with `∑ᵢ ξᵢ²` (`Work.Diff.EXT.basis_coeff_norm_equiv`) turns these into the stated bounds
with the uniform constants `mlo = min_j c_j / K₁` and `Mhi = max_j C_j · K₂`.
-/

noncomputable section

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.STE.B3

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-- **The quadratic form of the chart matrix of `g` is the metric of the combination.**  As
`Work.Diff.EXT.sum_chartMatFun_eq_inner`, but with the two summation factors commuted into the shape
used by the window bounds and with the frame vector of the *combination* `∑ᵢ ξᵢ • bBᵢ`. -/
lemma chartMatFun_qform_window
    (g : Submission.Diff.SMet I M) (x₀ : M) (y : E) (ξ : Fin (Module.finrank ℝ E) → ℝ) :
    (∑ a, ∑ b, Work.Diff.EXT.chartMatFun (I := I) g x₀ y a b * ξ a * ξ b)
      = g.inner ((extChartAt I x₀).symm y)
          (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y)
            (∑ i, ξ i • Work.Diff.EXT.bB (E := E) i))
          (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y)
            (∑ i, ξ i • Work.Diff.EXT.bB (E := E) i)) := by
  rw [Work.Diff.EXT.frameVector_sum_tfree (I := I) (s := Finset.univ) (x₀ := x₀)
    (p := (extChartAt I x₀).symm y) (c := ξ) (w := fun i => Work.Diff.EXT.bB (E := E) i)]
  rw [← Work.Diff.EXT.sum_chartMatFun_eq_inner (I := I) (M := M) g x₀ y ξ]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  ring

/-- The arithmetic step of the lower bound: if `S ≤ K₁ T`, `K₁ > 0` and `c ≥ 0`, then
`(c / K₁) * S ≤ c * T`. -/
lemma div_mul_le_of_le_mul {c K1 S T : ℝ} (hK : 0 < K1) (hc : 0 ≤ c) (h : S ≤ K1 * T) :
    c / K1 * S ≤ c * T := by
  rw [div_mul_eq_mul_div, div_le_iff₀ hK]
  calc c * S ≤ c * (K1 * T) := mul_le_mul_of_nonneg_left h hc
    _ = c * T * K1 := by ring

/-- The arithmetic step of the upper bound: if `T ≤ K₂ S` and `c ≥ 0`, then `c * T ≤ c * K₂ * S`. -/
lemma mul_le_mul_mul_of_le_mul {c K2 T S : ℝ} (hc : 0 ≤ c) (h : T ≤ K2 * S) :
    c * T ≤ c * K2 * S := by
  calc c * T ≤ c * (K2 * S) := mul_le_mul_of_nonneg_left h hc
    _ = c * K2 * S := by ring

theorem bg_window_aux
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) :
    ∃ (δ mlo Mhi : ℝ), 0 < δ ∧ 0 < mlo ∧ 0 < Mhi ∧
      (∀ (j : ι₀) (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ 2 * D.σ j + δ →
        Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target) ∧
      (∀ (j : ι₀) (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ 2 * D.σ j + δ →
        ∀ ξ : Fin (Module.finrank ℝ E) → ℝ,
        mlo * ∑ i, (ξ i) ^ 2
          ≤ ∑ a, ∑ b, Work.Diff.EXT.chartMatFun (I := I) g₀ (D.x₀ j)
              (Work.Diff.STE.flatToE (I := I) (D.x₀ j) z) a b * ξ a * ξ b) ∧
      (∀ (j : ι₀) (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ 2 * D.σ j + δ →
        ∀ ξ : Fin (Module.finrank ℝ E) → ℝ,
        (∑ a, ∑ b, Work.Diff.EXT.chartMatFun (I := I) g₀ (D.x₀ j)
              (Work.Diff.STE.flatToE (I := I) (D.x₀ j) z) a b * ξ a * ξ b)
          ≤ Mhi * ∑ i, (ξ i) ^ 2) := by
  classical
  -- the enlarged chart radius
  obtain ⟨δ, hδpos, hδt⟩ := Work.Diff.STE.Lead.Gal.gardTargetDelta (I := I) (M := M) D
  -- the coefficient norm constants of the canonical basis of the model space
  obtain ⟨K1, K2, hK1pos, hK2pos, hbb⟩ :=
    Work.Diff.EXT.basis_coeff_norm_equiv (E := E) (Work.Diff.EXT.bB (E := E))
  -- on each enlarged chart ball the chart matrix is uniformly elliptic
  have hper : ∀ j : ι₀, ∃ (mlo Mhi : ℝ), 0 < mlo ∧ 0 < Mhi ∧
      (∀ (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ 2 * D.σ j + δ →
        ∀ ξ : Fin (Module.finrank ℝ E) → ℝ,
        mlo * ∑ i, (ξ i) ^ 2
          ≤ ∑ a, ∑ b, Work.Diff.EXT.chartMatFun (I := I) g₀ (D.x₀ j)
              (Work.Diff.STE.flatToE (I := I) (D.x₀ j) z) a b * ξ a * ξ b) ∧
      (∀ (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ 2 * D.σ j + δ →
        ∀ ξ : Fin (Module.finrank ℝ E) → ℝ,
        (∑ a, ∑ b, Work.Diff.EXT.chartMatFun (I := I) g₀ (D.x₀ j)
              (Work.Diff.STE.flatToE (I := I) (D.x₀ j) z) a b * ξ a * ξ b)
          ≤ Mhi * ∑ i, (ξ i) ^ 2) := by
    intro j
    set K : Set E := Work.Diff.STE.flatToE (I := I) (D.x₀ j) ''
        Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j + δ) with hKdef
    have hKc : IsCompact K := by
      rw [hKdef]
      exact IsCompact.image (isCompact_closedBall _ _)
        (Work.Diff.STE.contDiff_flatToE (I := I) (D.x₀ j)).continuous
    have hKt : K ⊆ (extChartAt I (D.x₀ j)).target := by
      intro y hy
      rw [hKdef] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      exact hδt j z (by simpa only [Metric.mem_closedBall, dist_zero_right] using hz)
    obtain ⟨c, hcpos, hcb⟩ :=
      Work.Diff.EXT.ConnCov.gram_lower_of_compact_metric (I := I) (M := M) g₀ (D.x₀ j) K hKc hKt
    obtain ⟨C, hCpos, hCb⟩ :=
      Work.Diff.STE.D.BasePos.smet_uniform_upper (I := I) (M := M) g₀ (D.x₀ j) K hKc hKt
    refine ⟨c / K1, C * K2, div_pos hcpos hK1pos, mul_pos hCpos hK2pos, ?_, ?_⟩
    · intro z hz ξ
      have hzK : Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈ K := by
        rw [hKdef]
        exact ⟨z, by simpa only [Metric.mem_closedBall, dist_zero_right] using hz, rfl⟩
      rw [chartMatFun_qform_window (I := I) (M := M) g₀ (D.x₀ j)
        (Work.Diff.STE.flatToE (I := I) (D.x₀ j) z) ξ]
      exact le_trans (div_mul_le_of_le_mul hK1pos hcpos.le (hbb ξ).1)
        (hcb (Work.Diff.STE.flatToE (I := I) (D.x₀ j) z) hzK
          (∑ i, ξ i • Work.Diff.EXT.bB (E := E) i))
    · intro z hz ξ
      have hzK : Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈ K := by
        rw [hKdef]
        exact ⟨z, by simpa only [Metric.mem_closedBall, dist_zero_right] using hz, rfl⟩
      rw [chartMatFun_qform_window (I := I) (M := M) g₀ (D.x₀ j)
        (Work.Diff.STE.flatToE (I := I) (D.x₀ j) z) ξ]
      exact le_trans (hCb (Work.Diff.STE.flatToE (I := I) (D.x₀ j) z) hzK
          (∑ i, ξ i • Work.Diff.EXT.bB (E := E) i))
        (mul_le_mul_mul_of_le_mul hCpos.le (hbb ξ).2)
  by_cases hι : Nonempty ι₀
  · haveI := hι
    choose mlo Mhi hmlopos hMhipos hbound using hper
    refine ⟨δ, Finset.univ.inf' Finset.univ_nonempty mlo,
      Finset.univ.sup' Finset.univ_nonempty Mhi, hδpos, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Finset.lt_inf'_iff Finset.univ_nonempty]
      exact fun j _ => hmlopos j
    · rw [Finset.lt_sup'_iff]
      exact ⟨Classical.arbitrary ι₀, Finset.mem_univ _, hMhipos _⟩
    · intro j z hz
      exact hδt j z hz
    · intro j z hz ξ
      have hnn : 0 ≤ ∑ i, (ξ i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
      exact le_trans (mul_le_mul_of_nonneg_right
          (Finset.inf'_le (f := mlo) (b := j) (Finset.mem_univ j)) hnn)
        ((hbound j).1 z hz ξ)
    · intro j z hz ξ
      have hnn : 0 ≤ ∑ i, (ξ i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
      exact le_trans ((hbound j).2 z hz ξ)
        (mul_le_mul_of_nonneg_right (Finset.le_sup' (f := Mhi) (Finset.mem_univ j)) hnn)
  · refine ⟨δ, 1, 1, hδpos, one_pos, one_pos, ?_, ?_, ?_⟩
    · intro j
      exact absurd ⟨j⟩ hι
    · intro j
      exact absurd ⟨j⟩ hι
    · intro j
      exact absurd ⟨j⟩ hι

end Work.Diff.STE.B3

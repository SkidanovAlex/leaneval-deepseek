import Mathlib
import Submission.Work.Diff.STE.B3.CoeffDefs
import Submission.Work.Diff.STE.B3.tmA_props
import Submission.Work.Diff.EXT.contMDiffAt_matrix_inv

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The vocabulary of the uniform coefficient matrix `gardAuniform`

This module fixes the definitions used by the proof of
`Work.Diff.STE.Lead.Gal.gardAuniform` (the uniform-in-`h` elliptic coefficient matrix of the
transport).

* `gardBump δ ρ` is an explicit bump on the space of `n × n` matrices: it is `1` on the set
  `{det ≥ δ, |entries| ≤ ρ}` and vanishes outside `{det > δ/2, ∑ entries² < n²ρ² + 1}`.
* `gardClamp δ ρ M` is the *clamped inverse*: it is the honest inverse `M⁻¹` on
  `{det ≥ δ, |entries| ≤ ρ}` and interpolates to the identity matrix near the singular matrices,
  so that it is a globally `C^∞` function of the entries of `M` (even where `M` is singular).
* `gardTargetDelta` is the (uniform in `j`) enlargement of the `2σ j`-ball on which the chart at
  `x₀ j` is still genuine.
* `gardTmPer_core` identifies the periodisation `tmPer` with the function itself on a ball whose
  radius plus the support radius is `< 1`.
-/

noncomputable section

open scoped Matrix BigOperators Topology ContDiff
open Set

namespace Work.Diff.STE.Lead.Gal

/-- **The clamped-inverse bump** on the space of matrices: an explicit smooth function which is
`1` on the set `{det ≥ δ, |entries| ≤ ρ}`. -/
def gardBump {n : ℕ} (δ ρ : ℝ) (M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  Real.smoothTransition ((M.det - δ / 2) / (δ / 2)) *
    Real.smoothTransition (((n : ℝ) ^ 2 * ρ ^ 2 + 1) - ∑ i : Fin n, ∑ j : Fin n, (M i j) ^ 2)

/-- **The clamped inverse** of a matrix: the honest inverse on the set
`{det ≥ δ, |entries| ≤ ρ}`, interpolated with the identity matrix near the singular matrices so
that it is a globally smooth function of the entries. -/
def gardClamp {n : ℕ} (δ ρ : ℝ) (M : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  gardBump δ ρ M • M⁻¹ + (1 - gardBump δ ρ M) • 1

variable {n : ℕ} {δ ρ : ℝ}

/-- The bump is `1` on the elliptic window. -/
lemma gardBump_eq_one (hδ : 0 < δ) (hρ : 0 < ρ) {M : Matrix (Fin n) (Fin n) ℝ}
    (hdet : δ ≤ M.det) (hentry : ∀ i j, |M i j| ≤ ρ) : gardBump δ ρ M = 1 := by
  have hdet' : (1 : ℝ) ≤ (M.det - δ / 2) / (δ / 2) := by
    rw [le_div_iff₀ (by linarith)]; linarith
  have hq : ∑ i : Fin n, ∑ j : Fin n, (M i j) ^ 2 ≤ (n : ℝ) ^ 2 * ρ ^ 2 := by
    calc ∑ i : Fin n, ∑ j : Fin n, (M i j) ^ 2 ≤ ∑ i : Fin n, ∑ _j : Fin n, ρ ^ 2 := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hentry i j) 2
      _ = (n : ℝ) ^ 2 * ρ ^ 2 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  rw [gardBump, Real.smoothTransition.one_of_one_le hdet',
    Real.smoothTransition.one_of_one_le (by linarith), mul_one]

/-- The clamped inverse is the honest inverse on the elliptic window. -/
lemma gardClamp_eq_inv (hδ : 0 < δ) (hρ : 0 < ρ) {M : Matrix (Fin n) (Fin n) ℝ}
    (hdet : δ ≤ M.det) (hentry : ∀ i j, |M i j| ≤ ρ) : gardClamp δ ρ M = M⁻¹ := by
  rw [gardClamp, gardBump_eq_one hδ hρ hdet hentry, one_smul, sub_self, zero_smul, add_zero]

/-- The clamped inverse of a symmetric matrix is symmetric. -/
lemma gardClamp_transpose {n : ℕ} {δ ρ : ℝ} {M : Matrix (Fin n) (Fin n) ℝ} (hM : Mᵀ = M) :
    (gardClamp δ ρ M)ᵀ = gardClamp δ ρ M := by
  show (gardBump δ ρ M • M⁻¹ + (1 - gardBump δ ρ M) • 1)ᵀ
      = gardBump δ ρ M • M⁻¹ + (1 - gardBump δ ρ M) • 1
  rw [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_smul, Matrix.transpose_one,
    Matrix.transpose_nonsing_inv, hM]

/-- The clamped inverse is a globally smooth function of the entries of the matrix. -/
lemma gardClamp_contDiff_entry (hδ : 0 < δ) (hρ : 0 < ρ) (i j : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun A : Fin n → Fin n → ℝ => gardClamp δ ρ (Matrix.of A) i j) := by
  have hbump : ContDiff ℝ (⊤ : ℕ∞) (fun A : Fin n → Fin n → ℝ => gardBump δ ρ (Matrix.of A)) := by
    unfold gardBump
    refine ContDiff.mul ?_ ?_
    · exact Real.smoothTransition.contDiff.comp
        ((Work.Diff.EXT.contDiff_matrix_det_pi.sub contDiff_const).div_const _)
    · refine Real.smoothTransition.contDiff.comp ?_
      refine ContDiff.sub contDiff_const ?_
      exact ContDiff.sum fun a _ => ContDiff.sum fun b _ =>
        (contDiff_apply_apply ℝ ℝ a b).pow 2
  rw [contDiff_iff_contDiffAt]
  intro A
  rw [show (fun B : Fin n → Fin n → ℝ => gardClamp δ ρ (Matrix.of B) i j)
      = fun B => gardBump δ ρ (Matrix.of B) * (Matrix.of B)⁻¹ i j
        + (1 - gardBump δ ρ (Matrix.of B)) * (1 : Matrix (Fin n) (Fin n) ℝ) i j from by
    funext B; simp only [gardClamp, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]]
  by_cases hA : δ / 4 < (Matrix.of A).det
  · have hdetne : (Matrix.of A).det ≠ 0 := by linarith
    have hinv : ContDiffAt ℝ (⊤ : ℕ∞) (fun B : Fin n → Fin n → ℝ => (Matrix.of B)⁻¹ i j) A :=
      (contDiffAt_pi.mp ((contDiffAt_pi.mp
        (Work.Diff.EXT.contDiffAt_matrix_inv_pi A hdetne)) i)) j
    exact ((hbump.contDiffAt).mul hinv).add
      (((contDiffAt_const).sub hbump.contDiffAt).mul contDiffAt_const)
  · push_neg at hA
    have hvan : ∀ᶠ B in nhds A, gardBump δ ρ (Matrix.of B) = 0 := by
      have hcont : ContinuousAt (fun B : Fin n → Fin n → ℝ => (Matrix.of B).det) A :=
        Work.Diff.EXT.contDiff_matrix_det_pi.continuous.continuousAt
      have hlt : ∀ᶠ B in nhds A, (Matrix.of B).det < δ / 2 :=
        hcont.eventually_lt continuousAt_const (by linarith)
      filter_upwards [hlt] with B hB
      have h1 : Real.smoothTransition (((Matrix.of B).det - δ / 2) / (δ / 2)) = 0 :=
        Real.smoothTransition.zero_of_nonpos
          (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))
      rw [gardBump, h1, zero_mul]
    refine (contDiffAt_const (c := (1 : Matrix (Fin n) (Fin n) ℝ) i j)).congr_of_eventuallyEq ?_
    filter_upwards [hvan] with B hB
    rw [hB]; ring

/-- **The uniform chart enlargement.**  There is `δ > 0` such that for every chart index `j` the
whole closed ball of radius `2 σ j + δ` in the flat coordinate of chart `j` still maps into the
target of the chart at `x₀ j`. -/
theorem gardTargetDelta
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
      [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) :
    ∃ δt : ℝ, 0 < δt ∧
      ∀ (j : ι₀) (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ 2 * D.σ j + δt →
        Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target := by
  classical
  by_cases hι : Nonempty ι₀
  · haveI := hι
    -- for each `j`, the target-preimage of the closed `2σ j`-ball is a positive thickening
    have hmarg : ∀ j : ι₀, ∃ ε : ℝ, 0 < ε ∧ ∀ w, ‖w‖ ≤ 2 * D.σ j + ε →
        Work.Diff.STE.flatToE (I := I) (D.x₀ j) w ∈ (extChartAt I (D.x₀ j)).target := by
      intro j
      have hK : IsCompact (Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ)
          (2 * D.σ j)) := isCompact_closedBall _ _
      have hU : IsOpen {w : Fin (Module.finrank ℝ E) → ℝ |
          Work.Diff.STE.flatToE (I := I) (D.x₀ j) w ∈ (extChartAt I (D.x₀ j)).target} :=
        (isOpen_extChartAt_target (I := I) (D.x₀ j)).preimage
          (Work.Diff.STE.contDiff_flatToE (I := I) (D.x₀ j)).continuous
      have hKU : Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j) ⊆
          {w : Fin (Module.finrank ℝ E) → ℝ |
            Work.Diff.STE.flatToE (I := I) (D.x₀ j) w ∈ (extChartAt I (D.x₀ j)).target} :=
        fun w hw => D.htarget j w (by simpa only [Metric.mem_closedBall, dist_zero_right] using hw)
      obtain ⟨ε, hεpos, hε⟩ := hK.exists_cthickening_subset_open hU hKU
      refine ⟨ε, hεpos, fun w hw => hε ?_⟩
      by_cases hwle : ‖w‖ ≤ 2 * D.σ j
      · exact Metric.mem_cthickening_of_dist_le w w ε
          (Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j))
          (by rw [Metric.mem_closedBall, dist_zero_right]; exact hwle)
          (by rw [dist_self]; exact hεpos.le)
      · push_neg at hwle
        have ha : 0 < 2 * D.σ j := by linarith [D.hσ j]
        have hn : 0 < ‖w‖ := lt_trans ha hwle
        refine Metric.mem_cthickening_of_dist_le w ((2 * D.σ j / ‖w‖) • w) ε
          (Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j)) ?_ ?_
        · rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
            abs_of_pos (div_pos ha hn), div_mul_cancel₀ _ (ne_of_gt hn)]
        · rw [dist_eq_norm]
          have hnorm : ‖w - (2 * D.σ j / ‖w‖) • w‖ = |1 - 2 * D.σ j / ‖w‖| * ‖w‖ := by
            rw [show w - (2 * D.σ j / ‖w‖) • w = (1 - 2 * D.σ j / ‖w‖) • w by module,
              norm_smul, Real.norm_eq_abs]
          rw [hnorm, abs_of_pos (by rw [sub_pos, div_lt_one hn]; linarith), sub_mul, one_mul,
            div_mul_cancel₀ _ (ne_of_gt hn)]
          linarith
    choose ε hεpos hε using hmarg
    refine ⟨Finset.inf' Finset.univ Finset.univ_nonempty ε / 2, ?_, ?_⟩
    · have : 0 < Finset.inf' Finset.univ Finset.univ_nonempty ε :=
        (Finset.lt_inf'_iff Finset.univ_nonempty).mpr fun z _ => hεpos z
      linarith
    · intro j z hz
      refine hε j z (le_trans hz ?_)
      have hle : Finset.inf' Finset.univ Finset.univ_nonempty ε ≤ ε j :=
        Finset.inf'_le _ (Finset.mem_univ j)
      have hinfpos : 0 < Finset.inf' Finset.univ Finset.univ_nonempty ε :=
        (Finset.lt_inf'_iff Finset.univ_nonempty).mpr fun z _ => hεpos z
      linarith [hle, hinfpos]
  · refine ⟨1, one_pos, ?_⟩
    intro j
    exact absurd ⟨j⟩ hι

/-- **The periodisation on the core ball.**  If `f` is supported in the ball of radius `R` and
`‖z‖ + R < 1`, then only the `m = 0` translate can contribute to the periodisation at `z`, so
`tmPer f z = f z`. -/
lemma gardTmPer_core {n : ℕ} {f : (Fin n → ℝ) → ℝ} {R R₀ : ℝ}
    (hR : R + R₀ < 1) (hsupp : Function.support f ⊆ Metric.ball 0 R) {z : Fin n → ℝ}
    (hz : ‖z‖ ≤ R₀) : Work.Diff.STE.B3.tmPer f z = f z := by
  have h := Work.Diff.STE.B3.tmPer_eq_of_unique f z 0 fun m hm => ?_
  · simpa using h
  by_contra hc
  have hmem : z + Work.Diff.STE.iVec m ∈ Metric.ball (0 : Fin n → ℝ) R :=
    hsupp (Function.mem_support.mpr hc)
  rw [Metric.mem_ball, dist_zero_right] at hmem
  have hm0 : m = 0 := by
    funext i
    have h1 : ‖Work.Diff.STE.iVec m‖ ≤ ‖z + Work.Diff.STE.iVec m‖ + ‖z‖ := by
      have := norm_sub_le (z + Work.Diff.STE.iVec m) z
      simpa using this
    have h2 : ‖((m i : ℤ) : ℝ)‖ ≤ ‖Work.Diff.STE.iVec m‖ := by
      simpa [Work.Diff.STE.iVec] using norm_le_pi_norm (Work.Diff.STE.iVec m) i
    have h3 : |((m i : ℤ) : ℝ)| < 1 := by
      rw [Real.norm_eq_abs] at h2
      linarith
    have h4 : m i = 0 := by
      have h5 := abs_lt.mp h3
      have : (-1 : ℤ) < m i ∧ m i < 1 := by exact_mod_cast h5
      omega
    simpa using h4
  exact hm hm0

end Work.Diff.STE.Lead.Gal

import Mathlib
import Submission.Work.CR.Flat.Cauchy.bmDefs

noncomputable section

open scoped NNReal ENNReal
open scoped Convolution
open MeasureTheory Set

namespace Work.CR.Flat.Cauchy

/-! ## Elementary estimates for the Euclidean norm on `ℂⁿ` -/

lemma eucNorm_neg {n : ℕ} (x : Fin n → ℂ) : eucNorm (-x) = eucNorm x := by
  simp [eucNorm]

lemma norm_apply_le_eucNorm {n : ℕ} (x : Fin n → ℂ) (i : Fin n) : ‖x i‖ ≤ eucNorm x := by
  rw [eucNorm]
  calc ‖x i‖ = Real.sqrt (‖x i‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (∑ j, ‖x j‖ ^ 2) := Real.sqrt_le_sqrt
        (Finset.single_le_sum (fun j _ => sq_nonneg ‖x j‖) (Finset.mem_univ i))

lemma norm_le_eucNorm {n : ℕ} (x : Fin n → ℂ) : ‖x‖ ≤ eucNorm x :=
  (pi_norm_le_iff_of_nonneg (eucNorm_nonneg x)).2 fun i => norm_apply_le_eucNorm x i

lemma bmKernel_neg {n : ℕ} (j : Fin n) (x : Fin n → ℂ) : bmKernel j (-x) = - bmKernel j x := by
  simp only [bmKernel, eucNorm_neg, Pi.neg_apply, map_neg, neg_div]

/-! ## The kernel is dominated by `‖x‖ ^ (1 - 2n)` -/

lemma norm_bmKernel {n : ℕ} (j : Fin n) (x : Fin n → ℂ) :
    ‖bmKernel j x‖ = ‖x j‖ / eucNorm x ^ (2 * n) := by
  rw [bmKernel, norm_div, norm_pow, starRingEnd_apply, norm_star, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (eucNorm_nonneg x)]

lemma norm_bmKernel_le {n : ℕ} (j : Fin n) (x : Fin n → ℂ) :
    ‖bmKernel j x‖ ≤ ‖x‖ ^ (1 - 2 * (n : ℝ)) := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [bmKernel, Pi.zero_apply, map_zero, zero_div, norm_zero]
    exact Real.rpow_nonneg (norm_nonneg _) _
  · have hx0 : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have he : 0 < eucNorm x := eucNorm_pos hx
    rw [norm_bmKernel]
    calc ‖x j‖ / eucNorm x ^ (2 * n)
        ≤ ‖x‖ / eucNorm x ^ (2 * n) :=
          div_le_div_of_nonneg_right (norm_le_pi_norm x j) (pow_nonneg (eucNorm_nonneg x) _)
      _ ≤ ‖x‖ / ‖x‖ ^ (2 * n) := by
          refine div_le_div_of_nonneg_left (norm_nonneg x) (pow_pos hx0 _) ?_
          exact pow_le_pow_left₀ (norm_nonneg x) (norm_le_eucNorm x) _
      _ = ‖x‖ ^ (1 - 2 * (n : ℝ)) := by
          have hexp : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
          rw [← Real.rpow_natCast, hexp, Real.rpow_sub hx0, Real.rpow_one]

lemma measurable_bmKernel {n : ℕ} (j : Fin n) : Measurable (bmKernel j) := by
  have h1 : Measurable fun x : Fin n → ℂ => starRingEnd ℂ (x j) := by
    have : (starRingEnd ℂ) = (star : ℂ → ℂ) := by funext z; exact starRingEnd_apply z
    rw [this]
    exact continuous_star.measurable.comp (measurable_pi_apply j)
  have h2 : Measurable fun x : Fin n → ℂ => (eucNorm x : ℂ) ^ (2 * n) :=
    ((Complex.continuous_ofReal.comp continuous_eucNorm).pow _).measurable
  exact h1.div h2

lemma locallyIntegrable_bmKernel {n : ℕ} (hn : 0 < n) (j : Fin n) :
    LocallyIntegrable (bmKernel j) := by
  have hfr : Module.finrank ℝ (Fin n → ℂ) = 2 * n := by
    rw [Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex, mul_comm]
  refine MeasureTheory.locallyIntegrable_of_norm_le_rpow (C := 1) (α := 2 * (n : ℝ) - 1)
    ?_ ?_ ?_ ?_
  · rw [hfr]; omega
  · rw [hfr]; push_cast; linarith
  · filter_upwards with x
    have h : -(2 * (n : ℝ) - 1) = 1 - 2 * (n : ℝ) := by ring
    rw [h, one_mul]
    exact norm_bmKernel_le j x
  · exact (measurable_bmKernel j).aestronglyMeasurable

/-! ## Support in a half polydisc gives compact support -/

lemma isCompact_closed_polydisc {n : ℕ} {c : Fin n → ℂ} {R : Fin n → ℝ} (hR : ∀ j, 0 ≤ R j) :
    IsCompact {z : Fin n → ℂ | ∀ k, ‖z k - c k‖ ≤ R k} := by
  set K : Set (Fin n → ℂ) := {z | ∀ k, ‖z k - c k‖ ≤ R k} with hK
  have hclosed : IsClosed K := by
    have h : K = ⋂ k, {z : Fin n → ℂ | ‖z k - c k‖ ≤ R k} := by
      ext z; simp [hK, Set.mem_iInter]
    rw [h]
    exact isClosed_iInter fun k =>
      isClosed_le ((continuous_apply k).sub continuous_const).norm continuous_const
  have hsub : K ⊆ Metric.closedBall c (∑ k, R k) := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm]
    rw [pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => hR i)]
    intro k
    exact (hz k).trans (Finset.single_le_sum (fun i _ => hR i) (Finset.mem_univ k))
  exact (isCompact_closedBall c _).of_isClosed_subset hclosed hsub

lemma hasCompactSupport_of_halfPolydisc {n : ℕ} {c : Fin n → ℂ} {r : Fin n → ℝ}
    (hr : ∀ j, 0 < r j) {g : (Fin n → ℂ) → ℂ}
    (hsupp : ∀ z, (∃ k, r k / 2 ≤ ‖z k - c k‖) → g z = 0) : HasCompactSupport g := by
  have hR : ∀ j, 0 ≤ r j / 2 := fun j => div_nonneg (le_of_lt (hr j)) (by norm_num)
  have hK : IsCompact {z : Fin n → ℂ | ∀ k, ‖z k - c k‖ ≤ r k / 2} :=
    isCompact_closed_polydisc hR
  refine hK.of_isClosed_subset (isClosed_tsupport g) ?_
  rw [tsupport]
  refine closure_minimal (fun z hz => ?_) hK.isClosed
  intro k
  by_contra hk
  exact hz (hsupp z ⟨k, le_of_lt (not_le.mp hk)⟩)

/-! ## The potential as a convolution -/

lemma integral_bmKernel_sub_eq {n : ℕ} (j : Fin n) (g : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) :
    ∫ ζ, bmKernel j (ζ - z) * g ζ = - ∫ t, bmKernel j t * g (z - t) := by
  have h1 : ∀ ζ : Fin n → ℂ, bmKernel j (ζ - z) * g ζ = - (bmKernel j (z - ζ) * g ζ) := by
    intro ζ
    have h : ζ - z = -(z - ζ) := by abel
    rw [h, bmKernel_neg, neg_mul]
  simp_rw [h1, MeasureTheory.integral_neg]
  congr 1
  rw [← MeasureTheory.integral_sub_left_eq_self (fun t => bmKernel j t * g (z - t)) volume z]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with ζ
  simp [sub_sub_cancel]

lemma bmPotential_eq_neg_conv {n : ℕ} (f : Fin n → (Fin n → ℂ) → ℂ) :
    bmPotential f =
      fun z => - ∑ j, (bmKernel j ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] f j) z := by
  funext z
  rw [bmPotential, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [MeasureTheory.convolution_def]
  simp only [ContinuousLinearMap.mul_apply']
  exact integral_bmKernel_sub_eq j (f j) z

/-! ## The main theorem -/

/-- **Regularity of the Bochner–Martinelli potential.**  For a family `f` of `C¹` functions on
`ℂⁿ` supported in the closed half-size polydisc `polydisc c (r/2)`, the Bochner–Martinelli
potential `bmPotential f z = Σ_j ∫ \overline{ζ_j - z_j} f_j(ζ)/‖ζ - z‖^{2n} dζ` (Euclidean norm,
see `Submission/Work/CR/Flat/Cauchy/bmDefs.lean`) is continuously differentiable.

Differentiating the kernel gives a `(-2n)`-homogeneous kernel, which is not absolutely integrable
at `ζ = z`; the mean-zero of the kernel's derivative over balls centred at `z` makes it legitimate
to subtract `f_j(z)`, and `|f_j(ζ) - f_j(z)| ≤ [f_j]_α ‖ζ - z‖^α` with `α > 0` then makes the
derivative integral absolutely convergent; dominated convergence with a `‖t‖^{-2n}`-bound on the
truncated difference quotients gives differentiability. -/
theorem bmPotential_contDiff_one {n : ℕ} (hn : 0 < n) {c : Fin n → ℂ} {r : Fin n → ℝ}
    (hr : ∀ j, 0 < r j) {f : Fin n → (Fin n → ℂ) → ℂ} (hf : ∀ j, ContDiff ℝ 1 (f j))
    (hsupp : ∀ j z, (∃ k, r k / 2 ≤ ‖z k - c k‖) → f j z = 0) :
    ContDiff ℝ 1 (bmPotential f) := by
  have hconv : ∀ j, ContDiff ℝ 1 (bmKernel j ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] f j) :=
    fun j => HasCompactSupport.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℂ)
      (hasCompactSupport_of_halfPolydisc hr fun z hz => hsupp j z hz)
      (locallyIntegrable_bmKernel hn j) (hf j)
  rw [bmPotential_eq_neg_conv f]
  exact ContDiff.neg (ContDiff.sum fun j _ => hconv j)

end Work.CR.Flat.Cauchy

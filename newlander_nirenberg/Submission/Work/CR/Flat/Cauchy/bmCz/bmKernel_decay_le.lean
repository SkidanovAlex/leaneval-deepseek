/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# Decay and measurability of the Bochner–Martinelli derivative kernels

This file proves `bmKernel_decay_le`: the Wirtinger derivatives
`∂_{z_k}(bmKernel j)` and `∂_{\bar z_k}(bmKernel j)` of the Bochner–Martinelli kernel are
(a) measurable (hence a.e. strongly measurable for the Lebesgue measure), and
(b) bounded by a constant times `‖x‖^{-2n}` away from the origin.

The key point is that the *numerators* of these kernels are quadratic in `x`, so that the
homogeneity `x ↦ ‖x‖^{1-2n}` of `bmKernel` upgrades to the Calderón–Zygmund rate
`‖x‖^{-2n}` for the first derivatives.
-/
import Mathlib
import Submission.Work.CR.Flat.Cauchy.bmCZDefs

namespace Work.CR.Flat.Cauchy.bmCz

open MeasureTheory Set
open Work.CR.Flat.Cauchy

/-! ### Elementary facts about `eucNorm` -/

/-- Each coordinate of `x` is bounded by its Euclidean norm. -/
private lemma norm_apply_le_eucNorm {n : ℕ} (x : Fin n → ℂ) (i : Fin n) : ‖x i‖ ≤ eucNorm x := by
  have h : ‖x i‖ ^ 2 ≤ eucNorm x ^ 2 := by
    rw [eucNorm_sq]
    exact Finset.single_le_sum (f := fun l : Fin n => ‖x l‖ ^ 2) (fun l _ => sq_nonneg (‖x l‖))
      (Finset.mem_univ i)
  have h3 : |‖x i‖| ≤ |eucNorm x| := sq_le_sq.mp h
  rwa [abs_of_nonneg (norm_nonneg (x i)), abs_of_nonneg (eucNorm_nonneg x)] at h3

/-- The norm of `(eucNorm x : ℂ) ^ m` is `(eucNorm x) ^ m`. -/
private lemma norm_eucNorm_pow {n : ℕ} (x : Fin n → ℂ) (m : ℕ) :
    ‖((eucNorm x : ℂ)) ^ m‖ = (eucNorm x) ^ m := by
  rw [norm_pow, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (eucNorm_nonneg x)]

/-- The homogeneous degree-`(-2n)` bound for the quadratic numerator `n ‖x_j‖ ‖x_k‖`. -/
private lemma num_div_pow_le {n : ℕ} (x : Fin n → ℂ) (hx : x ≠ 0) (j k : Fin n) :
    (n : ℝ) * ‖x j‖ * ‖x k‖ / (eucNorm x) ^ (2 * n + 2) ≤ (n : ℝ) / (eucNorm x) ^ (2 * n) := by
  have hXpos : 0 < eucNorm x := eucNorm_pos hx
  have hXne : eucNorm x ≠ 0 := ne_of_gt hXpos
  have hle : (n : ℝ) * ‖x j‖ * ‖x k‖ ≤ (n : ℝ) * (eucNorm x) ^ 2 := by
    have hj := norm_apply_le_eucNorm x j
    have hk := norm_apply_le_eucNorm x k
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    calc (n : ℝ) * ‖x j‖ * ‖x k‖ ≤ (n : ℝ) * eucNorm x * eucNorm x := by gcongr
      _ = (n : ℝ) * (eucNorm x) ^ 2 := by ring
  calc (n : ℝ) * ‖x j‖ * ‖x k‖ / (eucNorm x) ^ (2 * n + 2)
      ≤ (n : ℝ) * (eucNorm x) ^ 2 / (eucNorm x) ^ (2 * n + 2) :=
        div_le_div_of_nonneg_right hle (by positivity)
    _ = (n : ℝ) / (eucNorm x) ^ (2 * n) := by
        rw [pow_add]
        rw [mul_div_mul_right _ _ (pow_ne_zero _ hXne)]

/-! ### Measurability of the kernels -/

private lemma measurable_conj_apply {n : ℕ} (i : Fin n) :
    Measurable (fun x : Fin n → ℂ => starRingEnd ℂ (x i)) :=
  Complex.continuous_conj.measurable.comp (continuous_apply i).measurable

private lemma measurable_eucNorm_pow {n : ℕ} (m : ℕ) :
    Measurable (fun x : Fin n → ℂ => ((eucNorm x : ℂ) ^ m)) :=
  Measurable.pow_const (Complex.continuous_ofReal.measurable.comp continuous_eucNorm.measurable) m

private lemma measurable_bmDzKernel {n : ℕ} (k j : Fin n) : Measurable (bmDzKernel k j) := by
  unfold bmDzKernel
  refine Measurable.div ?_ ?_
  · exact (measurable_const.mul (measurable_conj_apply j)).mul (measurable_conj_apply k)
  · exact measurable_eucNorm_pow _

private lemma measurable_bmDbarKernel {n : ℕ} (k j : Fin n) : Measurable (bmDbarKernel k j) := by
  unfold bmDbarKernel
  refine Measurable.sub ?_ ?_
  · exact Measurable.div measurable_const (measurable_eucNorm_pow _)
  · refine Measurable.div ?_ ?_
    · exact (measurable_const.mul (measurable_conj_apply j)).mul (continuous_apply k).measurable
    · exact measurable_eucNorm_pow _

/-! ### The decay statement -/

theorem bmKernel_decay_le {n : ℕ} (hn : 0 < n) :
    (∀ (k j : Fin n), MeasureTheory.AEStronglyMeasurable (Work.CR.Flat.Cauchy.bmDzKernel k j) MeasureTheory.volume) ∧
    (∀ (j k : Fin n), MeasureTheory.AEStronglyMeasurable (Work.CR.Flat.Cauchy.bmDbarKernel j k) MeasureTheory.volume) ∧
    ∃ C : ℝ, 0 < C ∧ (∀ (k j : Fin n) (x : Fin n → ℂ), x ≠ 0 →
        ‖Work.CR.Flat.Cauchy.bmDzKernel k j x‖ ≤ C / (Work.CR.Flat.Cauchy.eucNorm x) ^ (2 * n)) ∧
      (∀ (j k : Fin n) (x : Fin n → ℂ), x ≠ 0 →
        ‖Work.CR.Flat.Cauchy.bmDbarKernel j k x‖ ≤ C / (Work.CR.Flat.Cauchy.eucNorm x) ^ (2 * n)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro k j
    exact (measurable_bmDzKernel k j).aestronglyMeasurable
  · intro j k
    exact (measurable_bmDbarKernel j k).aestronglyMeasurable
  · refine ⟨(n : ℝ) + 1, by positivity, ?_, ?_⟩
    · intro k j x hx
      have hXnn : 0 ≤ eucNorm x := eucNorm_nonneg x
      simp only [bmDzKernel]
      rw [norm_div]
      have h1 : ‖-((n : ℂ)) * starRingEnd ℂ (x j) * starRingEnd ℂ (x k)‖
          = (n : ℝ) * ‖x j‖ * ‖x k‖ := by
        rw [norm_mul, norm_mul, norm_neg, Complex.norm_natCast, Complex.norm_conj, Complex.norm_conj]
      rw [h1, norm_eucNorm_pow]
      calc (n : ℝ) * ‖x j‖ * ‖x k‖ / (eucNorm x) ^ (2 * n + 2)
          ≤ (n : ℝ) / (eucNorm x) ^ (2 * n) := num_div_pow_le x hx j k
        _ ≤ ((n : ℝ) + 1) / (eucNorm x) ^ (2 * n) := by
            apply div_le_div_of_nonneg_right (by linarith) (pow_nonneg hXnn _)
    · intro j k x hx
      have hXnn : 0 ≤ eucNorm x := eucNorm_nonneg x
      have hA : ‖(if j = k then (1 : ℂ) else 0) / ((eucNorm x : ℂ) ^ (2 * n))‖
          ≤ 1 / (eucNorm x) ^ (2 * n) := by
        rw [norm_div, norm_eucNorm_pow]
        apply div_le_div_of_nonneg_right
        · split_ifs <;> simp
        · exact pow_nonneg hXnn _
      have hB : ‖(n : ℂ) * starRingEnd ℂ (x k) * x j / ((eucNorm x : ℂ) ^ (2 * n + 2))‖
          ≤ (n : ℝ) / (eucNorm x) ^ (2 * n) := by
        rw [norm_div]
        have h1 : ‖(n : ℂ) * starRingEnd ℂ (x k) * x j‖ = (n : ℝ) * ‖x k‖ * ‖x j‖ := by
          rw [norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_conj]
        rw [h1, norm_eucNorm_pow]
        exact num_div_pow_le x hx k j
      calc ‖bmDbarKernel j k x‖
          = ‖(if j = k then (1 : ℂ) else 0) / ((eucNorm x : ℂ) ^ (2 * n))
              - (n : ℂ) * starRingEnd ℂ (x k) * x j / ((eucNorm x : ℂ) ^ (2 * n + 2))‖ := by
            simp only [bmDbarKernel]
        _ ≤ ‖(if j = k then (1 : ℂ) else 0) / ((eucNorm x : ℂ) ^ (2 * n))‖
              + ‖(n : ℂ) * starRingEnd ℂ (x k) * x j / ((eucNorm x : ℂ) ^ (2 * n + 2))‖ :=
            norm_sub_le _ _
        _ ≤ 1 / (eucNorm x) ^ (2 * n) + (n : ℝ) / (eucNorm x) ^ (2 * n) := add_le_add hA hB
        _ = ((n : ℝ) + 1) / (eucNorm x) ^ (2 * n) := by rw [← add_div]; ring

end Work.CR.Flat.Cauchy.bmCz

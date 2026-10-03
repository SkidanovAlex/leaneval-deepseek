import Mathlib
import Submission.Work.HornSC.Cells

namespace Work.HornSC.CellDistBound

open Set

/-- Two points of `ℂ` whose real and imaginary parts differ by at most `2` are at distance at
most `2√2`. -/
lemma dist_le_two_sqrt_two_of_abs_le {z w : ℂ}
    (hr : |z.re - w.re| ≤ 2) (hi : |z.im - w.im| ≤ 2) :
    dist z w ≤ 2 * Real.sqrt 2 := by
  rw [Complex.dist_eq]
  have hb : (0 : ℝ) ≤ 2 * Real.sqrt 2 := by positivity
  have hsq : ‖z - w‖ ^ 2 ≤ (2 * Real.sqrt 2) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    have h8 : (2 * Real.sqrt 2) ^ 2 = 8 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    rw [h8]
    have h1 : (z.re - w.re) ^ 2 ≤ 4 := by
      have h := sq_le_sq' (abs_le.mp hr).1 (abs_le.mp hr).2
      norm_num at h ⊢
      exact h
    have h2 : (z.im - w.im) ^ 2 ≤ 4 := by
      have h := sq_le_sq' (abs_le.mp hi).1 (abs_le.mp hi).2
      norm_num at h ⊢
      exact h
    nlinarith [h1, h2]
  have hthis := sq_le_sq.mp hsq
  rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hb] at hthis
  exact hthis

theorem dist_le_of_mem_cellUnion_dil3 {A : Finset (ℤ × ℤ)} {C : Set ℂ}
    (hA : ∀ p ∈ A, (cell p ∩ C).Nonempty) {z : ℂ} (hz : z ∈ cellUnion (dil3 A)) :
    Metric.infDist z C ≤ 2 * Real.sqrt 2 := by
  obtain ⟨p, hp, hzp⟩ := Set.mem_iUnion₂.mp hz
  obtain ⟨q, hq, h1, h2⟩ := mem_dil3.mp hp
  obtain ⟨w, hwq, hwC⟩ := hA q hq
  obtain ⟨hz1, hz2, hz3, hz4⟩ := mem_cell.mp hzp
  obtain ⟨hw1, hw2, hw3, hw4⟩ := mem_cell.mp hwq
  have h1' : |((p.1 : ℝ) - (q.1 : ℝ))| ≤ 1 := by exact_mod_cast h1
  have h2' : |((p.2 : ℝ) - (q.2 : ℝ))| ≤ 1 := by exact_mod_cast h2
  have hr : |z.re - w.re| ≤ 2 := by
    rw [abs_le] at h1' ⊢
    constructor <;> linarith [h1'.1, h1'.2]
  have hi : |z.im - w.im| ≤ 2 := by
    rw [abs_le] at h2' ⊢
    constructor <;> linarith [h2'.1, h2'.2]
  calc Metric.infDist z C ≤ dist z w := Metric.infDist_le_dist_of_mem hwC
    _ ≤ 2 * Real.sqrt 2 := dist_le_two_sqrt_two_of_abs_le hr hi

end Work.HornSC.CellDistBound

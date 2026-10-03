import Mathlib.Analysis.Complex.ReImTopology
import Submission.Lib.Unif2.Commons.Topology.Plane.exists_dyadic_exhaustion_of_isOpen_complex

namespace Commons.Topology.Plane

/-- A point in the interior of a dyadic cell satisfies strict inequalities with respect to
the four sides of the closed cell. -/
lemma interior_dyadicCell_strict {n : ℕ} {p : ℤ × ℤ} {z : ℂ}
    (hz : z ∈ interior (dyadicCell n p)) :
    (p.1 : ℝ) / 2 ^ n < z.re ∧ z.re < ((p.1 : ℝ) + 1) / 2 ^ n ∧
    (p.2 : ℝ) / 2 ^ n < z.im ∧ z.im < ((p.2 : ℝ) + 1) / 2 ^ n := by
  have h1 : z ∈ interior {w : ℂ | (p.1 : ℝ) / 2 ^ n ≤ w.re} :=
    interior_mono (fun w hw => hw.1) hz
  have h2 : z ∈ interior {w : ℂ | w.re ≤ ((p.1 : ℝ) + 1) / 2 ^ n} :=
    interior_mono (fun w hw => hw.2.1) hz
  have h3 : z ∈ interior {w : ℂ | (p.2 : ℝ) / 2 ^ n ≤ w.im} :=
    interior_mono (fun w hw => hw.2.2.1) hz
  have h4 : z ∈ interior {w : ℂ | w.im ≤ ((p.2 : ℝ) + 1) / 2 ^ n} :=
    interior_mono (fun w hw => hw.2.2.2) hz
  rw [Complex.interior_setOfPred_le_re] at h1
  rw [Complex.interior_setOfPred_re_le] at h2
  rw [Complex.interior_setOfPred_le_im] at h3
  rw [Complex.interior_setOfPred_im_le] at h4
  exact ⟨h1, h2, h3, h4⟩

/-- A real number strictly inside a level-`n` dyadic interval is not a level-`n` grid point. -/
lemma div_pow_ne_grid_of_between {n : ℕ} {a j : ℤ} {x : ℝ}
    (hlo : (a : ℝ) / 2 ^ n < x) (hhi : x < ((a : ℝ) + 1) / 2 ^ n) :
    x ≠ (j : ℝ) / 2 ^ n := by
  intro heq
  have h2n : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  rcases le_or_gt j a with hj | hj
  · have hle : (j : ℝ) / 2 ^ n ≤ (a : ℝ) / 2 ^ n :=
      div_le_div_of_nonneg_right (by exact_mod_cast hj) (le_of_lt h2n)
    linarith
  · have hle : ((a : ℝ) + 1) / 2 ^ n ≤ (j : ℝ) / 2 ^ n := by
      apply div_le_div_of_nonneg_right _ (le_of_lt h2n)
      have h : (a : ℝ) + 1 ≤ (j : ℝ) := by
        exact_mod_cast (show a + 1 ≤ j by omega)
      linarith
    linarith

/-- A level-`m` grid point is a level-`n` grid point when `m ≤ n`. -/
lemma int_div_pow_eq_mul_div_pow {m n : ℕ} (hmn : m ≤ n) (k : ℤ) :
    (((k * (2 : ℤ) ^ (n - m) : ℤ)) : ℝ) / (2 : ℝ) ^ n = (k : ℝ) / (2 : ℝ) ^ m := by
  have hpow : (2 : ℝ) ^ n = (2 : ℝ) ^ m * (2 : ℝ) ^ (n - m) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hpow]
  have hne : (2 : ℝ) ^ (n - m) ≠ 0 := by positivity
  push_cast
  rw [mul_div_mul_right (k : ℝ) ((2 : ℝ) ^ m) hne]

theorem dyadicCell_grid_avoidance {n m : ℕ} (hmn : m ≤ n) {p : ℤ × ℤ} {z : ℂ} {k : ℤ}
    (hz : z ∈ interior (Commons.Topology.Plane.dyadicCell n p)) :
    z.re ≠ (k : ℝ) / 2 ^ m ∧ z.im ≠ (k : ℝ) / 2 ^ m := by
  obtain ⟨h1, h2, h3, h4⟩ := interior_dyadicCell_strict hz
  refine ⟨?_, ?_⟩
  · rw [← int_div_pow_eq_mul_div_pow hmn k]
    exact div_pow_ne_grid_of_between h1 h2
  · rw [← int_div_pow_eq_mul_div_pow hmn k]
    exact div_pow_ne_grid_of_between h3 h4

end Commons.Topology.Plane
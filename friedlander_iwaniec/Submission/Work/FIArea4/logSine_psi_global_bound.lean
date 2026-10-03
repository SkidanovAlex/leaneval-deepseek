import Mathlib
import Submission.Work.FIArea4.logSine_defs
import Submission.Work.FIArea4.logSine_psi_deriv

namespace Work.FIArea4

open scoped Topology

noncomputable section

/-- Elementary: `1/(2 (N:ℝ)^2) ≤ 2/(N:ℝ)^2`. -/
lemma one_div_two_sq_le_two_div_sq (N : ℕ) (hN : 1 ≤ N) :
    (1:ℝ) / (2 * (N:ℝ)^2) ≤ 2 / (N:ℝ)^2 := by
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hB : (0:ℝ) < (N:ℝ)^2 := by positivity
  have hpos1 : 0 < 1 / (N:ℝ)^2 := div_pos one_pos hB
  have e1 : (1:ℝ) / (2 * (N:ℝ)^2) = (1/2) * (1 / (N:ℝ)^2) := by ring
  have e2 : (2:ℝ) / (N:ℝ)^2 = 2 * (1 / (N:ℝ)^2) := by ring
  rw [e1, e2]; linarith

/-- Above the window, i.e. for `y ≥ 2/N²`, the first derivative bound holds. -/
lemma abs_deriv_Psi_le_of_ge (N : ℕ) (hN : 2 ≤ N) (K : ℝ) (hK : 1 ≤ K)
    (hK1 : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ K)
    (hK2 : ∀ x : ℝ, |deriv (deriv Real.smoothTransition) x| ≤ K) {y : ℝ}
    (h : 2 / (N:ℝ)^2 ≤ y) :
    |deriv (Psi N) y| ≤ 4 * K * (N:ℝ)^2 * (Real.log N + 1) := by
  have hN1 : 1 ≤ N := le_trans (by norm_num) hN
  have hB : (0:ℝ) < (N:ℝ)^2 := by positivity
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN1)
  have hK0 : 0 ≤ K := by linarith
  have hBpos : (0:ℝ) < 2/(N:ℝ)^2 := div_pos (by norm_num) hB
  have hypos : 0 < y := lt_of_lt_of_le hBpos h
  obtain ⟨hA, _, _, _, _⟩ := logSine_psi_deriv N hN K hK hK1 hK2
  rw [hA y h, abs_of_pos (div_pos one_pos (by linarith : (0:ℝ) < 2*y))]
  have h1y : 1/y ≤ 2*(N:ℝ)^2 := one_div_le_of_window N hN1
    (le_trans (one_div_two_sq_le_two_div_sq N hN1) h)
  have hKlog : 1 ≤ K * (Real.log N + 1) := by nlinarith [hK, hlogN]
  have hN2nn : 0 ≤ (N:ℝ)^2 := le_of_lt hB
  have hstep : (N:ℝ)^2 ≤ 4 * K * (N:ℝ)^2 * (Real.log N + 1) := by
    have h1 := mul_le_mul_of_nonneg_left hKlog hN2nn
    have h2 : 0 ≤ (N:ℝ)^2 * (K * (Real.log N + 1)) := mul_nonneg hN2nn (by linarith)
    nlinarith [h1, h2]
  calc 1/(2*y) = (1/2) * (1/y) := by ring
    _ ≤ (1/2) * (2*(N:ℝ)^2) := mul_le_mul_of_nonneg_left h1y (by norm_num)
    _ = (N:ℝ)^2 := by ring
    _ ≤ 4 * K * (N:ℝ)^2 * (Real.log N + 1) := hstep

/-- Above the window, i.e. for `y ≥ 2/N²`, the second derivative bound holds. -/
lemma abs_deriv_deriv_Psi_le_of_ge (N : ℕ) (hN : 2 ≤ N) (K : ℝ) (hK : 1 ≤ K)
    (hK1 : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ K)
    (hK2 : ∀ x : ℝ, |deriv (deriv Real.smoothTransition) x| ≤ K) {y : ℝ}
    (h : 2 / (N:ℝ)^2 ≤ y) :
    |deriv (deriv (Psi N)) y| ≤ 8 * K * (N:ℝ)^4 * (Real.log N + 1) := by
  have hN1 : 1 ≤ N := le_trans (by norm_num) hN
  have hB : (0:ℝ) < (N:ℝ)^2 := by positivity
  have hB4 : (0:ℝ) < (N:ℝ)^4 := by positivity
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN1)
  have hK0 : 0 ≤ K := by linarith
  have hBpos : (0:ℝ) < 2/(N:ℝ)^2 := div_pos (by norm_num) hB
  have hypos : 0 < y := lt_of_lt_of_le hBpos h
  obtain ⟨_, hA, _, _, _⟩ := logSine_psi_deriv N hN K hK hK1 hK2
  rw [hA y h, abs_neg, abs_of_pos (by positivity : (0:ℝ) < 1/(2*y^2))]
  have h1y : 1/y^2 ≤ 4*(N:ℝ)^4 := one_div_sq_le_of_window N hN1
    (le_trans (one_div_two_sq_le_two_div_sq N hN1) h)
  have hKlog : 1 ≤ K * (Real.log N + 1) := by nlinarith [hK, hlogN]
  have hN4nn : 0 ≤ (N:ℝ)^4 := le_of_lt hB4
  have hstep : 2*(N:ℝ)^4 ≤ 8 * K * (N:ℝ)^4 * (Real.log N + 1) := by
    have h1 := mul_le_mul_of_nonneg_left hKlog hN4nn
    have h2 : 0 ≤ (N:ℝ)^4 * (K * (Real.log N + 1)) := mul_nonneg hN4nn (by linarith)
    nlinarith [h1, h2]
  calc 1/(2*y^2) = (1/2) * (1/y^2) := by ring
    _ ≤ (1/2) * (4*(N:ℝ)^4) := mul_le_mul_of_nonneg_left h1y (by norm_num)
    _ = 2*(N:ℝ)^4 := by ring
    _ ≤ 8 * K * (N:ℝ)^4 * (Real.log N + 1) := hstep

/-- Global pointwise bounds for the first two derivatives of the mollifier `Psi N`, valid at
*every* `y ≥ 0` (merging the "off the window" and "inside the window" regimes of
`logSine_psi_deriv` into one bound). -/
theorem logSine_psi_global_bound (N : ℕ) (hN : 2 ≤ N) (K : ℝ) (hK : 1 ≤ K)
    (hK1 : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ K)
    (hK2 : ∀ x : ℝ, |deriv (deriv Real.smoothTransition) x| ≤ K) :
    (∀ y : ℝ, 0 ≤ y → |deriv (Psi N) y| ≤ 4 * K * (N:ℝ)^2 * (Real.log N + 1)) ∧
    (∀ y : ℝ, 0 ≤ y → |deriv (deriv (Psi N)) y| ≤ 8 * K * (N:ℝ)^4 * (Real.log N + 1)) := by
  have hN1 : 1 ≤ N := le_trans (by norm_num) hN
  have hB : (0:ℝ) < (N:ℝ)^2 := by positivity
  have hB4 : (0:ℝ) < (N:ℝ)^4 := by positivity
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN1)
  have hK0 : 0 ≤ K := by linarith
  have hR1 : 0 ≤ 4 * K * (N:ℝ)^2 * (Real.log N + 1) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hK0) (le_of_lt hB)) (by linarith)
  have hR2 : 0 ≤ 8 * K * (N:ℝ)^4 * (Real.log N + 1) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hK0) (le_of_lt hB4)) (by linarith)
  obtain ⟨_, _, hC, hD, hE⟩ := logSine_psi_deriv N hN K hK hK1 hK2
  constructor
  · intro y _
    rcases lt_or_ge y (1/(2*(N:ℝ)^2)) with hlt | hge
    · rw [hC y hlt]; simpa using hR1
    · rcases le_or_gt y (2/(N:ℝ)^2) with hle | hgt
      · exact (hE y hge hle).1
      · exact abs_deriv_Psi_le_of_ge N hN K hK hK1 hK2 (le_of_lt hgt)
  · intro y _
    rcases lt_or_ge y (1/(2*(N:ℝ)^2)) with hlt | hge
    · rw [hD y hlt]; simpa using hR2
    · rcases le_or_gt y (2/(N:ℝ)^2) with hle | hgt
      · exact (hE y hge hle).2
      · exact abs_deriv_deriv_Psi_le_of_ge N hN K hK hK1 hK2 (le_of_lt hgt)

end

end Work.FIArea4

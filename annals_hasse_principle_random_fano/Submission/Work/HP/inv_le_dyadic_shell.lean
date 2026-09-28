import Mathlib
import Submission.Work.HP.dyadic_summation

namespace Work.HP

/-- The dyadic shell index: a real `u` with `1 ≤ u` lies in `[2^(j0), 2^(j0+1)]` for
`j0 = Nat.find (fun j => u ≤ 2^(j+1))`. This is the "floor of the dyadic logarithm" of `u`,
chosen so that the term of index `j0` in the dyadic shell sum contributes `≥ 1/t`. -/
theorem inv_le_dyadic_shell {A t : ℝ} (hA : 1 ≤ A) (ht1 : 1 ≤ t) (htA : t ≤ A) :
    1 / t ≤ ∑ j ∈ Finset.range (dyIdx A + 1),
      ((2 : ℝ) ^ (j + 1) / A) * (if t ≤ A / (2 : ℝ) ^ j then (1 : ℝ) else 0) := by
  classical
  have hA0 : (0 : ℝ) < A := by linarith
  have ht0 : (0 : ℝ) < t := by linarith
  set u : ℝ := A / t with hu
  have hu1 : 1 ≤ u := by rw [hu]; rw [le_div_iff₀ ht0]; linarith
  have huA : u ≤ A := by rw [hu]; rw [div_le_iff₀ ht0]; nlinarith
  -- a dyadic shell index for `u = A/t`
  have hex : ∃ j : ℕ, u ≤ (2 : ℝ) ^ (j + 1) :=
    ⟨dyIdx u, le_trans (le_pow_dyIdx u)
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega))⟩
  set j0 : ℕ := Nat.find hex with hj0def
  have hj0_spec : u ≤ (2 : ℝ) ^ (j0 + 1) := by
    rw [hj0def]; exact Nat.find_spec hex
  have hj0_le_u : j0 ≤ dyIdx u := by
    rw [hj0def]
    exact Nat.find_min' hex (le_trans (le_pow_dyIdx u)
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)))
  have hj0_le_A : j0 ≤ dyIdx A := le_trans hj0_le_u (dyIdx_mono huA)
  -- `2^j0 ≤ u`: from minimality of `j0` (or trivially when `j0 = 0`)
  have hle_u : (2 : ℝ) ^ j0 ≤ u := by
    rcases Nat.eq_zero_or_pos j0 with h | h
    · rw [h]; simpa using hu1
    · have hlt' : j0 - 1 < Nat.find hex := by rw [← hj0def]; omega
      have hmin := Nat.find_min hex hlt'
      rw [Nat.sub_add_cancel h] at hmin
      exact le_of_lt (not_le.mp hmin)
  -- hence `t` lies in the shell `(A/2^(j0+1), A/2^j0]`
  have hshell : t ≤ A / (2 : ℝ) ^ j0 := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ j0)]
    rw [hu] at hle_u
    have h := (le_div_iff₀ ht0).mp hle_u
    calc t * (2 : ℝ) ^ j0 = (2 : ℝ) ^ j0 * t := by ring
      _ ≤ A := h
  have hmem : j0 ∈ Finset.range (dyIdx A + 1) := by
    rw [Finset.mem_range]; omega
  -- all summands are nonnegative, so the sum dominates its `j0`-th term
  have hnn : ∀ j ∈ Finset.range (dyIdx A + 1),
      0 ≤ ((2 : ℝ) ^ (j + 1) / A) * (if t ≤ A / (2 : ℝ) ^ j then (1 : ℝ) else 0) := by
    intro j _
    have h1 : (0 : ℝ) ≤ (2 : ℝ) ^ (j + 1) / A := div_nonneg (by positivity) hA0.le
    by_cases h : t ≤ A / (2 : ℝ) ^ j
    · simp [h, h1]
    · simp [h]
  have hsingle : ((2 : ℝ) ^ (j0 + 1) / A) * (if t ≤ A / (2 : ℝ) ^ j0 then (1 : ℝ) else 0)
      ≤ ∑ j ∈ Finset.range (dyIdx A + 1),
          ((2 : ℝ) ^ (j + 1) / A) * (if t ≤ A / (2 : ℝ) ^ j then (1 : ℝ) else 0) :=
    Finset.single_le_sum hnn hmem
  refine le_trans ?_ hsingle
  rw [ite_eq_left hshell, mul_one]
  rw [hu] at hj0_spec
  -- `1/t = u/A ≤ 2^(j0+1)/A`
  rw [div_le_div_iff₀ ht0 hA0, one_mul, ← div_mul_cancel₀ A (ne_of_gt ht0)]
  exact mul_le_mul_of_nonneg_right hj0_spec ht0.le

end Work.HP

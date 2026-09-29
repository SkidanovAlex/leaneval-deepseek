import Mathlib
import Submission.Work.Fx.ExpDefs

namespace Work.Fx

/-
Algebraic facts about `hval`/`pot` (see `Submission/Work/Fx/ExpDefs.lean`).
Proof: split off the `k = 0` term and reindex, using `(d-1)!/(d-1+k)! = (1/d)·d!/(d+k-1)!`
(`Nat.factorial_succ`); the bounds use `(d+1)⋯(d+k) ≥ k!` and `Z ≥ 0`.
-/
theorem expRec :
    (∀ (z : ℂ) (d i : ℕ), 1 ≤ d → hval z (d - 1) (i + 1) = 1 + (z / d) * hval z d i) ∧
    (∀ (Z : ℝ) (d i : ℕ), 1 ≤ d → 0 ≤ Z → pot Z (d - 1) (i + 1) = 1 + (Z / d) * pot Z d i) ∧
    (∀ (Z : ℝ), 0 ≤ Z → ∀ d i : ℕ, pot Z d i ≤ Real.exp Z) ∧
    (∀ (z : ℂ) (i : ℕ), hval z 0 i = ∑ k ∈ Finset.range (i + 1), z ^ k / (k.factorial : ℂ)) ∧
    (∀ (Z : ℝ) (M : ℕ), pot Z 0 M = ∑ k ∈ Finset.range M, Z ^ k / (k.factorial : ℝ)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- complex Horner recursion
    intro z d i hd
    rw [hval, hval, Finset.sum_range_succ', Finset.mul_sum]
    have hf0 : z ^ 0 * (((d - 1).factorial : ℂ) / ((d - 1 + 0).factorial : ℂ)) = 1 := by
      rw [pow_zero, Nat.add_zero, one_mul, div_self]
      exact_mod_cast Nat.factorial_ne_zero _
    rw [hf0]
    have hsum : (∑ k ∈ Finset.range (i + 1), z ^ (k + 1) *
        (((d - 1).factorial : ℂ) / ((d - 1 + (k + 1)).factorial : ℂ)))
        = ∑ k ∈ Finset.range (i + 1),
            (z / d) * (z ^ k * ((d.factorial : ℂ) / ((d + k).factorial : ℂ))) := by
      apply Finset.sum_congr rfl
      intro k _
      have hdk : d - 1 + (k + 1) = d + k := by omega
      rw [hdk]
      have hfac : ((d.factorial : ℕ) : ℂ) = (d : ℂ) * (((d - 1).factorial : ℕ) : ℂ) := by
        obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
        simp [Nat.factorial_succ]
      have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
      have hf0 : (((d - 1).factorial : ℕ) : ℂ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero _
      have hf1 : (((d + k).factorial : ℕ) : ℂ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero _
      rw [hfac, pow_succ]
      field_simp
    rw [hsum, add_comm]
  · -- real Horner recursion
    intro Z d i hd _
    rw [pot, pot, Finset.sum_range_succ', Finset.mul_sum]
    have hf0 : Z ^ 0 * (((d - 1).factorial : ℝ) / ((d - 1 + 0).factorial : ℝ)) = 1 := by
      rw [pow_zero, Nat.add_zero, one_mul, div_self]
      exact_mod_cast Nat.factorial_ne_zero _
    rw [hf0]
    have hsum : (∑ k ∈ Finset.range i, Z ^ (k + 1) *
        (((d - 1).factorial : ℝ) / ((d - 1 + (k + 1)).factorial : ℝ)))
        = ∑ k ∈ Finset.range i,
            (Z / d) * (Z ^ k * ((d.factorial : ℝ) / ((d + k).factorial : ℝ))) := by
      apply Finset.sum_congr rfl
      intro k _
      have hdk : d - 1 + (k + 1) = d + k := by omega
      rw [hdk]
      have hfac : ((d.factorial : ℕ) : ℝ) = (d : ℝ) * (((d - 1).factorial : ℕ) : ℝ) := by
        obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
        simp [Nat.factorial_succ]
      have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
      have hf0 : (((d - 1).factorial : ℕ) : ℝ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero _
      have hf1 : (((d + k).factorial : ℕ) : ℝ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero _
      rw [hfac, pow_succ]
      field_simp
    rw [hsum, add_comm]
  · -- the potential is dominated by the exponential
    intro Z hZ d i
    rw [pot]
    calc ∑ k ∈ Finset.range i, Z ^ k * ((d.factorial : ℝ) / ((d + k).factorial : ℝ))
        ≤ ∑ k ∈ Finset.range i, Z ^ k / (k.factorial : ℝ) := by
          apply Finset.sum_le_sum
          intro k _
          have hfac : ((d.factorial : ℝ) * (k.factorial : ℝ)) ≤ ((d + k).factorial : ℝ) := by
            have hdvd := Nat.factorial_mul_factorial_dvd_factorial_add d k
            have hle : d.factorial * k.factorial ≤ (d + k).factorial :=
              Nat.le_of_dvd (Nat.factorial_pos _) hdvd
            exact_mod_cast hle
          have hk1 : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
          have hdk1 : (0 : ℝ) < ((d + k).factorial : ℝ) := by
            exact_mod_cast Nat.factorial_pos (d + k)
          have key : (d.factorial : ℝ) / ((d + k).factorial : ℝ) ≤ 1 / (k.factorial : ℝ) := by
            rw [div_le_iff₀ hdk1, one_div, inv_mul_eq_div, le_div_iff₀ hk1]
            exact hfac
          have hZk : 0 ≤ Z ^ k := pow_nonneg hZ k
          have h := mul_le_mul_of_nonneg_left key hZk
          simpa only [one_div, div_eq_mul_inv, one_mul] using h
      _ ≤ Real.exp Z := Real.sum_le_exp_of_nonneg hZ i
  · -- `hval` at `d = 0` is the truncated exponential series
    intro z i
    rw [hval]
    apply Finset.sum_congr rfl
    intro k _
    simp [div_eq_mul_inv]
  · -- `pot` at `d = 0` is the truncated exponential series
    intro Z M
    rw [pot]
    apply Finset.sum_congr rfl
    intro k _
    simp [div_eq_mul_inv]

end Work.Fx

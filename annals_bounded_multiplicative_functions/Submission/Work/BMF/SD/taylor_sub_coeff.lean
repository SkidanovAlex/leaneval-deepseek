import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.wsc_basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.SD

theorem taylor_sub_coeff (k : ℕ) (d : ℕ) (P : Polynomial ℝ) (hP : P.natDegree ≤ k + 1) :
    (Polynomial.taylor (d:ℝ) P - P).natDegree ≤ k ∧
    ∀ i : ℕ, (Polynomial.taylor (d:ℝ) P - P).coeff i
      = ∑ j ∈ Finset.Icc (i+1) (k+1), P.coeff j * (d:ℝ)^(j-i) * ((j.choose i : ℕ) : ℝ) := by
  -- Coefficient of the Taylor shift, expanded in the monomial basis.
  have htaylor : ∀ i : ℕ, (Polynomial.taylor (d:ℝ) P).coeff i
      = ∑ j ∈ Finset.range (k+2), P.coeff j * (d:ℝ)^(j-i) * ((j.choose i : ℕ) : ℝ) := by
    intro i
    have hdeg : P.natDegree < k + 2 := by omega
    conv_lhs => rw [P.as_sum_range' (k+2) hdeg]
    rw [map_sum]
    rw [Polynomial.finsetSum_coeff]
    apply Finset.sum_congr rfl
    intro j _
    rw [Polynomial.taylor_monomial]
    rw [Polynomial.coeff_C_mul]
    rw [Polynomial.coeff_X_add_C_pow]
    ring
  -- The range sum is the `i`-th coefficient plus the sum over `i+1 ≤ j ≤ k+1`.
  have hrange : ∀ i : ℕ,
      (∑ j ∈ Finset.range (k+2), P.coeff j * (d:ℝ)^(j-i) * ((j.choose i : ℕ) : ℝ))
      = P.coeff i + ∑ j ∈ Finset.Icc (i+1) (k+1),
          P.coeff j * (d:ℝ)^(j-i) * ((j.choose i : ℕ) : ℝ) := by
    intro i
    by_cases hi : i ≤ k + 1
    · have hle : i ≤ k + 2 := by omega
      have hlt : i < k + 2 := by omega
      have hsplit := Finset.sum_range_add_sum_Ico
          (fun j => P.coeff j * (d:ℝ)^(j-i) * ((j.choose i : ℕ) : ℝ)) hle
      have hzero : (∑ j ∈ Finset.range i,
          P.coeff j * (d:ℝ)^(j-i) * ((j.choose i : ℕ) : ℝ)) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        rw [Finset.mem_range] at hj
        simp [Nat.choose_eq_zero_of_lt hj]
      rw [hzero, zero_add] at hsplit
      rw [← hsplit]
      rw [Finset.sum_eq_sum_Ico_succ_bot hlt]
      have hfi : P.coeff i * (d:ℝ)^(i-i) * ((i.choose i : ℕ) : ℝ) = P.coeff i := by simp
      rw [hfi]
      congr 1
    · push Not at hi
      have hzero : (∑ j ∈ Finset.range (k+2),
          P.coeff j * (d:ℝ)^(j-i) * ((j.choose i : ℕ) : ℝ)) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        rw [Finset.mem_range] at hj
        have hji : j < i := by omega
        simp [Nat.choose_eq_zero_of_lt hji]
      have hci : P.coeff i = 0 := by
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        omega
      have hempty : Finset.Icc (i+1) (k+1) = ∅ := by
        rw [Finset.Icc_eq_empty_iff]
        omega
      rw [hzero, hci, hempty, Finset.sum_empty, add_zero]
  have hcoeff : ∀ i : ℕ, (Polynomial.taylor (d:ℝ) P - P).coeff i
      = ∑ j ∈ Finset.Icc (i+1) (k+1),
          P.coeff j * (d:ℝ)^(j-i) * ((j.choose i : ℕ) : ℝ) := by
    intro i
    rw [Polynomial.coeff_sub, htaylor i, hrange i]
    ring
  constructor
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [hcoeff N]
    have hempty : Finset.Icc (N+1) (k+1) = ∅ := by
      rw [Finset.Icc_eq_empty_iff]
      omega
    rw [hempty, Finset.sum_empty]
  · exact hcoeff

end Work.BMF.SD

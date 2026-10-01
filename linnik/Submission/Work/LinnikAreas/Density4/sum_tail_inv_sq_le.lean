import Mathlib
import Submission.Work.LinnikAreas.Density4.sum_range_inv_succ_sq_le_two
import Submission.Work.LinnikAreas.Density4.tsum_tail_bound

namespace Work.LinnikAreas.Density4

/-- Partial sums of `1/a²` over `Icc 1 M` are at most `2`. -/
lemma sum_Icc_one_inv_sq_le_two (M : ℕ) :
    ∑ a ∈ Finset.Icc 1 M, (1 : ℝ) / (a : ℝ) ^ 2 ≤ 2 := by
  have hIcc : Finset.Icc 1 M = Finset.Ico 1 (M + 1) := by
    ext x; simp [Finset.mem_Icc, Finset.mem_Ico]
  rw [hIcc, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  calc ∑ k ∈ Finset.range M, (1 : ℝ) / (((1 + k : ℕ)) : ℝ) ^ 2
      = ∑ k ∈ Finset.range M, (((k + 1 : ℕ) : ℝ) ^ 2)⁻¹ := by
        apply Finset.sum_congr rfl
        intro k _
        have h : (((1 + k : ℕ)) : ℝ) = ((k + 1 : ℕ) : ℝ) := by push_cast; ring
        rw [h, one_div]
    _ ≤ 2 := sum_range_inv_succ_sq_le_two M

/-- Partial sums of `1/a²` over `Icc (k+1) M` are at most `1/k` for `k ≥ 1`. -/
lemma sum_Icc_succ_inv_sq_le_inv (M k : ℕ) (hk : 1 ≤ k) :
    ∑ a ∈ Finset.Icc (k + 1) M, (1 : ℝ) / (a : ℝ) ^ 2 ≤ 1 / (k : ℝ) := by
  have hIcc : Finset.Icc (k + 1) M = Finset.Ico (k + 1) (M + 1) := by
    ext x; simp [Finset.mem_Icc, Finset.mem_Ico]
  rw [hIcc, Finset.sum_Ico_eq_sum_range]
  have hsub : M + 1 - (k + 1) ≤ M := by omega
  calc ∑ j ∈ Finset.range (M + 1 - (k + 1)), (1 : ℝ) / (((k + 1) + j : ℕ) : ℝ) ^ 2
      ≤ ∑ j ∈ Finset.range M, (1 : ℝ) / (((k + 1) + j : ℕ) : ℝ) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hsub)
          (by intro j _ _; positivity)
    _ = ∑ j ∈ Finset.range M, (1 : ℝ) / ((j + (k + 1) : ℕ) : ℝ) ^ 2 := by
        apply Finset.sum_congr rfl
        intro j _
        rw [Nat.add_comm (k + 1) j]
    _ ≤ 1 / (k : ℝ) := sum_range_inv_sq_shift_le k M hk

/-- **Tail of the square-reciprocal series beyond a real threshold.**  For every `t > 0` and
every `M`, `∑_{1 ≤ a ≤ M, t < a} 1/a² ≤ 2/t`.

Route: if `t < 1`, the index set is contained in `Icc 1 M` and
`∑_{a ∈ Icc 1 M} 1/a² = ∑_{j < M} 1/(j+1)² ≤ 2 ≤ 2/t`
(use `Work.LinnikAreas.Density4.sum_range_inv_succ_sq_le_two`, reindexing `Icc 1 M` ↔ `range M`).
If `1 ≤ t`, put `k = ⌊t⌋₊` (so `1 ≤ k` and `k ≤ t < k+1`): the index set is contained in
`Icc (k+1) M`, and `1/a² ≤ 1/(a-1) - 1/a` telescopes to `1/k - 1/M ≤ 1/k ≤ 2/t`
(the last step since `t < k+1 ≤ 2k`). -/
lemma sum_tail_inv_sq_le (M : ℕ) {t : ℝ} (ht : 0 < t) :
    (∑ a ∈ (Finset.Icc 1 M).filter (fun a : ℕ => t < (a : ℝ)), 1 / (a : ℝ) ^ 2) ≤ 2 / t := by
  by_cases h1 : t < 1
  · have h2t : (2 : ℝ) ≤ 2 / t := by
      have h := div_le_div_of_nonneg_left (show (0 : ℝ) ≤ 2 by norm_num) ht (le_of_lt h1)
      simpa using h
    calc (∑ a ∈ (Finset.Icc 1 M).filter (fun a : ℕ => t < (a : ℝ)), 1 / (a : ℝ) ^ 2)
        ≤ ∑ a ∈ Finset.Icc 1 M, 1 / (a : ℝ) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (by intro a _ _; positivity)
      _ ≤ 2 := sum_Icc_one_inv_sq_le_two M
      _ ≤ 2 / t := h2t
  · have h1' : (1 : ℝ) ≤ t := not_lt.mp h1
    have hk1 : 1 ≤ ⌊t⌋₊ := by
      have hcast : (((1 : ℕ)) : ℝ) ≤ t := by exact_mod_cast h1'
      exact Nat.le_floor hcast
    have hkt : ((⌊t⌋₊ : ℕ) : ℝ) ≤ t := Nat.floor_le (le_of_lt ht)
    have htu : t < ((⌊t⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one t
    have hk1R : (1 : ℝ) ≤ ((⌊t⌋₊ : ℕ) : ℝ) := by exact_mod_cast hk1
    have hkpos : (0 : ℝ) < ((⌊t⌋₊ : ℕ) : ℝ) := by linarith
    have hsub : (Finset.Icc 1 M).filter (fun a : ℕ => t < (a : ℝ)) ⊆
        Finset.Icc (⌊t⌋₊ + 1) M := by
      intro a ha
      simp only [Finset.mem_filter, Finset.mem_Icc] at ha
      obtain ⟨⟨_, haM⟩, hta⟩ := ha
      simp only [Finset.mem_Icc]
      refine ⟨?_, haM⟩
      have hlt : ⌊t⌋₊ < a := by exact_mod_cast (lt_of_le_of_lt hkt hta)
      omega
    have hkey : (1 / ((⌊t⌋₊ : ℕ) : ℝ)) * t ≤ 2 := by
      rw [one_div, inv_mul_eq_div, div_le_iff₀ hkpos]
      linarith
    calc (∑ a ∈ (Finset.Icc 1 M).filter (fun a : ℕ => t < (a : ℝ)), 1 / (a : ℝ) ^ 2)
        ≤ ∑ a ∈ Finset.Icc (⌊t⌋₊ + 1) M, 1 / (a : ℝ) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (by intro a _ _; positivity)
      _ ≤ 1 / ((⌊t⌋₊ : ℕ) : ℝ) := sum_Icc_succ_inv_sq_le_inv M ⌊t⌋₊ hk1
      _ ≤ 2 / t := by
          rw [le_div_iff₀ ht]
          exact hkey

end Work.LinnikAreas.Density4

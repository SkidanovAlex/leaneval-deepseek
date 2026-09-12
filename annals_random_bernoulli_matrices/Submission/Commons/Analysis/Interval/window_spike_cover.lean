import Mathlib
import Submission.Commons.Analysis.Interval.aux_averaging_count
open scoped BigOperators

set_option maxHeartbeats 600000
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace Commons.Analysis.Interval

theorem window_spike_cover {F : ℤ → ℝ} {η : ℝ} {N : ℕ} {c d : ℤ} {C : ℝ}
    (hN1 : 1 ≤ N)
    (hC : ∀ lo : ℤ,
      (((Finset.Icc lo (lo + (N : ℤ) - 1)).filter (fun t : ℤ => η ≤ F t)).card : ℝ) ≤ C)
    (hS : (N : ℝ) ≤ ((Finset.Icc c d).card : ℝ)) :
    ((((Finset.Icc c d).filter (fun t : ℤ => η ≤ F t)).card : ℝ) ≤
      C * ((((Finset.Icc c d).card : ℝ) / (N : ℝ)) + 1)) := by
  classical
  let n : ℕ := N
  let m : ℕ := (Finset.Icc c d).card
  let k : ℕ := m / n + 1
  let spike : ℤ → Prop := fun t => η ≤ F t
  let W : ℕ → Finset ℤ := fun j =>
    Finset.Icc (c + (j : ℤ) * (n : ℤ)) (c + (j : ℤ) * (n : ℤ) + (n : ℤ) - 1)
  let S : Finset ℤ := (Finset.Icc c d).filter spike
  have hn0 : 0 < n := by
    dsimp [n]
    omega
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  have hnn : (n : ℝ) ≠ 0 := ne_of_gt hnR
  -- windows cover [c, d]
  have hcover : ∀ y : ℤ, y ∈ Finset.Icc c d → ∃ j : ℕ, j < k ∧ y ∈ W j := by
    intro y hy
    exact covered_by_windows (n := n) (k := k) (m := m) hn0 (by rfl) (by rfl) hy
  -- S is contained in union of spiky parts of windows
  have hsub : S ⊆ (Finset.range k).biUnion (fun j : ℕ => (W j).filter spike) := by
    intro y hy
    rcases Finset.mem_filter.mp hy with ⟨hyIcc, hyspike⟩
    rcases hcover y hyIcc with ⟨j, hjk, hjy⟩
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hjk,
      Finset.mem_filter.mpr ⟨hjy, hyspike⟩⟩
  have hSleSum :
      (S.card : ℝ) ≤ ∑ j ∈ Finset.range k, (((W j).filter spike).card : ℝ) := by
    have h1 : S.card ≤ ((Finset.range k).biUnion (fun j : ℕ => (W j).filter spike)).card :=
      Finset.card_le_card hsub
    have h2 : ((Finset.range k).biUnion (fun j : ℕ => (W j).filter spike)).card ≤
        ∑ j ∈ Finset.range k, ((W j).filter spike).card := by
      simpa [Finset.sum_attach] using (Finset.card_biUnion_le : _)
    exact_mod_cast (le_trans h1 h2)
  -- each window's spiky count is at most C
  have hper : ∀ j ∈ Finset.range k, (((W j).filter spike).card : ℝ) ≤ C := by
    intro j hj
    simpa [W, n, spike] using hC (c + (j : ℤ) * (N : ℤ))
  have hSumLe : (∑ j ∈ Finset.range k, (((W j).filter spike).card : ℝ)) ≤ (k : ℝ) * C := by
    have hle := Finset.sum_le_sum hper
    rw [Finset.sum_const, nsmul_eq_mul] at hle
    simpa using hle
  -- k * n ≤ m + n
  have hknR : (k : ℝ) * (n : ℝ) ≤ (m : ℝ) + (n : ℝ) := by
    dsimp [k]
    have hdivm : ((m / n : ℕ) : ℝ) * (n : ℝ) ≤ (m : ℝ) := by
      exact_mod_cast (Nat.div_mul_le_self m n)
    have hq : (((m / n + 1 : ℕ) : ℕ) : ℝ) = ((m / n : ℕ) : ℝ) + 1 := by
      simpa using (Nat.cast_add (R := ℝ) (m / n) 1)
    nlinarith
  -- k ≤ m/n + 1 in reals
  have hk_le : (k : ℝ) ≤ (m : ℝ) / (n : ℝ) + 1 := by
    calc
      (k : ℝ) ≤ ((m : ℝ) + (n : ℝ)) / (n : ℝ) := by
        rw [le_div_iff₀ hnR]
        exact hknR
      _ = (m : ℝ) / (n : ℝ) + 1 := by
        field_simp [hnn]
  -- C ≥ 0
  have hC0 : 0 ≤ C := by
    have hle0 := hC 0
    have hnonneg : (0 : ℝ) ≤
        (((Finset.Icc (0 : ℤ) (0 + (N : ℤ) - 1)).filter (fun t : ℤ => η ≤ F t)).card : ℝ) := by
      exact_mod_cast Nat.zero_le _
    linarith
  -- final
  have hfin : (S.card : ℝ) ≤ C * ((m : ℝ) / (n : ℝ) + 1) := by
    calc
      (S.card : ℝ) ≤ ∑ j ∈ Finset.range k, (((W j).filter spike).card : ℝ) := hSleSum
      _ ≤ (k : ℝ) * C := hSumLe
      _ ≤ ((m : ℝ) / (n : ℝ) + 1) * C := mul_le_mul_of_nonneg_right hk_le hC0
      _ = C * ((m : ℝ) / (n : ℝ) + 1) := by ring
  -- reassemble into the original statement
  change (((Finset.Icc c d).filter spike).card : ℝ) ≤ C * ((m : ℝ) / (n : ℝ) + 1)
  simpa [S, m, n] using hfin

end Commons.Analysis.Interval

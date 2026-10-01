import Mathlib

namespace Work.ZeroDensity.Ingham

/-- Reindexing the inner harmonic sum: reflection of `Finset.Ico 1 n` about its midpoint
turns `1 / (n - m)` into `1 / m`. -/
private lemma sum_Ico_oneDiv_sub_eq (n : ℕ) :
    ∑ m ∈ Finset.Ico 1 n, (1 : ℝ) / ((n : ℝ) - (m : ℝ))
      = ∑ m ∈ Finset.Ico 1 n, (1 : ℝ) / (m : ℝ) := by
  have h := Finset.sum_Ico_reflect (fun x : ℕ => (1 : ℝ) / (x : ℝ)) 1
    (m := n) (n := n) (by omega : n ≤ n + 1)
  rw [Nat.add_sub_cancel_left, Nat.add_sub_cancel] at h
  rw [← h]
  refine Finset.sum_congr rfl ?_
  intro m hm
  have hmle : m ≤ n := by have := Finset.mem_Ico.mp hm; omega
  rw [Nat.cast_sub hmle]

theorem innerHarmonicBound (N n : ℕ) (hn : 1 ≤ n) (hnN : n ≤ N) :
    ∑ m ∈ Finset.Ico 1 n, (1 : ℝ) / ((n : ℝ) - (m : ℝ)) ≤ 1 + Real.log (N : ℝ) := by
  rw [sum_Ico_oneDiv_sub_eq n]
  have hle1 : ∑ m ∈ Finset.Ico 1 n, (1 : ℝ) / (m : ℝ)
      ≤ ∑ m ∈ Finset.Icc 1 n, (1 : ℝ) / (m : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.Ico_subset_Icc_self
      (fun i _ _ => by positivity)
  have hle2 : ∑ m ∈ Finset.Icc 1 n, (1 : ℝ) / (m : ℝ) ≤ 1 + Real.log (n : ℝ) := by
    have h := harmonic_le_one_add_log n
    rw [harmonic_eq_sum_Icc] at h
    push_cast at h
    simpa [one_div] using h
  have hlog : Real.log (n : ℝ) ≤ Real.log (N : ℝ) :=
    Real.log_le_log (by exact_mod_cast (show 0 < n by omega)) (by exact_mod_cast hnN)
  linarith

end Work.ZeroDensity.Ingham

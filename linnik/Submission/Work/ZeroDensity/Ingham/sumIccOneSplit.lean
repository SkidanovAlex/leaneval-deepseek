import Mathlib

namespace Work.ZeroDensity.Ingham

theorem sumIccOneSplit (N : ℕ) (hN : 1 ≤ N) (f : ℕ → ℂ) :
    ∑ n ∈ Finset.Icc 1 N, f n = f 1 + ∑ n ∈ Finset.Icc 2 N, f n := by
  have h : Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [h, Finset.sum_insert (by simp [Finset.mem_Icc])]

end Work.ZeroDensity.Ingham

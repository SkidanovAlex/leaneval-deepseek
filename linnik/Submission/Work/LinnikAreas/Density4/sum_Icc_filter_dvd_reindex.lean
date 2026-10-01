import Mathlib

namespace Work.LinnikAreas.Density4

/-- Reindexing a sum over the multiples of `d ≤ N` by writing `m = d*k`: for `d ≥ 1` and any
`φ : ℕ → ℝ`, `Σ_{1 ≤ m ≤ N, d ∣ m} φ m = Σ_{1 ≤ k ≤ N/d} φ (d*k)`. -/
theorem sum_Icc_filter_dvd_reindex (N d : ℕ) (hd : 1 ≤ d) (φ : ℕ → ℝ) :
    (∑ m ∈ (Finset.Icc 1 N).filter (fun m => d ∣ m), φ m)
      = ∑ k ∈ Finset.Icc 1 (N / d), φ (d * k) := by
  classical
  have hdpos : 0 < d := by omega
  have hset : (Finset.Icc 1 N).filter (fun m => d ∣ m)
      = (Finset.Icc 1 (N / d)).image (fun k => d * k) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨hm1, hmN⟩, hdvd⟩
      have hmpos : 0 < m := hm1
      have hdm : d ≤ m := Nat.le_of_dvd hmpos hdvd
      exact ⟨m / d, ⟨(Nat.one_le_div_iff hdpos).mpr hdm, Nat.div_le_div_right hmN⟩,
             Nat.mul_div_cancel' hdvd⟩
    · rintro ⟨k, ⟨hk1, hkN⟩, rfl⟩
      exact ⟨⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)),
              le_trans (Nat.mul_le_mul_left d hkN) (Nat.mul_div_le N d)⟩,
             dvd_mul_right d k⟩
  rw [hset, Finset.sum_image]
  intro x hx y hy hxy
  exact Nat.mul_left_cancel hdpos hxy

end Work.LinnikAreas.Density4

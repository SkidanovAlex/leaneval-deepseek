import Mathlib

namespace Work.LinnikBurgess

/-- Reindexing the sum over multiples of `e` in `[1, N]` as a sum over `s ∈ [1, N / e]`
of the value at `e * s`. -/
theorem sum_filter_dvd_Icc (e N : ℕ) (he : 0 < e) (f : ℕ → ℝ) :
    (∑ c ∈ (Finset.Icc 1 N).filter (fun c => e ∣ c), f c)
      = ∑ s ∈ Finset.Icc 1 (N / e), f (e * s) := by
  refine Finset.sum_bij (fun c _ => c / e) ?_ ?_ ?_ ?_
  · -- membership of `c / e` in `[1, N / e]`
    intro c hc
    rw [Finset.mem_filter, Finset.mem_Icc] at hc
    obtain ⟨⟨hc1, hcN⟩, hedvd⟩ := hc
    have hle : e ≤ c := Nat.le_of_dvd (by omega) hedvd
    rw [Finset.mem_Icc]
    exact ⟨(Nat.le_div_iff_mul_le he).mpr (by simpa using hle),
      Nat.div_le_div_right hcN⟩
  · -- injectivity
    intro c1 hc1 c2 hc2 heq
    rw [Finset.mem_filter] at hc1 hc2
    rw [← Nat.mul_div_cancel' hc1.2, heq, Nat.mul_div_cancel' hc2.2]
  · -- surjectivity
    intro b hb
    rw [Finset.mem_Icc] at hb
    obtain ⟨hb1, hbN⟩ := hb
    refine ⟨e * b, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨Nat.succ_le_of_lt (Nat.mul_pos he (by omega)), by
        calc e * b ≤ e * (N / e) := Nat.mul_le_mul_left e hbN
          _ ≤ N := Nat.mul_div_le N e⟩, dvd_mul_right e b⟩
    · exact Nat.mul_div_right b he
  · -- the summands agree
    intro c hc
    rw [Finset.mem_filter] at hc
    rw [Nat.mul_div_cancel' hc.2]

end Work.LinnikBurgess

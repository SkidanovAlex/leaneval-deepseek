import Mathlib

namespace Work.LinnikAreas

theorem hbCount (N d E : ℕ) (hd : 0 < d) (hE : N / d ≤ E) :
    ((N / d : ℕ) : ℂ) = ∑ e ∈ Finset.Icc 1 E, (if d * e ≤ N then (1 : ℂ) else 0) := by
  have hset : (Finset.Icc 1 E).filter (fun e => d * e ≤ N) = Finset.Icc 1 (N / d) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h1, _⟩, hde⟩
      refine ⟨h1, ?_⟩
      rw [Nat.le_div_iff_mul_le hd, Nat.mul_comm e d]
      exact hde
    · rintro ⟨h1, h2⟩
      refine ⟨⟨h1, h2.trans hE⟩, ?_⟩
      rw [Nat.le_div_iff_mul_le hd] at h2
      rw [Nat.mul_comm d e]
      exact h2
  rw [Finset.sum_boole, hset, Nat.card_Icc]
  simp

end Work.LinnikAreas

import Mathlib

namespace Work.FIArea2

theorem sum_Icc_int_eq_sum_Ico_nat (h : ℤ → ℝ) (a b : ℕ) :
    (∑ u ∈ Finset.Icc (a : ℤ) (b : ℤ), h u) = ∑ k ∈ Finset.Ico a (b + 1), h (k : ℤ) := by
  symm
  refine Finset.sum_bij (fun k _ => (k : ℤ)) ?_ ?_ ?_ ?_
  · intro k hk
    rw [Finset.mem_Ico] at hk
    rw [Finset.mem_Icc]
    refine ⟨?_, ?_⟩
    · exact_mod_cast hk.1
    · have hkb : k ≤ b := by omega
      exact_mod_cast hkb
  · intro k₁ _ k₂ _ heq
    exact Int.ofNat_injective heq
  · intro u hu
    rw [Finset.mem_Icc] at hu
    have h0 : (0 : ℤ) ≤ u := le_trans (Int.natCast_nonneg a) hu.1
    refine ⟨u.toNat, ?_, Int.toNat_of_nonneg h0⟩
    rw [Finset.mem_Ico]
    refine ⟨?_, ?_⟩
    · rw [Int.le_toNat h0]; exact hu.1
    · have hupper : u.toNat ≤ b := by rw [Int.toNat_le]; exact hu.2
      omega
  · intro k _
    rfl

end Work.FIArea2

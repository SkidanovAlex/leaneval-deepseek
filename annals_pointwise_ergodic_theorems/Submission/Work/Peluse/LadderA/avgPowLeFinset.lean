import Mathlib

namespace Work.Peluse.LadderA

theorem avgPowLeFinset {α : Type} (s : Finset α) (X : α → ℝ) (h0 : ∀ a, 0 ≤ X a)
    (hs : s.Nonempty) {N : ℕ} (hN : 1 ≤ N) :
    ((s.card : ℝ)⁻¹ * ∑ a ∈ s, X a) ^ N ≤ (s.card : ℝ)⁻¹ * ∑ a ∈ s, (X a) ^ N := by
  have hcard : (s.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr hs)
  have hw : ∀ a ∈ s, 0 ≤ (s.card : ℝ)⁻¹ := fun a _ => inv_nonneg.mpr (Nat.cast_nonneg _)
  have hwsum : ∑ a ∈ s, (s.card : ℝ)⁻¹ = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_inv_cancel₀ hcard]
  have h : (∑ a ∈ s, (s.card : ℝ)⁻¹ * X a) ^ (N : ℝ) ≤
      ∑ a ∈ s, (s.card : ℝ)⁻¹ * X a ^ (N : ℝ) :=
    Real.rpow_arith_mean_le_arith_mean_rpow s (fun _ => (s.card : ℝ)⁻¹) X hw hwsum
      (fun a _ => h0 a) (by exact_mod_cast hN)
  simp only [Real.rpow_natCast] at h
  simpa only [Finset.mul_sum] using h

end Work.Peluse.LadderA

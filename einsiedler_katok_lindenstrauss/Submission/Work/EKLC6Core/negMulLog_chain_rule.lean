import Mathlib

namespace Work.EKLC6Core

/-- Per-term identity behind the chain rule: for `b > 0` and `c ≥ 0`,
`b * negMulLog (b⁻¹ * c) = -c * log c + c * log b`. -/
private lemma mul_negMulLog_inv_mul {b c : ℝ} (hb : 0 < b) (hc : 0 ≤ c) :
    b * Real.negMulLog (b⁻¹ * c) = -c * Real.log c + c * Real.log b := by
  rcases eq_or_lt_of_le hc with h | h
  · subst h; simp [Real.negMulLog]
  · have hbne : b ≠ 0 := ne_of_gt hb
    have hcne : c ≠ 0 := ne_of_gt h
    have hbc : Real.log (b⁻¹ * c) = -Real.log b + Real.log c := by
      rw [Real.log_mul (inv_ne_zero hbne) hcne, Real.log_inv]
    rw [Real.negMulLog, hbc]
    field_simp
    ring

theorem negMulLog_chain_rule {ι : Type*} [Fintype ι] (b : ℝ) (c : ι → ℝ)
    (hc : ∀ i, 0 ≤ c i) (hb : b = ∑ i, c i) :
    b * ∑ i, Real.negMulLog (b⁻¹ * c i) = ∑ i, Real.negMulLog (c i) - Real.negMulLog b := by
  have hb0 : 0 ≤ b := by rw [hb]; exact Finset.sum_nonneg (fun i _ => hc i)
  rcases eq_or_lt_of_le hb0 with hbzero | hbpos
  · subst hbzero
    have hci : ∀ i, c i = 0 := by
      intro i
      have hz : (∑ j, c j) = 0 := hb.symm
      have hle : c i ≤ ∑ j, c j :=
        Finset.single_le_sum (fun j _ => hc j) (Finset.mem_univ i)
      exact le_antisymm (by rw [hz] at hle; exact hle) (hc i)
    simp [hci, Real.negMulLog_zero]
  · have hsum : ∑ i, (-c i * Real.log (c i) + c i * Real.log b)
        = ∑ i, Real.negMulLog (c i) - Real.negMulLog b := by
      have hterm : ∑ i, (-c i * Real.log (c i)) = ∑ i, Real.negMulLog (c i) :=
        Finset.sum_congr rfl (fun i _ => by rw [Real.negMulLog])
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, hterm, ← hb, Real.negMulLog]
      ring
    calc b * ∑ i, Real.negMulLog (b⁻¹ * c i)
        = ∑ i, b * Real.negMulLog (b⁻¹ * c i) := by rw [Finset.mul_sum]
      _ = ∑ i, (-c i * Real.log (c i) + c i * Real.log b) :=
            Finset.sum_congr rfl (fun i _ => mul_negMulLog_inv_mul hbpos (hc i))
      _ = ∑ i, Real.negMulLog (c i) - Real.negMulLog b := hsum

end Work.EKLC6Core

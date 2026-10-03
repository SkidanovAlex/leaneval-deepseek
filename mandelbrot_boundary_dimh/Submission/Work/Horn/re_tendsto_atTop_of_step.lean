import Mathlib

namespace Work.Horn

/-- If the real parts of a sequence of complex numbers increase by at least a fixed
positive amount `c` from some index `N` onwards, their real parts are unbounded above. -/
theorem re_tendsto_atTop_of_step {v : ℕ → ℂ} {N : ℕ} {c B : ℝ} (hc : 0 < c)
    (hstep : ∀ n : ℕ, N ≤ n → (v n).re + c ≤ (v (n + 1)).re) :
    ∃ n : ℕ, B < (v n).re := by
  have hmono : ∀ k : ℕ, (v N).re + (k : ℝ) * c ≤ (v (N + k)).re := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h1 : (v (N + k)).re + c ≤ (v (N + k + 1)).re :=
        hstep (N + k) (Nat.le_add_right N k)
      have h2 : N + (k + 1) = N + k + 1 := by omega
      rw [h2]
      push_cast
      linarith
  obtain ⟨k, hk⟩ := exists_nat_gt ((B - (v N).re) / c)
  refine ⟨N + k, ?_⟩
  have h := hmono k
  have hk' : (B - (v N).re) / c * c < (k : ℝ) * c :=
    mul_lt_mul_of_pos_right hk hc
  rw [div_mul_cancel₀ _ (ne_of_gt hc)] at hk'
  linarith

end Work.Horn

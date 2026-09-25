import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

namespace Commons.Analysis.Fourier

theorem schwartz_decay_real (ψ : SchwartzMap ℝ ℂ) (N : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ x : ℝ, ‖ψ x‖ ≤ B * (1 + |x|) ^ (-(N:ℝ)) := by
  refine ⟨max (2 ^ N * ((Finset.Iic ((N, 0) : ℕ × ℕ)).sup
      (fun m' => SchwartzMap.seminorm ℂ m'.1 m'.2) ψ)) 1,
    lt_of_lt_of_le one_pos (le_max_right _ _), fun x => ?_⟩
  have ha : 0 < (1 + |x| : ℝ) := by positivity
  have hbound : (1 + |x|) ^ N * ‖ψ x‖ ≤
      2 ^ N * ((Finset.Iic ((N, 0) : ℕ × ℕ)).sup
        (fun m' => SchwartzMap.seminorm ℂ m'.1 m'.2) ψ) := by
    simpa using SchwartzMap.one_add_le_sup_seminorm_apply
      (m := ((N, 0) : ℕ × ℕ)) (k := N) (n := 0) le_rfl le_rfl ψ x
  have hle : (1 + |x|) ^ N * ‖ψ x‖ ≤
      max (2 ^ N * ((Finset.Iic ((N, 0) : ℕ × ℕ)).sup
        (fun m' => SchwartzMap.seminorm ℂ m'.1 m'.2) ψ)) 1 :=
    hbound.trans (le_max_left _ _)
  have haN : (1 + |x|) ^ (-(N : ℝ)) * (1 + |x|) ^ N = 1 := by
    rw [← Real.rpow_natCast (1 + |x|) N, ← Real.rpow_add ha, neg_add_cancel, Real.rpow_zero]
  calc ‖ψ x‖
      = (1 + |x|) ^ (-(N : ℝ)) * ((1 + |x|) ^ N * ‖ψ x‖) := by
        rw [← mul_assoc, haN, one_mul]
    _ ≤ (1 + |x|) ^ (-(N : ℝ)) *
        max (2 ^ N * ((Finset.Iic ((N, 0) : ℕ × ℕ)).sup
          (fun m' => SchwartzMap.seminorm ℂ m'.1 m'.2) ψ)) 1 :=
        mul_le_mul_of_nonneg_left hle (Real.rpow_nonneg ha.le _)
    _ = max (2 ^ N * ((Finset.Iic ((N, 0) : ℕ × ℕ)).sup
          (fun m' => SchwartzMap.seminorm ℂ m'.1 m'.2) ψ)) 1 *
        (1 + |x|) ^ (-(N : ℝ)) := by rw [mul_comm]

end Commons.Analysis.Fourier
import Mathlib

namespace Work.TMC16Core.Basic

/-- A sequence on `ℤ` with polynomial growth everywhere (`‖u n‖ ≤ C₀ (1 + |n|)`) and
exponential decay `exp (-(c k))` on a half-line `[K, ∞)` decays exponentially on the
whole nonnegative half-line, at the same rate `c`.

The proof takes the cutoff `K₀ = max K 0 ≥ K`; the finitely many indices `0 ≤ k ≤ K₀`
are absorbed into a large constant using the polynomial bound together with the fact
that `exp (-(c k)) ≥ exp (-(c K₀))` there. -/
theorem expDecay_of_eventual {u : ℤ → ℂ} {C₀ c K : ℝ}
    (hc : 0 < c) (hC₀ : ∀ n : ℤ, ‖u n‖ ≤ C₀ * (1 + |(n : ℝ)|))
    (hK : ∀ k : ℤ, K ≤ (k : ℝ) → ‖u k‖ ≤ Real.exp (-(c * (k : ℝ)))) :
    ∃ c' : ℝ, 0 < c' ∧ ∃ C' : ℝ, ∀ k : ℤ, 0 ≤ k → ‖u k‖ ≤ C' * Real.exp (-(c' * (k : ℝ))) := by
  -- `C₀` is nonnegative, from the polynomial bound at `n = 0`.
  have hC₀_nonneg : 0 ≤ C₀ := by
    have h := hC₀ 0
    simp only [Int.cast_zero, abs_zero, add_zero, mul_one] at h
    exact le_trans (norm_nonneg _) h
  -- The cutoff, chosen `≥ 0` and `≥ K`.
  let K₀ : ℝ := max K 0
  have hK₀_ge : K ≤ K₀ := le_max_left K 0
  have hK₀_nonneg : 0 ≤ K₀ := le_max_right K 0
  -- The resulting constant.
  let C' : ℝ := max 1 (C₀ * (1 + K₀) * Real.exp (c * K₀))
  refine ⟨c, hc, C', ?_⟩
  intro k hk
  have hk_real : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  rcases lt_or_ge (k : ℝ) K with hklt | hkle
  · -- Finite range `0 ≤ k < K`: use the polynomial bound and monotonicity of `exp`.
    have hkk₀ : (k : ℝ) ≤ K₀ := le_trans (le_of_lt hklt) hK₀_ge
    have hpoly : ‖u k‖ ≤ C₀ * (1 + (k : ℝ)) := by
      have h := hC₀ k
      rwa [abs_of_nonneg hk_real] at h
    have hstep1 : C₀ * (1 + (k : ℝ)) ≤ C₀ * (1 + K₀) :=
      mul_le_mul_of_nonneg_left (by linarith) hC₀_nonneg
    -- The exponential factor at `k` dominates the one at the cutoff `K₀`.
    have hGG₀ : Real.exp (-(c * K₀)) ≤ Real.exp (-(c * (k : ℝ))) := by
      apply Real.exp_le_exp.mpr
      have hmul : c * (k : ℝ) ≤ c * K₀ := mul_le_mul_of_nonneg_left hkk₀ (le_of_lt hc)
      linarith
    have hP_nonneg : 0 ≤ C₀ * (1 + K₀) * Real.exp (c * K₀) :=
      mul_nonneg (mul_nonneg hC₀_nonneg (by linarith)) (le_of_lt (Real.exp_pos _))
    have hPle : C₀ * (1 + K₀) * Real.exp (c * K₀) ≤ C' := le_max_right 1 _
    have hPG₀ : (C₀ * (1 + K₀) * Real.exp (c * K₀)) * Real.exp (-(c * K₀))
        = C₀ * (1 + K₀) := by
      rw [show C₀ * (1 + K₀) * Real.exp (c * K₀) * Real.exp (-(c * K₀))
            = C₀ * (1 + K₀) * (Real.exp (c * K₀) * Real.exp (-(c * K₀))) by ring]
      rw [← Real.exp_add, show c * K₀ + -(c * K₀) = 0 by ring, Real.exp_zero, mul_one]
    have h2 : (C₀ * (1 + K₀) * Real.exp (c * K₀)) * Real.exp (-(c * K₀))
        ≤ (C₀ * (1 + K₀) * Real.exp (c * K₀)) * Real.exp (-(c * (k : ℝ))) :=
      mul_le_mul_of_nonneg_left hGG₀ hP_nonneg
    have h1 : (C₀ * (1 + K₀) * Real.exp (c * K₀)) * Real.exp (-(c * (k : ℝ)))
        ≤ C' * Real.exp (-(c * (k : ℝ))) :=
      mul_le_mul_of_nonneg_right hPle (le_of_lt (Real.exp_pos _))
    have hstep2 : C₀ * (1 + K₀) ≤ C' * Real.exp (-(c * (k : ℝ))) := by
      have h := le_trans h2 h1
      rwa [hPG₀] at h
    exact le_trans hpoly (le_trans hstep1 hstep2)
  · -- Tail `k ≥ K`: apply the hypothesis `hK`, and use `1 ≤ C'`.
    have h1 := hK k hkle
    have hG : 0 ≤ Real.exp (-(c * (k : ℝ))) := le_of_lt (Real.exp_pos _)
    have hC'1 : 1 ≤ C' := le_max_left 1 (C₀ * (1 + K₀) * Real.exp (c * K₀))
    calc ‖u k‖ ≤ Real.exp (-(c * (k : ℝ))) := h1
      _ = 1 * Real.exp (-(c * (k : ℝ))) := (one_mul _).symm
      _ ≤ C' * Real.exp (-(c * (k : ℝ))) := mul_le_mul_of_nonneg_right hC'1 hG

end Work.TMC16Core.Basic

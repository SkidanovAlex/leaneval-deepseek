import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-- **The elementary moment integral.**  For `k ≥ 1`, `∫_ℝ (1 + |t|)^{-2k} dt ≤ 4`.

Indeed `(1+|t|)^{-2k} ≤ (1+|t|)^{-2}` and `∫_ℝ (1+|t|)^{-2}dt = 2∫_0^∞ (1+t)^{-2}dt = 2`.
This is the factor that converts the pointwise decay `π₀(P)/(1+|t|)` of the principal
`[P,2P]` prime sum into the `1/N`-decay of the N4 count. -/
theorem n4_moment_integral (k : ℕ) (hk : 1 ≤ k) :
    ∫ t : ℝ, (((1 + |t|) ^ (2 * k) : ℝ))⁻¹ ≤ 4 := by
  have h2k : 2 ≤ 2 * k := by omega
  -- Pointwise domination by the integrable Cauchy kernel `(1 + t²)⁻¹`.
  have hpt : ∀ t : ℝ, ((1 + |t|) ^ (2 * k))⁻¹ ≤ (1 + t ^ 2)⁻¹ := by
    intro t
    have hb1 : 0 < 1 + t ^ 2 := by positivity
    have hb : 1 + t ^ 2 ≤ (1 + |t|) ^ (2 * k) := by
      have h1 : 1 + t ^ 2 ≤ (1 + |t|) ^ 2 := by
        rw [add_sq]
        nlinarith [sq_abs t, abs_nonneg t]
      have h2 : (1 + |t|) ^ 2 ≤ (1 + |t|) ^ (2 * k) :=
        pow_le_pow_right₀ (by linarith [abs_nonneg t]) h2k
      linarith
    simpa only [one_div] using one_div_le_one_div_of_le hb1 hb
  calc ∫ t : ℝ, ((1 + |t|) ^ (2 * k))⁻¹
      ≤ ∫ t : ℝ, (1 + t ^ 2)⁻¹ :=
        MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall (fun t => by positivity))
          integrable_inv_one_add_sq
          (Filter.Eventually.of_forall hpt)
    _ = Real.pi := integral_univ_inv_one_add_sq
    _ ≤ 4 := le_of_lt Real.pi_lt_four

end Work.BMF

import Mathlib
import Submission.Work.BourgainPlan.Oscillation.lacunary_defs
import Submission.Work.BourgainPlan.Oscillation.lacScale_error_tsum_le

/-!
# The lacunary radius family drops a dyadic level every `M` steps

Bourgain's oscillation inequality is stated along the lacunary scales `N_i = ⌊ρ ^ i⌋` (`ρ > 1`),
and its "half-shell" counting step (`nbrhd_window_count`) needs the elementary input that the
corresponding *radii* `r_i = (N_i ^ d)⁻¹` (with `d = P.natDegree ≥ 2`, so that doubling the scale
more than halves the radius) fall one dyadic level `2 ^ (-(j+1)) ↦ 2 ^ (-(j+2))` after a *bounded*
number `M` of steps — uniformly in `j`:

  `(N_t ^ d)⁻¹ ≤ 2 ^ (-(j+1))  ⟹  (N_{t+M} ^ d)⁻¹ ≤ 2 ^ (-(j+2))`.

The only input is the geometric growth of the scale. If `ρ ^ M ≥ 4`, then

  `2 * ⌊ρ ^ t⌋ ≤ ⌊ρ ^ (t + M)⌋`   (`two_mul_lacScale_le_add`),

because `2⌊ρ^t⌋ ≤ 4⌊ρ^t⌋ ≤ 4ρ^t ≤ ρ^{t+M}` (using `⌊ρ^t⌋ ≥ 1` and `⌊ρ^t⌋ ≤ ρ^t`).
Hence `N_{t+M} ^ d ≥ (2 N_t) ^ d ≥ 2 ^ d N_t ^ d ≥ 4 N_t ^ d`, and passing to inverses turns the
hypothesis `(N_t^d)⁻¹ ≤ 2^{-(j+1)}` into `2^{j+1} ≤ N_t^d`, so that
`2^{j+2} = 2 · 2^{j+1} ≤ 4 N_t^d ≤ N_{t+M}^d`, which is the conclusion.
-/

namespace Work.BourgainPlan.Oscillation

open Finset

noncomputable section

/-- **Geometric doubling of the lacunary scale.** If `ρ ^ M ≥ 4` then `M` steps of the lacunary
sequence at least double the scale `⌊ρ ^ t⌋`. -/
lemma two_mul_lacScale_le_add (ρ : ℝ) (hρ : 1 < ρ) {M : ℕ} (hM : (4 : ℝ) ≤ ρ ^ M) (t : ℕ) :
    2 * lacScale ρ t ≤ lacScale ρ (t + M) := by
  have hρ0 : 0 < ρ := lt_trans zero_lt_one hρ
  have hN1 : (1 : ℝ) ≤ (lacScale ρ t : ℝ) := by
    exact_mod_cast one_le_lacScale ρ hρ.le t
  have hNle : (lacScale ρ t : ℝ) ≤ ρ ^ t := lacScale_le_pow ρ hρ0.le t
  have hpow : ((2 * lacScale ρ t : ℕ) : ℝ) ≤ ρ ^ (t + M) := by
    rw [pow_add]
    calc ((2 * lacScale ρ t : ℕ) : ℝ) = 2 * (lacScale ρ t : ℝ) := by push_cast; ring
      _ ≤ 4 * (lacScale ρ t : ℝ) := by linarith
      _ ≤ 4 * ρ ^ t := by linarith
      _ ≤ ρ ^ M * ρ ^ t := mul_le_mul_of_nonneg_right hM (pow_nonneg hρ0.le t)
      _ = ρ ^ t * ρ ^ M := by ring
  rw [lacScale]
  exact Nat.le_floor hpow

theorem lacScale_radii_window_count (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (ρ : ℝ)
    (hρ : 1 < ρ) :
    ∃ M : ℕ, ∀ (j t : ℕ),
      (Work.BourgainPlan.Oscillation.polyDilN P (Work.BourgainPlan.Oscillation.lacScale ρ t))⁻¹
          ≤ (2 : ℝ) ^ (-(j : ℝ) - 1) →
      (Work.BourgainPlan.Oscillation.polyDilN P
          (Work.BourgainPlan.Oscillation.lacScale ρ (t + M)))⁻¹
        ≤ (2 : ℝ) ^ (-(j : ℝ) - 2) := by
  obtain ⟨M, hM⟩ := pow_unbounded_of_one_lt (4 : ℝ) hρ
  have hM4 : (4 : ℝ) ≤ ρ ^ M := le_of_lt hM
  refine ⟨M, ?_⟩
  intro j t h
  -- positivity of the two dilations
  have hNt1 : (1 : ℝ) ≤ (lacScale ρ t : ℝ) := by
    exact_mod_cast one_le_lacScale ρ hρ.le t
  have hNM1 : (1 : ℝ) ≤ (lacScale ρ (t + M) : ℝ) := by
    exact_mod_cast one_le_lacScale ρ hρ.le (t + M)
  have ha_pos : 0 < polyDilN P (lacScale ρ t) := by
    rw [polyDilN]; positivity
  have hb_pos : 0 < polyDilN P (lacScale ρ (t + M)) := by
    rw [polyDilN]; positivity
  -- the scale at least doubles every `M` steps
  have hNM2 : 2 * lacScale ρ t ≤ lacScale ρ (t + M) := two_mul_lacScale_le_add ρ hρ hM4 t
  have hle2 : 2 * (lacScale ρ t : ℝ) ≤ (lacScale ρ (t + M) : ℝ) := by exact_mod_cast hNM2
  have h2d : (4 : ℝ) ≤ (2 : ℝ) ^ P.natDegree := by
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ P.natDegree := pow_le_pow_right₀ (by norm_num) hd
  -- hence the dilation at least quadruples
  have hle_ab : 4 * polyDilN P (lacScale ρ t) ≤ polyDilN P (lacScale ρ (t + M)) := by
    have hpos : (0 : ℝ) ≤ (lacScale ρ t : ℝ) ^ P.natDegree := by positivity
    calc 4 * polyDilN P (lacScale ρ t)
        = 4 * (lacScale ρ t : ℝ) ^ P.natDegree := by rw [polyDilN]
      _ ≤ (2 : ℝ) ^ P.natDegree * (lacScale ρ t : ℝ) ^ P.natDegree :=
          mul_le_mul_of_nonneg_right h2d hpos
      _ = (2 * (lacScale ρ t : ℝ)) ^ P.natDegree := by rw [mul_pow]
      _ ≤ (lacScale ρ (t + M) : ℝ) ^ P.natDegree :=
          pow_le_pow_left₀ (by positivity) hle2 P.natDegree
      _ = polyDilN P (lacScale ρ (t + M)) := by rw [polyDilN]
  -- the hypothesis, with the exponent rewritten
  have hR1 : (2 : ℝ) ^ (-(j : ℝ) - 1) = ((2 : ℝ) ^ ((j : ℝ) + 1))⁻¹ := by
    rw [show -(j : ℝ) - 1 = -((j : ℝ) + 1) by ring, Real.rpow_neg (by norm_num)]
  have h2j1pos : (0 : ℝ) < (2 : ℝ) ^ ((j : ℝ) + 1) := Real.rpow_pos_of_pos (by norm_num) _
  have hle_a : (2 : ℝ) ^ ((j : ℝ) + 1) ≤ polyDilN P (lacScale ρ t) := by
    rw [hR1] at h
    exact (inv_le_inv₀ ha_pos h2j1pos).mp h
  have hle_b : (2 : ℝ) ^ ((j : ℝ) + 2) ≤ polyDilN P (lacScale ρ (t + M)) := by
    have h3 : (2 : ℝ) ^ ((j : ℝ) + 2) = (2 : ℝ) ^ ((j : ℝ) + 1) * 2 := by
      rw [show (j : ℝ) + 2 = ((j : ℝ) + 1) + 1 by ring, Real.rpow_add (by norm_num),
        Real.rpow_one]
    rw [h3]
    linarith [hle_a, hle_ab]
  have hR2 : (2 : ℝ) ^ (-(j : ℝ) - 2) = ((2 : ℝ) ^ ((j : ℝ) + 2))⁻¹ := by
    rw [show -(j : ℝ) - 2 = -((j : ℝ) + 2) by ring, Real.rpow_neg (by norm_num)]
  rw [hR2]
  exact (inv_le_inv₀ hb_pos (Real.rpow_pos_of_pos (by norm_num) _)).mpr hle_b

end

end Work.BourgainPlan.Oscillation

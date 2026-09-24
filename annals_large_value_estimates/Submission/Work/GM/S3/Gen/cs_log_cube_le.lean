import Mathlib

namespace Work.GM.S3.Gen

/-- For every fixed `A > 0`, eventually `A * (1 + log N)^3 ≤ N^{0.3}`. -/
theorem cs_log_cube_le (A : ℝ) (hA : 0 < A) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      A * (1 + Real.log (N : ℝ)) ^ 3 ≤ (N : ℝ) ^ (0.3 : ℝ) := by
  let M : ℝ := max 1 ((9261 * A) ^ ((0.15 : ℝ)⁻¹))
  refine ⟨⌈M⌉₊, ?_⟩
  intro N hN
  set x : ℝ := (N : ℝ) with hx
  have hcast : ((⌈M⌉₊ : ℕ) : ℝ) ≤ x := by
    rw [hx]; exact_mod_cast hN
  have hmax : M ≤ x := le_trans (Nat.le_ceil M) hcast
  have hx1 : (1 : ℝ) ≤ x := le_trans (le_max_left _ _) hmax
  have hxpos : 0 < x := lt_of_lt_of_le one_pos hx1
  have hxnn : 0 ≤ x := le_of_lt hxpos
  have hXle : (9261 * A) ^ ((0.15 : ℝ)⁻¹) ≤ x := le_trans (le_max_right _ _) hmax
  have hApos : 0 < 9261 * A := by positivity
  have hXval : ((9261 * A) ^ ((0.15 : ℝ)⁻¹)) ^ (0.15 : ℝ) = 9261 * A := by
    rw [← Real.rpow_mul (le_of_lt hApos) ((0.15 : ℝ)⁻¹) (0.15 : ℝ)]
    rw [show (0.15 : ℝ)⁻¹ * 0.15 = 1 by norm_num, Real.rpow_one]
  have hb : 9261 * A ≤ x ^ (0.15 : ℝ) := by
    have hle := Real.rpow_le_rpow
      (le_of_lt (Real.rpow_pos_of_pos hApos ((0.15 : ℝ)⁻¹))) hXle (by norm_num : (0 : ℝ) ≤ 0.15)
    rwa [hXval] at hle
  have hlog : Real.log x ≤ x ^ (0.05 : ℝ) / (0.05 : ℝ) :=
    Real.log_le_rpow_div hxnn (by norm_num)
  have hx05 : (1 : ℝ) ≤ x ^ (0.05 : ℝ) := Real.one_le_rpow hx1 (by norm_num)
  have hdiv : x ^ (0.05 : ℝ) / (0.05 : ℝ) = 20 * x ^ (0.05 : ℝ) := by
    rw [div_eq_mul_inv, show (0.05 : ℝ)⁻¹ = 20 by norm_num]; ring
  have hsum : 1 + Real.log x ≤ 21 * x ^ (0.05 : ℝ) := by
    have h1 : 1 + Real.log x ≤ 1 + x ^ (0.05 : ℝ) / (0.05 : ℝ) := by linarith [hlog]
    rw [hdiv] at h1
    have h2 : 1 + 20 * x ^ (0.05 : ℝ) ≤ 21 * x ^ (0.05 : ℝ) := by nlinarith [hx05]
    linarith
  have h1L : 0 ≤ 1 + Real.log x := by
    have := Real.log_nonneg hx1; linarith
  have hkey : (21 * x ^ (0.05 : ℝ)) ^ 3 = 9261 * x ^ (0.15 : ℝ) := by
    rw [mul_pow]
    have h3rpow : (x ^ (0.05 : ℝ)) ^ (3 : ℝ) = x ^ (0.15 : ℝ) := by
      rw [← Real.rpow_mul hxnn (0.05 : ℝ) (3 : ℝ)]
      rw [show (0.05 : ℝ) * 3 = 0.15 by norm_num]
    have h3 : (x ^ (0.05 : ℝ)) ^ 3 = x ^ (0.15 : ℝ) := by
      rw [← Real.rpow_natCast (x ^ (0.05 : ℝ)) 3]
      exact h3rpow
    rw [h3]; norm_num
  have hcube : (1 + Real.log x) ^ 3 ≤ 9261 * x ^ (0.15 : ℝ) := by
    have h := pow_le_pow_left₀ h1L hsum 3
    rwa [hkey] at h
  have hfin : A * (1 + Real.log x) ^ 3 ≤ x ^ (0.3 : ℝ) := by
    have hx15pos : 0 < x ^ (0.15 : ℝ) := Real.rpow_pos_of_pos hxpos _
    have hmul : (9261 * A) * x ^ (0.15 : ℝ) ≤ x ^ (0.15 : ℝ) * x ^ (0.15 : ℝ) :=
      mul_le_mul_of_nonneg_right hb (le_of_lt hx15pos)
    have hprod : x ^ (0.15 : ℝ) * x ^ (0.15 : ℝ) = x ^ (0.3 : ℝ) := by
      rw [← Real.rpow_add hxpos (0.15 : ℝ) (0.15 : ℝ)]
      rw [show (0.15 : ℝ) + 0.15 = 0.3 by norm_num]
    calc A * (1 + Real.log x) ^ 3
        ≤ A * (9261 * x ^ (0.15 : ℝ)) :=
          mul_le_mul_of_nonneg_left hcube (le_of_lt hA)
      _ = (9261 * A) * x ^ (0.15 : ℝ) := by ring
      _ ≤ x ^ (0.15 : ℝ) * x ^ (0.15 : ℝ) := hmul
      _ = x ^ (0.3 : ℝ) := hprod
  exact hfin

end Work.GM.S3.Gen

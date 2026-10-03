import Mathlib
import Submission.Work.FIArea7.exists_squareWave_fourier
import Submission.Work.FIArea7.finset_sum_coeff_le

namespace Work.FIArea7

open MeasureTheory intervalIntegral Filter
open scoped Topology BigOperators

noncomputable section

/-- **Friedlander–Iwaniec (20.17)–(20.19)**, with the derivative bound `M` given explicitly.
The Fourier coefficients `ĉ` of the smoothed square wave `t(α) = sign(cos α)` form an
`ℓ¹`-sequence bounded by `(7M+1)·log(2R)`, with the individual bounds `‖ĉ k‖ ≤ M/|k|` and
`‖ĉ k‖ ≤ 3MR/(2k²)`, and on the arc `|cos α| ≥ 1/R` the series sums to `sign(cos α)`. -/
theorem sqWaveCoeffExists (M : ℝ) (hM0 : 0 ≤ M)
    (hM1 : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ M)
    (hM2 : ∀ x : ℝ, |deriv (deriv Real.smoothTransition) x| ≤ M)
    (R : ℕ) (hR : 2 ≤ R) :
    ∃ ĉ : ℤ → ℂ,
      (∀ s : Finset ℤ, ∑ k ∈ s, ‖ĉ k‖ ≤ (7 * M + 1) * Real.log (2 * (R : ℝ))) ∧
      (∀ k : ℤ, k ≠ 0 → ‖ĉ k‖ ≤ M / |(k : ℝ)|) ∧
      (∀ k : ℤ, k ≠ 0 → ‖ĉ k‖ ≤ 3 * M * (R : ℝ) / (2 * (k : ℝ) ^ 2)) ∧
      (∀ z : ℂ, ‖z‖ = 1 → (1 : ℝ) / (R : ℝ) ≤ |z.re| →
        HasSum (fun k : ℤ => ĉ k * z ^ k) (if 0 < z.re then 1 else -1)) := by
  set β : ℝ := 1 / (R : ℝ) with hβdef
  have hβ : 0 < β := by rw [hβdef]; positivity
  have hβ1 : β ≤ 1 := by
    rw [hβdef, div_le_one (by positivity)]; exact_mod_cast (by omega : 1 ≤ R)
  have hconv2 : ∀ n : ℤ,
      3 * M / (2 * β * (n : ℝ) ^ 2) = 3 * M * (R : ℝ) / (2 * (n : ℝ) ^ 2) := by
    intro n; rw [hβdef]; field_simp <;> ring_nf
  refine ⟨fun k => fourierCoeff (sqWaveF β) k, ?_, ?_, ?_, ?_⟩
  · intro s
    exact finset_sum_coeff_le R hR M hM0 (fun k => fourierCoeff (sqWaveF β) k)
      (norm_fourierCoeff_sqWaveF_zero β)
      (fun k hk => fourierCoeff_sqWaveF_bound1 hβ hβ1 hM1 k hk)
      (fun k hk => by
        rw [← hconv2 k]
        exact fourierCoeff_sqWaveF_bound2 hβ hβ1 hM0 hM1 hM2 k hk) s
  · intro k hk
    exact fourierCoeff_sqWaveF_bound1 hβ hβ1 hM1 k hk
  · intro k hk
    rw [← hconv2 k]
    exact fourierCoeff_sqWaveF_bound2 hβ hβ1 hM0 hM1 hM2 k hk
  · intro z hz hzre
    have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz
    have hzw : Complex.exp ((z.arg : ℂ) * Complex.I) = z := by
      have h := Complex.norm_mul_exp_arg_mul_I z
      simpa [hz] using h
    have hfour : ∀ i : ℤ, (fourier i) (z.arg : AddCircle (2 * Real.pi)) = z ^ i := by
      intro i
      rw [fourier_coe_apply]
      have harg : (2 * (Real.pi : ℂ) * Complex.I * (i : ℂ) * (z.arg : ℂ)) / (↑(2 * Real.pi) : ℂ)
          = (i : ℂ) * ((z.arg : ℂ) * Complex.I) := by push_cast; field_simp
      rw [harg, Complex.exp_int_mul, hzw]
    have hval : sqWaveF β (z.arg : AddCircle (2 * Real.pi))
        = (if 0 < z.re then (1 : ℂ) else -1) := by
      rw [sqWaveF_coe]
      change ((sqWave β z.arg : ℝ) : ℂ) = (if 0 < z.re then (1 : ℂ) else -1)
      have hcz : Real.cos z.arg = z.re := by rw [Complex.cos_arg hz0, hz, div_one]
      rcases lt_or_ge (0 : ℝ) z.re with hp | hp
      · have hcos : β ≤ Real.cos z.arg := by
          rw [hcz, hβdef]
          rw [abs_of_pos hp] at hzre
          exact hzre
        rw [sqWave_eq_one hβ hcos, if_pos hp]; simp
      · have hcos : Real.cos z.arg ≤ -β := by
          rw [hcz, hβdef]
          rw [abs_of_nonpos hp] at hzre
          linarith
        rw [sqWave_eq_neg_one hβ hcos, if_neg (not_lt.mpr hp)]; simp
    have hsumm : Summable (fun k : ℤ => ‖fourierCoeff (sqWaveF β) k‖) := by
      have hs1 : Summable (fun k : ℤ => 3 * M * (R : ℝ) / (2 * (k : ℝ) ^ 2)) := by
        have h := (Real.summable_one_div_int_pow (p := 2)).mpr (by norm_num : (1:ℕ) < 2)
        have h2 := h.mul_left (3 * M * (R : ℝ) / 2)
        refine h2.congr (fun k => ?_)
        ring_nf
      have hs2 : Summable (fun k : ℤ => if k = 0 then (1 : ℝ) else 0) :=
        (hasSum_single (0 : ℤ) (fun b hb => by rw [if_neg hb])).summable
      have hb := hs1.add hs2
      apply Summable.of_nonneg_of_le (fun k => norm_nonneg _) _ hb
      intro k
      rcases eq_or_ne k 0 with h | h
      · rw [h, if_pos rfl]
        simpa using norm_fourierCoeff_sqWaveF_zero β
      · rw [if_neg h, add_zero]
        rw [← hconv2 k]
        exact fourierCoeff_sqWaveF_bound2 hβ hβ1 hM0 hM1 hM2 k h
    have hps := has_pointwise_sum_fourier_series_of_summable hsumm.of_norm
      (z.arg : AddCircle (2 * Real.pi))
    rw [← hval]
    convert hps using 1
    ext i
    rw [hfour i, smul_eq_mul]

end

end Work.FIArea7

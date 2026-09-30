import Mathlib
import Submission.Commons.NumberTheory.Mertens.mertens_lower

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.HL

open Finset Real

/-- `Σ_{p ≤ y} (log p)/p ≤ C log y` for `y ≥ 2`, with an absolute constant `C`.
This is Abel summation against Mertens' two-sided estimate
`Commons.NumberTheory.Mertens.primeRecips_sub_loglog_bound`
(`|∑_{p ≤ z} 1/p − log log z| ≤ C0` for `z ≥ 11`, module
`Submission.Commons.NumberTheory.Mertens.primeRecips_sub_loglog_bound`); the part `2 ≤ y ≤ 11` is a
finite check.  The true size is `Σ_{p≤y}(log p)/p = log y + O(1)`, so `C ≥ 2` has slack. -/
theorem sum_log_div_prime_le :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 2 ≤ y →
      (∑ p ∈ (⌊y⌋₊).primesLE, Real.log p / (p : ℝ)) ≤ C * Real.log y := by
  refine ⟨2, by norm_num, ?_⟩
  intro y hy
  have hy0 : (0 : ℝ) < y := by linarith
  have hlogy : Real.log 2 ≤ Real.log y := Real.log_le_log (by norm_num) hy
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2lt1 : Real.log 2 < 1 := lt_trans Real.log_two_lt_d9 (by norm_num)
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  change Commons.NumberTheory.Mertens.logDiv y ≤ 2 * Real.log y
  rw [Commons.NumberTheory.Mertens.logDiv_eq_theta_div_add_integral hy]
  have hA : Chebyshev.theta y / y ≤ Real.log 4 := by
    rw [div_le_iff₀ hy0]
    exact Chebyshev.theta_le_log4_mul_x hy0.le
  have hint_f : IntervalIntegrable (fun t : ℝ => Chebyshev.theta t / (t * t)) MeasureTheory.volume 2 y := by
    have hθ : IntervalIntegrable Chebyshev.theta MeasureTheory.volume 2 y := Chebyshev.theta_mono.intervalIntegrable
    have hg : ContinuousOn (fun t : ℝ => (t * t)⁻¹) (Set.uIcc (2:ℝ) y) := by
      apply ContinuousOn.inv₀
      · fun_prop
      · intro t ht
        have ht2 : (2 : ℝ) ≤ t := (Set.uIcc_of_le hy ▸ ht).1
        positivity
    simpa [div_eq_mul_inv] using hθ.mul_continuousOn hg
  have hint_g : IntervalIntegrable (fun t : ℝ => Real.log 4 * t⁻¹) MeasureTheory.volume 2 y := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.inv₀ continuousOn_id
    intro t ht
    have ht2 : (2 : ℝ) ≤ t := (Set.uIcc_of_le hy ▸ ht).1
    simp only [id_eq]
    intro h
    linarith
  have hB : (∫ t in (2 : ℝ)..y, Chebyshev.theta t / (t * t)) ≤
      Real.log 4 * Real.log (y / 2) := by
    calc (∫ t in (2 : ℝ)..y, Chebyshev.theta t / (t * t))
        ≤ ∫ t in (2 : ℝ)..y, Real.log 4 * t⁻¹ := by
          apply intervalIntegral.integral_mono_on hy hint_f hint_g
          intro t ht
          have ht0 : 0 < t := by linarith [ht.1]
          have hθ : Chebyshev.theta t ≤ Real.log 4 * t :=
            Chebyshev.theta_le_log4_mul_x (le_of_lt ht0)
          calc Chebyshev.theta t / (t * t) ≤ (Real.log 4 * t) / (t * t) :=
                div_le_div_of_nonneg_right hθ (by positivity)
            _ = Real.log 4 * t⁻¹ := by field_simp
      _ = Real.log 4 * (∫ t in (2 : ℝ)..y, t⁻¹) := by
            rw [intervalIntegral.integral_const_mul]
      _ = Real.log 4 * Real.log (y / 2) := by
            rw [integral_inv_of_pos (by norm_num) hy0]
  have hlogy2 : Real.log (y / 2) = Real.log y - Real.log 2 :=
    Real.log_div (by linarith) (by norm_num)
  have hfinal : Real.log 4 + Real.log 4 * Real.log (y / 2) ≤ 2 * Real.log y := by
    rw [hlogy2, hlog4]
    nlinarith [hlogy, hlog2pos, hlog2lt1]
  have hcomb : Chebyshev.theta y / y + (∫ t in (2 : ℝ)..y, Chebyshev.theta t / (t * t)) ≤
      2 * Real.log y := by
    have := add_le_add hA hB
    linarith
  linarith [hcomb]

end Work.BMF.HL

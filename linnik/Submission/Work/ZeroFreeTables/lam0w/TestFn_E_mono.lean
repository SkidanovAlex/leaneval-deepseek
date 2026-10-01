import Mathlib
import Submission.Work.ZeroFreeTables.Engine
import Submission.Work.ZeroFreeTables.TestFn_F_eq_integral

open scoped Real BigOperators
noncomputable section
namespace Work.ZeroFreeTables.lam0w

open Work.ZeroFreeTables

/-- For a test function `T`, the two-sided difference
`E(a,b) = 2 (F(-a) - F(b-a)) = 2 ∫₀^{x₀} e^{at}(1 - e^{-bt}) f t dt` is increasing in both
arguments (`a`, and `b ≥ 0`). -/
theorem TestFn_E_mono (T : TestFn) {a a' b b' : ℝ} (ha : a ≤ a') (hb : b ≤ b') (hb0 : 0 ≤ b) :
    2 * (T.F (-a) - T.F (b - a)) ≤ 2 * (T.F (-a') - T.F (b' - a')) := by
  have huIcc : Set.uIcc (0:ℝ) T.x₀ = Set.Icc 0 T.x₀ := Set.uIcc_of_le T.x₀_pos.le
  have hfcont : ContinuousOn T.f (Set.uIcc (0:ℝ) T.x₀) := by
    rw [huIcc]; exact T.f_cont.mono Set.Icc_subset_Ici_self
  have hIi : ∀ (g : ℝ → ℝ), Continuous g →
      IntervalIntegrable (fun t : ℝ => g t * T.f t) MeasureTheory.volume (0:ℝ) T.x₀ := by
    intro g hg
    exact (hg.continuousOn.mul hfcont).intervalIntegrable
  have hrepr : ∀ z w : ℝ, T.F (-z) - T.F (w - z)
      = ∫ t in (0:ℝ)..T.x₀, Real.exp (z * t) * (1 - Real.exp (-(w * t))) * T.f t := by
    intro z w
    rw [TestFn_F_eq_integral T (-z), TestFn_F_eq_integral T (w - z)]
    have hA : (∫ t in (0:ℝ)..T.x₀, Real.exp (-(-z * t)) * T.f t)
        = ∫ t in (0:ℝ)..T.x₀, Real.exp (z * t) * T.f t :=
      intervalIntegral.integral_congr (fun t _ => by
        show Real.exp (-(-z * t)) * T.f t = Real.exp (z * t) * T.f t
        rw [show -(-z * t) = z * t by ring])
    have hB : (∫ t in (0:ℝ)..T.x₀, Real.exp (-((w - z) * t)) * T.f t)
        = ∫ t in (0:ℝ)..T.x₀, Real.exp (z * t) * Real.exp (-(w * t)) * T.f t :=
      intervalIntegral.integral_congr (fun t _ => by
        show Real.exp (-((w - z) * t)) * T.f t
          = Real.exp (z * t) * Real.exp (-(w * t)) * T.f t
        rw [show -((w - z) * t) = z * t + (-(w * t)) by ring, Real.exp_add])
    rw [hA, hB]
    rw [← intervalIntegral.integral_sub
      (hIi (fun t => Real.exp (z * t)) (by fun_prop))
      (hIi (fun t => Real.exp (z * t) * Real.exp (-(w * t))) (by fun_prop))]
    exact intervalIntegral.integral_congr (fun t _ => by
      show Real.exp (z * t) * T.f t - Real.exp (z * t) * Real.exp (-(w * t)) * T.f t
        = Real.exp (z * t) * (1 - Real.exp (-(w * t))) * T.f t
      ring)
  have hstep1 : (∫ t in (0:ℝ)..T.x₀, Real.exp (a * t) * (1 - Real.exp (-(b * t))) * T.f t)
      ≤ ∫ t in (0:ℝ)..T.x₀, Real.exp (a' * t) * (1 - Real.exp (-(b * t))) * T.f t := by
    apply intervalIntegral.integral_mono_on (le_of_lt T.x₀_pos)
    · exact hIi (fun t => Real.exp (a * t) * (1 - Real.exp (-(b * t)))) (by fun_prop)
    · exact hIi (fun t => Real.exp (a' * t) * (1 - Real.exp (-(b * t)))) (by fun_prop)
    · intro t ht
      have ht0 : 0 ≤ t := ht.1
      have h1 : Real.exp (a * t) ≤ Real.exp (a' * t) := Real.exp_le_exp.mpr (by nlinarith)
      have h2 : (0:ℝ) ≤ 1 - Real.exp (-(b * t)) := by
        have : Real.exp (-(b * t)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
        linarith
      have h3 : (0:ℝ) ≤ T.f t := T.f_nonneg t
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 h2) h3
  have hstep2 : (∫ t in (0:ℝ)..T.x₀, Real.exp (a' * t) * (1 - Real.exp (-(b * t))) * T.f t)
      ≤ ∫ t in (0:ℝ)..T.x₀, Real.exp (a' * t) * (1 - Real.exp (-(b' * t))) * T.f t := by
    apply intervalIntegral.integral_mono_on (le_of_lt T.x₀_pos)
    · exact hIi (fun t => Real.exp (a' * t) * (1 - Real.exp (-(b * t)))) (by fun_prop)
    · exact hIi (fun t => Real.exp (a' * t) * (1 - Real.exp (-(b' * t)))) (by fun_prop)
    · intro t ht
      have ht0 : 0 ≤ t := ht.1
      have h1 : Real.exp (-(b' * t)) ≤ Real.exp (-(b * t)) := Real.exp_le_exp.mpr (by nlinarith)
      have h2 : (0:ℝ) ≤ Real.exp (a' * t) := Real.exp_nonneg _
      have h3 : (0:ℝ) ≤ T.f t := T.f_nonneg t
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) h2) h3
  have hE1 : 2 * (T.F (-a) - T.F (b - a)) ≤ 2 * (T.F (-a') - T.F (b - a')) := by
    rw [hrepr a b, hrepr a' b]
    exact mul_le_mul_of_nonneg_left hstep1 (by norm_num)
  have hE2 : 2 * (T.F (-a') - T.F (b - a')) ≤ 2 * (T.F (-a') - T.F (b' - a')) := by
    rw [hrepr a' b, hrepr a' b']
    exact mul_le_mul_of_nonneg_left hstep2 (by norm_num)
  exact hE1.trans hE2

end Work.ZeroFreeTables.lam0w

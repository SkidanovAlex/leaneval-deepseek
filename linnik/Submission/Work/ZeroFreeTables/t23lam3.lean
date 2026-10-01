import Mathlib
import Submission.Work.ZeroFreeTables.t23Defs

open scoped BigOperators
noncomputable section

namespace Work.ZeroFreeTables

/-! ## The fixed-scale (`λ = 3`) failure, `GlueLam3`

With `λ₀ = a0 ≥ 4` and `λ₁ = a1 < e^{-2a0/3}`, the `F`-expression of HB Lemma 6.3 at the scale
`3` fails.  In normalized form we must show

`(1/15)(G(a0/3) − G((a0−a1)/3)) < 8/9 − CertSlack·(16·3/15)`.

Writing `G(x) = ∫₀² g(u)e^{xu}du` and using `hb72G_sub`,

`G(a0/3) − G((a0−a1)/3) = ∫₀² g(u)e^{a0u/3}(1 − e^{−a1u/3})du`,

and since `0 ≤ g` on `[0,2]`, `1 − e^{−x} ≤ x` and `a1e^{a0u/3} < e^{-2a0/3+a0u/3} = e^{(a0/3)(u-2)}
≤ e^{(4/3)(u-2)}` for `u ≤ 2`, this is at most

`(1/3)∫₀² u·g(u)·e^{(4/3)(u−2)}du < (1/3)·3.3 = 11/10`,

so the left side is `< 11/150 < 8/9 − CertSlack·(16/5)`. -/

/-- The HB Lemma 7.2 density is nonnegative on the integration range:
`g(u) = (2−u)³(4 + 6u + u²)`. -/
theorem hb72g_nonneg_of_mem_Icc (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 2) : 0 ≤ hb72g u := by
  have h1 : 0 ≤ 2 - u := by linarith [hu.2]
  have h2 : 0 ≤ 4 + 6 * u + u ^ 2 := by nlinarith [sq_nonneg u, hu.1]
  have hfac : hb72g u = (2 - u) ^ 3 * (4 + 6 * u + u ^ 2) := by unfold hb72g; ring
  rw [hfac]
  exact mul_nonneg (pow_nonneg h1 3) h2

theorem t23lam3 : Work.ZeroFreeTables.GlueLam3 := by
  intro a0 a1 ha0 ha1pos ha1small hnum
  have hnum' : (∫ u in (0 : ℝ)..2, u * hb72g u * Real.exp ((4 / 3) * (u - 2))) < 3.3 := hnum
  have hA : hb72G (a0 / 3) - hb72G ((a0 - a1) / 3)
      = ∫ u in (0 : ℝ)..2, hb72g u * Real.exp (a0 / 3 * u) * (1 - Real.exp (-(a1 / 3 * u))) := by
    have h := hb72G_sub (a0 / 3) (a1 / 3)
    rw [show (a0 - a1) / 3 = a0 / 3 - a1 / 3 by ring]
    exact h
  have hpoint : ∀ u ∈ Set.Icc (0 : ℝ) 2,
      hb72g u * Real.exp (a0 / 3 * u) * (1 - Real.exp (-(a1 / 3 * u)))
        ≤ (1 / 3) * (u * hb72g u * Real.exp ((4 / 3) * (u - 2))) := by
    intro u hu
    have hu0 : 0 ≤ u := hu.1
    have hu2 : u ≤ 2 := hu.2
    have hg : 0 ≤ hb72g u := hb72g_nonneg_of_mem_Icc u hu
    have hexppos : 0 < Real.exp (a0 / 3 * u) := Real.exp_pos _
    have step1 : 1 - Real.exp (-(a1 / 3 * u)) ≤ a1 / 3 * u := by
      have h := Real.add_one_le_exp (-(a1 / 3 * u))
      linarith
    have hmono : Real.exp (-(2 / 3) * a0) * Real.exp (a0 / 3 * u)
        ≤ Real.exp ((4 / 3) * (u - 2)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [ha0, hu2]
    have hgu : 0 ≤ hb72g u * (u / 3) := mul_nonneg hg (by linarith)
    calc hb72g u * Real.exp (a0 / 3 * u) * (1 - Real.exp (-(a1 / 3 * u)))
        ≤ hb72g u * Real.exp (a0 / 3 * u) * (a1 / 3 * u) :=
          mul_le_mul_of_nonneg_left step1 (mul_nonneg hg hexppos.le)
      _ = (hb72g u * (u / 3)) * (a1 * Real.exp (a0 / 3 * u)) := by ring
      _ ≤ (hb72g u * (u / 3)) * (Real.exp (-(2 / 3) * a0) * Real.exp (a0 / 3 * u)) := by
          apply mul_le_mul_of_nonneg_left _ hgu
          exact mul_le_mul_of_nonneg_right ha1small.le (Real.exp_pos _).le
      _ ≤ (hb72g u * (u / 3)) * Real.exp ((4 / 3) * (u - 2)) :=
          mul_le_mul_of_nonneg_left hmono hgu
      _ = (1 / 3) * (u * hb72g u * Real.exp ((4 / 3) * (u - 2))) := by ring
  have hint_f : IntervalIntegrable
      (fun u : ℝ => hb72g u * Real.exp (a0 / 3 * u) * (1 - Real.exp (-(a1 / 3 * u))))
      MeasureTheory.volume (0 : ℝ) 2 := by
    apply Continuous.intervalIntegrable
    unfold hb72g
    fun_prop
  have hint_h : IntervalIntegrable
      (fun u : ℝ => (1 / 3) * (u * hb72g u * Real.exp ((4 / 3) * (u - 2))))
      MeasureTheory.volume (0 : ℝ) 2 := by
    apply Continuous.intervalIntegrable
    unfold hb72g
    fun_prop
  have hmono_int : (∫ u in (0 : ℝ)..2,
        hb72g u * Real.exp (a0 / 3 * u) * (1 - Real.exp (-(a1 / 3 * u))))
      ≤ ∫ u in (0 : ℝ)..2, (1 / 3) * (u * hb72g u * Real.exp ((4 / 3) * (u - 2))) :=
    intervalIntegral.integral_mono_on (by norm_num) hint_f hint_h hpoint
  have hconst : (∫ u in (0 : ℝ)..2, (1 / 3) * (u * hb72g u * Real.exp ((4 / 3) * (u - 2))))
      = (1 / 3) * ∫ u in (0 : ℝ)..2, u * hb72g u * Real.exp ((4 / 3) * (u - 2)) :=
    intervalIntegral.integral_const_mul (1 / 3) _
  have hlt : (∫ u in (0 : ℝ)..2,
        hb72g u * Real.exp (a0 / 3 * u) * (1 - Real.exp (-(a1 / 3 * u)))) < (1 / 3) * 3.3 := by
    refine lt_of_le_of_lt hmono_int ?_
    rw [hconst]
    exact mul_lt_mul_of_pos_left hnum' (by norm_num)
  have hmain : (1 / 15) * (hb72G (a0 / 3) - hb72G ((a0 - a1) / 3)) < (1 / 15) * ((1 / 3) * 3.3) := by
    rw [hA]
    exact mul_lt_mul_of_pos_left hlt (by norm_num)
  have hnum2 : (1 / 15) * ((1 / 3) * 3.3) < 8 / 9 - CertSlack * (16 * 3 / 15) := by
    unfold CertSlack
    norm_num
  linarith

end Work.ZeroFreeTables

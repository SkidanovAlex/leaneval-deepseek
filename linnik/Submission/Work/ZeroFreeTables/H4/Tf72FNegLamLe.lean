/-
# ZeroFreeTables — `F(-λ₁) ≤ 1147/1000` for HB Lemma 7.2 with λ = 3/4

For HB Lemma 7.2's test function `f = tf72f (3/4)` (supported on `[0, 8/3]`) and every
`0 ≤ λ₁ ≤ 87/250`,

  `∫_0^{8/3} e^{λ₁ t} f(t) dt ≤ 1147/1000`,

i.e. `F(-λ₁) ≤ 1147/1000` for the Laplace transform `F` of `f`.

Route.  On `[0, 8/3]`, `f` is the quintic `hP` (`Tf72FDefs`), `hP ≥ 0` there, and
`λ₁ ≤ 87/250` gives `e^{λ₁ t} ≤ e^{(87/250) t}`, so it suffices to bound
`∫_0^{8/3} e^{(87/250) t} hP t`.  The Taylor bound `expTaylorL`
(`e^{x} ≤ Σ_{j<6} x^j/j! + 7x⁶/(6!·6)` for `x ≤ 1`; here `x = (87/250)t ≤ 696/750 ≤ 1`)
then reduces this to the exact moments `hM j = ∫_0^{8/3} t^j hP t` (`hP_moment`), giving
`Σ_{j<6} (87/250)^j hM j/j! + (87/250)⁶·7/(6!·6)·hM 6 = 876182058751382744/764751434326171875
 = 1.1457082… ≤ 1.147`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.testFn72_defs
import Submission.Work.ZeroFreeTables.H4.Tf72FDefs
import Submission.Work.ZeroFreeTables.H4.expTaylorL

open MeasureTheory intervalIntegral Finset
open scoped Interval
noncomputable section

namespace Work.ZeroFreeTables.H4

/-- **The moments of `hP`**: `∫_0^{8/3} t^j · hP t = hM j` for every `j`, obtained by
expanding `t^j · hP t` and integrating term by term (`integral_pow`). -/
lemma hP_moment (j : ℕ) : ∫ t in (0:ℝ)..(8/3), t^j * hP t = hM j := by
  have key : ∀ t : ℝ, t^j * hP t = (4/5)*t^j - (9/16)*t^(j+2)
      + (27/128)*t^(j+3) - (243/40960)*t^(j+5) := by
    intro t; unfold hP; ring
  rw [show (∫ t in (0:ℝ)..(8/3), t^j * hP t)
      = ∫ t in (0:ℝ)..(8/3), ((4/5)*t^j - (9/16)*t^(j+2)
          + (27/128)*t^(j+3) - (243/40960)*t^(j+5)) from by
    apply intervalIntegral.integral_congr; intro t ht; exact key t]
  rw [intervalIntegral.integral_sub, intervalIntegral.integral_add, intervalIntegral.integral_sub]
  · rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    rw [integral_pow, integral_pow, integral_pow, integral_pow]
    unfold hM; simp; ring
  all_goals exact Continuous.intervalIntegrable (by continuity) 0 (8/3)

/-- The Taylor upper function of `exp` at `x = (87/250)·t` used for the bound:
`Σ_{j<6} x^j/j! + 7x⁶/(6!·6)`. -/
def tayL (t : ℝ) : ℝ :=
  (∑ j ∈ Finset.range 6, ((87/250)*t)^j/(j.factorial:ℝ))
    + ((87/250)*t)^6 * 7 / ((6:ℕ).factorial * 6)

/-- `exp ((87/250)·t) ≤ tayL t` on `[0, 8/3]` (from `expTaylorL`). -/
lemma exp_le_tayL (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 8/3) :
    Real.exp ((87/250)*t) ≤ tayL t := by
  simpa [tayL] using expTaylorL t h0 h1

/-- Integral of the Taylor polynomial of `exp` against `hP`, evaluated via the moments. -/
lemma hIntPS : ∫ t in (0:ℝ)..(8/3), tayL t * hP t
    = (∑ j ∈ Finset.range 6, (87/250)^j * hM j/(j.factorial:ℝ))
        + (87/250)^6 * 7/((6:ℕ).factorial*6) * hM 6 := by
  have h1 : ∀ i ∈ Finset.range 6,
      IntervalIntegrable (fun t : ℝ => ((87/250)*t)^i/(i.factorial:ℝ) * hP t) volume (0:ℝ) (8/3) :=
    fun i _ => Continuous.intervalIntegrable (by simp only [hP]; fun_prop) 0 (8/3)
  have h2 : IntervalIntegrable
      (fun t : ℝ => ((87/250)*t)^6 * 7/((6:ℕ).factorial*6) * hP t) volume (0:ℝ) (8/3) :=
    Continuous.intervalIntegrable (by simp only [hP]; fun_prop) 0 (8/3)
  have hsum : IntervalIntegrable
      (fun t : ℝ => ∑ i ∈ Finset.range 6, ((87/250)*t)^i/(i.factorial:ℝ) * hP t)
      volume (0:ℝ) (8/3) :=
    Continuous.intervalIntegrable (by simp only [hP]; fun_prop) 0 (8/3)
  have hcongr : (∫ t in (0:ℝ)..(8/3), tayL t * hP t)
      = ∫ t in (0:ℝ)..(8/3), (∑ i ∈ Finset.range 6, ((87/250)*t)^i/(i.factorial:ℝ) * hP t)
          + ((87/250)*t)^6 * 7/((6:ℕ).factorial*6) * hP t := by
    apply intervalIntegral.integral_congr
    intro t ht
    simp only [tayL, add_mul, Finset.sum_mul]
  rw [hcongr, intervalIntegral.integral_add hsum h2]
  congr 1
  · rw [intervalIntegral.integral_finsetSum h1]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [show (∫ t in (0:ℝ)..(8/3), ((87/250)*t)^i/(i.factorial:ℝ) * hP t)
        = ∫ t in (0:ℝ)..(8/3), ((87/250)^i/(i.factorial:ℝ)) * (t^i * hP t) from by
      apply intervalIntegral.integral_congr; intro t ht; ring]
    rw [intervalIntegral.integral_const_mul, hP_moment]
    ring
  · rw [show (∫ t in (0:ℝ)..(8/3), ((87/250)*t)^6 * 7/((6:ℕ).factorial*6) * hP t)
        = ∫ t in (0:ℝ)..(8/3), ((87/250)^6 * 7/((6:ℕ).factorial*6)) * (t^6 * hP t) from by
      apply intervalIntegral.integral_congr; intro t ht; ring]
    rw [intervalIntegral.integral_const_mul, hP_moment 6]

theorem Tf72FNegLamLe {lam₁ : ℝ} (h0 : 0 ≤ lam₁) (h1 : lam₁ ≤ 87/250) :
    ∫ t in (0:ℝ)..(8/3), Real.exp (lam₁ * t) * Work.ZeroFreeTables.tf72f (3/4) t ≤ 1147/1000 := by
  have _ : (0:ℝ) ≤ lam₁ := h0
  have hA : ∫ t in (0:ℝ)..(8/3), Real.exp (lam₁*t) * Work.ZeroFreeTables.tf72f (3/4) t
      = ∫ t in (0:ℝ)..(8/3), Real.exp (lam₁*t) * hP t := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Set.Icc (0:ℝ) (8/3) := by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 8/3)] at ht; exact ht
    show Real.exp (lam₁*t) * Work.ZeroFreeTables.tf72f (3/4) t = Real.exp (lam₁*t) * hP t
    rw [tf72f34_eq t ht']
  have hmono : ∫ t in (0:ℝ)..(8/3), Real.exp (lam₁*t)*hP t
      ≤ ∫ t in (0:ℝ)..(8/3), Real.exp ((87/250)*t)*hP t := by
    apply intervalIntegral.integral_mono_on (by norm_num)
    · exact Continuous.intervalIntegrable (by simp only [hP]; fun_prop) 0 (8/3)
    · exact Continuous.intervalIntegrable (by simp only [hP]; fun_prop) 0 (8/3)
    · intro t ht
      have he : Real.exp (lam₁*t) ≤ Real.exp ((87/250)*t) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right h1 ht.1)
      exact mul_le_mul_of_nonneg_right he (hP_nonneg t ht.1 ht.2)
  have hbnd : ∫ t in (0:ℝ)..(8/3), Real.exp ((87/250)*t)*hP t
      ≤ ∫ t in (0:ℝ)..(8/3), tayL t * hP t := by
    apply intervalIntegral.integral_mono_on (by norm_num)
    · exact Continuous.intervalIntegrable (by simp only [hP]; fun_prop) 0 (8/3)
    · exact Continuous.intervalIntegrable (by simp only [tayL, hP]; fun_prop) 0 (8/3)
    · intro t ht
      exact mul_le_mul_of_nonneg_right (exp_le_tayL t ht.1 ht.2) (hP_nonneg t ht.1 ht.2)
  calc ∫ t in (0:ℝ)..(8/3), Real.exp (lam₁*t) * Work.ZeroFreeTables.tf72f (3/4) t
      = ∫ t in (0:ℝ)..(8/3), Real.exp (lam₁*t) * hP t := hA
    _ ≤ ∫ t in (0:ℝ)..(8/3), Real.exp ((87/250)*t)*hP t := hmono
    _ ≤ ∫ t in (0:ℝ)..(8/3), tayL t * hP t := hbnd
    _ = (∑ j ∈ Finset.range 6, (87/250)^j * hM j/(j.factorial:ℝ))
        + (87/250)^6 * 7/((6:ℕ).factorial*6) * hM 6 := hIntPS
    _ ≤ 1147/1000 := by
        simp only [Finset.sum_range_succ, Finset.sum_range_zero]
        norm_num [hM]

end Work.ZeroFreeTables.H4

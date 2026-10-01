/-
# ZeroFreeTables/XY/SupScLe

`Sc λ t ≤ λ·max (Yc t) 0 + Esc λ`.

Write `f = xyFf` (non-negative) and recall

  `Sc λ t = ∫₀^{3/2} sinh(λx) cos(tx) f x dx`,
  `Yc t   = ∫₀^{3/2} x cos(tx) f x dx`,
  `Esc λ  = ∫₀^{3/2} (sinh(λx) - λx) f x dx`.

Pointwise on `[0,3/2]` the integrand of `Sc` splits as
`sinh(λx) cos(tx) f = (sinh(λx)-λx) cos(tx) f + λ·(x cos(tx) f)`,
whose second term integrates to `λ Yc t`; and the first term is `≤ (sinh(λx)-λx) f`
because `sinh(λx) - λx ≥ 0` (for `λ ≥ 0`, `x ≥ 0`), `f ≥ 0` and `cos(tx) ≤ 1`, so its
integral is `≤ Esc λ`.  Hence `Sc λ t ≤ Esc λ + λ Yc t ≤ Esc λ + λ·max (Yc t) 0`
(the last step using `λ ≥ 0`).
-/
import Mathlib
import Submission.Work.ZeroFreeTables.XY.LamPrimeData

open MeasureTheory intervalIntegral
open scoped Classical BigOperators

namespace Work.ZeroFreeTables.XY

theorem SupScLe (lam t : ℝ) (h0 : 0 ≤ lam) :
    Work.ZeroFreeTables.XY.Sc lam t ≤ lam * max (Work.ZeroFreeTables.XY.Yc t) 0 + Work.ZeroFreeTables.XY.Esc lam := by
  -- `f = xyFf` is continuous on `[0,3/2]`
  have hf : ContinuousOn xyFf (Set.Icc (0:ℝ) (3/2)) := by
    rw [xyFf_eq_testFn]
    exact xyT.f_cont.mono (fun x hx => hx.1)
  have h1c : ContinuousOn (fun x : ℝ => (Real.sinh (lam*x) - lam*x) * Real.cos (t*x))
      (Set.Icc (0:ℝ) (3/2)) := by fun_prop
  have hBint : IntervalIntegrable
      (fun x : ℝ => (Real.sinh (lam*x) - lam*x) * Real.cos (t*x) * xyFf x) volume (0:ℝ) (3/2) :=
    ContinuousOn.intervalIntegrable_of_Icc (by norm_num) (h1c.mul hf)
  have hCint : IntervalIntegrable
      (fun x : ℝ => lam * (x * Real.cos (t*x) * xyFf x)) volume (0:ℝ) (3/2) :=
    ContinuousOn.intervalIntegrable_of_Icc (by norm_num) (by
      have h2 : ContinuousOn (fun x : ℝ => x * Real.cos (t*x)) (Set.Icc (0:ℝ) (3/2)) := by fun_prop
      exact continuousOn_const.mul (h2.mul hf))
  have h2c : ContinuousOn (fun x : ℝ => Real.sinh (lam*x) - lam*x) (Set.Icc (0:ℝ) (3/2)) := by fun_prop
  have hDint : IntervalIntegrable
      (fun x : ℝ => (Real.sinh (lam*x) - lam*x) * xyFf x) volume (0:ℝ) (3/2) :=
    ContinuousOn.intervalIntegrable_of_Icc (by norm_num) (h2c.mul hf)
  -- splitting the integrand of `Sc`
  have hAEq : (∫ x in (0:ℝ)..(3/2), Real.sinh (lam*x) * Real.cos (t*x) * xyFf x)
      = (∫ x in (0:ℝ)..(3/2), (Real.sinh (lam*x) - lam*x) * Real.cos (t*x) * xyFf x)
        + (∫ x in (0:ℝ)..(3/2), lam * (x * Real.cos (t*x) * xyFf x)) := by
    rw [← intervalIntegral.integral_add hBint hCint]
    refine intervalIntegral.integral_congr fun x _ => ?_
    ring
  have hCEq : (∫ x in (0:ℝ)..(3/2), lam * (x * Real.cos (t*x) * xyFf x))
      = lam * (∫ x in (0:ℝ)..(3/2), x * Real.cos (t*x) * xyFf x) :=
    intervalIntegral.integral_const_mul lam _
  -- pointwise comparison `(sinh-λx) cos(tx) f ≤ (sinh-λx) f`
  have hBle : (∫ x in (0:ℝ)..(3/2), (Real.sinh (lam*x) - lam*x) * Real.cos (t*x) * xyFf x)
      ≤ ∫ x in (0:ℝ)..(3/2), (Real.sinh (lam*x) - lam*x) * xyFf x := by
    refine intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 3/2) hBint hDint ?_
    intro x hx
    have hs : 0 ≤ Real.sinh (lam*x) - lam*x := by
      have := (Real.self_le_sinh_iff (x := lam*x)).mpr (mul_nonneg h0 hx.1)
      linarith
    have hfn : 0 ≤ xyFf x := xyFf_nonneg x
    have hco : Real.cos (t*x) ≤ 1 := Real.cos_le_one (t*x)
    have step1 : (Real.sinh (lam*x) - lam*x) * Real.cos (t*x) ≤ (Real.sinh (lam*x) - lam*x) * 1 :=
      mul_le_mul_of_nonneg_left hco hs
    have step2 := mul_le_mul_of_nonneg_right step1 hfn
    simpa using step2
  have h6 : lam * (∫ x in (0:ℝ)..(3/2), x * Real.cos (t*x) * xyFf x)
      ≤ lam * max (∫ x in (0:ℝ)..(3/2), x * Real.cos (t*x) * xyFf x) 0 :=
    mul_le_mul_of_nonneg_left (le_max_left _ _) h0
  rw [Sc, Yc, Esc, hAEq, hCEq]
  linarith [hBle, h6]

end Work.ZeroFreeTables.XY

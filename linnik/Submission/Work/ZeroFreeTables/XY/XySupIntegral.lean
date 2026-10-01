/-
# ZeroFreeTables — XY/XySupIntegral

The two sup-estimates of Xylouris §2 (order-2 case) as *explicit oscillatory integrals*:
writing `f = tf72f (4/3)` for the test function of HB Lemma 7.2 (`xyT = tf72T (4/3)`),

  `xyRe x t        = ∫_0^{3/2} e^{-x s} cos(t s) f(s) ds`,
  `xySup1 lam t    = ∫_0^{3/2} (14900 e^{s} − 30480 e^{(1−lam)s}) cos(t s) f(s) ds`,
  `xySup2 lam t    = ∫_0^{3/2} ( 1250 e^{s} −  6000 e^{(1−lam)s}) cos(t s) f(s) ds`.

The first identity is `xyRe_eq_integral` (`XYEngineDefs`) with the factors reordered; the
last two are the linearity of the interval integral applied to the definition
`xySup i lam t = c_i · xyRe (-1) t − d_i · xyRe (lam - 1) t`, together with
`-(x·s) = s` at `x = -1` and `-((lam−1)·s) = (1−lam)·s`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.XYDefs
import Submission.Work.ZeroFreeTables.testFn72_defs
import Submission.Work.ZeroFreeTables.XY.XYEngineDefs

namespace Work.ZeroFreeTables.XY

open MeasureTheory

/-- If `g` is continuous on `[0, 3/2]`, then `s ↦ g(s) cos (t s) f(s)` (`f = tf72f (4/3)`) is
interval integrable on `[0, 3/2]`. -/
lemma intervalIntegrable_cos_mul_tf72f (g : ℝ → ℝ) (t : ℝ)
    (hg : ContinuousOn g (Set.Icc (0:ℝ) (3/2))) :
    IntervalIntegrable (fun s : ℝ => g s * Real.cos (t*s) * tf72f (4/3) s)
      volume (0:ℝ) (3/2) := by
  have hf : ContinuousOn (tf72f (4/3)) (Set.Icc (0:ℝ) (3/2)) :=
    (tf72f_cont (4/3) (by norm_num)).mono (fun x hx => hx.1)
  have hc : ContinuousOn (fun s : ℝ => g s * Real.cos (t*s)) (Set.Icc (0:ℝ) (3/2)) :=
    hg.mul ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn)
  exact ContinuousOn.intervalIntegrable_of_Icc (by norm_num) (hc.mul hf)

/-- `xyRe x t` with the integrand written in the factor order of `XySupIntegral`. -/
lemma xyRe_eq_orderedIntegral (x t : ℝ) :
    xyRe x t = ∫ s in (0:ℝ)..(3/2),
      Real.exp (-(x*s)) * Real.cos (t*s) * tf72f (4/3) s := by
  have hfun : (fun s : ℝ => Real.cos (t*s) * (Real.exp (-(x*s)) * xyT.f s))
      = (fun s : ℝ => Real.exp (-(x*s)) * Real.cos (t*s) * tf72f (4/3) s) := by
    funext s
    rw [show xyT.f s = tf72f (4/3) s from rfl]
    ring
  rw [xyRe_eq_integral, hfun]

/-- Linearity of the interval integral in the combination
`c · ∫ e^{s} cos(t s) f − d · ∫ e^{a s} cos(t s) f`, written as one integral. -/
lemma integral_exp_combination (c d a t : ℝ) :
    c * (∫ s in (0:ℝ)..(3/2), Real.exp s * Real.cos (t*s) * tf72f (4/3) s)
      - d * (∫ s in (0:ℝ)..(3/2), Real.exp (a*s) * Real.cos (t*s) * tf72f (4/3) s)
    = ∫ s in (0:ℝ)..(3/2),
        (c * Real.exp s - d * Real.exp (a*s)) * Real.cos (t*s) * tf72f (4/3) s := by
  have hi1 : IntervalIntegrable
      (fun s : ℝ => Real.exp s * Real.cos (t*s) * tf72f (4/3) s) volume (0:ℝ) (3/2) :=
    intervalIntegrable_cos_mul_tf72f (fun s : ℝ => Real.exp s) t
      Real.continuous_exp.continuousOn
  have hi2 : IntervalIntegrable
      (fun s : ℝ => Real.exp (a*s) * Real.cos (t*s) * tf72f (4/3) s) volume (0:ℝ) (3/2) :=
    intervalIntegrable_cos_mul_tf72f (fun s : ℝ => Real.exp (a*s)) t
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn)
  rw [← intervalIntegral.integral_const_mul c, ← intervalIntegral.integral_const_mul d,
      ← intervalIntegral.integral_sub (hi1.const_mul c) (hi2.const_mul d)]
  apply intervalIntegral.integral_congr
  intro s _
  ring

theorem XySupIntegral :
    (∀ (x t : ℝ), xyRe x t
        = ∫ s in (0:ℝ)..(3/2), Real.exp (-(x*s)) * Real.cos (t*s) * Work.ZeroFreeTables.tf72f (4/3) s)
  ∧ (∀ (lam t : ℝ), xySup1 lam t
        = ∫ s in (0:ℝ)..(3/2),
            (14900 * Real.exp s - 30480 * Real.exp ((1-lam)*s)) * Real.cos (t*s)
              * Work.ZeroFreeTables.tf72f (4/3) s)
  ∧ (∀ (lam t : ℝ), xySup2 lam t
        = ∫ s in (0:ℝ)..(3/2),
            (1250 * Real.exp s - 6000 * Real.exp ((1-lam)*s)) * Real.cos (t*s)
              * Work.ZeroFreeTables.tf72f (4/3) s) := by
  refine ⟨fun x t => xyRe_eq_orderedIntegral x t, ?_, ?_⟩
  · intro lam t
    have hf1 : (fun s : ℝ => Real.exp (-((-1:ℝ)*s)) * Real.cos (t*s) * tf72f (4/3) s)
        = (fun s : ℝ => Real.exp s * Real.cos (t*s) * tf72f (4/3) s) := by
      funext s
      rw [show -((-1:ℝ)*s) = s by ring]
    have hf2 : (fun s : ℝ => Real.exp (-((lam - 1)*s)) * Real.cos (t*s) * tf72f (4/3) s)
        = (fun s : ℝ => Real.exp ((1-lam)*s) * Real.cos (t*s) * tf72f (4/3) s) := by
      funext s
      rw [show -((lam - 1)*s) = (1-lam)*s by ring]
    have h1 : xyRe (-1) t = ∫ s in (0:ℝ)..(3/2),
        Real.exp s * Real.cos (t*s) * tf72f (4/3) s := by
      rw [xyRe_eq_orderedIntegral, hf1]
    have h2 : xyRe (lam - 1) t = ∫ s in (0:ℝ)..(3/2),
        Real.exp ((1-lam)*s) * Real.cos (t*s) * tf72f (4/3) s := by
      rw [xyRe_eq_orderedIntegral, hf2]
    show 14900 * xyRe (-1) t - 30480 * xyRe (lam - 1) t = _
    rw [h1, h2]
    exact integral_exp_combination 14900 30480 (1-lam) t
  · intro lam t
    have hf1 : (fun s : ℝ => Real.exp (-((-1:ℝ)*s)) * Real.cos (t*s) * tf72f (4/3) s)
        = (fun s : ℝ => Real.exp s * Real.cos (t*s) * tf72f (4/3) s) := by
      funext s
      rw [show -((-1:ℝ)*s) = s by ring]
    have hf2 : (fun s : ℝ => Real.exp (-((lam - 1)*s)) * Real.cos (t*s) * tf72f (4/3) s)
        = (fun s : ℝ => Real.exp ((1-lam)*s) * Real.cos (t*s) * tf72f (4/3) s) := by
      funext s
      rw [show -((lam - 1)*s) = (1-lam)*s by ring]
    have h1 : xyRe (-1) t = ∫ s in (0:ℝ)..(3/2),
        Real.exp s * Real.cos (t*s) * tf72f (4/3) s := by
      rw [xyRe_eq_orderedIntegral, hf1]
    have h2 : xyRe (lam - 1) t = ∫ s in (0:ℝ)..(3/2),
        Real.exp ((1-lam)*s) * Real.cos (t*s) * tf72f (4/3) s := by
      rw [xyRe_eq_orderedIntegral, hf2]
    show 1250 * xyRe (-1) t - 6000 * xyRe (lam - 1) t = _
    rw [h1, h2]
    exact integral_exp_combination 1250 6000 (1-lam) t

end Work.ZeroFreeTables.XY

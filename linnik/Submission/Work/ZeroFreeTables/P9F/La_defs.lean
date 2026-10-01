/-
# P9F — the real-axis Laplace integral `La` and its monotonicity

`La θ lam x = ∫₀^{x₀} e^{xt} f(t) dt` for HB Lemma 7.1's test function `f = tf71f θ lam`
(with `x₀ = 2 tf71γ`).  Lemma 9.2's inequality evaluates `F(−λ) = La θ lam λ`,
`F(0) = La θ lam 0`, and the closed form `tf71Fr θ lam z` is `La θ lam (−z)`
(`tf71F_real_eq`).

The two monotonicity facts used by the Table 9 assembly are
* `La_mono`: `x ↦ La θ lam x` is non-decreasing, and
* `La_sub_mono`: for `c ≥ 0`, `x ↦ La θ lam x − La θ lam (x − c)` is non-decreasing
  (pointwise: `e^{xt} − e^{(x−c)t} = e^{xt}(1 − e^{−ct})`, and `(e^{xt} − e^{yt})(1 − e^{−ct}) ≤ 0`
  for `x ≤ y`, `t ≥ 0`, `c ≥ 0`).
-/
import Mathlib
import Submission.Work.ZeroFreeTables.testFn71_defs
import Submission.Work.ZeroFreeTables.testFn7_1

noncomputable section
open scoped Real
namespace Work.ZeroFreeTables.P9F

open Work.ZeroFreeTables

/-- HB Lemma 7.1's Laplace integral on the real axis, as a function of the exponent. -/
def La (θ lam x : ℝ) : ℝ :=
  ∫ t in (0:ℝ)..(2 * tf71γ θ lam), Real.exp (x * t) * tf71f θ lam t

theorem tf71f_continuousOn_Icc {θ lam : ℝ} :
    ContinuousOn (tf71f θ lam) (Set.Icc (0:ℝ) (2 * tf71γ θ lam)) :=
  (tf71f_cont θ lam).mono (fun t ht => ht.1)

theorem intervalIntegrable_exp_mul {θ lam : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hlam : 0 < lam) (x : ℝ) :
    IntervalIntegrable
      (fun t : ℝ => Real.exp (x * t) * tf71f θ lam t) MeasureTheory.volume
      (0 : ℝ) (2 * tf71γ θ lam) := by
  have hγ : 0 < 2 * tf71γ θ lam := by have := tf71γ_pos hθ0 hθ1 hlam; linarith
  refine ContinuousOn.intervalIntegrable_of_Icc hγ.le ?_
  exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn).mul
    tf71f_continuousOn_Icc

/-- `x ↦ La θ lam x` is non-decreasing. -/
theorem La_mono {θ lam : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) (hlam : 0 < lam)
    {x y : ℝ} (hxy : x ≤ y) : La θ lam x ≤ La θ lam y := by
  unfold La
  have hγ : 0 < 2 * tf71γ θ lam := by have := tf71γ_pos hθ0 hθ1 hlam; linarith
  exact intervalIntegral.integral_mono_on hγ.le (intervalIntegrable_exp_mul hθ0 hθ1 hlam x)
    (intervalIntegrable_exp_mul hθ0 hθ1 hlam y) (fun t ht => by
      have ht0 : 0 ≤ t := ht.1
      have h1 : Real.exp (x * t) ≤ Real.exp (y * t) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hxy ht0)
      exact mul_le_mul_of_nonneg_right h1 (tf71f_nonneg θ lam hθ0 hθ1 hlam t))

/-- For `c ≥ 0`, `x ↦ La θ lam x − La θ lam (x − c)` is non-decreasing. -/
theorem La_sub_mono {θ lam c : ℝ} (hc : 0 ≤ c) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hlam : 0 < lam) {x y : ℝ} (hxy : x ≤ y) :
    La θ lam x - La θ lam (x - c) ≤ La θ lam y - La θ lam (y - c) := by
  unfold La
  have hγ : 0 < 2 * tf71γ θ lam := by have := tf71γ_pos hθ0 hθ1 hlam; linarith
  set x₀ : ℝ := 2 * tf71γ θ lam with hx₀
  have hI (z : ℝ) : IntervalIntegrable (fun t : ℝ => Real.exp (z * t) * tf71f θ lam t)
      MeasureTheory.volume (0:ℝ) x₀ := by
    rw [hx₀]; exact intervalIntegrable_exp_mul hθ0 hθ1 hlam z
  have hx : (∫ t in (0:ℝ)..x₀, Real.exp (x * t) * tf71f θ lam t)
      - (∫ t in (0:ℝ)..x₀, Real.exp ((x - c) * t) * tf71f θ lam t)
      = ∫ t in (0:ℝ)..x₀,
          (Real.exp (x * t) * tf71f θ lam t - Real.exp ((x - c) * t) * tf71f θ lam t) :=
    (intervalIntegral.integral_sub (hI x) (hI (x - c))).symm
  have hy : (∫ t in (0:ℝ)..x₀, Real.exp (y * t) * tf71f θ lam t)
      - (∫ t in (0:ℝ)..x₀, Real.exp ((y - c) * t) * tf71f θ lam t)
      = ∫ t in (0:ℝ)..x₀,
          (Real.exp (y * t) * tf71f θ lam t - Real.exp ((y - c) * t) * tf71f θ lam t) :=
    (intervalIntegral.integral_sub (hI y) (hI (y - c))).symm
  rw [hx, hy]
  refine intervalIntegral.integral_mono_on hγ.le ?_ ?_ ?_
  · exact (hI x).sub (hI (x - c))
  · exact (hI y).sub (hI (y - c))
  · intro t ht
    have ht0 : 0 ≤ t := ht.1
    have h1 : Real.exp (x * t) ≤ Real.exp (y * t) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hxy ht0)
    have hfac : 0 ≤ 1 - Real.exp (-(c * t)) := by
      have h2 : Real.exp (-(c * t)) ≤ 1 := by
        rw [Real.exp_le_one_iff]; nlinarith [mul_nonneg hc ht0]
      linarith
    have hchain : Real.exp (x * t) * (1 - Real.exp (-(c * t)))
        ≤ Real.exp (y * t) * (1 - Real.exp (-(c * t))) :=
      mul_le_mul_of_nonneg_right h1 hfac
    have hf := tf71f_nonneg θ lam hθ0 hθ1 hlam t
    have e1 : Real.exp ((x - c) * t) = Real.exp (x * t) * Real.exp (-(c * t)) := by
      rw [← Real.exp_add]; ring_nf
    have e2 : Real.exp ((y - c) * t) = Real.exp (y * t) * Real.exp (-(c * t)) := by
      rw [← Real.exp_add]; ring_nf
    rw [e1, e2]
    nlinarith [hchain, hf, Real.exp_nonneg (x * t), Real.exp_nonneg (y * t),
      Real.exp_nonneg (-(c * t))]

end Work.ZeroFreeTables.P9F

import Mathlib
import Submission.Work.ZeroFreeTables.OffAxis.RectRepDefs
import Submission.Work.ZeroFreeTables.OffAxis.RepHNear
import Submission.Work.ZeroFreeTables.Rep9.nearSum_bounds

namespace Work.ZeroFreeTables.OffAxis

open DirichletCharacter Complex
open scoped Classical BigOperators

noncomputable section

open Work.ZeroFreeTables Work.LinnikContract

/-! ## The near-summands at height `3H`

This is the height-`3H` form of `Work.ZeroFreeTables.Rep9.nearSum_term_nonneg_H` (which is
private in `OffAxis/RepHNear.lean`): every summand of `P3NearSumL` over the zeros within `δ`
of `1 + i·Im s` is non-negative, the minimality clause `IsMinWideAt H W` being applied to the
near zero `u` via `|u.im| ≤ |s.im| + δ < 3H + 1 ≤ W`. -/

/-- `(s - u)·log q = (a + λ(u)) + i·log q·(Im s - Im u)` when `Re s = 1 + a/log q`. -/
private lemma sub_mul_log_eq {q : ℕ} [NeZero q] {a : ℝ} (hq : 2 ≤ q) {s u : ℂ}
    (hs : s.re = 1 + a / Real.log (q : ℝ)) :
    (s - u) * ((Real.log (q : ℝ) : ℝ) : ℂ) =
      ((a + Work.LinnikContract.lamOf q u : ℝ) : ℂ)
        + ((Real.log (q : ℝ) * (s.im - u.im) : ℝ) : ℂ) * Complex.I := by
  have hL : Real.log (q : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast (by omega : 1 < q)))
  have h1 : ((s - u) * ((Real.log (q : ℝ) : ℝ) : ℂ)).re
      = a + Work.LinnikContract.lamOf q u := by
    simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_im, zero_mul]
    rw [Work.LinnikContract.lamOf, hs]
    field_simp
    ring
  have h2 : ((s - u) * ((Real.log (q : ℝ) : ℝ) : ℂ)).im
      = Real.log (q : ℝ) * (s.im - u.im) := by
    simp only [Complex.mul_im, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  apply Complex.ext
  · rw [h1]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero]
    ring
  · rw [h2]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add]
    ring

/-- HB (4.11) in the shape needed by the near sum: if `Re s = 1 + a/log q`, `0 < a + λ₁` and
`λ₁ ≤ λ(u)` then `Re P₃((a+λ₁)/((s-u)·log q)) ≥ 0`. -/
private lemma P3_sub_mul_log_nonneg {q : ℕ} [NeZero q] {a lam : ℝ} {s u : ℂ} (hq : 2 ≤ q)
    (hs : s.re = 1 + a / Real.log (q : ℝ)) (hα : 0 < a + lam)
    (hβ : a + lam ≤ a + Work.LinnikContract.lamOf q u) :
    0 ≤ (Work.ZeroFreeTables.P3
      (((a : ℂ) + ((lam : ℝ) : ℂ))
        / ((s - u) * ((Real.log (q : ℝ) : ℝ) : ℂ)))).re := by
  rw [sub_mul_log_eq hq hs]
  have hnum : ((a : ℂ) + ((lam : ℝ) : ℂ)) = (((a + lam : ℝ)) : ℂ) := by push_cast; ring
  rw [hnum]
  exact Work.ZeroFreeTables.P3.P3Bounds.1 (a + lam) (a + Work.LinnikContract.lamOf q u)
    (Real.log (q : ℝ) * (s.im - u.im)) hα hβ

/-- The divisor of the completed `L`-function at level `q`, computed as the vanishing order
(and `0` outside the ball on which the divisor is taken). -/
private lemma pdiv_eq_order {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (s u : ℂ) :
    Work.ZeroFreeTables.pdiv q χ s u
      = if u ∈ Metric.closedBall (0 : ℂ) (|s.im| + 2)
          then (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℤ) else 0 := by
  rw [Work.ZeroFreeTables.pdiv]
  by_cases hu : u ∈ Metric.closedBall (0 : ℂ) (|s.im| + 2)
  · rw [if_pos hu]
    have hAn : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall (0 : ℂ) (|s.im| + 2)) :=
      fun z _ => (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt z
    rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hAn hu]
    simp only [analyticOrderNatAt]
    cases h : analyticOrderAt (DirichletCharacter.completedLFunction χ) u with
    | top => simp
    | coe n => simp
  · rw [if_neg hu, MeromorphicOn.divisor_def]
    simp [hu]

/-- **Every summand of the near sum is non-negative** at test points of height `≤ 3H`.  A near
zero `u` (within `δ < 1` of `1 + i·Im s`) has `|u.im| ≤ |s.im| + δ < 3H + 1 ≤ W`, so
`λ(u) ≥ λ₁` by the wide minimality of `ρ₁`; its multiplicity is then a genuine `zeroMult`
zero, whence `Re P₃(α/((s-u)𝓛)) ≥ 0` by HB (4.11). -/
private lemma nearSum_term_nonneg_3H {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ)
    {H W a δ : ℝ} (hq : 2 ≤ q) (hmin : Work.ZeroFreeTables.IsMinWideAt H W χ₁ ρ₁)
    (hW : 3 * H + 1 ≤ W) (hlam₁nn : 0 ≤ Work.LinnikContract.lamOf q ρ₁)
    (ha : 0 < a) (hδ1 : δ < 1)
    {ψ : DirichletCharacter ℂ q} (hψ : ψ ≠ 1) {s u : ℂ} (hγ : |s.im| ≤ 3 * H)
    (hs : s.re = 1 + a / Real.log (q : ℝ)) :
    0 ≤ ((Work.ZeroFreeTables.pdiv q ψ s u : ℤ) : ℝ) *
      (if ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ
        then (Work.ZeroFreeTables.P3
          ((a + Work.LinnikContract.lamOf q ρ₁) / ((s - u) * ((Real.log (q : ℝ) : ℝ) : ℂ)))).re
        else 0) := by
  by_cases hnear : ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ
  · rw [if_pos hnear]
    by_cases hdiv : Work.ZeroFreeTables.pdiv q ψ s u = 0
    · rw [hdiv]; simp
    · have hre : |1 - u.re| ≤ δ := by
        have h1 : ((1 : ℂ) + (s.im : ℂ) * Complex.I - u).re = 1 - u.re := by simp
        rw [← h1]
        exact le_trans (Complex.abs_re_le_norm _) hnear
      have him : |s.im - u.im| ≤ δ := by
        have h1 : ((1 : ℂ) + (s.im : ℂ) * Complex.I - u).im = s.im - u.im := by simp
        rw [← h1]
        exact le_trans (Complex.abs_im_le_norm _) hnear
      have hu0 : 0 < u.re := by
        have h2 := abs_le.mp hre
        linarith [h2.1, hδ1]
      have huW : |u.im| ≤ W := by
        have h2 := abs_le.mp him
        have h3 := abs_le.mp hγ
        rw [abs_le]
        constructor <;> linarith [h2.1, h2.2, h3.1, h3.2, hδ1, hW]
      have hball : u ∈ Metric.closedBall (0 : ℂ) (|s.im| + 2) := by
        by_contra hb
        exact hdiv (by rw [pdiv_eq_order ψ hψ s u, if_neg hb])
      have hord : analyticOrderNatAt (DirichletCharacter.completedLFunction ψ) u ≠ 0 := by
        intro h0
        exact hdiv (by rw [pdiv_eq_order ψ hψ s u, if_pos hball, h0]; rfl)
      have hzm : Work.LinnikContract.zeroMult ψ u ≠ 0 :=
        Work.ZeroFreeTables.Rep9.zeroMult_ne_zero_of_completedLFunction_eq_zero ψ hψ hu0
          (apply_eq_zero_of_analyticOrderNatAt_ne_zero hord)
      have hlam : Work.LinnikContract.lamOf q ρ₁ ≤ Work.LinnikContract.lamOf q u :=
        hmin.2.2.2 ψ u hψ hzm huW
      have hdivnn : (0 : ℝ) ≤ ((Work.ZeroFreeTables.pdiv q ψ s u : ℤ) : ℝ) := by
        rw [pdiv_eq_order ψ hψ s u, if_pos hball]
        positivity
      have hP3 : 0 ≤ (Work.ZeroFreeTables.P3
          ((a + Work.LinnikContract.lamOf q ρ₁)
            / ((s - u) * ((Real.log (q : ℝ) : ℝ) : ℂ)))).re :=
        P3_sub_mul_log_nonneg hq hs (by linarith) (by linarith)
      exact mul_nonneg hdivnn hP3
  · rw [if_neg hnear]
    simp

/-- **The near sum is non-negative.**  `P3NearSumL` is the `∑ᶠ` of its (non-negative) summands
over the zeros of the completed `L`-function of `ψ` within `δ` of `1 + i·Im s`, so it is
`≥ 0`. -/
theorem RectRepNearSum {q : ℕ} [NeZero q] (χ₁ ψ : DirichletCharacter ℂ q) (ρ₁ : ℂ) {H W a δ : ℝ}
    (hq : 2 ≤ q) (hmin : Work.ZeroFreeTables.IsMinWideAt H W χ₁ ρ₁) (hW : 3 * H + 1 ≤ W)
    (hψ : ψ ≠ 1) (hlam : 0 ≤ Work.LinnikContract.lamOf q ρ₁) (ha : 0 < a) (hδ0 : 0 < δ)
    (hδ1 : δ < 1) {s : ℂ} (hsre : s.re = 1 + a / Real.log (q : ℝ)) (hsim : |s.im| ≤ 3 * H) :
    0 ≤ Work.ZeroFreeTables.P3NearSumL q (Real.log (q : ℝ)) ψ s a
      (Work.LinnikContract.lamOf q ρ₁) δ := by
  rw [Work.ZeroFreeTables.P3NearSumL]
  exact finsum_nonneg fun u =>
    nearSum_term_nonneg_3H χ₁ ρ₁ hq hmin hW hlam ha hδ1 hψ hsim hsre

end

end Work.ZeroFreeTables.OffAxis

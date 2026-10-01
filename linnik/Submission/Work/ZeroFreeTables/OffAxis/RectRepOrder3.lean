import Mathlib
import Submission.Work.ZeroFreeTables.OffAxis.RectRepDefs
import Submission.Work.ZeroFreeTables.Rep9.order3_extraM

open DirichletCharacter Complex
open scoped Classical BigOperators

namespace Work.ZeroFreeTables.OffAxis

/-!
# `OffAxis/RectRepOrder3`

The **order-3 branch** of the repeated-zero `P₃` engine at rectangle height `H`: the pair
`(χ₁, ρ₁)` has `χ₁³ = 1` (so `χ₁² = χ̄₁ ≠ 1`) and `ρ₁` is a **multiple** zero at height
`|Im ρ₁| ≤ H`, with `λ₁ = lamOf q ρ₁` minimal over all non-principal zeros of height `≤ W`,
where `W ≥ 3H + 1`.

* **near** (`RectRepOrder3Near`): if the conjugate zero `ρ̄₁` — which is a zero of `χ₁²` of
  multiplicity `zeroMult χ₁ ρ₁ ≥ 2` (`A7.zeroMult_conj_inv`, `χ₁² = χ₁⁻¹`) — lies in the near
  window of the point `1 + 2i·Im ρ₁`, then the corresponding summand of
  `P3NearSumL q (log q) (χ₁²) (1 + a/log q + 2i·Im ρ₁)` is
  `2·Re P₃((a+λ₁)/((a+λ₁) + 3i·Im ρ₁·log q))`, and every other summand is non-negative by HB
  (4.11) together with the wide minimality of `ρ₁`;
* **far** (`Rep9.order3_extraM_far`): outside the window the quotient `(a+λ₁)/(a + 3iγ𝓛)` is
  `O(1/𝓛)`, so the same `Re P₃` is `≤ e` for large `q`.

This is the height-`H` form of the first conjunct of `Rep9.order3_extraM` (`IsMin1WideAt 10` +
`IsZ` replaced by `IsMinWideAt H W` with room `3H + 1 ≤ W`): only the window bound on the near
summands uses the height, a zero `u` in the window `‖1 + i·Im s - u‖ ≤ δ < 1` of the point
`s = σ + 2iγ` having `|Im u| ≤ 2|γ| + δ < 2H + 1 ≤ 3H + 1 ≤ W`.
-/

/-! ## Helpers (copies of the private tooling of `Rep9.nearSum_bounds` / `OffAxis.RectRepCaseCNear`) -/

/-- `(s - u)·L = (a + λ(u)) + i·L·(Im s - Im u)` when `Re s = 1 + a/L`. -/
private lemma sub_mul_log_eq_W {q : ℕ} [NeZero q] {a : ℝ} (hq : 2 ≤ q) {s u : ℂ}
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

/-- HB (4.11) in the shape needed by the near sum. -/
private lemma P3_sub_mul_log_nonneg_W {q : ℕ} [NeZero q] {a lam : ℝ} {s u : ℂ} (hq : 2 ≤ q)
    (hs : s.re = 1 + a / Real.log (q : ℝ)) (hα : 0 < a + lam)
    (hβ : a + lam ≤ a + Work.LinnikContract.lamOf q u) :
    0 ≤ (Work.ZeroFreeTables.P3
      (((a : ℂ) + ((lam : ℝ) : ℂ))
        / ((s - u) * ((Real.log (q : ℝ) : ℝ) : ℂ)))).re := by
  rw [sub_mul_log_eq_W hq hs]
  have hnum : ((a : ℂ) + ((lam : ℝ) : ℂ)) = (((a + lam : ℝ)) : ℂ) := by push_cast; ring
  rw [hnum]
  exact Work.ZeroFreeTables.P3.P3Bounds.1 (a + lam) (a + Work.LinnikContract.lamOf q u)
    (Real.log (q : ℝ) * (s.im - u.im)) hα hβ

/-- The divisor of the completed `L`-function at level `q`, computed as the vanishing order
(and `0` outside the ball on which the divisor is taken). -/
private lemma pdiv_eq_order_W {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
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

/-- The multiplicity of `ρ̄₁` as a zero of `χ₁²` (`χ₁³ = 1`): it is `zeroMult χ₁ ρ₁`. -/
private theorem zeroMult_conj_cube {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ)
    (hcube : χ₁ ^ 3 = 1) :
    Work.LinnikContract.zeroMult (χ₁ ^ 2) ((starRingEnd ℂ) ρ₁)
      = Work.LinnikContract.zeroMult χ₁ ρ₁ := by
  have hmul : χ₁ ^ 2 * χ₁ = 1 := by rw [← pow_succ]; exact hcube
  have h3 : χ₁ ^ 2 = χ₁⁻¹ := eq_inv_of_mul_eq_one_left hmul
  rw [h3]
  exact Work.A7.zeroMult_conj_inv χ₁ ρ₁

/-- **Every summand of the near sum is non-negative**: a near zero `u` (within `δ < 1` of
`1 + i·Im s`) has `|Im u| ≤ |Im s| + δ < 2H + 1 ≤ 3H + 1 ≤ W` when `|Im s| ≤ 2H`, so its
`λ` dominates `λ₁` by the wide minimality of `ρ₁`; HB (4.11) then gives `Re P₃ ≥ 0`. -/
private lemma nearTerm_nonneg_W {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ)
    {H W a δ : ℝ} (hq : 2 ≤ q) (hmin : Work.ZeroFreeTables.IsMinWideAt H W χ₁ ρ₁)
    (hW : 3 * H + 1 ≤ W) (ha : 0 < a) (hδ1 : δ < 1)
    {ψ : DirichletCharacter ℂ q} (hψ : ψ ≠ 1) {s u : ℂ} (hγ : |s.im| ≤ 2 * H)
    (hs : s.re = 1 + a / Real.log (q : ℝ)) :
    0 ≤ ((Work.ZeroFreeTables.pdiv q ψ s u : ℤ) : ℝ) *
      (if ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ
        then (Work.ZeroFreeTables.P3
          ((a + Work.LinnikContract.lamOf q ρ₁) / ((s - u) * ((Real.log (q : ℝ) : ℝ) : ℂ)))).re
        else 0) := by
  have hHnn : 0 ≤ H := le_trans (abs_nonneg ρ₁.im) hmin.2.2.1
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
        have h2 := (abs_le.mp hre).2
        linarith
      have huW : |u.im| ≤ W := by
        have h2 := abs_le.mp him
        have h3 := abs_le.mp hγ
        rw [abs_le]
        constructor <;> linarith [h2.1, h2.2, h3.1, h3.2, hδ1, hW, hHnn]
      have hball : u ∈ Metric.closedBall (0 : ℂ) (|s.im| + 2) := by
        by_contra hb
        exact hdiv (by rw [pdiv_eq_order_W ψ hψ s u, if_neg hb])
      have hord : analyticOrderNatAt (DirichletCharacter.completedLFunction ψ) u ≠ 0 := by
        intro h0
        exact hdiv (by rw [pdiv_eq_order_W ψ hψ s u, if_pos hball, h0]; rfl)
      have hzm : Work.LinnikContract.zeroMult ψ u ≠ 0 :=
        Work.ZeroFreeTables.Rep9.zeroMult_ne_zero_of_completedLFunction_eq_zero ψ hψ hu0
          (apply_eq_zero_of_analyticOrderNatAt_ne_zero hord)
      have hlam : Work.LinnikContract.lamOf q ρ₁ ≤ Work.LinnikContract.lamOf q u :=
        hmin.2.2.2 ψ u hψ hzm huW
      have hdivnn : (0 : ℝ) ≤ ((Work.ZeroFreeTables.pdiv q ψ s u : ℤ) : ℝ) := by
        rw [pdiv_eq_order_W ψ hψ s u, if_pos hball]
        positivity
      have hlamnn : 0 ≤ Work.LinnikContract.lamOf q ρ₁ :=
        Work.ZeroFreeTables.OffAxis.IsMinWideAt.lam_nonneg hmin
      have hP3 : 0 ≤ (Work.ZeroFreeTables.P3
          ((a + Work.LinnikContract.lamOf q ρ₁)
            / ((s - u) * ((Real.log (q : ℝ) : ℝ) : ℂ)))).re :=
        P3_sub_mul_log_nonneg_W hq hs (by linarith) (by linarith)
      exact mul_nonneg hdivnn hP3
  · rw [if_neg hnear]
    simp

/-! ## The near branch -/

/-- The near branch of the order-3 case: the conjugate zero `ρ̄₁` of the companion character
`χ₁²` contributes `2·Re P₃((a+λ₁)/((a+λ₁) + 3iγ𝓛))` to the near sum at the point `σ + 2iγ`. -/
theorem RectRepOrder3Near {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hδ1 : δ < 1)
    {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ) (hq : 2 ≤ q)
    {H W : ℝ} (hmin : Work.ZeroFreeTables.IsMinWideAt H W χ₁ ρ₁) (hW : 3 * H + 1 ≤ W)
    (hmult : 2 ≤ Work.LinnikContract.zeroMult χ₁ ρ₁) (hcube : χ₁ ^ 3 = 1)
    (hδL : Work.LinnikContract.lamOf q ρ₁ / Real.log (q : ℝ) ≤ δ)
    (hnear : ‖(1 : ℂ) + (((2 * ρ₁.im : ℝ)) : ℂ) * Complex.I - (starRingEnd ℂ) ρ₁‖ ≤ δ) :
    (2 : ℝ) * (Work.ZeroFreeTables.P3
        (((a + Work.LinnikContract.lamOf q ρ₁) : ℂ)
          / (((a + Work.LinnikContract.lamOf q ρ₁) : ℂ)
              + ((3 * ρ₁.im * Real.log (q : ℝ) : ℝ) : ℂ) * Complex.I))).re
      ≤ Work.ZeroFreeTables.P3NearSumL q (Real.log (q : ℝ)) (χ₁ ^ 2)
          ((((1 + a / Real.log (q : ℝ) : ℝ)) : ℂ) + (((2 * ρ₁.im : ℝ)) : ℂ) * Complex.I) a
          (Work.LinnikContract.lamOf q ρ₁) δ := by
  have hχ1 : χ₁ ≠ 1 := hmin.1
  have hzm : Work.LinnikContract.zeroMult χ₁ ρ₁ ≠ 0 := hmin.2.1
  have himH : |ρ₁.im| ≤ H := hmin.2.2.1
  have hHnn : 0 ≤ H := le_trans (abs_nonneg ρ₁.im) himH
  have hlamnn : 0 ≤ Work.LinnikContract.lamOf q ρ₁ := Work.ZeroFreeTables.OffAxis.IsMinWideAt.lam_nonneg hmin
  have hαpos : 0 < a + Work.LinnikContract.lamOf q ρ₁ := by linarith
  have hcast : ((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁ : ℝ) : ℂ))
      = ((a + Work.LinnikContract.lamOf q ρ₁ : ℝ) : ℂ) := by rw [Complex.ofReal_add]
  have hχ2 : χ₁ ^ 2 ≠ 1 := by
    intro h2
    have hmul : χ₁ ^ 2 * χ₁ = 1 := by rw [← pow_succ]; exact hcube
    have h3 : χ₁ ^ 2 = χ₁⁻¹ := eq_inv_of_mul_eq_one_left hmul
    rw [h3] at h2
    exact hχ1 (inv_eq_one.mp h2)
  have hmultconj := zeroMult_conj_cube χ₁ ρ₁ hcube
  have hre1 : ρ₁.re < 1 := Work.LinnikAreas.boxMaxZeroAux.zeroMult_re_lt_one χ₁ hzm
  have hdec : ((1 : ℂ) + (((2 * ρ₁.im : ℝ)) : ℂ) * Complex.I - (starRingEnd ℂ) ρ₁)
      = (((1 - ρ₁.re : ℝ)) : ℂ) + (((3 * ρ₁.im : ℝ)) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp <;> ring
  have hre_abs : |1 - ρ₁.re| ≤ δ := by
    have h1 : |1 - ρ₁.re| ≤
        ‖(1 : ℂ) + (((2 * ρ₁.im : ℝ)) : ℂ) * Complex.I - (starRingEnd ℂ) ρ₁‖ := by
      simpa [hdec] using Complex.abs_re_le_norm
        ((1 : ℂ) + (((2 * ρ₁.im : ℝ)) : ℂ) * Complex.I - (starRingEnd ℂ) ρ₁)
    exact h1.trans hnear
  have hrepos : 0 < ρ₁.re := by
    have := (abs_le.mp hre_abs).2
    linarith
  set s : ℂ := ((1 + a / Real.log (q : ℝ) : ℝ) : ℂ)
    + (((2 * ρ₁.im : ℝ)) : ℂ) * Complex.I with hsdef
  have hsr : s.re = 1 + a / Real.log (q : ℝ) := by
    rw [hsdef]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, sub_zero]
  have hsi : s.im = 2 * ρ₁.im := by
    rw [hsdef]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
  have hγ2H : |s.im| ≤ 2 * H := by
    rw [hsi]
    have h2 : |(2 : ℝ)| = 2 := by norm_num
    rw [abs_mul, h2]
    linarith
  set f : ℂ → ℝ := fun u => ((Work.ZeroFreeTables.pdiv q (χ₁ ^ 2) s u : ℤ) : ℝ) *
      (if ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ
        then (Work.ZeroFreeTables.P3
          ((a + Work.LinnikContract.lamOf q ρ₁)
            / ((s - u) * ((Real.log (q : ℝ) : ℝ) : ℂ)))).re
        else 0) with hfdef
  have hterm_nonneg : ∀ u : ℂ, 0 ≤ f u := by
    intro u
    simp only [hfdef]
    exact nearTerm_nonneg_W χ₁ ρ₁ hq hmin hW ha hδ1 hχ2 hγ2H hsr
  have hfinDiv : Function.HasFiniteSupport (Work.ZeroFreeTables.pdiv q (χ₁ ^ 2) s) := by
    have hAn : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction (χ₁ ^ 2))
        (Metric.closedBall (0 : ℂ) (|s.im| + 2)) :=
      fun z _ => (DirichletCharacter.differentiable_completedLFunction hχ2).analyticAt z
    have hd : Function.HasFiniteSupport (fun u : ℂ => MeromorphicOn.divisor
        (DirichletCharacter.completedLFunction (χ₁ ^ 2))
        (Metric.closedBall (0 : ℂ) (|s.im| + 2)) u) := by
      simpa only [Function.HasFiniteSupport] using
        (MeromorphicOn.divisor_support_finite_of_subset
          (f := DirichletCharacter.completedLFunction (χ₁ ^ 2))
          (U := Metric.closedBall (0 : ℂ) (|s.im| + 2))
          (V := Metric.closedBall (0 : ℂ) (|s.im| + 2))
          hAn.meromorphicOn (isCompact_closedBall (0 : ℂ) (|s.im| + 2)) (le_refl _))
    exact hd
  have hfin : Function.HasFiniteSupport f := hfinDiv.subset (fun u hu => by
    rw [Function.mem_support] at hu ⊢
    intro h0
    exact hu (by simp only [hfdef]; rw [h0]; simp))
  -- `ρ̄₁` is in the ball and in the near window
  have hcball : (starRingEnd ℂ) ρ₁ ∈ Metric.closedBall (0 : ℂ) (|s.im| + 2) := by
    rw [Metric.mem_closedBall, dist_zero_right, starRingEnd_apply, norm_star]
    calc ‖ρ₁‖ ≤ |ρ₁.re| + |ρ₁.im| := Complex.norm_le_abs_re_add_abs_im ρ₁
      _ ≤ 1 + |ρ₁.im| := by
          have h1 : |ρ₁.re| ≤ 1 := by rw [abs_of_pos hrepos]; linarith
          linarith [h1]
      _ ≤ |s.im| + 2 := by
          rw [hsi, abs_mul]
          have h2 : |(2 : ℝ)| = 2 := by norm_num
          rw [h2]
          linarith [abs_nonneg ρ₁.im]
  have hif : ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - (starRingEnd ℂ) ρ₁‖ ≤ δ := by
    rw [hsi]; exact hnear
  have hrepos_c : 0 < ((starRingEnd ℂ) ρ₁).re := by simpa using hrepos
  have hre1_c : ((starRingEnd ℂ) ρ₁).re < 1 := by simpa using hre1
  have hdivρ1 : (2 : ℤ) ≤ Work.ZeroFreeTables.pdiv q (χ₁ ^ 2) s ((starRingEnd ℂ) ρ₁) := by
    rw [pdiv_eq_order_W (χ₁ ^ 2) hχ2 s ((starRingEnd ℂ) ρ₁), if_pos hcball,
      ← Work.ZeroFreeTables.Rep9.zeroMult_eq_analyticOrderNatAt_of_re_pos_of_re_lt_one
        (χ₁ ^ 2) hχ2 hrepos_c hre1_c, hmultconj]
    exact_mod_cast hmult
  have hargc : (s - (starRingEnd ℂ) ρ₁) * ((Real.log (q : ℝ) : ℝ) : ℂ)
      = ((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁ : ℝ) : ℂ))
        + ((3 * ρ₁.im * Real.log (q : ℝ) : ℝ) : ℂ) * Complex.I := by
    have h := sub_mul_log_eq_W (q := q) hq (s := s) (u := (starRingEnd ℂ) ρ₁) hsr
    have hc : Work.LinnikContract.lamOf q ((starRingEnd ℂ) ρ₁)
        = Work.LinnikContract.lamOf q ρ₁ := by
      simp [Work.LinnikContract.lamOf]
    have hcj : ((starRingEnd ℂ) ρ₁).im = -ρ₁.im := Complex.conj_im ρ₁
    rw [hc, hsi, hcj] at h
    rw [h, ← hcast]
    have hre : Real.log (q : ℝ) * (2 * ρ₁.im - -ρ₁.im) = 3 * ρ₁.im * Real.log (q : ℝ) := by ring
    rw [hre]
  have hP3nn : 0 ≤ (Work.ZeroFreeTables.P3
      (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁ : ℝ) : ℂ))
        / (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁ : ℝ) : ℂ))
            + ((3 * ρ₁.im * Real.log (q : ℝ) : ℝ) : ℂ) * Complex.I))).re := by
    rw [hcast]
    exact Work.ZeroFreeTables.P3.P3Bounds.1 (a + Work.LinnikContract.lamOf q ρ₁)
      (a + Work.LinnikContract.lamOf q ρ₁) (3 * ρ₁.im * Real.log (q : ℝ)) hαpos le_rfl
  have hterm : 2 * (Work.ZeroFreeTables.P3
        (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁ : ℝ) : ℂ))
          / (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁ : ℝ) : ℂ))
              + ((3 * ρ₁.im * Real.log (q : ℝ) : ℝ) : ℂ) * Complex.I))).re
      ≤ f ((starRingEnd ℂ) ρ₁) := by
    simp only [hfdef]
    rw [if_pos hif, hargc]
    have h2 : (2 : ℝ) ≤
        ((Work.ZeroFreeTables.pdiv q (χ₁ ^ 2) s ((starRingEnd ℂ) ρ₁) : ℤ) : ℝ) := by
      exact_mod_cast hdivρ1
    exact mul_le_mul_of_nonneg_right h2 hP3nn
  have hsingle : f ((starRingEnd ℂ) ρ₁) ≤ ∑ u ∈ hfin.toFinset, f u := by
    by_cases hmem : (starRingEnd ℂ) ρ₁ ∈ hfin.toFinset
    · exact Finset.single_le_sum (fun u _ => hterm_nonneg u) hmem
    · have h0 : f ((starRingEnd ℂ) ρ₁) = 0 := by
        by_contra hc
        exact hmem ((Set.Finite.mem_toFinset hfin).mpr (by simpa [Function.mem_support] using hc))
      rw [h0]
      exact Finset.sum_nonneg (fun u _ => hterm_nonneg u)
  have hPNS : Work.ZeroFreeTables.P3NearSumL q (Real.log (q : ℝ)) (χ₁ ^ 2) s a
      (Work.LinnikContract.lamOf q ρ₁) δ = ∑ᶠ u : ℂ, f u := by
    rw [Work.ZeroFreeTables.P3NearSumL]
  rw [hPNS, finsum_eq_sum f hfin]
  exact le_trans hterm hsingle

/-! ## Assembly -/

theorem RectRepOrder3 {a δ e M : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hδ1 : δ < 1) (he : 0 < e)
    (hM : 0 ≤ M) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ) {H W : ℝ},
      Work.ZeroFreeTables.IsMinWideAt H W χ₁ ρ₁ → 3 * H + 1 ≤ W →
      2 ≤ Work.LinnikContract.zeroMult χ₁ ρ₁ → χ₁ ^ 3 = 1 →
      Work.LinnikContract.lamOf q ρ₁ / Real.log (q:ℝ) ≤ δ →
      Work.LinnikContract.lamOf q ρ₁ ≤ M →
      (‖(1 : ℂ) + (((2 * ρ₁.im : ℝ)) : ℂ) * Complex.I - (starRingEnd ℂ) ρ₁‖ ≤ δ →
        (2 : ℝ) * (Work.ZeroFreeTables.P3
            (((a + Work.LinnikContract.lamOf q ρ₁) : ℂ)
              / (((a + Work.LinnikContract.lamOf q ρ₁) : ℂ)
                  + ((3 * ρ₁.im * Real.log (q:ℝ) : ℝ) : ℂ) * Complex.I))).re
          ≤ Work.ZeroFreeTables.P3NearSumL q (Real.log (q:ℝ)) (χ₁ ^ 2)
              ((((1 + a / Real.log (q:ℝ) : ℝ)) : ℂ) + (((2 * ρ₁.im : ℝ)) : ℂ) * Complex.I) a
              (Work.LinnikContract.lamOf q ρ₁) δ)
      ∧ (¬ (‖(1 : ℂ) + (((2 * ρ₁.im : ℝ)) : ℂ) * Complex.I - (starRingEnd ℂ) ρ₁‖ ≤ δ) →
        (Work.ZeroFreeTables.P3
            (((a + Work.LinnikContract.lamOf q ρ₁) : ℂ)
              / ((a : ℂ) + ((3 * ρ₁.im * Real.log (q:ℝ) : ℝ) : ℂ) * Complex.I))).re ≤ e) := by
  obtain ⟨q₀f, hf⟩ :=
    Work.ZeroFreeTables.Rep9.order3_extraM_far (a := a) (δ := δ) (e := e) (M := M) ha hδ he hM
  refine ⟨max q₀f 2, ?_⟩
  intro q hq _inst χ₁ ρ₁ H W hmin hW hmult hcube hδL hMle
  have hq2 : 2 ≤ q := le_trans (le_max_right q₀f 2) hq
  have hlamnn : 0 ≤ Work.LinnikContract.lamOf q ρ₁ := Work.ZeroFreeTables.OffAxis.IsMinWideAt.lam_nonneg hmin
  refine ⟨?_, ?_⟩
  · intro hnear
    exact RectRepOrder3Near ha hδ hδ1 χ₁ ρ₁ hq2 hmin hW hmult hcube hδL hnear
  · intro hfar
    exact hf q (le_trans (le_max_left q₀f 2) hq) ρ₁ hlamnn hδL hMle hfar

end Work.ZeroFreeTables.OffAxis

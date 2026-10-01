import Mathlib
import Submission.Work.ZeroFreeTables.P3.DefsL
import Submission.Work.ZeroFreeTables.Engine
import Submission.Work.ZeroFreeTables.API
import Submission.Work.A7.zeroMult_conj_inv
import Submission.Work.ZeroFreeTables.P3.P3Bounds
import Submission.Work.LinnikAreas.boxMaxZero
import Submission.Work.ZeroFreeTables.Rep9.nearSum_bounds
import Submission.Work.ZeroFreeTables.Rep9.order3_extraM_far

namespace Work.ZeroFreeTables.Rep9

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

/-! ## The no3_extraM lemma: the order-3 case of HB §9

In the order-3 case (`χ₁³ = 1`, `χ₁² = χ̄₁ ≠ 1`) the diagonal combination (9.1) uses the
character `χ₁² = χ̄₁` at the point `σ + 2iγ` (`γ = Im ρ₁`).  The conjugate `ρ̄₁` of the multiple
zero `ρ₁` is a zero of `χ₁²` of multiplicity `zeroMult χ₁ ρ₁ ≥ 2`
(`A7.zeroMult_conj_inv`, `χ₁² = χ₁⁻¹`).  This file isolates the two branches of the argument:

* **near** (`order3_extraM_near`): if `ρ̄₁` lies in the near window of `1 + 2iγ` then the
  corresponding summand of `P3NearSumL q (log q) (χ₁²) (1 + a/log q + 2iγ)` is
  `≥ 2·Re P₃((a+λ₁)/((a+λ₁) + 3iγ log q))`, and all other summands are non-negative by HB
  (4.11) plus the wide minimality of `ρ₁`;
* **far** (`order3_extraM_far`): outside the window the argument `(a+λ₁)/(a + 3iγ log q)` is
  `O(1/log q)`, so the same `Re P₃` is `≤ e` for large `q`.
-/

/-! ## Helpers (from `Rep9/nearSum_bounds`) -/

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

/-- **Every summand of the near sum is non-negative.**  This is HB's §9 step "drop the far
zeros": a near zero `u` (within `δ < 1` of `1 + i·Im s`) has `λ(u) ≥ λ₁` by the wide minimality
of `ρ₁` — so its multiplicity is a genuine `zeroMult` zero (`pdiv` counts the complete
`L`-function at the level `q`, `zeroMult` that of the primitive character) — whence
`Re P₃(α/((s-u)𝓛)) ≥ 0` by HB (4.11). -/
private lemma nearSum_term_nonneg {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ)
    {a δ : ℝ} (hq : 2 ≤ q) (hmin : Work.ZeroFreeTables.IsMin1WideAt 10 χ₁ ρ₁)
    (hZ : Work.LinnikContract.IsZ χ₁ ρ₁) (ha : 0 < a) (hδ1 : δ < 1)
    {ψ : DirichletCharacter ℂ q} (hψ : ψ ≠ 1) {s u : ℂ} (hγ : |s.im| ≤ 8)
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
      have hu10 : |u.im| ≤ 10 := by
        have h2 := abs_le.mp him
        have h3 := abs_le.mp hγ
        rw [abs_le]
        constructor <;> linarith [h2.1, h2.2, h3.1, h3.2, hδ1]
      have hball : u ∈ Metric.closedBall (0 : ℂ) (|s.im| + 2) := by
        by_contra hb
        exact hdiv (by rw [pdiv_eq_order ψ hψ s u, if_neg hb])
      have hord : analyticOrderNatAt (DirichletCharacter.completedLFunction ψ) u ≠ 0 := by
        intro h0
        exact hdiv (by rw [pdiv_eq_order ψ hψ s u, if_pos hball, h0]; rfl)
      have hzm : Work.LinnikContract.zeroMult ψ u ≠ 0 :=
        zeroMult_ne_zero_of_completedLFunction_eq_zero ψ hψ hu0
          (apply_eq_zero_of_analyticOrderNatAt_ne_zero hord)
      have hlam : Work.LinnikContract.lamOf q ρ₁ ≤ Work.LinnikContract.lamOf q u :=
        hmin.2 ψ u hψ hzm hu10
      have hdivnn : (0 : ℝ) ≤ ((Work.ZeroFreeTables.pdiv q ψ s u : ℤ) : ℝ) := by
        rw [pdiv_eq_order ψ hψ s u, if_pos hball]
        positivity
      have hlamnn : 0 ≤ Work.LinnikContract.lamOf q ρ₁ :=
        Work.LinnikContract.API.isZ_lambda_nonneg hq hZ
      have hP3 : 0 ≤ (Work.ZeroFreeTables.P3
          ((a + Work.LinnikContract.lamOf q ρ₁)
            / ((s - u) * ((Real.log (q : ℝ) : ℝ) : ℂ)))).re :=
        P3_sub_mul_log_nonneg hq hs (by linarith) (by linarith)
      exact mul_nonneg hdivnn hP3
  · rw [if_neg hnear]
    simp

/-! ## The near branch -/

/-- The multiplicity of the conjugate zero `ρ̄₁` as a zero of the companion character `χ₁²`
(`χ₁³ = 1`): it equals `zeroMult χ₁ ρ₁` by `A7.zeroMult_conj_inv` and `χ₁² = χ₁⁻¹`. -/
private theorem zeroMult_conj_cube {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ)
    (hcube : χ₁ ^ 3 = 1) :
    Work.LinnikContract.zeroMult (χ₁ ^ 2) ((starRingEnd ℂ) ρ₁)
      = Work.LinnikContract.zeroMult χ₁ ρ₁ := by
  have hmul : χ₁ ^ 2 * χ₁ = 1 := by rw [← pow_succ]; exact hcube
  have h3 : χ₁ ^ 2 = χ₁⁻¹ := eq_inv_of_mul_eq_one_left hmul
  rw [h3]
  exact Work.A7.zeroMult_conj_inv χ₁ ρ₁

theorem order3_extraM_near {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hδ1 : δ < 1)
    {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ) (hq : 2 ≤ q)
    (hmin : Work.ZeroFreeTables.IsMin1WideAt 10 χ₁ ρ₁)
    (hZ : Work.LinnikContract.IsZ χ₁ ρ₁)
    (hmult : 2 ≤ Work.LinnikContract.zeroMult χ₁ ρ₁)
    (hcube : χ₁ ^ 3 = 1)
    (hδL : Work.LinnikContract.lamOf q ρ₁ / Real.log (q : ℝ) ≤ δ)
    (hnear : ‖(1 : ℂ) + (((2 * ρ₁.im : ℝ)) : ℂ) * Complex.I - (starRingEnd ℂ) ρ₁‖ ≤ δ) :
    (2 : ℝ) * (Work.ZeroFreeTables.P3
        (((a + Work.LinnikContract.lamOf q ρ₁) : ℂ)
          / (((a + Work.LinnikContract.lamOf q ρ₁) : ℂ)
              + ((3 * ρ₁.im * Real.log (q : ℝ) : ℝ) : ℂ) * Complex.I))).re
      ≤ Work.ZeroFreeTables.P3NearSumL q (Real.log (q : ℝ)) (χ₁ ^ 2)
          ((((1 + a / Real.log (q : ℝ) : ℝ)) : ℂ) + (((2 * ρ₁.im : ℝ)) : ℂ) * Complex.I) a
          (Work.LinnikContract.lamOf q ρ₁) δ := by
  have hχ1 : χ₁ ≠ 1 := hZ.1
  have hzm : Work.LinnikContract.zeroMult χ₁ ρ₁ ≠ 0 := hZ.2.1
  have him1 : |ρ₁.im| ≤ 1 := hZ.2.2
  have hlamnn : 0 ≤ Work.LinnikContract.lamOf q ρ₁ :=
    Work.LinnikContract.API.isZ_lambda_nonneg hq hZ
  have hαpos : 0 < a + Work.LinnikContract.lamOf q ρ₁ := by linarith
  -- the two castings of `a + λ₁` agree
  have hcast : ((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁ : ℝ) : ℂ))
      = ((a + Work.LinnikContract.lamOf q ρ₁ : ℝ) : ℂ) := by rw [Complex.ofReal_add]
  -- the companion character is non-principal
  have hχ2 : χ₁ ^ 2 ≠ 1 := by
    intro h2
    have hmul : χ₁ ^ 2 * χ₁ = 1 := by rw [← pow_succ]; exact hcube
    have h3 : χ₁ ^ 2 = χ₁⁻¹ := eq_inv_of_mul_eq_one_left hmul
    rw [h3] at h2
    exact hχ1 (inv_eq_one.mp h2)
  have hmultconj := zeroMult_conj_cube χ₁ ρ₁ hcube
  have hre1 : ρ₁.re < 1 := Work.LinnikAreas.boxMaxZeroAux.zeroMult_re_lt_one χ₁ hzm
  -- geometry: `ρ̄₁` sits at distance `(1 - Re ρ₁) + 3i·Im ρ₁` from `1 + 2i·Im ρ₁`
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
  -- the test point
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
  have hγ8 : |s.im| ≤ 8 := by
    rw [hsi]
    have h2 : |(2 : ℝ)| = 2 := by norm_num
    rw [abs_mul, h2]
    linarith [him1]
  -- the summands of the near sum
  set f : ℂ → ℝ := fun u => ((Work.ZeroFreeTables.pdiv q (χ₁ ^ 2) s u : ℤ) : ℝ) *
      (if ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ
        then (Work.ZeroFreeTables.P3
          ((a + Work.LinnikContract.lamOf q ρ₁)
            / ((s - u) * ((Real.log (q : ℝ) : ℝ) : ℂ)))).re
        else 0) with hfdef
  have hterm_nonneg : ∀ u : ℂ, 0 ≤ f u := by
    intro u
    simp only [hfdef]
    exact nearSum_term_nonneg χ₁ ρ₁ hq hmin hZ ha hδ1 hχ2 hγ8 hsr
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
      _ ≤ 1 + 1 := by
          have h1 : |ρ₁.re| ≤ 1 := by rw [abs_of_pos hrepos]; linarith
          linarith [h1, him1]
      _ ≤ |s.im| + 2 := by rw [hsi]; linarith [abs_nonneg (2 * ρ₁.im)]
  have hif : ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - (starRingEnd ℂ) ρ₁‖ ≤ δ := by
    rw [hsi]; exact hnear
  have hrepos_c : 0 < ((starRingEnd ℂ) ρ₁).re := by simpa using hrepos
  have hre1_c : ((starRingEnd ℂ) ρ₁).re < 1 := by simpa using hre1
  have hdivρ1 : (2 : ℤ) ≤ Work.ZeroFreeTables.pdiv q (χ₁ ^ 2) s ((starRingEnd ℂ) ρ₁) := by
    rw [pdiv_eq_order (χ₁ ^ 2) hχ2 s ((starRingEnd ℂ) ρ₁), if_pos hcball,
      ← zeroMult_eq_analyticOrderNatAt_of_re_pos_of_re_lt_one (χ₁ ^ 2) hχ2 hrepos_c hre1_c,
      hmultconj]
    exact_mod_cast hmult
  -- the value of the `ρ̄₁`-summand
  have hargc : (s - (starRingEnd ℂ) ρ₁) * ((Real.log (q : ℝ) : ℝ) : ℂ)
      = ((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁ : ℝ) : ℂ))
        + ((3 * ρ₁.im * Real.log (q : ℝ) : ℝ) : ℂ) * Complex.I := by
    have h := sub_mul_log_eq (q := q) hq (s := s) (u := (starRingEnd ℂ) ρ₁) hsr
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
  -- the sum dominates its `ρ̄₁`-summand
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

/-- The far branch, in the exact shape needed below (`∀ ρ₁` after the threshold `q₀`). -/
theorem order3_extraM_far_apply {a δ e M : ℝ} (ha : 0 < a) (hδ : 0 < δ) (he : 0 < e)
    (hM : 0 ≤ M) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ (ρ₁ : ℂ),
      0 ≤ Work.LinnikContract.lamOf q ρ₁ →
      Work.LinnikContract.lamOf q ρ₁ / Real.log (q : ℝ) ≤ δ →
      Work.LinnikContract.lamOf q ρ₁ ≤ M →
      ¬ (‖(1 : ℂ) + (((2 * ρ₁.im : ℝ)) : ℂ) * Complex.I - (starRingEnd ℂ) ρ₁‖ ≤ δ) →
      (Work.ZeroFreeTables.P3
          (((a + Work.LinnikContract.lamOf q ρ₁) : ℂ)
            / ((a : ℂ) + ((3 * ρ₁.im * Real.log (q : ℝ) : ℝ) : ℂ) * Complex.I))).re ≤ e :=
  order3_extraM_far ha hδ he hM

theorem order3_extraM {a δ e M : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hδ1 : δ < 1) (he : 0 < e)
    (hM : 0 ≤ M) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      Work.ZeroFreeTables.IsMin1WideAt 10 χ₁ ρ₁ → Work.LinnikContract.IsZ χ₁ ρ₁ →
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
  obtain ⟨q₀f, hf⟩ := order3_extraM_far_apply (a := a) (δ := δ) (e := e) (M := M) ha hδ he hM
  refine ⟨max q₀f 2, ?_⟩
  intro q hq hqne χ₁ ρ₁ hmin hZ hmult hcube hδL hMle
  refine ⟨?_, ?_⟩
  · intro hnear
    exact order3_extraM_near ha hδ hδ1 χ₁ ρ₁ (le_trans (le_max_right q₀f 2) hq)
      hmin hZ hmult hcube hδL hnear
  · intro hfar
    exact hf q (le_trans (le_max_left q₀f 2) hq) ρ₁
      (Work.LinnikContract.API.isZ_lambda_nonneg (le_trans (le_max_right q₀f 2) hq) hZ)
      hδL hMle hfar

end

end Work.ZeroFreeTables.Rep9

import Mathlib
import Submission.Work.ZeroFreeTables.Engine
import Submission.Work.ZeroFreeTables.CertData
import Submission.Work.ZeroFreeTables.TestFn_F_eq_integral
import Submission.Work.ZeroFreeTables.TestFn_F_nonneg
import Submission.Work.LinnikAreas.DhRepel.lemma8_5
import Submission.Work.NumberTheory.Linnik.scratch_l62app_phi
import Submission.Commons.NumberTheory.Linnik.Ksum_principal_le
import Submission.Commons.Analysis.Complex.exterior_jensen_multiplicity
import Submission.Work.LinnikContract.API.isZ_lambda_nonneg

open scoped BigOperators
open Commons.NumberTheory.Linnik (re_div_cpow_eq mul_re_mul_re star_apply_eq_inv star_cpow_ofReal_neg)

namespace Work.ZeroFreeTables

/-- The complex Laplace integral with a real argument is the real-axis Laplace transform. -/
lemma TestFn_re_integral_eq_F (T : TestFn) {z : ℂ} (hz : z.im = 0) :
    (∫ t in (0:ℝ)..T.x₀, Complex.exp (-(z * (t:ℂ))) * ((T.f t : ℝ):ℂ)).re = T.F z.re := by
  rw [Work.LinnikAreas.DhRepel.re_integral_exp_ofReal hz T.f, TestFn_F_eq_integral T z.re]

/-- F(-x) as an integral with the positive exponential. -/
lemma TestFn_F_neg_eq_integral (T : TestFn) (x : ℝ) :
    T.F (-x) = ∫ t in (0:ℝ)..T.x₀, Real.exp (x * t) * T.f t := by
  rw [TestFn_F_eq_integral T (-x)]
  apply intervalIntegral.integral_congr
  intro t _
  simp only [neg_mul, neg_neg]

/-- The primitive character inducing a non-trivial character is non-trivial. -/
lemma primitiveCharacter_ne_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) : χ.primitiveCharacter ≠ 1 := by
  intro h1
  have h2 := DirichletCharacter.changeLevel_primitiveCharacter χ
  rw [h1, DirichletCharacter.changeLevel_one χ.conductor_dvd_level] at h2
  exact hχ h2.symm

/-- L52Hyp depends on c and epsilon only through c + epsilon / 4. -/
lemma L52Hyp_reparam {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} [NeZero χ.conductor]
    {c c' ε ε' δ : ℝ} (h : c' + ε' / 4 = c + ε / 4)
    (H : Commons.NumberTheory.Linnik.L52Hyp χ c ε δ) :
    Commons.NumberTheory.Linnik.L52Hyp χ c' ε' δ := by
  intro s h1 h2 h3
  refine le_trans (H s h1 h2 h3) ?_
  rw [← h]

/-- A non-trivial zero of a non-principal Dirichlet L-function lies in the critical strip. -/
lemma zeroMult_re_mem_strip {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {ρ : ℂ}
    (hχ : χ ≠ 1) (h : Work.LinnikContract.zeroMult χ ρ ≠ 0) : 0 < ρ.re ∧ ρ.re < 1 := by
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hψ : χ.primitiveCharacter ≠ 1 := primitiveCharacter_ne_one hχ
  have hz : DirichletCharacter.completedLFunction χ.primitiveCharacter ρ = 0 :=
    apply_eq_zero_of_analyticOrderNatAt_ne_zero h
  exact Commons.NumberTheory.Linnik.completedL_zero_strip χ.primitiveCharacter hψ
    (DirichletCharacter.primitiveCharacter_isPrimitive χ) hz

/-- The divisor of the completed L-function is non-zero at a zero. -/
lemma divisor_ne_zero_of_zeroMult93 {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    [NeZero χ.conductor] {ρ : ℂ} {R : ℝ}
    (hχ : χ ≠ 1) (hR : ‖ρ‖ ≤ R) (h : Work.LinnikContract.zeroMult χ ρ ≠ 0) :
    (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
      (Metric.closedBall 0 R)) ρ ≠ 0 := by
  have hψ : χ.primitiveCharacter ≠ 1 := primitiveCharacter_ne_one hχ
  have han : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ.primitiveCharacter)
      (Metric.closedBall 0 R) :=
    fun z _ => (DirichletCharacter.differentiable_completedLFunction hψ).analyticAt z
  have hmem : ρ ∈ Metric.closedBall 0 R := by
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]; exact hR
  have hcast : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
      (Metric.closedBall 0 R)) ρ = ((Work.LinnikContract.zeroMult χ ρ : ℕ) : ℤ) :=
    Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast han hmem
  intro h0
  rw [hcast] at h0
  exact h (Nat.cast_eq_zero.mp h0)

/-- Converse: a non-zero divisor means a zero. -/
lemma zeroMult_ne_zero_of_divisor93 {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    [NeZero χ.conductor] {ρ : ℂ} {R : ℝ}
    (hχ : χ ≠ 1)
    (h : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
      (Metric.closedBall 0 R)) ρ ≠ 0) : Work.LinnikContract.zeroMult χ ρ ≠ 0 := by
  have hψ : χ.primitiveCharacter ≠ 1 := primitiveCharacter_ne_one hχ
  have han : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ.primitiveCharacter)
      (Metric.closedBall 0 R) :=
    fun z _ => (DirichletCharacter.differentiable_completedLFunction hψ).analyticAt z
  have hmem : ρ ∈ Metric.closedBall 0 R := Commons.Analysis.Complex.divisor_mem_of_ne_zero h
  have hcast : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
      (Metric.closedBall 0 R)) ρ = ((Work.LinnikContract.zeroMult χ ρ : ℕ) : ℤ) :=
    Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast han hmem
  intro h0
  rw [hcast, h0] at h
  exact h rfl

/-- A zero of chi near 1 + i y (with |y| at most 3 and delta less than 1) is no further right than rho_1. -/
lemma window_le_of_min1Wide {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ}
    (hmin : IsMin1WideAt 10 χ₁ ρ₁) (hLpos : 0 < Real.log (q:ℝ))
    {χ : DirichletCharacter ℂ q} [NeZero χ.conductor] (hχ : χ ≠ 1) {δ y : ℝ}
    (hδ1 : δ < 1) (hy : |y| ≤ 3)
    {u : ℂ}
    (hdiv : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
      (Metric.closedBall 0 (|y| + 2))) u ≠ 0)
    (hwin : ‖(1:ℂ) + (y : ℂ) * Complex.I - u‖ ≤ δ) : u.re ≤ ρ₁.re := by
  have h1 : |u.im| ≤ |y| + δ := by
    have hthis := Complex.abs_im_le_norm ((1:ℂ) + (y : ℂ) * Complex.I - u)
    have h2 : (((1:ℂ) + (y : ℂ) * Complex.I - u).im) = y - u.im := by simp
    rw [h2] at hthis
    have h3 : |u.im| ≤ |y| + |y - u.im| := by
      calc |u.im| = |y - (y - u.im)| := by ring_nf
        _ ≤ |y| + |y - u.im| := abs_sub _ _
    linarith only [hthis, h3, hwin]
  have h10 : |u.im| ≤ 10 := by linarith only [h1, abs_nonneg y, hδ1.le, hy]
  have hzm : Work.LinnikContract.zeroMult χ u ≠ 0 := zeroMult_ne_zero_of_divisor93 hχ hdiv
  have hle := hmin.2 χ u hχ hzm h10
  simp only [Work.LinnikContract.lamOf] at hle
  have hle2 : 1 - ρ₁.re ≤ 1 - u.re := le_of_mul_le_mul_right hle hLpos
  linarith only [hle2]




lemma l93_scalar_identity {a b : ℂ} (hb : ‖b‖ = 1) (k : ℝ) :
    (k ^ 2 + 1/2) * (1 + a.re) + 2 * k * b.re + k * (a * b).re + k * (a * star b).re
      + (1/2) * (b ^ 2).re + (1/4) * (a * b ^ 2).re + (1/4) * (a * star (b ^ 2)).re
      = (1 + a.re) * (k + b.re) ^ 2 := by
  have hb2 : b.re * b.re + b.im * b.im = 1 := by
    have h := Complex.normSq_eq_norm_sq b
    rw [hb] at h
    have h1 : Complex.normSq b = b.re * b.re + b.im * b.im := Complex.normSq_apply b
    rw [h1] at h
    norm_num at h
    linarith [h]
  simp only [pow_two, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.star_def,
    Complex.conj_re, Complex.conj_im]
  ring_nf
  linear_combination (-(1/2) * (1 + a.re)) * hb2

/-- **Pointwise form of the section 9 positivity of Heath-Brown for Lemma 9.3.** -/
theorem ksum_pointwise_L93 {q : ℕ} [NeZero q] {f : ℝ → ℝ} (hf : ∀ t, 0 ≤ f t)
    {L β γ₁ γ₂ k : ℝ} (χ₁ χ₂ : DirichletCharacter ℂ q) {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ (k ^ 2 + 1/2) *
          ((ArithmeticFunction.vonMangoldt n : ℝ) *
              ((1 : DirichletCharacter ℂ q) (n : ZMod q) / (n : ℂ) ^ (β : ℂ)).re
                * f (Real.log n / L)
            + (ArithmeticFunction.vonMangoldt n : ℝ) *
              (χ₁ (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + (γ₁ : ℂ) * Complex.I)).re
                * f (Real.log n / L))
      + 2 * k * ((ArithmeticFunction.vonMangoldt n : ℝ) *
              (χ₂ (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + (γ₂ : ℂ) * Complex.I)).re
                * f (Real.log n / L))
      + k * ((ArithmeticFunction.vonMangoldt n : ℝ) *
              ((χ₁ * χ₂) (n : ZMod q) /
                (n : ℂ) ^ ((β : ℂ) + ((γ₁ : ℂ) + (γ₂ : ℂ)) * Complex.I)).re
                * f (Real.log n / L))
      + k * ((ArithmeticFunction.vonMangoldt n : ℝ) *
              ((χ₁ * χ₂⁻¹) (n : ZMod q) /
                (n : ℂ) ^ ((β : ℂ) + ((γ₁ : ℂ) - (γ₂ : ℂ)) * Complex.I)).re
                * f (Real.log n / L))
      + (1/2) * ((ArithmeticFunction.vonMangoldt n : ℝ) *
              ((χ₂ ^ 2) (n : ZMod q) /
                (n : ℂ) ^ ((β : ℂ) + ((γ₂ : ℂ) + (γ₂ : ℂ)) * Complex.I)).re
                * f (Real.log n / L))
      + (1/4) * ((ArithmeticFunction.vonMangoldt n : ℝ) *
              ((χ₁ * χ₂ ^ 2) (n : ZMod q) /
                (n : ℂ) ^ ((β : ℂ) + ((γ₁ : ℂ) + 2 * (γ₂ : ℂ)) * Complex.I)).re
                * f (Real.log n / L))
      + (1/4) * ((ArithmeticFunction.vonMangoldt n : ℝ) *
              ((χ₁ * ((χ₂⁻¹) ^ 2)) (n : ZMod q) /
                (n : ℂ) ^ ((β : ℂ) + ((γ₁ : ℂ) - 2 * (γ₂ : ℂ)) * Complex.I)).re
                * f (Real.log n / L)) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnc : (n : ℂ) ≠ 0 := by simp only [ne_eq, Nat.cast_eq_zero]; omega
  set a₁ : ℂ := χ₁ (n : ZMod q) * (n : ℂ) ^ (-((γ₁ : ℂ) * Complex.I)) with ha₁
  set a₂ : ℂ := χ₂ (n : ZMod q) * (n : ℂ) ^ (-((γ₂ : ℂ) * Complex.I)) with ha₂
  have hq01 : ((1 : DirichletCharacter ℂ q) (n : ZMod q)) = 0 ∨
      ((1 : DirichletCharacter ℂ q) (n : ZMod q)) = 1 := by
    by_cases h : IsUnit (n : ZMod q)
    · right; rw [← h.unit_spec]; exact MulChar.one_apply h
    · left; exact MulChar.map_nonunit (1 : DirichletCharacter ℂ q) h
  have e0 : ((1 : DirichletCharacter ℂ q) (n : ZMod q) / (n : ℂ) ^ (β : ℂ)).re
      = (n : ℝ) ^ (-β) * ((1 : DirichletCharacter ℂ q) (n : ZMod q)).re := by
    have h := re_div_cpow_eq (1 : DirichletCharacter ℂ q) hn β 0
    simpa only [add_zero, neg_zero, Complex.cpow_zero, mul_one] using h
  have e1 : (χ₁ (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + (γ₁ : ℂ) * Complex.I)).re
      = (n : ℝ) ^ (-β) * a₁.re := by
    rw [re_div_cpow_eq χ₁ hn β ((γ₁ : ℂ) * Complex.I), ha₁]
  have e2 : (χ₂ (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + (γ₂ : ℂ) * Complex.I)).re
      = (n : ℝ) ^ (-β) * a₂.re := by
    rw [re_div_cpow_eq χ₂ hn β ((γ₂ : ℂ) * Complex.I), ha₂]
  have hsplit3 : (n : ℂ) ^ (-(((γ₁ : ℂ) + (γ₂ : ℂ)) * Complex.I))
      = (n : ℂ) ^ (-((γ₁ : ℂ) * Complex.I)) * (n : ℂ) ^ (-((γ₂ : ℂ) * Complex.I)) := by
    rw [← Complex.cpow_add _ _ hnc]; congr 1; ring
  have hsplit4 : (n : ℂ) ^ (-(((γ₁ : ℂ) - (γ₂ : ℂ)) * Complex.I))
      = (n : ℂ) ^ (-((γ₁ : ℂ) * Complex.I)) * (n : ℂ) ^ ((γ₂ : ℂ) * Complex.I) := by
    rw [← Complex.cpow_add _ _ hnc]; congr 1; ring
  have hsplit5 : (n : ℂ) ^ (-(((γ₂ : ℂ) + (γ₂ : ℂ)) * Complex.I))
      = (n : ℂ) ^ (-((γ₂ : ℂ) * Complex.I)) * (n : ℂ) ^ (-((γ₂ : ℂ) * Complex.I)) := by
    rw [← Complex.cpow_add _ _ hnc]; congr 1; ring
  have hsplit6 : (n : ℂ) ^ (-(((γ₁ : ℂ) + 2 * (γ₂ : ℂ)) * Complex.I))
      = (n : ℂ) ^ (-((γ₁ : ℂ) * Complex.I)) * ((n : ℂ) ^ (-((γ₂ : ℂ) * Complex.I))) ^ 2 := by
    rw [show -(((γ₁ : ℂ) + 2 * (γ₂ : ℂ)) * Complex.I)
        = (-((γ₁ : ℂ) * Complex.I)) + ((-((γ₂ : ℂ) * Complex.I)) + (-((γ₂ : ℂ) * Complex.I)))
        by ring,
      Complex.cpow_add _ _ hnc, Complex.cpow_add _ _ hnc, pow_two]
  have hsplit7 : (n : ℂ) ^ (-(((γ₁ : ℂ) - 2 * (γ₂ : ℂ)) * Complex.I))
      = (n : ℂ) ^ (-((γ₁ : ℂ) * Complex.I)) * (((n : ℂ) ^ ((γ₂ : ℂ) * Complex.I))) ^ 2 := by
    rw [show -(((γ₁ : ℂ) - 2 * (γ₂ : ℂ)) * Complex.I)
        = (-((γ₁ : ℂ) * Complex.I)) + (((γ₂ : ℂ) * Complex.I) + ((γ₂ : ℂ) * Complex.I))
        by ring,
      Complex.cpow_add _ _ hnc, Complex.cpow_add _ _ hnc, pow_two]
  have hstar2 : star (a₂ ^ 2) = (star a₂) ^ 2 := map_pow (starRingEnd ℂ) a₂ 2
  have hsa₂ : star a₂ = (n : ℂ) ^ ((γ₂ : ℂ) * Complex.I) * χ₂⁻¹ (n : ZMod q) := by
    rw [ha₂, star_mul, star_apply_eq_inv χ₂, star_cpow_ofReal_neg hn γ₂]
  have e3 : ((χ₁ * χ₂) (n : ZMod q) /
        (n : ℂ) ^ ((β : ℂ) + ((γ₁ : ℂ) + (γ₂ : ℂ)) * Complex.I)).re
      = (n : ℝ) ^ (-β) * (a₁ * a₂).re := by
    rw [re_div_cpow_eq (χ₁ * χ₂) hn β (((γ₁ : ℂ) + (γ₂ : ℂ)) * Complex.I)]
    congr 1
    rw [MulChar.mul_apply, ha₁, ha₂, hsplit3]
    ring
  have e4 : ((χ₁ * χ₂⁻¹) (n : ZMod q) /
        (n : ℂ) ^ ((β : ℂ) + ((γ₁ : ℂ) - (γ₂ : ℂ)) * Complex.I)).re
      = (n : ℝ) ^ (-β) * (a₁ * star a₂).re := by
    rw [re_div_cpow_eq (χ₁ * χ₂⁻¹) hn β (((γ₁ : ℂ) - (γ₂ : ℂ)) * Complex.I)]
    congr 1
    rw [MulChar.mul_apply, ha₁, hsa₂, hsplit4]
    ring
  have e5 : ((χ₂ ^ 2) (n : ZMod q) /
        (n : ℂ) ^ ((β : ℂ) + ((γ₂ : ℂ) + (γ₂ : ℂ)) * Complex.I)).re
      = (n : ℝ) ^ (-β) * (a₂ ^ 2).re := by
    rw [re_div_cpow_eq (χ₂ ^ 2) hn β (((γ₂ : ℂ) + (γ₂ : ℂ)) * Complex.I)]
    congr 1
    rw [pow_two, MulChar.mul_apply, ha₂, hsplit5, pow_two]
    ring
  have e6 : ((χ₁ * χ₂ ^ 2) (n : ZMod q) /
        (n : ℂ) ^ ((β : ℂ) + ((γ₁ : ℂ) + 2 * (γ₂ : ℂ)) * Complex.I)).re
      = (n : ℝ) ^ (-β) * (a₁ * a₂ ^ 2).re := by
    rw [re_div_cpow_eq (χ₁ * χ₂ ^ 2) hn β (((γ₁ : ℂ) + 2 * (γ₂ : ℂ)) * Complex.I)]
    congr 1
    rw [MulChar.mul_apply, pow_two, MulChar.mul_apply, ha₁, ha₂, hsplit6, pow_two]
    ring
  have e7 : ((χ₁ * ((χ₂⁻¹) ^ 2)) (n : ZMod q) /
        (n : ℂ) ^ ((β : ℂ) + ((γ₁ : ℂ) - 2 * (γ₂ : ℂ)) * Complex.I)).re
      = (n : ℝ) ^ (-β) * (a₁ * star (a₂ ^ 2)).re := by
    rw [re_div_cpow_eq (χ₁ * ((χ₂⁻¹) ^ 2)) hn β (((γ₁ : ℂ) - 2 * (γ₂ : ℂ)) * Complex.I)]
    congr 1
    rw [MulChar.mul_apply, pow_two, MulChar.mul_apply, ha₁, hstar2, hsa₂, hsplit7, pow_two]
    ring
  rcases hq01 with h | h
  · have hnu : ¬ IsUnit (n : ZMod q) := fun hunit => by
      have h1 : ((1 : DirichletCharacter ℂ q) (n : ZMod q)) = 1 := by
        rw [← hunit.unit_spec]; exact MulChar.one_apply hunit
      rw [h] at h1; exact zero_ne_one h1
    have hχ₁0 : χ₁ (n : ZMod q) = 0 := MulChar.map_nonunit χ₁ hnu
    have hχ₂0 : χ₂ (n : ZMod q) = 0 := MulChar.map_nonunit χ₂ hnu
    have hχ₂i0 : χ₂⁻¹ (n : ZMod q) = 0 := MulChar.map_nonunit (χ₂⁻¹) hnu
    rw [h]
    simp only [MulChar.mul_apply, pow_two]
    rw [hχ₁0, hχ₂0, hχ₂i0]
    simp only [zero_div, Complex.zero_re, mul_zero, add_zero, zero_add]
    norm_num
  · have hunit : IsUnit (n : ZMod q) := by
      by_contra hnu
      rw [MulChar.map_nonunit (1 : DirichletCharacter ℂ q) hnu] at h
      exact zero_ne_one h
    have hnormχ₂ : ‖χ₂ (n : ZMod q)‖ = 1 := by
      have hN : χ₂ ^ Fintype.card (ZMod q)ˣ = 1 := MulChar.pow_card_eq_one χ₂
      have h1 : χ₂ (n : ZMod q) ^ Fintype.card (ZMod q)ˣ = 1 := by
        rw [← hunit.unit_spec, ← MulChar.pow_apply_coe χ₂ _ hunit.unit, hN,
          MulChar.one_apply_coe]
      exact Complex.norm_eq_one_of_pow_eq_one h1 Fintype.card_ne_zero
    have hnormz₂ : ‖(n : ℂ) ^ (-((γ₂ : ℂ) * Complex.I))‖ = 1 := by
      rw [show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_cpow_eq_rpow_re_of_pos hnpos]
      simp
    have hnorm₂ : ‖a₂‖ = 1 := by rw [ha₂, Complex.norm_mul, hnormχ₂, hnormz₂, one_mul]
    have hnormχ₁ : ‖χ₁ (n : ZMod q)‖ ≤ 1 := DirichletCharacter.norm_le_one χ₁ _
    have hnormz₁ : ‖(n : ℂ) ^ (-((γ₁ : ℂ) * Complex.I))‖ ≤ 1 := by
      rw [show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_cpow_eq_rpow_re_of_pos hnpos]
      simp
    have hnorm₁ : ‖a₁‖ ≤ 1 := by
      rw [ha₁, Complex.norm_mul]
      exact mul_le_one₀ hnormχ₁ (norm_nonneg _) hnormz₁
    have h1a : 0 ≤ 1 + a₁.re := by
      have hle := Complex.abs_re_le_norm a₁
      rw [abs_le] at hle
      linarith [hle.1, hnorm₁]
    have hscalar : (k ^ 2 + 1/2) * (1 + a₁.re) + 2 * k * a₂.re
        + k * (a₁ * a₂).re + k * (a₁ * star a₂).re + (1/2) * (a₂ ^ 2).re
        + (1/4) * (a₁ * a₂ ^ 2).re + (1/4) * (a₁ * star (a₂ ^ 2)).re
        = (1 + a₁.re) * (k + a₂.re) ^ 2 := l93_scalar_identity hnorm₂ k
    have hmain : (k ^ 2 + 1/2) *
          ((ArithmeticFunction.vonMangoldt n : ℝ) *
              ((1 : DirichletCharacter ℂ q) (n : ZMod q) / (n : ℂ) ^ (β : ℂ)).re
                * f (Real.log n / L)
            + (ArithmeticFunction.vonMangoldt n : ℝ) *
              (χ₁ (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + (γ₁ : ℂ) * Complex.I)).re
                * f (Real.log n / L))
      + 2 * k * ((ArithmeticFunction.vonMangoldt n : ℝ) *
              (χ₂ (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + (γ₂ : ℂ) * Complex.I)).re
                * f (Real.log n / L))
      + k * ((ArithmeticFunction.vonMangoldt n : ℝ) *
              ((χ₁ * χ₂) (n : ZMod q) /
                (n : ℂ) ^ ((β : ℂ) + ((γ₁ : ℂ) + (γ₂ : ℂ)) * Complex.I)).re
                * f (Real.log n / L))
      + k * ((ArithmeticFunction.vonMangoldt n : ℝ) *
              ((χ₁ * χ₂⁻¹) (n : ZMod q) /
                (n : ℂ) ^ ((β : ℂ) + ((γ₁ : ℂ) - (γ₂ : ℂ)) * Complex.I)).re
                * f (Real.log n / L))
      + (1/2) * ((ArithmeticFunction.vonMangoldt n : ℝ) *
              ((χ₂ ^ 2) (n : ZMod q) /
                (n : ℂ) ^ ((β : ℂ) + ((γ₂ : ℂ) + (γ₂ : ℂ)) * Complex.I)).re
                * f (Real.log n / L))
      + (1/4) * ((ArithmeticFunction.vonMangoldt n : ℝ) *
              ((χ₁ * χ₂ ^ 2) (n : ZMod q) /
                (n : ℂ) ^ ((β : ℂ) + ((γ₁ : ℂ) + 2 * (γ₂ : ℂ)) * Complex.I)).re
                * f (Real.log n / L))
      + (1/4) * ((ArithmeticFunction.vonMangoldt n : ℝ) *
              ((χ₁ * ((χ₂⁻¹) ^ 2)) (n : ZMod q) /
                (n : ℂ) ^ ((β : ℂ) + ((γ₁ : ℂ) - 2 * (γ₂ : ℂ)) * Complex.I)).re
                * f (Real.log n / L))
        = (ArithmeticFunction.vonMangoldt n : ℝ) * f (Real.log n / L) * (n : ℝ) ^ (-β)
            * ((1 + a₁.re) * (k + a₂.re) ^ 2) := by
      rw [e0, e1, e2, e3, e4, e5, e6, e7, h, Complex.one_re, ← hscalar]
      ring
    rw [hmain]
    have hΛ : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) := by positivity
    have hFf : 0 ≤ f (Real.log n / L) := hf _
    have hnb : 0 ≤ (n : ℝ) ^ (-β) := Real.rpow_nonneg hnpos.le _
    have hk2 : 0 ≤ (k + a₂.re) ^ 2 := sq_nonneg _
    exact mul_nonneg (mul_nonneg (mul_nonneg hΛ hFf) hnb) (mul_nonneg h1a hk2)

/-- **The section 9 positivity of Heath-Brown for Lemma 9.3, at the level of the von Mangoldt sums.** -/
theorem ksum_positivity_L93 {q : ℕ} [NeZero q] {f : ℝ → ℝ} (hf : ∀ t : ℝ, 0 ≤ f t)
    {x₀ L β γ₁ γ₂ k : ℝ} (hx₀ : 0 < x₀) (hL : 0 < L) (hk : 0 ≤ k)
    (hsupp : ∀ t : ℝ, x₀ ≤ t → f t = 0) (χ₁ χ₂ : DirichletCharacter ℂ q) :
    0 ≤ (k ^ 2 + 1/2) * (Ksum q f L β (1 : DirichletCharacter ℂ q)
          + Ksum q f L (β + (γ₁ : ℂ) * Complex.I) χ₁)
      + 2 * k * Ksum q f L (β + (γ₂ : ℂ) * Complex.I) χ₂
      + k * Ksum q f L (β + ((γ₁ : ℂ) + (γ₂ : ℂ)) * Complex.I) (χ₁ * χ₂)
      + k * Ksum q f L (β + ((γ₁ : ℂ) - (γ₂ : ℂ)) * Complex.I) (χ₁ * χ₂⁻¹)
      + (1/2) * Ksum q f L (β + ((γ₂ : ℂ) + (γ₂ : ℂ)) * Complex.I) (χ₂ ^ 2)
      + (1/4) * Ksum q f L (β + ((γ₁ : ℂ) + 2 * (γ₂ : ℂ)) * Complex.I) (χ₁ * χ₂ ^ 2)
      + (1/4) * Ksum q f L (β + ((γ₁ : ℂ) - 2 * (γ₂ : ℂ)) * Complex.I) (χ₁ * ((χ₂⁻¹) ^ 2)) := by
  classical
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → x₀ ≤ Real.log n / L := by
    refine ⟨Nat.ceil (Real.exp (x₀ * L)) + 1, fun n hn => ?_⟩
    have h1 : Real.exp (x₀ * L) ≤ (n : ℝ) := by
      have : (Nat.ceil (Real.exp (x₀ * L)) : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast (le_trans (Nat.le_succ _) hn)
      exact le_trans (Nat.le_ceil _) this
    have h2 : x₀ * L ≤ Real.log (n : ℝ) := by
      have := Real.log_le_log (Real.exp_pos _) h1
      rwa [Real.log_exp] at this
    rw [le_div_iff₀ hL]
    linarith
  set s₀ : ℕ → ℝ := fun n => (ArithmeticFunction.vonMangoldt n : ℝ) *
      ((1 : DirichletCharacter ℂ q) (n : ZMod q) / (n : ℂ) ^ (β : ℂ)).re * f (Real.log n / L) with hs₀
  set s₁ : ℕ → ℝ := fun n => (ArithmeticFunction.vonMangoldt n : ℝ) *
      (χ₁ (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + (γ₁ : ℂ) * Complex.I)).re
      * f (Real.log n / L) with hs₁
  set s₂ : ℕ → ℝ := fun n => (ArithmeticFunction.vonMangoldt n : ℝ) *
      (χ₂ (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + (γ₂ : ℂ) * Complex.I)).re
      * f (Real.log n / L) with hs₂
  set s₃ : ℕ → ℝ := fun n => (ArithmeticFunction.vonMangoldt n : ℝ) *
      ((χ₁ * χ₂) (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + ((γ₁ : ℂ) + (γ₂ : ℂ)) * Complex.I)).re
      * f (Real.log n / L) with hs₃
  set s₄ : ℕ → ℝ := fun n => (ArithmeticFunction.vonMangoldt n : ℝ) *
      ((χ₁ * χ₂⁻¹) (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + ((γ₁ : ℂ) - (γ₂ : ℂ)) * Complex.I)).re
      * f (Real.log n / L) with hs₄
  set s₅ : ℕ → ℝ := fun n => (ArithmeticFunction.vonMangoldt n : ℝ) *
      ((χ₂ ^ 2) (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + ((γ₂ : ℂ) + (γ₂ : ℂ)) * Complex.I)).re
      * f (Real.log n / L) with hs₅
  set s₆ : ℕ → ℝ := fun n => (ArithmeticFunction.vonMangoldt n : ℝ) *
      ((χ₁ * χ₂ ^ 2) (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + ((γ₁ : ℂ) + 2 * (γ₂ : ℂ)) * Complex.I)).re
      * f (Real.log n / L) with hs₆
  set s₇ : ℕ → ℝ := fun n => (ArithmeticFunction.vonMangoldt n : ℝ) *
      ((χ₁ * ((χ₂⁻¹) ^ 2)) (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + ((γ₁ : ℂ) - 2 * (γ₂ : ℂ)) * Complex.I)).re
      * f (Real.log n / L) with hs₇
  have hzero : ∀ n : ℕ, N ≤ n → s₀ n = 0 ∧ s₁ n = 0 ∧ s₂ n = 0 ∧ s₃ n = 0 ∧ s₄ n = 0
      ∧ s₅ n = 0 ∧ s₆ n = 0 ∧ s₇ n = 0 := by
    intro n hn
    have hf0 : f (Real.log n / L) = 0 := hsupp _ (hN n hn)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      · simp only [hs₀, hs₁, hs₂, hs₃, hs₄, hs₅, hs₆, hs₇, hf0]
        ring
  have h₀ : (∑' n : ℕ, s₀ n) = ∑ n ∈ Finset.range N, s₀ n :=
    tsum_eq_sum (fun n hn => (hzero n (by simpa using hn)).1)
  have h₁ : (∑' n : ℕ, s₁ n) = ∑ n ∈ Finset.range N, s₁ n :=
    tsum_eq_sum (fun n hn => (hzero n (by simpa using hn)).2.1)
  have h₂ : (∑' n : ℕ, s₂ n) = ∑ n ∈ Finset.range N, s₂ n :=
    tsum_eq_sum (fun n hn => (hzero n (by simpa using hn)).2.2.1)
  have h₃ : (∑' n : ℕ, s₃ n) = ∑ n ∈ Finset.range N, s₃ n :=
    tsum_eq_sum (fun n hn => (hzero n (by simpa using hn)).2.2.2.1)
  have h₄ : (∑' n : ℕ, s₄ n) = ∑ n ∈ Finset.range N, s₄ n :=
    tsum_eq_sum (fun n hn => (hzero n (by simpa using hn)).2.2.2.2.1)
  have h₅ : (∑' n : ℕ, s₅ n) = ∑ n ∈ Finset.range N, s₅ n :=
    tsum_eq_sum (fun n hn => (hzero n (by simpa using hn)).2.2.2.2.2.1)
  have h₆ : (∑' n : ℕ, s₆ n) = ∑ n ∈ Finset.range N, s₆ n :=
    tsum_eq_sum (fun n hn => (hzero n (by simpa using hn)).2.2.2.2.2.2.1)
  have h₇ : (∑' n : ℕ, s₇ n) = ∑ n ∈ Finset.range N, s₇ n :=
    tsum_eq_sum (fun n hn => (hzero n (by simpa using hn)).2.2.2.2.2.2.2)
  have hterm : ∀ n ∈ Finset.range N,
      0 ≤ (k ^ 2 + 1/2) * (s₀ n + s₁ n) + 2 * k * s₂ n + k * s₃ n + k * s₄ n
        + (1/2) * s₅ n + (1/4) * s₆ n + (1/4) * s₇ n := by
    intro n hn
    rw [Finset.mem_range] at hn
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      have hΛ0 : ArithmeticFunction.vonMangoldt 0 = 0 := by
        rw [ArithmeticFunction.vonMangoldt_eq_zero_iff]; exact not_isPrimePow_zero
      simp only [hs₀, hs₁, hs₂, hs₃, hs₄, hs₅, hs₆, hs₇]
      rw [hΛ0]
      norm_num
    · exact ksum_pointwise_L93 (q := q) hf (L := L) (β := β) (γ₁ := γ₁) (γ₂ := γ₂)
        (k := k) χ₁ χ₂ h
  have hfin : ∑ n ∈ Finset.range N,
        ((k ^ 2 + 1/2) * (s₀ n + s₁ n) + 2 * k * s₂ n + k * s₃ n + k * s₄ n
          + (1/2) * s₅ n + (1/4) * s₆ n + (1/4) * s₇ n)
      = (k ^ 2 + 1/2) * ((∑ n ∈ Finset.range N, s₀ n) + (∑ n ∈ Finset.range N, s₁ n))
        + 2 * k * (∑ n ∈ Finset.range N, s₂ n) + k * (∑ n ∈ Finset.range N, s₃ n)
        + k * (∑ n ∈ Finset.range N, s₄ n) + (1/2) * (∑ n ∈ Finset.range N, s₅ n)
        + (1/4) * (∑ n ∈ Finset.range N, s₆ n) + (1/4) * (∑ n ∈ Finset.range N, s₇ n) := by
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hsum : 0 ≤ ∑ n ∈ Finset.range N,
      ((k ^ 2 + 1/2) * (s₀ n + s₁ n) + 2 * k * s₂ n + k * s₃ n + k * s₄ n
        + (1/2) * s₅ n + (1/4) * s₆ n + (1/4) * s₇ n) := Finset.sum_nonneg hterm
  simp only [Ksum]
  rw [h₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇]
  exact hfin ▸ hsum
/-- **Heath-Brown Lemma 9.3, engine form.**  For a test function of HB Conditions 1 and 2 and
any slack parameters, the (9.14) inequality holds for large q, with the constant from the
window bounds of Lemma 5.2/5.3. -/
theorem hbLemma9_3_engine (T : Work.ZeroFreeTables.TestFn) (k c ε δ : ℝ) (hk : 0 ≤ k)
    (hε : 0 < ε) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ χ₂ : DirichletCharacter ℂ q) (ρ₁ ρ₂ : ℂ),
      (∀ (χ : DirichletCharacter ℂ q) [NeZero χ.conductor], χ ≠ 1 →
        Commons.NumberTheory.Linnik.L52Hyp χ c ε δ) →
      Work.ZeroFreeTables.IsMin1WideAt 10 χ₁ ρ₁ → Work.LinnikContract.IsZ χ₁ ρ₁ →
      Work.LinnikContract.IsZ χ₂ ρ₂ → χ₁ ≠ 1 → χ₂ ≠ 1 →
      χ₂ ≠ χ₁ → χ₂ ≠ χ₁⁻¹ → χ₂ ^ 2 ≠ 1 → χ₂ ^ 2 ≠ χ₁ → χ₂ ^ 2 ≠ χ₁⁻¹ →
      Work.LinnikContract.lamOf q ρ₁ ≤ 1 → Work.LinnikContract.lamOf q ρ₂ ≤ 1 →
      0 ≤ (k ^ 2 + 1 / 2) * (T.F (-(Work.LinnikContract.lamOf q ρ₁)) - T.F 0) -
            2 * k * T.F (Work.LinnikContract.lamOf q ρ₂ - Work.LinnikContract.lamOf q ρ₁) +
            T.f 0 * ((k ^ 2 + 4 * k + 3 / 2) * (c + ε)) := by
  obtain ⟨B, hB, hBnd⟩ := T.f_bound
  set c₁ : ℝ := c + ε / 8 with hc₁
  set ε₁ : ℝ := ε / 2 with hε₁
  have hcε : c₁ + ε₁ / 4 = c + ε / 4 := by rw [hc₁, hε₁]; ring
  have hε₁pos : 0 < ε₁ := by rw [hε₁]; linarith only [hε]
  set εp : ℝ := 3 * (k ^ 2 + 4 * k + 3 / 2) * ε / (8 * (k ^ 2 + 1 / 2)) with hεp
  have hεppos : 0 < εp := by
    rw [hεp]
    apply div_pos (by positivity)
    positivity
  have hnum : (k ^ 2 + 1 / 2) * εp + (k ^ 2 + 4 * k + 3 / 2) * (c₁ + ε₁)
      = (k ^ 2 + 4 * k + 3 / 2) * (c + ε) := by
    rw [hεp, hc₁, hε₁]
    have hw : (0:ℝ) < 8 * (k ^ 2 + 1 / 2) := by positivity
    field_simp
    ring
  have hF : ∀ z : ℂ, 0 ≤ z.re →
      0 ≤ (∫ t in (0:ℝ)..T.x₀, Complex.exp (-(z * (t:ℂ))) * ((T.f t : ℝ):ℂ)).re :=
    fun z hz => by rw [← T.Fc_spec]; exact T.Fc_re_nonneg z hz
  obtain ⟨qP, hqP⟩ := Commons.NumberTheory.Linnik.Ksum_principal_le T.x₀ B T.x₀_pos hB
    T.f_cont T.f_supp T.f_diff hBnd hεppos T.f0_pos
  obtain ⟨qS, hqS⟩ := Commons.NumberTheory.Linnik.Ksum_le_self_of_L52_phi T.x₀ B c₁
    T.x₀_pos hB T.f_cont T.f_supp T.f_diff hBnd T.f0_pos hF hε₁pos hδ0 hδ1
  obtain ⟨qN, hqN⟩ := Work.LinnikAreas.DhRepel.Ksum_le_single_ne_of_L52_phi T.x₀ B c₁
    T.x₀_pos hB T.f_cont T.f_supp T.f_diff hBnd T.f0_pos hF hε₁pos hδ0 hδ1
  set R : ℕ := max (max qP qS) qN with hRdef
  set S : ℕ := max 16 (Nat.ceil (Real.exp (1 / δ)) + 1) with hSdef
  refine ⟨max R S + 1, ?_⟩
  intro q hq _inst χ₁ χ₂ ρ₁ ρ₂ hL52 hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE hlam₁ hlam₂
  have hRq : R ≤ q := by omega
  have hSq : S ≤ q := by omega
  have hqP'' : qP ≤ q := by
    have : qP ≤ R := by rw [hRdef]; exact le_trans (le_max_left _ _) (le_max_left _ _)
    omega
  have hqS'' : qS ≤ q := by
    have : qS ≤ R := by rw [hRdef]; exact le_trans (le_max_right _ _) (le_max_left _ _)
    omega
  have hqN'' : qN ≤ q := by
    have : qN ≤ R := by rw [hRdef]; exact le_max_right _ _
    omega
  have hq16 : 16 ≤ q := by
    have : 16 ≤ S := by rw [hSdef]; exact le_max_left _ _
    omega
  have hexp : Real.exp (1 / δ) ≤ (q : ℝ) := by
    have h1 : Nat.ceil (Real.exp (1 / δ)) + 1 ≤ S := by rw [hSdef]; exact le_max_right _ _
    have h2 : Real.exp (1 / δ) ≤ ((Nat.ceil (Real.exp (1 / δ)) : ℕ) : ℝ) := Nat.le_ceil _
    have h3 : (Nat.ceil (Real.exp (1 / δ)) + 1) ≤ q := le_trans h1 hSq
    have h4 : ((Nat.ceil (Real.exp (1 / δ)) : ℕ) : ℝ) + 1 ≤ (q : ℝ) := by exact_mod_cast h3
    linarith only [h2, h4]
  have hq1 : 1 < q := by omega
  have hLpos : 0 < Real.log (q:ℝ) := Real.log_pos (by exact_mod_cast hq1)
  have hlog2 : (0.69 : ℝ) < Real.log 2 := by linarith only [Real.log_two_gt_d9]
  have hlog16 : (2.75 : ℝ) < Real.log 16 := by
    rw [show (16:ℝ) = 2^4 by norm_num, Real.log_pow]
    push_cast
    linarith only [hlog2]
  have hL27 : (2.75 : ℝ) < Real.log (q:ℝ) :=
    lt_of_lt_of_le hlog16 (Real.log_le_log (by norm_num) (by exact_mod_cast hq16))
  have hL1 : 1 ≤ Real.log (q:ℝ) := by linarith only [hL27]
  have hLL1 : 1 ≤ Real.log (Real.log (q:ℝ)) := by
    have he1 : Real.exp 1 < 2.75 := by linarith only [Real.exp_one_lt_d9]
    have h : Real.exp 1 ≤ Real.log (q:ℝ) := by linarith only [he1, hL27]
    have := Real.log_le_log (Real.exp_pos 1) h
    rwa [Real.log_exp] at this
  have hsqrt1 : 1 ≤ Real.sqrt (Real.log (Real.log (q:ℝ))) := Real.one_le_sqrt.mpr hLL1
  have hδL : 1 ≤ δ * Real.log (q:ℝ) := by
    have h : 1 / δ ≤ Real.log (q:ℝ) := by
      have := Real.log_le_log (by positivity) hexp
      rwa [Real.log_exp] at this
    have h2 : δ * (1 / δ) = 1 := by field_simp
    calc (1:ℝ) = δ * (1 / δ) := h2.symm
      _ ≤ δ * Real.log (q:ℝ) := mul_le_mul_of_nonneg_left h hδ0.le
  have hzm₁ : Work.LinnikContract.zeroMult χ₁ ρ₁ ≠ 0 := hZ₁.2.1
  have hzm₂ : Work.LinnikContract.zeroMult χ₂ ρ₂ ≠ 0 := hZ₂.2.1
  have hγ₁ : |ρ₁.im| ≤ 1 := hZ₁.2.2
  have hγ₂ : |ρ₂.im| ≤ 1 := hZ₂.2.2
  have hstrip₁ : 0 < ρ₁.re ∧ ρ₁.re < 1 := zeroMult_re_mem_strip hχ₁ hzm₁
  have hstrip₂ : 0 < ρ₂.re ∧ ρ₂.re < 1 := zeroMult_re_mem_strip hχ₂ hzm₂
  haveI hinst₁ : NeZero χ₁.conductor := ⟨χ₁.conductor_ne_zero⟩
  haveI hinst₂ : NeZero χ₂.conductor := ⟨χ₂.conductor_ne_zero⟩
  have hlam₁nn : 0 ≤ Work.LinnikContract.lamOf q ρ₁ := by
    rw [Work.LinnikContract.lamOf]
    exact mul_nonneg (by linarith only [hstrip₁.2]) hLpos.le
  have hminle : Work.LinnikContract.lamOf q ρ₁ ≤ Work.LinnikContract.lamOf q ρ₂ :=
    hmin.2 χ₂ ρ₂ hχ₂ hzm₂ (by linarith only [hγ₂])
  have hsqle : |Work.LinnikContract.lamOf q ρ₁| ≤ Real.sqrt (Real.log (Real.log (q:ℝ))) := by
    rw [abs_of_nonneg hlam₁nn]
    exact le_trans hlam₁ hsqrt1
  have hbase₁ : (1 - ρ₁.re) * Real.log (q:ℝ) ≤ Real.sqrt (Real.log (Real.log (q:ℝ))) := by
    have h := hsqle
    rw [Work.LinnikContract.lamOf] at h
    rwa [abs_of_nonneg (mul_nonneg (by linarith only [hstrip₁.2]) hLpos.le)] at h
  have hbase₂ : (1 - ρ₂.re) * Real.log (q:ℝ) ≤ Real.sqrt (Real.log (Real.log (q:ℝ))) := by
    have h2 : 0 ≤ Work.LinnikContract.lamOf q ρ₂ := by
      rw [Work.LinnikContract.lamOf]
      exact mul_nonneg (by linarith only [hstrip₂.2]) hLpos.le
    have h : |Work.LinnikContract.lamOf q ρ₂| ≤ Real.sqrt (Real.log (Real.log (q:ℝ))) := by
      rw [abs_of_nonneg h2]; exact le_trans hlam₂ hsqrt1
    rw [Work.LinnikContract.lamOf] at h
    rwa [abs_of_nonneg (mul_nonneg (by linarith only [hstrip₂.2]) hLpos.le)] at h
  have hreg1 : |ρ₁.re - 1| ≤ Real.sqrt (Real.log (Real.log (q:ℝ))) / Real.log (q:ℝ) := by
    rw [abs_sub_comm, abs_of_nonneg (by linarith only [hstrip₁.2]), le_div_iff₀ hLpos]
    exact hbase₁
  have hreg2 : 1 - Real.sqrt (Real.log (Real.log (q:ℝ))) / Real.log (q:ℝ) ≤ ρ₁.re := by
    rw [sub_le_comm, le_div_iff₀ hLpos]
    exact hbase₁
  have hrept : ∀ y : ℝ, (((ρ₁.re : ℂ) + (y : ℂ) * Complex.I).re) = ρ₁.re := fun y => by simp
  have himpt : ∀ y : ℝ, (((ρ₁.re : ℂ) + (y : ℂ) * Complex.I).im) = y := fun y => by simp
  have hR₁ : ‖ρ₁‖ ≤ |ρ₁.im| + 2 := by
    have h1 : ‖ρ₁‖ ≤ |ρ₁.re| + |ρ₁.im| := Complex.norm_le_abs_re_add_abs_im ρ₁
    have h2 : |ρ₁.re| < 1 := by rw [abs_of_pos hstrip₁.1]; exact hstrip₁.2
    linarith only [h1, h2]
  have hR₂ : ‖ρ₂‖ ≤ |ρ₂.im| + 2 := by
    have h1 : ‖ρ₂‖ ≤ |ρ₂.re| + |ρ₂.im| := Complex.norm_le_abs_re_add_abs_im ρ₂
    have h2 : |ρ₂.re| < 1 := by rw [abs_of_pos hstrip₂.1]; exact hstrip₂.2
    linarith only [h1, h2]
  have hdiv₁ : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
      (Metric.closedBall 0 (|ρ₁.im| + 2))) ρ₁ ≠ 0 :=
    divisor_ne_zero_of_zeroMult93 hχ₁ hR₁ hzm₁
  have hdiv₂ : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₂.primitiveCharacter)
      (Metric.closedBall 0 (|ρ₂.im| + 2))) ρ₂ ≠ 0 :=
    divisor_ne_zero_of_zeroMult93 hχ₂ hR₂ hzm₂
  have hzwz : ∀ (χ : DirichletCharacter ℂ q) [NeZero χ.conductor], χ ≠ 1 →
      ∀ (y : ℝ), |y| ≤ 3 → ∀ u : ℂ, Work.LinnikContract.zeroMult χ u ≠ 0 →
      ‖(1:ℂ) + (y : ℂ) * Complex.I - u‖ ≤ δ →
      u.re ≤ (((ρ₁.re : ℂ) + (y : ℂ) * Complex.I).re) := by
    intro χ inst hχ y hy u hzm hwin
    have hle := hmin.2 χ u hχ hzm (by
      have h1 : |u.im| ≤ |y| + δ := by
        have hthis := Complex.abs_im_le_norm ((1:ℂ) + (y : ℂ) * Complex.I - u)
        have h2 : (((1:ℂ) + (y : ℂ) * Complex.I - u).im) = y - u.im := by simp
        rw [h2] at hthis
        have h3 : |u.im| ≤ |y| + |y - u.im| := by
          calc |u.im| = |y - (y - u.im)| := by ring_nf
            _ ≤ |y| + |y - u.im| := abs_sub _ _
        linarith only [hthis, h3, hwin]
      linarith only [h1, abs_nonneg y, hδ1.le, hy])
    simp only [Work.LinnikContract.lamOf] at hle
    have hle2 : 1 - ρ₁.re ≤ 1 - u.re := le_of_mul_le_mul_right hle hLpos
    have hre : (((ρ₁.re : ℂ) + (y : ℂ) * Complex.I).re) = ρ₁.re := by simp
    rw [hre]
    linarith only [hle2]
  have hwinχ : ∀ (χ : DirichletCharacter ℂ q) [NeZero χ.conductor], χ ≠ 1 → ∀ (y : ℝ),
      |y| ≤ 3 → ∀ u : ℂ,
      (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
        (Metric.closedBall 0 (|(((ρ₁.re : ℂ) + (y : ℂ) * Complex.I).im)| + 2))) u ≠ 0 →
      ‖(1:ℂ) + ((((ρ₁.re : ℂ) + (y : ℂ) * Complex.I).im) : ℂ) * Complex.I - u‖ ≤ δ →
      u.re ≤ (((ρ₁.re : ℂ) + (y : ℂ) * Complex.I).re) := by
    intro χ inst hχ y hy u hdiv hwin
    rw [himpt y] at hdiv hwin
    exact hzwz χ hχ y hy u (zeroMult_ne_zero_of_divisor93 hχ hdiv) hwin
  have hw₁ : ‖(1:ℂ) + ((ρ₁.im : ℂ)) * Complex.I - ρ₁‖ ≤ δ := by
    have h1 : (1:ℂ) + ((ρ₁.im : ℂ)) * Complex.I - ρ₁ = ((1 - ρ₁.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    rw [h1, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith only [hstrip₁.2])]
    have hlam₁' := hlam₁
    rw [Work.LinnikContract.lamOf] at hlam₁'
    have h2 : (1 - ρ₁.re) * Real.log (q:ℝ) ≤ δ * Real.log (q:ℝ) := by
      linarith only [hlam₁', hδL]
    exact le_of_mul_le_mul_right h2 hLpos
  have hw₂ : ‖(1:ℂ) + ((ρ₂.im : ℂ)) * Complex.I - ρ₂‖ ≤ δ := by
    have h1 : (1:ℂ) + ((ρ₂.im : ℂ)) * Complex.I - ρ₂ = ((1 - ρ₂.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    rw [h1, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith only [hstrip₂.2])]
    have hlam₂' := hlam₂
    rw [Work.LinnikContract.lamOf] at hlam₂'
    have h2 : (1 - ρ₂.re) * Real.log (q:ℝ) ≤ δ * Real.log (q:ℝ) := by
      linarith only [hlam₂', hδL]
    exact le_of_mul_le_mul_right h2 hLpos
  have hρnn₁ : 0 ≤ (∫ t in (0:ℝ)..T.x₀,
      Complex.exp (-(((((ρ₁.re : ℂ) + (ρ₁.im : ℂ) * Complex.I) - ρ₁) * (Real.log (q:ℝ))) * (t:ℂ)))
        * ((T.f t : ℝ):ℂ)).re := by
    have h0 : (((ρ₁.re : ℂ) + (ρ₁.im : ℂ) * Complex.I) - ρ₁) * (Real.log (q:ℝ)) = 0 := by
      have h1 : ((ρ₁.re : ℂ) + (ρ₁.im : ℂ) * Complex.I) - ρ₁ = 0 := by
        apply Complex.ext <;> simp
      rw [h1, zero_mul]
    rw [h0]
    simp only [zero_mul, neg_zero, Complex.exp_zero, one_mul]
    rw [intervalIntegral.integral_ofReal, Complex.ofReal_re]
    exact intervalIntegral.integral_nonneg (le_of_lt T.x₀_pos) (fun t _ => T.f_nonneg t)
  have hpt₂ : ((ρ₁.re : ℂ) + (ρ₂.im : ℂ) * Complex.I) - ρ₂ = ((ρ₁.re - ρ₂.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
  have hcast₂ : (((ρ₁.re : ℂ) + (ρ₂.im : ℂ) * Complex.I) - ρ₂) * (Real.log (q:ℝ))
      = ((Work.LinnikContract.lamOf q ρ₂ - Work.LinnikContract.lamOf q ρ₁ : ℝ) : ℂ) := by
    rw [hpt₂, ← Complex.ofReal_mul]
    congr 1
    rw [Work.LinnikContract.lamOf, Work.LinnikContract.lamOf]; ring
  have hρnn₂ : 0 ≤ (∫ t in (0:ℝ)..T.x₀,
      Complex.exp (-(((((ρ₁.re : ℂ) + (ρ₂.im : ℂ) * Complex.I) - ρ₂) * (Real.log (q:ℝ))) * (t:ℂ)))
        * ((T.f t : ℝ):ℂ)).re := by
    rw [hcast₂, TestFn_re_integral_eq_F T (by simp), Complex.ofReal_re]
    exact TestFn_F_nonneg T _
  have hI1 : (∫ t in (0:ℝ)..T.x₀,
      Complex.exp (-(((((ρ₁.re : ℂ) + (ρ₁.im : ℂ) * Complex.I) - ρ₁) * (Real.log (q:ℝ))) * (t:ℂ)))
        * ((T.f t : ℝ):ℂ)).re = T.F 0 := by
    have h0 : (((ρ₁.re : ℂ) + (ρ₁.im : ℂ) * Complex.I) - ρ₁) * (Real.log (q:ℝ)) = 0 := by
      have h1 : ((ρ₁.re : ℂ) + (ρ₁.im : ℂ) * Complex.I) - ρ₁ = 0 := by
        apply Complex.ext <;> simp
      rw [h1, zero_mul]
    rw [h0]
    simp only [zero_mul, neg_zero, Complex.exp_zero, one_mul]
    rw [intervalIntegral.integral_ofReal, Complex.ofReal_re, TestFn_F_eq_integral T 0]
    apply intervalIntegral.integral_congr
    intro t _
    simp
  have hI2 : (∫ t in (0:ℝ)..T.x₀,
      Complex.exp (-(((((ρ₁.re : ℂ) + (ρ₂.im : ℂ) * Complex.I) - ρ₂) * (Real.log (q:ℝ))) * (t:ℂ)))
        * ((T.f t : ℝ):ℂ)).re
      = T.F (Work.LinnikContract.lamOf q ρ₂ - Work.LinnikContract.lamOf q ρ₁) := by
    rw [hcast₂, TestFn_re_integral_eq_F T (by simp), Complex.ofReal_re]
  have hK0 : Ksum q T.f (Real.log (q:ℝ)) (ρ₁.re : ℂ) (1 : DirichletCharacter ℂ q)
      ≤ Real.log (q:ℝ) * T.F (-(Work.LinnikContract.lamOf q ρ₁))
        + T.f 0 * εp * Real.log (q:ℝ) := by
    have h := hqP (q := q) hqP'' (β := ρ₁.re) (lam := Work.LinnikContract.lamOf q ρ₁)
      (by rw [Work.LinnikContract.lamOf]; ring) hreg1
    rw [← TestFn_F_neg_eq_integral T (Work.LinnikContract.lamOf q ρ₁)] at h
    exact h
  have hself : ∀ (χ : DirichletCharacter ℂ q) [NeZero χ.conductor], χ ≠ 1 →
      ∀ (y : ℝ) (s : ℂ), s = ((ρ₁.re : ℂ) + (y : ℂ) * Complex.I) → |y| ≤ 3 →
      Ksum q T.f (Real.log (q:ℝ)) s χ ≤ T.f 0 * (c₁ + ε₁) * Real.log (q:ℝ) := by
    intro χ inst hχ y s hs hy
    subst hs
    haveI : NeZero χ.conductor := inst
    refine hqS (q := q) hqS'' χ hχ ?_ ?_ ?_ ?_ ?_
    · rw [hrept y]; exact hreg1
    · rw [himpt y]; linarith only [hy, hL1]
    · rw [hrept y]; exact hreg2
    · exact L52Hyp_reparam hcε (hL52 χ hχ)
    · exact hwinχ χ hχ y hy
  have hy34 : |ρ₁.im + ρ₂.im| ≤ 3 := by
    have h : |ρ₁.im + ρ₂.im| ≤ |ρ₁.im| + |ρ₂.im| := abs_add_le _ _
    linarith only [h, hγ₁, hγ₂]
  have hy56 : |ρ₁.im - ρ₂.im| ≤ 3 := by
    have h : |ρ₁.im - ρ₂.im| ≤ |ρ₁.im| + |ρ₂.im| := by
      calc |ρ₁.im - ρ₂.im| = |ρ₁.im + -ρ₂.im| := by ring_nf
        _ ≤ |ρ₁.im| + |-ρ₂.im| := abs_add_le _ _
        _ = |ρ₁.im| + |ρ₂.im| := by rw [abs_neg]
    linarith only [h, hγ₁, hγ₂]
  have hy5 : |ρ₂.im + ρ₂.im| ≤ 3 := by
    have h : |ρ₂.im + ρ₂.im| ≤ |ρ₂.im| + |ρ₂.im| := abs_add_le _ _
    linarith only [h, hγ₂]
  have hy67 : |ρ₁.im + 2 * ρ₂.im| ≤ 3 := by
    have h : |ρ₁.im + 2 * ρ₂.im| ≤ |ρ₁.im| + |2 * ρ₂.im| := abs_add_le _ _
    have h2 : |2 * ρ₂.im| = 2 * |ρ₂.im| := by rw [abs_mul]; norm_num
    linarith only [h, h2, hγ₁, hγ₂]
  have hy77 : |ρ₁.im - 2 * ρ₂.im| ≤ 3 := by
    have h : |ρ₁.im - 2 * ρ₂.im| ≤ |ρ₁.im| + |2 * ρ₂.im| := by
      calc |ρ₁.im - 2 * ρ₂.im| = |ρ₁.im + -(2 * ρ₂.im)| := by ring_nf
        _ ≤ |ρ₁.im| + |-(2 * ρ₂.im)| := abs_add_le _ _
        _ = |ρ₁.im| + |2 * ρ₂.im| := by rw [abs_neg]
    have h2 : |2 * ρ₂.im| = 2 * |ρ₂.im| := by rw [abs_mul]; norm_num
    linarith only [h, h2, hγ₁, hγ₂]
  have hK1 : Ksum q T.f (Real.log (q:ℝ)) ((ρ₁.re : ℂ) + (ρ₁.im : ℂ) * Complex.I) χ₁
      ≤ -(Real.log (q:ℝ)) * T.F 0 + T.f 0 * (c₁ + ε₁) * Real.log (q:ℝ) := by
    have h := hqN (q := q) hqN'' χ₁ hχ₁
      (s := ((ρ₁.re : ℂ) + (ρ₁.im : ℂ) * Complex.I)) (ρ := ρ₁)
      (by rw [hrept ρ₁.im]; exact hreg1)
      (by rw [himpt ρ₁.im]; linarith only [hγ₁, hL1])
      (by rw [hrept ρ₁.im]; exact hreg2)
      (L52Hyp_reparam hcε (hL52 χ₁ hχ₁))
      (by rw [himpt ρ₁.im]; exact hdiv₁)
      (by rw [himpt ρ₁.im]; exact hw₁)
      hρnn₁
      (fun u hdiv hwin _ => hwinχ χ₁ hχ₁ ρ₁.im (by linarith only [hγ₁]) u hdiv hwin)
    rw [hI1] at h
    exact h
  have hK2 : Ksum q T.f (Real.log (q:ℝ)) ((ρ₁.re : ℂ) + (ρ₂.im : ℂ) * Complex.I) χ₂
      ≤ -(Real.log (q:ℝ)) * T.F (Work.LinnikContract.lamOf q ρ₂ - Work.LinnikContract.lamOf q ρ₁)
        + T.f 0 * (c₁ + ε₁) * Real.log (q:ℝ) := by
    have h := hqN (q := q) hqN'' χ₂ hχ₂
      (s := ((ρ₁.re : ℂ) + (ρ₂.im : ℂ) * Complex.I)) (ρ := ρ₂)
      (by rw [hrept ρ₂.im]; exact hreg1)
      (by rw [himpt ρ₂.im]; linarith only [hγ₂, hL1])
      (by rw [hrept ρ₂.im]; exact hreg2)
      (L52Hyp_reparam hcε (hL52 χ₂ hχ₂))
      (by rw [himpt ρ₂.im]; exact hdiv₂)
      (by rw [himpt ρ₂.im]; exact hw₂)
      hρnn₂
      (fun u hdiv hwin _ => hwinχ χ₂ hχ₂ ρ₂.im (by linarith only [hγ₂]) u hdiv hwin)
    rw [hI2] at h
    exact h
  have hK3 : Ksum q T.f (Real.log (q:ℝ))
      ((ρ₁.re : ℂ) + ((ρ₁.im : ℂ) + (ρ₂.im : ℂ)) * Complex.I) (χ₁ * χ₂)
      ≤ T.f 0 * (c₁ + ε₁) * Real.log (q:ℝ) := by
    haveI : NeZero (χ₁ * χ₂).conductor := ⟨(χ₁ * χ₂).conductor_ne_zero⟩
    have hne : χ₁ * χ₂ ≠ 1 := by
      intro hcon
      refine hneB ?_
      have h' := congrArg (fun z => χ₁⁻¹ * z) hcon
      rw [mul_one] at h'
      rw [← h']
      group
    exact hself (χ₁ * χ₂) hne (ρ₁.im + ρ₂.im)
      ((ρ₁.re : ℂ) + ((ρ₁.im : ℂ) + (ρ₂.im : ℂ)) * Complex.I) (by push_cast; ring) hy34
  have hK4 : Ksum q T.f (Real.log (q:ℝ))
      ((ρ₁.re : ℂ) + ((ρ₁.im : ℂ) - (ρ₂.im : ℂ)) * Complex.I) (χ₁ * χ₂⁻¹)
      ≤ T.f 0 * (c₁ + ε₁) * Real.log (q:ℝ) := by
    haveI : NeZero (χ₁ * χ₂⁻¹).conductor := ⟨(χ₁ * χ₂⁻¹).conductor_ne_zero⟩
    have hne : χ₁ * χ₂⁻¹ ≠ 1 := by
      intro hcon
      refine hneA ?_
      have h' := congrArg (fun z => z * χ₂) hcon
      rw [one_mul] at h'
      rw [← h']
      group
    exact hself (χ₁ * χ₂⁻¹) hne (ρ₁.im - ρ₂.im)
      ((ρ₁.re : ℂ) + ((ρ₁.im : ℂ) - (ρ₂.im : ℂ)) * Complex.I) (by push_cast; ring) hy56
  have hK5 : Ksum q T.f (Real.log (q:ℝ))
      ((ρ₁.re : ℂ) + ((ρ₂.im : ℂ) + (ρ₂.im : ℂ)) * Complex.I) (χ₂ ^ 2)
      ≤ T.f 0 * (c₁ + ε₁) * Real.log (q:ℝ) := by
    haveI : NeZero (χ₂ ^ 2).conductor := ⟨(χ₂ ^ 2).conductor_ne_zero⟩
    exact hself (χ₂ ^ 2) hneC (ρ₂.im + ρ₂.im)
      ((ρ₁.re : ℂ) + ((ρ₂.im : ℂ) + (ρ₂.im : ℂ)) * Complex.I) (by push_cast; ring) hy5
  have hK6 : Ksum q T.f (Real.log (q:ℝ))
      ((ρ₁.re : ℂ) + ((ρ₁.im : ℂ) + 2 * (ρ₂.im : ℂ)) * Complex.I) (χ₁ * χ₂ ^ 2)
      ≤ T.f 0 * (c₁ + ε₁) * Real.log (q:ℝ) := by
    haveI : NeZero (χ₁ * χ₂ ^ 2).conductor := ⟨(χ₁ * χ₂ ^ 2).conductor_ne_zero⟩
    have hne : χ₁ * χ₂ ^ 2 ≠ 1 := by
      intro hcon
      refine hneE ?_
      have h' := congrArg (fun z => χ₁⁻¹ * z) hcon
      rw [mul_one] at h'
      rw [← h']
      group
    exact hself (χ₁ * χ₂ ^ 2) hne (ρ₁.im + 2 * ρ₂.im)
      ((ρ₁.re : ℂ) + ((ρ₁.im : ℂ) + 2 * (ρ₂.im : ℂ)) * Complex.I) (by push_cast; ring) hy67
  have hK7 : Ksum q T.f (Real.log (q:ℝ))
      ((ρ₁.re : ℂ) + ((ρ₁.im : ℂ) - 2 * (ρ₂.im : ℂ)) * Complex.I) (χ₁ * ((χ₂⁻¹) ^ 2))
      ≤ T.f 0 * (c₁ + ε₁) * Real.log (q:ℝ) := by
    haveI : NeZero (χ₁ * ((χ₂⁻¹) ^ 2)).conductor := ⟨(χ₁ * ((χ₂⁻¹) ^ 2)).conductor_ne_zero⟩
    have hne : χ₁ * ((χ₂⁻¹) ^ 2) ≠ 1 := by
      intro hcon
      refine hneD ?_
      have h' := congrArg (fun z => z * χ₂ ^ 2) hcon
      rw [one_mul] at h'
      rw [← h']
      group
    exact hself (χ₁ * ((χ₂⁻¹) ^ 2)) hne (ρ₁.im - 2 * ρ₂.im)
      ((ρ₁.re : ℂ) + ((ρ₁.im : ℂ) - 2 * (ρ₂.im : ℂ)) * Complex.I) (by push_cast; ring) hy77
  -- the positivity
  have hpos := ksum_positivity_L93 (q := q) T.f_nonneg T.x₀_pos hLpos hk T.f_supp χ₁ χ₂
    (L := Real.log (q:ℝ)) (β := ρ₁.re) (γ₁ := ρ₁.im) (γ₂ := ρ₂.im) (k := k)
  -- weighted bounds
  have hw0 : 0 ≤ k ^ 2 + 1 / 2 := by positivity
  have h2k : 0 ≤ 2 * k := by linarith only [hk]
  have hk0 : 0 ≤ k := hk
  have h12 : 0 ≤ (1/2 : ℝ) := by norm_num
  have h14 : 0 ≤ (1/4 : ℝ) := by norm_num
  have hK0w := mul_le_mul_of_nonneg_left hK0 hw0
  have hK1w := mul_le_mul_of_nonneg_left hK1 hw0
  have hK2w := mul_le_mul_of_nonneg_left hK2 h2k
  have hK3w := mul_le_mul_of_nonneg_left hK3 hk0
  have hK4w := mul_le_mul_of_nonneg_left hK4 hk0
  have hK5w := mul_le_mul_of_nonneg_left hK5 h12
  have hK6w := mul_le_mul_of_nonneg_left hK6 h14
  have hK7w := mul_le_mul_of_nonneg_left hK7 h14
  have hcomb : 0 ≤ (k ^ 2 + 1 / 2) *
        ((Real.log (q:ℝ) * T.F (-(Work.LinnikContract.lamOf q ρ₁))
            + T.f 0 * εp * Real.log (q:ℝ))
          + (-(Real.log (q:ℝ)) * T.F 0 + T.f 0 * (c₁ + ε₁) * Real.log (q:ℝ)))
      + 2 * k * (-(Real.log (q:ℝ)) * T.F (Work.LinnikContract.lamOf q ρ₂ - Work.LinnikContract.lamOf q ρ₁)
          + T.f 0 * (c₁ + ε₁) * Real.log (q:ℝ))
      + k * (T.f 0 * (c₁ + ε₁) * Real.log (q:ℝ))
      + k * (T.f 0 * (c₁ + ε₁) * Real.log (q:ℝ))
      + (1/2) * (T.f 0 * (c₁ + ε₁) * Real.log (q:ℝ))
      + (1/4) * (T.f 0 * (c₁ + ε₁) * Real.log (q:ℝ))
      + (1/4) * (T.f 0 * (c₁ + ε₁) * Real.log (q:ℝ)) := by
    linarith only [hpos, hK0w, hK1w, hK2w, hK3w, hK4w, hK5w, hK6w, hK7w]
  have hkey : Real.log (q:ℝ) * ((k ^ 2 + 1 / 2) * (T.F (-(Work.LinnikContract.lamOf q ρ₁)) - T.F 0)
        - 2 * k * T.F (Work.LinnikContract.lamOf q ρ₂ - Work.LinnikContract.lamOf q ρ₁)
        + T.f 0 * ((k ^ 2 + 4 * k + 3 / 2) * (c + ε)))
      = (k ^ 2 + 1 / 2) *
        ((Real.log (q:ℝ) * T.F (-(Work.LinnikContract.lamOf q ρ₁))
            + T.f 0 * εp * Real.log (q:ℝ))
          + (-(Real.log (q:ℝ)) * T.F 0 + T.f 0 * (c₁ + ε₁) * Real.log (q:ℝ)))
      + 2 * k * (-(Real.log (q:ℝ)) * T.F (Work.LinnikContract.lamOf q ρ₂ - Work.LinnikContract.lamOf q ρ₁)
          + T.f 0 * (c₁ + ε₁) * Real.log (q:ℝ))
      + k * (T.f 0 * (c₁ + ε₁) * Real.log (q:ℝ))
      + k * (T.f 0 * (c₁ + ε₁) * Real.log (q:ℝ))
      + (1/2) * (T.f 0 * (c₁ + ε₁) * Real.log (q:ℝ))
      + (1/4) * (T.f 0 * (c₁ + ε₁) * Real.log (q:ℝ))
      + (1/4) * (T.f 0 * (c₁ + ε₁) * Real.log (q:ℝ)) := by
    rw [← hnum]
    ring
  rw [← hkey] at hcomb
  exact (mul_nonneg_iff_of_pos_left hLpos).mp hcomb

end Work.ZeroFreeTables

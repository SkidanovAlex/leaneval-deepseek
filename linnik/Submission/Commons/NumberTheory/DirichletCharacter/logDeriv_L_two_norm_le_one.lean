import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.NumberTheory.LSeries.DirichletContinuation

open scoped BigOperators LSeries.notation ArithmeticFunction
open Set MeasureTheory intervalIntegral
set_option autoImplicit false
noncomputable section

namespace Commons.NumberTheory.DirichletCharacter

/-!
# The logarithmic derivative of a Dirichlet L-function on the line `Re s = 2`

We prove the unconditional bound

`‖L'(χ, 2+iT) / L(χ, 2+iT)‖ ≤ 1` for every Dirichlet character `χ` (including the principal
one) and every real `T`.

The proof avoids the Euler product and uses the classical Dirichlet-series identity
`L'/L(s) = -∑_n Λ(n) χ(n) n^{-s}` on `Re s > 1`, which is exactly
`DirichletCharacter.LSeries_twist_vonMangoldt_eq` in Mathlib.  The bound then follows from
`‖χ(n)‖ ≤ 1`, `Λ(n) ≥ 0` and the elementary estimate `∑_n Λ(n)/n² ≤ ∑_{n≥2} log n/n² ≤ 1`.

The latter is proved by the integral test: `x ↦ log x / x²` is antitone on `[3, ∞)` with
`∫_3^∞ log x/x² dx = (log 3 + 1)/3`, so
`∑_{n≥2} log n/n² ≤ log 2/4 + log 3/9 + (log 3 + 1)/3 < 359/360 < 1`.
-/

/-! ### The elementary tail estimate `∑_{n ≥ 2} log n / n² ≤ 1` -/

/-- The antiderivative `-((log x + 1)/x)` of `log x / x²`. -/
private lemma hasDerivAt_log_antideriv (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun x : ℝ => -(Real.log x + 1) / x) (Real.log x / x ^ 2) x := by
  have h1 : HasDerivAt (fun x : ℝ => -(Real.log x + 1)) (-(x⁻¹)) x :=
    (Real.hasDerivAt_log hx).add_const 1 |>.neg
  have h2 : HasDerivAt (fun x : ℝ => x) 1 x := hasDerivAt_id x
  have hd := h1.div h2 hx
  have heq : (-x⁻¹ * x - -(Real.log x + 1) * 1) / x ^ 2 = Real.log x / x ^ 2 := by
    field_simp
    ring
  rw [heq] at hd
  exact hd

/-- `x ↦ log x / x²` is antitone on `[3, ∞)`. -/
private lemma log_div_sq_antitoneOn_Ici_three :
    AntitoneOn (fun x : ℝ => Real.log x / x ^ 2) (Ici 3) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici (3 : ℝ))
  · have hlog : ContinuousOn Real.log (Ici (3 : ℝ)) :=
      Real.continuousOn_log.mono (fun x hx => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        have := Set.mem_Ici.mp hx
        linarith)
    exact hlog.div (by fun_prop) (fun x hx => by
      have := Set.mem_Ici.mp hx
      exact pow_ne_zero 2 (by linarith))
  · rw [interior_Ici]
    have hlog : DifferentiableOn ℝ Real.log (Ioi (3 : ℝ)) := fun x hx =>
      (Real.differentiableAt_log (by have := Set.mem_Ioi.mp hx; linarith)).differentiableWithinAt
    exact hlog.div (by fun_prop) (fun x hx => by
      have := Set.mem_Ioi.mp hx
      exact pow_ne_zero 2 (by linarith))
  · rw [interior_Ici]
    intro x hx
    have hx3 : (3 : ℝ) < x := Set.mem_Ioi.mp hx
    have hx0 : x ≠ 0 := by linarith
    have hderiv : HasDerivAt (fun x : ℝ => Real.log x / x ^ 2)
        ((x⁻¹ * x ^ 2 - Real.log x * (2 * x)) / (x ^ 2) ^ 2) x :=
      (Real.hasDerivAt_log hx0).div (by simpa using (hasDerivAt_pow 2 x)) (by positivity)
    rw [hderiv.deriv]
    have hlogx : (1 : ℝ) < Real.log x := by
      have h3 : (1 : ℝ) < Real.log 3 := by
        have h := Real.log_three_gt_d9; linarith
      have hle : Real.log 3 ≤ Real.log x := Real.log_le_log (by norm_num) (by linarith)
      linarith
    have hnum : x⁻¹ * x ^ 2 - Real.log x * (2 * x) ≤ 0 := by
      have h1 : x⁻¹ * x ^ 2 = x := by field_simp
      rw [h1]
      nlinarith
    have hden : 0 < (x ^ 2) ^ 2 := by positivity
    exact div_nonpos_of_nonpos_of_nonneg hnum (le_of_lt hden)

/-- The value of the improper integral `∫_a^b log x / x² dx`. -/
private lemma integral_log_div_sq (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ∫ x in a..b, Real.log x / x ^ 2 =
      -(Real.log b + 1) / b + (Real.log a + 1) / a := by
  have hderiv : ∀ x ∈ Ioo a b, HasDerivAt (fun x : ℝ => -(Real.log x + 1) / x)
      (Real.log x / x ^ 2) x := fun x hx =>
    hasDerivAt_log_antideriv x (by have := Set.mem_Ioo.mp hx; linarith [this.1, ha])
  have hcontF : ContinuousOn (fun x : ℝ => -(Real.log x + 1) / x) (Icc a b) := by
    have hlog : ContinuousOn Real.log (Icc a b) :=
      Real.continuousOn_log.mono (fun x hx => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        have := Set.mem_Icc.mp hx
        linarith [this.1, ha])
    have h1 : ContinuousOn (fun x : ℝ => -(Real.log x + 1)) (Icc a b) :=
      (hlog.add continuousOn_const).neg
    refine h1.div continuousOn_id (fun x hx => ?_)
    have := Set.mem_Icc.mp hx
    linarith [this.1, ha]
  have hint : IntervalIntegrable (fun x : ℝ => Real.log x / x ^ 2) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    have hlog : ContinuousOn Real.log (Icc a b) :=
      Real.continuousOn_log.mono (fun x hx => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        have := Set.mem_Icc.mp hx
        linarith [this.1, ha])
    refine hlog.div (by fun_prop) (fun x hx => ?_)
    have hx0 : x ≠ 0 := by have := Set.mem_Icc.mp hx; linarith [this.1, ha]
    exact pow_ne_zero 2 hx0
  have h := integral_eq_sub_of_hasDerivAt_of_le hab hcontF hderiv hint
  rw [h]
  ring

private lemma log_div_sq_nonneg (n : ℕ) : 0 ≤ Real.log (n : ℝ) / (n : ℝ) ^ 2 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · exact div_nonneg (Real.log_nonneg (by exact_mod_cast hn)) (by positivity)

/-- Every partial sum of `∑_{n ≥ 2} log n / n²` is at most `1`. -/
private lemma sum_range_log_div_sq_le_one (K : ℕ) :
    (∑ n ∈ Finset.range K, Real.log (n : ℝ) / (n : ℝ) ^ 2) ≤ 1 := by
  set f : ℕ → ℝ := fun n => Real.log (n : ℝ) / (n : ℝ) ^ 2 with hfdef
  by_cases hK : K ≤ 4
  · calc (∑ n ∈ Finset.range K, f n)
        ≤ ∑ n ∈ Finset.range 4, f n :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset.mpr (fun x hx => by
              simp only [Finset.mem_range] at hx ⊢; omega))
            (fun n _ _ => by simp only [hfdef]; exact log_div_sq_nonneg n)
      _ = Real.log 2 / 4 + Real.log 3 / 9 := by
          simp only [hfdef]
          norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Real.log_zero, Real.log_one]
      _ ≤ 1 := by
          have h2 := Real.log_two_lt_d9
          have h3 := Real.log_three_lt_d9
          nlinarith
  · have hK5 : 5 ≤ K := by omega
    have hf0 : f 0 = 0 := by simp [hfdef]
    have hf1 : f 1 = 0 := by simp [hfdef]
    have h04 : (∑ n ∈ Finset.Ico 0 4, f n) = f 2 + f 3 := by
      rw [Finset.sum_Ico_eq_sum_range]
      norm_num [Finset.sum_range_succ, Finset.sum_range_zero, hf0, hf1]
    have h24 : (∑ n ∈ Finset.Ico 2 4, f n) = f 2 + f 3 := by
      rw [Finset.sum_Ico_eq_sum_range]
      norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
    have hrange : (∑ n ∈ Finset.range K, f n) = f 2 + f 3 + ∑ n ∈ Finset.Ico 4 K, f n := by
      rw [Finset.range_eq_Ico]
      rw [← Finset.sum_Ico_consecutive (f := f) (m := 0) (n := 4) (k := K) (by norm_num)
        (by omega : 4 ≤ K)]
      rw [h04]
    have hreindex : (∑ n ∈ Finset.Ico 4 K, f n)
        = ∑ i ∈ Finset.Ico 3 (K - 1), (fun x : ℝ => Real.log x / x ^ 2) (i + 1 : ℕ) := by
      rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
      rw [show K - 4 = (K - 1) - 3 by omega]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [hfdef]
      have hidx : (4 + j : ℕ) = 3 + j + 1 := by omega
      rw [hidx]
    have hanti : AntitoneOn (fun x : ℝ => Real.log x / x ^ 2) (Icc (3 : ℝ) ((K - 1 : ℕ) : ℝ)) :=
      log_div_sq_antitoneOn_Ici_three.mono (fun x hx => hx.1)
    have hbound := hanti.sum_le_integral_Ico (a := 3) (b := K - 1) (by omega)
    have hint : ∫ x in (3 : ℝ)..((K - 1 : ℕ) : ℝ), Real.log x / x ^ 2
        = -(Real.log ((K - 1 : ℕ) : ℝ) + 1) / ((K - 1 : ℕ) : ℝ) + (Real.log 3 + 1) / 3 :=
      integral_log_div_sq 3 ((K - 1 : ℕ) : ℝ) (by norm_num) (by
        have : (3 : ℕ) ≤ K - 1 := by omega
        exact_mod_cast this)
    have htail_nonpos : -(Real.log ((K - 1 : ℕ) : ℝ) + 1) / ((K - 1 : ℕ) : ℝ) ≤ 0 := by
      have hy1 : (1 : ℝ) ≤ ((K - 1 : ℕ) : ℝ) := by
        have : (1 : ℕ) ≤ K - 1 := by omega
        exact_mod_cast this
      have hlogpos : 0 ≤ Real.log ((K - 1 : ℕ) : ℝ) := Real.log_nonneg hy1
      have hypos : 0 < ((K - 1 : ℕ) : ℝ) := by linarith
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt hypos)
    calc (∑ n ∈ Finset.range K, f n)
        = f 2 + f 3 + ∑ n ∈ Finset.Ico 4 K, f n := hrange
      _ = f 2 + f 3 + ∑ i ∈ Finset.Ico 3 (K - 1),
            (fun x : ℝ => Real.log x / x ^ 2) (i + 1 : ℕ) := by rw [hreindex]
      _ ≤ f 2 + f 3 + ∫ x in (3 : ℝ)..((K - 1 : ℕ) : ℝ), Real.log x / x ^ 2 := by
            linarith [hbound]
      _ = f 2 + f 3 + (-(Real.log ((K - 1 : ℕ) : ℝ) + 1) / ((K - 1 : ℕ) : ℝ)
            + (Real.log 3 + 1) / 3) := by rw [hint]
      _ ≤ f 2 + f 3 + (Real.log 3 + 1) / 3 := by linarith [htail_nonpos]
      _ ≤ 1 := by
            have h2 := Real.log_two_lt_d9
            have h3 := Real.log_three_lt_d9
            simp only [hfdef]
            push_cast
            nlinarith

private lemma summable_log_div_sq :
    Summable (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ) ^ 2) :=
  summable_of_sum_range_le log_div_sq_nonneg sum_range_log_div_sq_le_one

/-! ### The Dirichlet series of the twisted von Mangoldt function -/

/-- The coefficients `χ(n) · Λ(n)`. -/
private def vonMangoldtTwist {N : ℕ} (χ : DirichletCharacter ℂ N) : ℕ → ℂ :=
  fun n : ℕ => χ (n : ZMod N) * (ArithmeticFunction.vonMangoldt n : ℂ)

private lemma mul_eq_vonMangoldtTwist {N : ℕ} (χ : DirichletCharacter ℂ N) :
    ((fun n : ℕ => χ (n : ZMod N)) * (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))) =
      vonMangoldtTwist χ := by
  ext n
  rfl

private lemma vonMangoldtTwist_summable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 1 < s.re) : Summable (fun n => LSeries.term (vonMangoldtTwist χ) s n) := by
  have h := DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hs
  rw [LSeriesSummable, mul_eq_vonMangoldtTwist] at h
  exact h

private lemma norm_vonMangoldtTwist_le {N : ℕ} (χ : DirichletCharacter ℂ N) (n : ℕ) :
    ‖vonMangoldtTwist χ n‖ ≤ (ArithmeticFunction.vonMangoldt n : ℝ) := by
  have h1 : ‖χ (n : ZMod N)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
  have h2 : ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)‖ =
      (ArithmeticFunction.vonMangoldt n : ℝ) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  calc ‖vonMangoldtTwist χ n‖ = ‖χ (n : ZMod N)‖ * ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)‖ := by
        simp [vonMangoldtTwist]
    _ ≤ 1 * (ArithmeticFunction.vonMangoldt n : ℝ) := by
        rw [h2]
        exact mul_le_mul_of_nonneg_right h1 ArithmeticFunction.vonMangoldt_nonneg
    _ = (ArithmeticFunction.vonMangoldt n : ℝ) := one_mul _

private lemma vonMangoldt_div_sq_nonneg (n : ℕ) :
    0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ 2 :=
  div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)

private lemma vonMangoldt_div_sq_le_log (n : ℕ) :
    (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ 2 ≤
      Real.log (n : ℝ) / (n : ℝ) ^ 2 :=
  div_le_div_of_nonneg_right ArithmeticFunction.vonMangoldt_le_log (by positivity)

private lemma summable_vonMangoldt_div_sq :
    Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ 2) :=
  Summable.of_nonneg_of_le vonMangoldt_div_sq_nonneg vonMangoldt_div_sq_le_log
    summable_log_div_sq

private lemma tsum_vonMangoldt_div_sq_le_one :
    (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ 2) ≤ 1 := by
  apply Real.tsum_le_of_sum_range_le vonMangoldt_div_sq_nonneg
  intro K
  exact (Finset.sum_le_sum (fun n _ => vonMangoldt_div_sq_le_log n)).trans
    (sum_range_log_div_sq_le_one K)

/-- `‖L(χ · Λ, 2 + iT)‖ ≤ 1`. -/
private lemma norm_vonMangoldtTwist_series_le_one {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (T : ℝ) :
    ‖LSeries (vonMangoldtTwist χ) ((2 : ℂ) + Complex.I * (T : ℂ))‖ ≤ 1 := by
  set s : ℂ := (2 : ℂ) + Complex.I * (T : ℂ) with hs_def
  have hs : 1 < s.re := by simp [s]
  have hs2 : s.re = 2 := by simp [s]
  have hsumm : Summable (fun n => LSeries.term (vonMangoldtTwist χ) s n) :=
    vonMangoldtTwist_summable χ hs
  have hterm : ∀ n : ℕ, ‖LSeries.term (vonMangoldtTwist χ) s n‖ ≤
      (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ 2 := by
    intro n
    rw [LSeries.norm_term_eq]
    by_cases hn : n = 0
    · subst hn; simp
    · rw [if_neg hn, hs2, Real.rpow_two]
      exact div_le_div_of_nonneg_right (norm_vonMangoldtTwist_le χ n) (by positivity)
  calc ‖LSeries (vonMangoldtTwist χ) s‖
      ≤ ∑' n : ℕ, ‖LSeries.term (vonMangoldtTwist χ) s n‖ :=
        norm_tsum_le_tsum_norm hsumm.norm
    _ ≤ ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ 2 :=
        Summable.tsum_le_tsum hterm hsumm.norm summable_vonMangoldt_div_sq
    _ ≤ 1 := tsum_vonMangoldt_div_sq_le_one

/-- The logarithmic derivative of the Dirichlet L-function on `Re s = 2` is the negative of the
L-series of the twisted von Mangoldt function. -/
private lemma logDeriv_LFunction_eq_neg_vonMangoldtTwist {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (T : ℝ) :
    logDeriv (DirichletCharacter.LFunction χ) ((2 : ℂ) + Complex.I * (T : ℂ)) =
      - LSeries (vonMangoldtTwist χ) ((2 : ℂ) + Complex.I * (T : ℂ)) := by
  have hs : 1 < (((2 : ℂ) + Complex.I * (T : ℂ))).re := by simp
  have htwist := DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs
  rw [mul_eq_vonMangoldtTwist] at htwist
  rw [logDeriv_apply, DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs,
      DirichletCharacter.LFunction_eq_LSeries χ hs, htwist]
  ring

theorem logDeriv_L_two_norm_le_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (T : ℝ) :
    ‖deriv (DirichletCharacter.LFunction χ) ((2 : ℂ) + Complex.I * (T : ℂ)) /
      DirichletCharacter.LFunction χ ((2 : ℂ) + Complex.I * (T : ℂ))‖ ≤ 1 := by
  have h1 : deriv (DirichletCharacter.LFunction χ) ((2 : ℂ) + Complex.I * (T : ℂ)) /
        DirichletCharacter.LFunction χ ((2 : ℂ) + Complex.I * (T : ℂ)) =
      logDeriv (DirichletCharacter.LFunction χ) ((2 : ℂ) + Complex.I * (T : ℂ)) := by
    rw [logDeriv_apply]
  rw [h1, logDeriv_LFunction_eq_neg_vonMangoldtTwist χ T, norm_neg]
  exact norm_vonMangoldtTwist_series_le_one χ T

end Commons.NumberTheory.DirichletCharacter
/-
# ZeroFreeTables/P9/SummableHbRawL

Absolute convergence of HB's `L`-summand `hbRawL q ψ s a λ₁` for `Re s > 1`.

`hbRawL q ψ s a λ₁ n = Λ(n) · Re(ψ(n) n^{-s}) · u(log n / log q)`, and for `s = σ + iΔ` with
`σ > 1` it is dominated by `Λ(n) n^{-σ} |u(log n / log q)|`.  Since `u` grows at most like
`(log n)²` (`hbWL_abs_le`) the `n`-th summand is bounded by a fixed constant times
`Λ(n)(log n)^A / n^σ` for `A = 0,1,2`, and each of those three series converges absolutely by
`SummableVonMangoldtLogPow`.  This is the `L`-counterpart of `P3/SummableSigmaTerm.lean`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.P3.WLBase
import Submission.Work.ZeroFreeTables.P3.SummableVonMangoldtLogPow

namespace Work.ZeroFreeTables.P9

open scoped BigOperators

/-- The constant in the growth bound of the coefficient-correct weight `u(y) = α + α²y + (1/3)α³y²`. -/
private noncomputable def C0 (a lam₁ : ℝ) : ℝ :=
  |a + lam₁| + |a + lam₁| ^ 2 * (Real.log 2)⁻¹
    + (1/3) * |a + lam₁| ^ 3 * ((Real.log 2)⁻¹) ^ 2

/-- Pointwise domination of the `hbRawL` summand by the three convergent
`Λ(n)(log n)^A / n^σ` series. -/
private lemma hbRawL_norm_le {q : ℕ} [NeZero q] (hq : 2 ≤ q) (ψ : DirichletCharacter ℂ q)
    {σ : ℝ} (hσ : 1 < σ) (Δ a lam₁ : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    ‖Work.ZeroFreeTables.P3.hbRawL q ψ ((σ : ℂ) + (Δ : ℂ) * Complex.I) a lam₁ n‖
      ≤ C0 a lam₁ * ((ArithmeticFunction.vonMangoldt n : ℝ) * (Real.log n) ^ 0 / (n : ℝ) ^ σ
          + (ArithmeticFunction.vonMangoldt n : ℝ) * (Real.log n) ^ 1 / (n : ℝ) ^ σ
          + (ArithmeticFunction.vonMangoldt n : ℝ) * (Real.log n) ^ 2 / (n : ℝ) ^ σ) := by
  have hσpos : 0 < σ := lt_trans zero_lt_one hσ
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le zero_lt_one hn : (0 : ℕ) < n)
  have hnnonneg : (0 : ℝ) ≤ (n : ℝ) := le_of_lt hnpos
  have hlogq : Real.log 2 ≤ Real.log (q : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hq)
  have h1 := Work.ZeroFreeTables.P3.hbRawL_abs_le ψ hσpos Δ a lam₁ n
  have h2 := Work.ZeroFreeTables.P3.hbWL_abs_le hlogq a lam₁ n
  have hΛ0 : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) :=
    ArithmeticFunction.vonMangoldt_nonneg
  have hnσ0 : (0 : ℝ) ≤ (n : ℝ) ^ (-σ) := Real.rpow_nonneg hnnonneg _
  rw [Real.norm_eq_abs]
  calc |Work.ZeroFreeTables.P3.hbRawL q ψ ((σ : ℂ) + (Δ : ℂ) * Complex.I) a lam₁ n|
      ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ)
          * |Work.ZeroFreeTables.hbWL (Real.log q) a lam₁ n| := h1
    _ ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ)
          * (C0 a lam₁ * (1 + Real.log n + (Real.log n) ^ 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hΛ0 hnσ0)
        simpa only [C0] using h2
    _ = C0 a lam₁ * ((ArithmeticFunction.vonMangoldt n : ℝ) * (Real.log n) ^ 0 / (n : ℝ) ^ σ
          + (ArithmeticFunction.vonMangoldt n : ℝ) * (Real.log n) ^ 1 / (n : ℝ) ^ σ
          + (ArithmeticFunction.vonMangoldt n : ℝ) * (Real.log n) ^ 2 / (n : ℝ) ^ σ) := by
        rw [Real.rpow_neg hnnonneg]
        ring

theorem SummableHbRawL {q : ℕ} [NeZero q] (hq : 2 ≤ q) (ψ : DirichletCharacter ℂ q)
    {σ : ℝ} (hσ : 1 < σ) (Δ a lam₁ : ℝ) :
    Summable (Work.ZeroFreeTables.P3.hbRawL q ψ ((σ : ℂ) + (Δ : ℂ) * Complex.I) a lam₁) := by
  have h0 := Work.ZeroFreeTables.P3.SummableVonMangoldtLogPow hσ 0
  have h1 := Work.ZeroFreeTables.P3.SummableVonMangoldtLogPow hσ 1
  have h2 := Work.ZeroFreeTables.P3.SummableVonMangoldtLogPow hσ 2
  have hg : Summable (fun n : ℕ =>
      (ArithmeticFunction.vonMangoldt n : ℝ) * (Real.log n) ^ 0 / (n : ℝ) ^ σ
        + (ArithmeticFunction.vonMangoldt n : ℝ) * (Real.log n) ^ 1 / (n : ℝ) ^ σ
        + (ArithmeticFunction.vonMangoldt n : ℝ) * (Real.log n) ^ 2 / (n : ℝ) ^ σ) :=
    (h0.add h1).add h2
  have hgc : Summable (fun n : ℕ => C0 a lam₁ *
      ((ArithmeticFunction.vonMangoldt n : ℝ) * (Real.log n) ^ 0 / (n : ℝ) ^ σ
        + (ArithmeticFunction.vonMangoldt n : ℝ) * (Real.log n) ^ 1 / (n : ℝ) ^ σ
        + (ArithmeticFunction.vonMangoldt n : ℝ) * (Real.log n) ^ 2 / (n : ℝ) ^ σ)) :=
    hg.mul_left _
  refine Summable.of_norm_bounded_eventually_nat hgc ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  exact hbRawL_norm_le hq ψ hσ Δ a lam₁ hn

end Work.ZeroFreeTables.P9

/-
# ZeroFreeTables/P10/summable_hbTermG

Absolute convergence of the free-scale summands `hbTermG N χ L σ Δ a λ₁` of
`SigmaP3L N L χ (σ + iΔ) a λ₁` for `σ > 1`.

`hbTermG` is dominated by `Λ n · n^{-σ} · |u(log n/L)|` (with `u` the smoothing
weight `α + α²y + (1/3)α³y²`, `α = a + λ₁`), and `|u(log n/L)| ≪ 1 + log n + (log n)²`
for any fixed `L > 0`, whence `SummableVonMangoldtLogPow`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.P10.Defs14
import Submission.Work.ZeroFreeTables.P3.SummableVonMangoldtLogPow

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables.P10

/-- Free-scale growth bound for the smoothing weight:
`|u(log n/L)| ≤ C (1 + log n + (log n)²)`, `C = |α| + |α|²/L + (1/3)|α|³/L²`, `α = a + λ₁`. -/
theorem hbWL_abs_le_free {L : ℝ} (hL : 0 < L) (a lam₁ : ℝ) (n : ℕ) :
    |Work.ZeroFreeTables.hbWL L a lam₁ n| ≤
      (|a + lam₁| + |a + lam₁| ^ 2 * L⁻¹ + (1/3) * |a + lam₁| ^ 3 * (L⁻¹) ^ 2)
        * (1 + Real.log n + (Real.log n) ^ 2) := by
  have hLinv : 0 ≤ L⁻¹ := inv_nonneg.mpr hL.le
  have hlogn : 0 ≤ Real.log n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h]
    · exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  set y : ℝ := Real.log n / L with hydef
  have hy0 : 0 ≤ y := by rw [hydef]; exact div_nonneg hlogn hL.le
  have hy1 : y ≤ Real.log n * L⁻¹ := by rw [hydef, div_eq_mul_inv]
  set C : ℝ := |a + lam₁| + |a + lam₁| ^ 2 * L⁻¹
    + (1/3) * |a + lam₁| ^ 3 * (L⁻¹) ^ 2 with hCdef
  have hnn3 : 0 ≤ (1/3) * |a + lam₁| ^ 3 * (L⁻¹) ^ 2 := by positivity
  have hnn2 : 0 ≤ |a + lam₁| ^ 2 * L⁻¹ := mul_nonneg (sq_nonneg _) hLinv
  have hnn1 : 0 ≤ |a + lam₁| := abs_nonneg _
  have hC1 : |a + lam₁| ≤ C := by rw [hCdef]; linarith [hnn1, hnn2, hnn3]
  have hC2 : |a + lam₁| ^ 2 * L⁻¹ ≤ C := by rw [hCdef]; linarith [hnn1, hnn2, hnn3]
  have hC3 : (1/3) * |a + lam₁| ^ 3 * (L⁻¹) ^ 2 ≤ C := by rw [hCdef]; linarith [hnn1, hnn2, hnn3]
  have hA2 : 0 ≤ |a + lam₁| ^ 2 := sq_nonneg _
  have key : |Work.ZeroFreeTables.hbWL L a lam₁ n| ≤
      |a + lam₁| + |a + lam₁| ^ 2 * y + (1/3) * |a + lam₁| ^ 3 * y ^ 2 := by
    rw [Work.ZeroFreeTables.hbWL, ← hydef]
    have h1 := abs_add_le ((a + lam₁) + (a + lam₁) ^ 2 * y) ((1/3) * (a + lam₁) ^ 3 * y ^ 2)
    have h2 := abs_add_le (a + lam₁) ((a + lam₁) ^ 2 * y)
    have e2 : |(a + lam₁) ^ 2 * y| = |a + lam₁| ^ 2 * y := by
      rw [abs_mul, abs_pow, abs_of_nonneg hy0]
    have e3 : |(1/3) * (a + lam₁) ^ 3 * y ^ 2| = (1/3) * |a + lam₁| ^ 3 * y ^ 2 := by
      rw [abs_mul, abs_mul, abs_pow, abs_pow, abs_of_nonneg hy0,
        abs_of_nonneg (by norm_num : (0:ℝ) ≤ (1:ℝ)/3)]
    linarith [h1, h2]
  have hy2 : y ^ 2 ≤ (Real.log n * L⁻¹) ^ 2 := pow_le_pow_left₀ hy0 hy1 2
  have hstep : |a + lam₁| + |a + lam₁| ^ 2 * y + (1/3) * |a + lam₁| ^ 3 * y ^ 2
      ≤ |a + lam₁| + |a + lam₁| ^ 2 * (Real.log n * L⁻¹)
        + (1/3) * |a + lam₁| ^ 3 * (Real.log n * L⁻¹) ^ 2 := by
    have hA' : |a + lam₁| ^ 2 * y ≤ |a + lam₁| ^ 2 * (Real.log n * L⁻¹) :=
      mul_le_mul_of_nonneg_left hy1 hA2
    have hB' : (1/3) * |a + lam₁| ^ 3 * y ^ 2
        ≤ (1/3) * |a + lam₁| ^ 3 * (Real.log n * L⁻¹) ^ 2 :=
      mul_le_mul_of_nonneg_left hy2 (by positivity)
    linarith
  refine key.trans (hstep.trans ?_)
  have e1 : |a + lam₁| ≤ C * 1 := by simpa using hC1
  have e2 : |a + lam₁| ^ 2 * (Real.log n * L⁻¹) ≤ C * Real.log n := by
    calc |a + lam₁| ^ 2 * (Real.log n * L⁻¹)
        = (|a + lam₁| ^ 2 * L⁻¹) * Real.log n := by ring
      _ ≤ C * Real.log n := mul_le_mul_of_nonneg_right hC2 hlogn
  have e3 : (1/3) * |a + lam₁| ^ 3 * (Real.log n * L⁻¹) ^ 2
      ≤ C * (Real.log n) ^ 2 := by
    calc (1/3) * |a + lam₁| ^ 3 * (Real.log n * L⁻¹) ^ 2
        = ((1/3) * |a + lam₁| ^ 3 * (L⁻¹) ^ 2) * (Real.log n) ^ 2 := by ring
      _ ≤ C * (Real.log n) ^ 2 := mul_le_mul_of_nonneg_right hC3 (sq_nonneg _)
  have hfin : C * 1 + C * Real.log n + C * (Real.log n) ^ 2
      = C * (1 + Real.log n + (Real.log n) ^ 2) := by ring
  linarith [e1, e2, e3, hfin]

/-- The summand of `SigmaP3L N L χ (σ+iΔ) a λ₁` is dominated by `Λ n · n^{-σ} · |u(log n/L)|`. -/
theorem hbTermG_abs_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (L σ Δ a lam₁ : ℝ)
    (n : ℕ) :
    |hbTermG N χ L σ Δ a lam₁ n| ≤
      (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ)
        * |Work.ZeroFreeTables.hbWL L a lam₁ n| := by
  have hΛ : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) :=
    ArithmeticFunction.vonMangoldt_nonneg
  have hre : |(χ (n : ZMod N) * Work.ZeroFreeTables.P3.hbE Δ n).re| ≤ 1 := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, Work.ZeroFreeTables.P3.hbE_norm, mul_one]
    exact DirichletCharacter.norm_le_one χ (n : ZMod N)
  have hrp : 0 ≤ (n : ℝ) ^ (-σ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hA : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ) := mul_nonneg hΛ hrp
  have hmain : (ArithmeticFunction.vonMangoldt n : ℝ) * |(χ (n : ZMod N) * Work.ZeroFreeTables.P3.hbE Δ n).re|
      * (n : ℝ) ^ (-σ) * |Work.ZeroFreeTables.hbWL L a lam₁ n|
      ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ)
        * |Work.ZeroFreeTables.hbWL L a lam₁ n| := by
    calc (ArithmeticFunction.vonMangoldt n : ℝ) * |(χ (n : ZMod N) * Work.ZeroFreeTables.P3.hbE Δ n).re|
          * (n : ℝ) ^ (-σ) * |Work.ZeroFreeTables.hbWL L a lam₁ n|
        = ((ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ))
            * (|(χ (n : ZMod N) * Work.ZeroFreeTables.P3.hbE Δ n).re|
              * |Work.ZeroFreeTables.hbWL L a lam₁ n|) := by ring
      _ ≤ ((ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ))
            * (1 * |Work.ZeroFreeTables.hbWL L a lam₁ n|) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hre (abs_nonneg _)) hA
      _ = (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ)
            * |Work.ZeroFreeTables.hbWL L a lam₁ n| := by ring
  simpa only [hbTermG, abs_mul, abs_of_nonneg hΛ, abs_of_nonneg hrp] using hmain

/-- **Absolute convergence of the free-scale summands** of `SigmaP3L`: for `σ > 1`, `L > 0`
the series `∑_n Λ(n) Re(χ(n) n^{-iΔ}) n^{-σ} u(log n/L)` converges absolutely. -/
theorem summable_hbTermG {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {σ : ℝ} (hσ : 1 < σ)
    (L : ℝ) (hL : 0 < L) (Δ a lam₁ : ℝ) :
    Summable (hbTermG N χ L σ Δ a lam₁) := by
  have h0 := Work.ZeroFreeTables.P3.SummableVonMangoldtLogPow (σ := σ) hσ 0
  have h1 := Work.ZeroFreeTables.P3.SummableVonMangoldtLogPow (σ := σ) hσ 1
  have h2 := Work.ZeroFreeTables.P3.SummableVonMangoldtLogPow (σ := σ) hσ 2
  set C : ℝ := |a + lam₁| + |a + lam₁| ^ 2 * L⁻¹ + (1/3) * |a + lam₁| ^ 3 * (L⁻¹) ^ 2
    with hCdef
  have hdom : Summable (fun n : ℕ => C *
      ((ArithmeticFunction.vonMangoldt n : ℝ) * (Real.log n) ^ 0 / (n : ℝ) ^ σ
        + (ArithmeticFunction.vonMangoldt n : ℝ) * (Real.log n) ^ 1 / (n : ℝ) ^ σ
        + (ArithmeticFunction.vonMangoldt n : ℝ) * (Real.log n) ^ 2 / (n : ℝ) ^ σ)) :=
    ((h0.add h1).add h2).mul_left C
  refine Summable.of_norm_bounded hdom (fun n => ?_)
  rw [Real.norm_eq_abs]
  refine (hbTermG_abs_le χ L σ Δ a lam₁ n).trans ?_
  have hW := hbWL_abs_le_free hL a lam₁ n
  refine (mul_le_mul_of_nonneg_left hW (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
    (Real.rpow_nonneg (Nat.cast_nonneg n) _))).trans ?_
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp [Real.log_zero, Real.zero_rpow (by linarith : (-σ) ≠ 0)]
  · have hnr : (0 : ℝ) < n := by exact_mod_cast hn
    rw [Real.rpow_neg hnr.le, div_eq_mul_inv, hCdef]
    exact le_of_eq (by ring)

end Work.ZeroFreeTables.P10

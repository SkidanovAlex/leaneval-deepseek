/-
# ZeroFreeTables/P9/SigmaP3L_eq_moments

The `P₃` smoothing functional `SigmaP3L` of HB (8.4), whose weight is
`u(y) = α + α²y + (1/3)α³y²` (`α = a + λ₁`), is a linear combination of the logarithmic
moments of the twisted von Mangoldt series:

`SigmaP3L χ s a λ₁ = c·M₀ + c²·M₁ + (c³/3)·M₂`,   `c = (a+λ₁)/L`,

where `M_j = Σ_n Λ(n) Re(χ(n)n^{-s}) (log n)^j` (`vonMangoldtMoment`).  The content is the
absolute convergence of the three moment series (`Re s > 1`, so `Σ_n Λ(n)(log n)^j/n^σ`
converges by `SummableVonMangoldtLogPow`), which permits the term-by-term splitting of the
`tsum` of the summand, followed by the elementary coefficient algebra.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.P9.SigmaP3LCoeffs
import Submission.Work.ZeroFreeTables.P3.SummableVonMangoldtLogPow

open scoped BigOperators
noncomputable section

namespace Work.ZeroFreeTables.P9

/-- The two descriptions of the `n`-th summand of the twisted von Mangoldt series agree:
`χ(n)/n^s = χ(n)·n^{-s}` for `n ≥ 1`, and both terms carry the factor `Λ(0) = 0` at `n = 0`. -/
private lemma vonMangoldt_mul_re_eq_div {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (s : ℂ) (n : ℕ) :
    (ArithmeticFunction.vonMangoldt n : ℝ) * (χ (n : ZMod N) / (n : ℂ) ^ s).re
      = (ArithmeticFunction.vonMangoldt n : ℝ) * chiTwistRe χ s n := by
  rcases eq_or_ne n 0 with hn | hn
  · subst hn
    rw [ArithmeticFunction.map_zero]
    ring
  · rw [show (χ (n : ZMod N) / (n : ℂ) ^ s).re = chiTwistRe χ s n from by
      rw [chiTwistRe, div_eq_mul_inv, Complex.cpow_neg]]

/-- The `n`-th moment summand is dominated by `Λ(n) n^{-Re s}`: `|χ(n)| ≤ 1` and
`‖n^{-s}‖ = n^{-Re s}`. -/
private lemma abs_chiTwistRe_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ)
    {n : ℕ} (hn : 1 ≤ n) : |chiTwistRe χ s n| ≤ (n : ℝ) ^ (-s.re) := by
  have hn0 : 0 < n := Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  rw [chiTwistRe, ← Real.norm_eq_abs]
  calc ‖((χ (n : ZMod N) : ℂ) * (n : ℂ) ^ (-s)).re‖
      ≤ ‖(χ (n : ZMod N) : ℂ) * (n : ℂ) ^ (-s)‖ := by
        rw [Real.norm_eq_abs]
        exact Complex.abs_re_le_norm _
    _ = ‖(χ (n : ZMod N) : ℂ)‖ * ‖(n : ℂ) ^ (-s)‖ := norm_mul _ _
    _ ≤ 1 * (n : ℝ) ^ ((-s).re) := by
        refine mul_le_mul (DirichletCharacter.norm_le_one χ _)
          (le_of_eq (Complex.norm_natCast_cpow_of_pos hn0 (-s))) (norm_nonneg _) (by norm_num)
    _ = (n : ℝ) ^ (-s.re) := by
        rw [Complex.neg_re, one_mul]

/-- Absolute convergence of the `j`-th logarithmic moment of the twisted von Mangoldt series:
`∑_n Λ(n) Re(χ(n)n^{-s}) (log n)^j` is summable for `Re s > 1`. -/
theorem summable_vonMangoldtMoment {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 1 < s.re) (j : ℕ) :
    Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * chiTwistRe χ s n
      * (Real.log n) ^ j) := by
  refine Summable.of_norm_bounded
    (P3.SummableVonMangoldtLogPow (σ := s.re) hs j) (fun n => ?_)
  rcases eq_or_ne n 0 with hn | hn
  · subst hn
    rw [ArithmeticFunction.map_zero]
    simp
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn)
    have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
    have hΛ0 : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) :=
      ArithmeticFunction.vonMangoldt_nonneg
    have hz : |chiTwistRe χ s n| ≤ (n : ℝ) ^ (-s.re) := abs_chiTwistRe_le χ s hn1
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hΛ0,
      abs_of_nonneg (pow_nonneg hlog0 j), div_eq_mul_inv, ← Real.rpow_neg (le_of_lt hnpos)]
    calc (ArithmeticFunction.vonMangoldt n : ℝ) * |chiTwistRe χ s n| * (Real.log (n : ℝ)) ^ j
        ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-s.re)
            * (Real.log (n : ℝ)) ^ j :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hz hΛ0) (pow_nonneg hlog0 j)
      _ = (ArithmeticFunction.vonMangoldt n : ℝ) * (Real.log (n : ℝ)) ^ j
            * (n : ℝ) ^ (-s.re) := by ring

theorem SigmaP3L_eq_moments {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 1 < s.re) (a lam₁ L : ℝ) :
    SigmaP3L N L χ s a lam₁
      = ((a + lam₁) / L) * vonMangoldtMoment χ s 0
        + ((a + lam₁) / L) ^ 2 * vonMangoldtMoment χ s 1
        + (1 / 3) * ((a + lam₁) / L) ^ 3 * vonMangoldtMoment χ s 2 := by
  set α : ℝ := a + lam₁ with hα
  let Q : ℕ → ℝ := fun n => (ArithmeticFunction.vonMangoldt n : ℝ) * chiTwistRe χ s n
  let T : ℕ → ℝ := fun n => (ArithmeticFunction.vonMangoldt n : ℝ) * chiTwistRe χ s n
      * hbWL L a lam₁ n
  -- summability of the three moment series
  have hQ : Summable Q := (summable_vonMangoldtMoment χ hs 0).congr (fun n => by simp [Q])
  have hQ1 : Summable (fun n => Q n * Real.log n) :=
    (summable_vonMangoldtMoment χ hs 1).congr (fun n => by simp [Q])
  have hQ2 : Summable (fun n => Q n * (Real.log n) ^ 2) :=
    (summable_vonMangoldtMoment χ hs 2).congr (fun n => by simp [Q])
  have hA : Summable (fun n => α * Q n) := hQ.mul_left α
  have hB : Summable (fun n => (α ^ 2 / L) * (Q n * Real.log n)) := hQ1.mul_left _
  have hC : Summable (fun n => ((1 / 3) * α ^ 3 / L ^ 2) * (Q n * (Real.log n) ^ 2)) :=
    hQ2.mul_left _
  have hAB : Summable (fun n => α * Q n + (α ^ 2 / L) * (Q n * Real.log n)) := hA.add hB
  -- identification of the moments
  have hM0 : (∑' n : ℕ, Q n) = vonMangoldtMoment χ s 0 := by
    unfold vonMangoldtMoment
    exact tsum_congr (fun n => by simp [Q])
  have hM1 : (∑' n : ℕ, Q n * Real.log n) = vonMangoldtMoment χ s 1 := by
    unfold vonMangoldtMoment
    exact tsum_congr (fun n => by simp [Q])
  have hM2 : (∑' n : ℕ, Q n * (Real.log n) ^ 2) = vonMangoldtMoment χ s 2 := by
    unfold vonMangoldtMoment
    exact tsum_congr (fun n => by simp [Q])
  -- the summand of `SigmaP3L`, rewritten with `chiTwistRe` instead of `χ(n)/n^s`
  have hTT : (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ)
        * (χ (n : ZMod N) / (n : ℂ) ^ s).re * hbWL L a lam₁ n) = ∑' n : ℕ, T n := by
    refine tsum_congr (fun n => ?_)
    simp only [T, vonMangoldt_mul_re_eq_div χ s n]
  -- the weighted `tsum` splits into the three moment sums
  have hsum : (∑' n : ℕ, T n)
      = α * vonMangoldtMoment χ s 0 + (α ^ 2 / L) * vonMangoldtMoment χ s 1
        + ((1 / 3) * α ^ 3 / L ^ 2) * vonMangoldtMoment χ s 2 := by
    calc (∑' n : ℕ, T n)
        = ∑' n : ℕ, ((α * Q n + (α ^ 2 / L) * (Q n * Real.log n))
            + ((1 / 3) * α ^ 3 / L ^ 2) * (Q n * (Real.log n) ^ 2)) := by
          refine tsum_congr (fun n => ?_)
          simp only [T, Q, hbWL]
          rw [← hα]
          ring
      _ = (∑' n : ℕ, (α * Q n + (α ^ 2 / L) * (Q n * Real.log n)))
            + ∑' n : ℕ, ((1 / 3) * α ^ 3 / L ^ 2) * (Q n * (Real.log n) ^ 2) :=
          Summable.tsum_add hAB hC
      _ = ((∑' n : ℕ, α * Q n) + ∑' n : ℕ, (α ^ 2 / L) * (Q n * Real.log n))
            + ∑' n : ℕ, ((1 / 3) * α ^ 3 / L ^ 2) * (Q n * (Real.log n) ^ 2) := by
          rw [Summable.tsum_add hA hB]
      _ = ((α * ∑' n : ℕ, Q n) + (α ^ 2 / L) * ∑' n : ℕ, Q n * Real.log n)
            + ((1 / 3) * α ^ 3 / L ^ 2) * ∑' n : ℕ, Q n * (Real.log n) ^ 2 := by
          rw [tsum_mul_left, tsum_mul_left, tsum_mul_left]
      _ = α * vonMangoldtMoment χ s 0 + (α ^ 2 / L) * vonMangoldtMoment χ s 1
            + ((1 / 3) * α ^ 3 / L ^ 2) * vonMangoldtMoment χ s 2 := by
          rw [hM0, hM1, hM2]
  rw [SigmaP3L_eq_tsum, hTT, hsum]
  ring

end Work.ZeroFreeTables.P9

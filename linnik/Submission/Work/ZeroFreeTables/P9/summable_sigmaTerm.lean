/-
# ZeroFreeTables/P9/summable_sigmaTerm

Absolute convergence of the summand `sigmaTerm M L χ s a λ₁` of HB's `Σ(s,χ)` of (8.4) at a
*general* smoothing scale `L > 0` (the scale `L` of `SigmaP3L` is a free parameter -- it is
`log q` only in the diagonal applications):

`sigmaTerm M L χ s a λ₁ n = Λ(n) · Re(χ(n) n^{-s}) · u(log n / L)`,  `u(y) = α + α²y + (1/3)α³y²`,
`α = a + λ₁`.

For `s = σ + iΔ` with `σ > 1` it is dominated by `Λ(n) n^{-σ} |u(log n / L)|`, and since `u`
grows at most like `(log n)²` *at any positive scale* `L` (the pointwise bound `hbWL_abs_le_pos`
below needs only `L > 0`, unlike `P3.hbWL_abs_le` which asks for `L ≥ log 2`), the `n`-th
summand is bounded by a fixed constant times `Λ(n)(log n)^A/n^σ` for `A = 0,1,2`; each of those
three series converges absolutely by `SummableVonMangoldtLogPow`.

This is the free-scale counterpart of `P9/SummableHbRawL.lean` (which fixes the scale to `log q`).
-/
import Mathlib
import Submission.Work.ZeroFreeTables.P9.SigmaP3LChangeLevelAux

namespace Work.ZeroFreeTables.P9

open scoped BigOperators

noncomputable section

/-- The constant in the growth bound of the smoothing weight `hbWL` at a general positive scale
`L`: `|α| + |α|²L⁻¹ + (1/3)|α|³L⁻²` with `α = a + λ₁`. -/
private noncomputable def wc (L a lam₁ : ℝ) : ℝ :=
  |a + lam₁| + |a + lam₁| ^ 2 * L⁻¹ + (1/3) * |a + lam₁| ^ 3 * (L⁻¹) ^ 2

private lemma wc_nonneg {L a lam₁ : ℝ} (hL : 0 < L) : 0 ≤ wc L a lam₁ := by
  have h : 0 ≤ L⁻¹ := inv_nonneg.mpr hL.le
  have h1 : 0 ≤ |a + lam₁| := abs_nonneg _
  have h2 : 0 ≤ |a + lam₁| ^ 2 * L⁻¹ := mul_nonneg (sq_nonneg _) h
  have h3 : 0 ≤ (1/3) * |a + lam₁| ^ 3 * (L⁻¹) ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg h1 3)) (sq_nonneg _)
  simp only [wc]
  linarith

/-- **Growth of the smoothing weight at a general positive scale.**  For `L > 0`,
`|u(log n / L)| ≤ wc L a λ₁ · (1 + log n + (log n)²)`.  (The existing `P3.hbWL_abs_le` assumes
`L ≥ log 2`; here only `L > 0` is needed, since `log n / L ≤ (log n) · L⁻¹` for `log n ≥ 0`.) -/
private lemma hbWL_abs_le_pos {L a lam₁ : ℝ} (hL : 0 < L) (n : ℕ) :
    |hbWL L a lam₁ n| ≤ wc L a lam₁ * (1 + Real.log n + (Real.log n) ^ 2) := by
  have hLnn : 0 ≤ L⁻¹ := inv_nonneg.mpr hL.le
  have hlogn : 0 ≤ Real.log n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h]
    · exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  set A : ℝ := |a + lam₁| with hA
  set y : ℝ := Real.log n / L with hy
  have hA0 : 0 ≤ A := by rw [hA]; exact abs_nonneg _
  have hy0 : 0 ≤ y := by rw [hy]; exact div_nonneg hlogn hL.le
  have hyeq : y = Real.log n * L⁻¹ := by rw [hy, div_eq_mul_inv]
  -- triangle inequality, term by term
  have hstep1 : |hbWL L a lam₁ n| ≤ A + A ^ 2 * y + (1/3) * A ^ 3 * y ^ 2 := by
    have hb : hbWL L a lam₁ n
        = (a + lam₁) + (a + lam₁) ^ 2 * y + (1/3) * (a + lam₁) ^ 3 * y ^ 2 := by
      rw [show hbWL L a lam₁ n = (a + lam₁) + (a + lam₁) ^ 2 * (Real.log n / L)
          + (1/3) * (a + lam₁) ^ 3 * (Real.log n / L) ^ 2 from rfl, hy]
    rw [hb]
    have h2 := abs_add_le ((a + lam₁) + (a + lam₁) ^ 2 * y)
      ((1/3) * (a + lam₁) ^ 3 * y ^ 2)
    have h3 := abs_add_le (a + lam₁) ((a + lam₁) ^ 2 * y)
    have e2 : |(a + lam₁) ^ 2 * y| = A ^ 2 * y := by
      rw [abs_mul, abs_pow, abs_of_nonneg hy0, ← hA]
    have e3 : |(1/3) * (a + lam₁) ^ 3 * y ^ 2| = (1/3) * A ^ 3 * y ^ 2 := by
      rw [abs_mul, abs_mul, abs_pow, abs_pow, abs_of_nonneg hy0,
        abs_of_nonneg (by norm_num : (0:ℝ) ≤ (1:ℝ)/3), ← hA]
    linarith
  -- insert the scale
  have hA2 : 0 ≤ A ^ 2 := sq_nonneg A
  have hA3 : 0 ≤ A ^ 3 := pow_nonneg hA0 3
  have hc2 : 0 ≤ A ^ 2 * L⁻¹ := mul_nonneg hA2 hLnn
  have hc3 : 0 ≤ (1/3) * A ^ 3 * (L⁻¹) ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num) hA3) (sq_nonneg _)
  have hy2 : A ^ 2 * y = (A ^ 2 * L⁻¹) * Real.log n := by rw [hyeq]; ring
  have hy3 : (1/3) * A ^ 3 * y ^ 2
      = ((1/3) * A ^ 3 * (L⁻¹) ^ 2) * (Real.log n) ^ 2 := by
    rw [hyeq]; ring
  have hwc : wc L a lam₁ = A + A ^ 2 * L⁻¹ + (1/3) * A ^ 3 * (L⁻¹) ^ 2 := by
    simp only [wc, ← hA]
  rw [hwc]
  calc |hbWL L a lam₁ n| ≤ A + A ^ 2 * y + (1/3) * A ^ 3 * y ^ 2 := hstep1
    _ = A + (A ^ 2 * L⁻¹) * Real.log n + ((1/3) * A ^ 3 * (L⁻¹) ^ 2) * (Real.log n) ^ 2 := by
        rw [hy2, hy3]
    _ ≤ (A + A ^ 2 * L⁻¹ + (1/3) * A ^ 3 * (L⁻¹) ^ 2) * (1 + Real.log n + (Real.log n) ^ 2) := by
        have h1 : A ≤ (A + A ^ 2 * L⁻¹ + (1/3) * A ^ 3 * (L⁻¹) ^ 2) * 1 := by linarith
        have h2 : (A ^ 2 * L⁻¹) * Real.log n
            ≤ (A + A ^ 2 * L⁻¹ + (1/3) * A ^ 3 * (L⁻¹) ^ 2) * Real.log n :=
          mul_le_mul_of_nonneg_right (by linarith) hlogn
        have h3 : ((1/3) * A ^ 3 * (L⁻¹) ^ 2) * (Real.log n) ^ 2
            ≤ (A + A ^ 2 * L⁻¹ + (1/3) * A ^ 3 * (L⁻¹) ^ 2) * (Real.log n) ^ 2 :=
          mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
        linarith

/-- **The character factor.**  For `Re s > 0`, `|Re(χ(n) n^{-s})| ≤ n^{-Re s}`
(with both sides `0` at `n = 0`, where `(0:ℂ)^s = 0`). -/
private lemma abs_re_chi_div_cpow_le {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) {s : ℂ}
    (hs : 0 < s.re) (n : ℕ) :
    |(χ (n : ZMod M) / (n : ℂ) ^ s).re| ≤ (n : ℝ) ^ (-s.re) := by
  refine (Complex.abs_re_le_norm _).trans ?_
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have hsne : s ≠ 0 := by
      intro h
      rw [h] at hs
      simp at hs
    have h0s : (((0 : ℕ)) : ℂ) ^ s = 0 := by
      rw [Nat.cast_zero]
      exact Complex.zero_cpow hsne
    have hz : ‖χ (((0 : ℕ)) : ZMod M) / (((0 : ℕ) : ℂ) ^ s)‖ = 0 := by
      rw [h0s, div_zero, norm_zero]
    have hz2 : (((0 : ℕ) : ℝ)) ^ (-s.re) = 0 := by
      rw [Nat.cast_zero, Real.zero_rpow (by linarith : (-s.re) ≠ 0)]
    rw [hz, hz2]
  · have hnp : (0 : ℝ) < n := by exact_mod_cast hn
    have hnorm : ‖(((n : ℝ)) : ℂ) ^ s‖ = (n : ℝ) ^ s.re :=
      Complex.norm_cpow_eq_rpow_re_of_pos hnp s
    rw [← Complex.ofReal_natCast n, Complex.norm_div, hnorm]
    calc ‖χ (n : ZMod M)‖ / (n : ℝ) ^ s.re ≤ 1 / (n : ℝ) ^ s.re :=
          div_le_div_of_nonneg_right (DirichletCharacter.norm_le_one χ (n : ZMod M))
            (Real.rpow_nonneg (Nat.cast_nonneg n) s.re)
      _ = (n : ℝ) ^ (-s.re) := by rw [Real.rpow_neg (Nat.cast_nonneg n)]; ring

/-- **Pointwise domination of the `sigmaTerm` summand**, at a general positive scale `L`: the
`n`-th summand is bounded by `wc L a λ₁` times the sum of the three convergent
`Λ(n)(log n)^A / n^σ` series (`σ = Re s`). -/
private lemma sigmaTerm_norm_le {M : ℕ} [NeZero M] (L : ℝ) (χ : DirichletCharacter ℂ M)
    {s : ℂ} (hs : 0 < s.re) (a lam₁ : ℝ) (hL : 0 < L) (n : ℕ) :
    ‖sigmaTerm M L χ s a lam₁ n‖ ≤ wc L a lam₁ *
      ((ArithmeticFunction.vonMangoldt n : ℝ) * (Real.log n) ^ 0 / (n : ℝ) ^ s.re
        + (ArithmeticFunction.vonMangoldt n : ℝ) * (Real.log n) ^ 1 / (n : ℝ) ^ s.re
        + (ArithmeticFunction.vonMangoldt n : ℝ) * (Real.log n) ^ 2 / (n : ℝ) ^ s.re) := by
  have hΛ : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) :=
    ArithmeticFunction.vonMangoldt_nonneg
  have hnnonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hχ := abs_re_chi_div_cpow_le χ hs n
  have hw := hbWL_abs_le_pos (L := L) (a := a) (lam₁ := lam₁) hL n
  have hstep : ‖sigmaTerm M L χ s a lam₁ n‖
      ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-s.re)
        * (wc L a lam₁ * (1 + Real.log n + (Real.log n) ^ 2)) := by
    rw [sigmaTerm, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hΛ]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hχ hΛ) hw (abs_nonneg _)
      (mul_nonneg hΛ (Real.rpow_nonneg hnnonneg _))
  refine hstep.trans (le_of_eq ?_)
  rw [Real.rpow_neg hnnonneg]
  ring

/-- **Absolute convergence of the summands of `SigmaP3L` at a free scale `L > 0`.** -/
theorem summable_sigmaTerm {M : ℕ} [NeZero M] (L : ℝ) (χ : DirichletCharacter ℂ M) {s : ℂ}
    (a lam₁ : ℝ) (hs : 1 < s.re) (ha : 0 < a) (hlam₁ : 0 ≤ lam₁) (hL : 0 < L) :
    Summable (Work.ZeroFreeTables.P9.sigmaTerm M L χ s a lam₁) := by
  have h0 := Work.ZeroFreeTables.P3.SummableVonMangoldtLogPow hs 0
  have h1 := Work.ZeroFreeTables.P3.SummableVonMangoldtLogPow hs 1
  have h2 := Work.ZeroFreeTables.P3.SummableVonMangoldtLogPow hs 2
  have hg : Summable (fun n : ℕ =>
      (ArithmeticFunction.vonMangoldt n : ℝ) * (Real.log n) ^ 0 / (n : ℝ) ^ s.re
        + (ArithmeticFunction.vonMangoldt n : ℝ) * (Real.log n) ^ 1 / (n : ℝ) ^ s.re
        + (ArithmeticFunction.vonMangoldt n : ℝ) * (Real.log n) ^ 2 / (n : ℝ) ^ s.re) :=
    (h0.add h1).add h2
  have hgc : Summable (fun n : ℕ => wc L a lam₁ *
      ((ArithmeticFunction.vonMangoldt n : ℝ) * (Real.log n) ^ 0 / (n : ℝ) ^ s.re
        + (ArithmeticFunction.vonMangoldt n : ℝ) * (Real.log n) ^ 1 / (n : ℝ) ^ s.re
        + (ArithmeticFunction.vonMangoldt n : ℝ) * (Real.log n) ^ 2 / (n : ℝ) ^ s.re)) :=
    hg.mul_left _
  exact Summable.of_norm_bounded hgc
    (fun n => sigmaTerm_norm_le L χ (lt_trans zero_lt_one hs) a lam₁ hL n)

end

end Work.ZeroFreeTables.P9

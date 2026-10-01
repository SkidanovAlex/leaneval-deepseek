import Mathlib
import Submission.Work.LinnikContract.Defs
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_logDeriv_eq_neg_LSeries_vonMangoldt
import Submission.Work.LinnikAreas.FarRepel.abscissaVonMangoldtLeOne
import Submission.Work.LinnikAreas.FarRepel.abscissaVonMangoldtTwistLeOne
import Submission.Work.LinnikAreas.FarRepel.imCharEqZero
import Submission.Work.LinnikAreas.FarRepel.reMulCpowOfImEqZero
import Submission.Work.LinnikAreas.FarRepel.reTermLogMulIterate

open scoped LSeries.notation

namespace Work.LinnikAreas.FarRepel

/-!
# The arithmetic side of the differentiated explicit formula (real form)

`arithKthDeriv` identifies the `k`-th derivative (`k` odd) of the logarithmic derivative of
`ζ · L(·,χ)` at `s` (with `Re s > 1`) with the real von Mangoldt series

`∑_n Λ(n) (1 + Re χ(n)) (log n)^k n^{-Re s} cos (Im s · log n)`.

The proof is three steps.

* On `Re z > 1` one has `logDeriv ζ z = -∑_n Λ(n) n^{-z}` and, unconditionally,
  `logDeriv (L · χ) z = -∑_n Λ(n) χ(n) n^{-z}`; both right-hand sides are `LSeries` of a
  coefficient sequence whose abscissa of absolute convergence is `≤ 1`.
* `Set.EqOn.iteratedDeriv_of_isOpen` transfers the `k`-th derivative to a neighbourhood,
  and Mathlib's `LSeries_iteratedDeriv` differentiates the Dirichlet series termwise:
  `(iteratedDeriv k (LSeries f)) s = (-1)^k · LSeries (logMul^[k] f) s`.
  Since `k` is odd, `(-1)^(k+1) = 1`.
* Real parts are taken termwise (`Complex.re_tsum`); a term of the `k`-fold `log`-multiplied
  L-series has real part `(log n)^k · Re (f n · n^{-s})`, and `Re n^{-s} = n^{-Re s} cos(Im s · log n)`.
  The character hypothesis `χ ^ 2 = 1` makes `χ n` real, so only `Re χ n` survives.
-/

/-- **Differentiating `logDeriv` of a Dirichlet series.** If `F` agrees with the negative of the
`LSeries` of `f` on the half-plane `Re z > 1`, and the abscissa of absolute convergence of `f`
is at most `1`, then at every `s` with `Re s > 1` the `k`-th derivative of `F` equals
`(-1)^(k+1)` times the `LSeries` of the `k`-fold `log`-multiple of `f`. -/
private lemma iteratedDeriv_eq_neg_LSeries_iterate {F : ℂ → ℂ} {f : ℕ → ℂ}
    (hF : Set.EqOn F (fun z => - LSeries f z) {z : ℂ | 1 < z.re})
    (hab : LSeries.abscissaOfAbsConv f ≤ 1) (k : ℕ) {s : ℂ} (hs : 1 < s.re) :
    iteratedDeriv k F s = (-1) ^ (k + 1) * LSeries (LSeries.logMul ^[k] f) s := by
  have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  rw [Set.EqOn.iteratedDeriv_of_isOpen hF hopen k hs, iteratedDeriv_fun_neg]
  rw [LSeries_iteratedDeriv k (lt_of_le_of_lt hab (EReal.coe_lt_coe_iff.mpr hs))]
  rw [← neg_mul, neg_eq_neg_one_mul, ← pow_succ']

/-- The logarithmic derivative of the Riemann zeta function is the negative of the von Mangoldt
`LSeries` on `Re z > 1`. -/
private lemma eqOn_zeta : Set.EqOn (logDeriv riemannZeta)
    (fun z => - LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) z)
    {z : ℂ | 1 < z.re} := by
  intro z hz
  show deriv riemannZeta z / riemannZeta z
    = - LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) z
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (s := z) hz]
  ring

/-- The logarithmic derivative of a Dirichlet `L`-function is the negative of the twisted von
Mangoldt `LSeries` on `Re z > 1`. -/
private lemma eqOn_L {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    Set.EqOn (logDeriv (DirichletCharacter.LFunction χ))
      (fun z => - LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) *
        (χ (n : ZMod q) : ℂ)) z)
      {z : ℂ | 1 < z.re} := by
  intro z hz
  rw [Commons.NumberTheory.DirichletCharacter.LFunction_logDeriv_eq_neg_LSeries_vonMangoldt χ hz]

/-- **The real part of one summand.** For `n ≠ 0`, the real part of the sum of the `n`-th terms
of the two `k`-fold `log`-multiplied `LSeries` (with coefficients `Λ` and `Λ · χ`, `χ ^ 2 = 1`)
is `Λ(n) (1 + Re χ(n)) (log n)^k n^{-Re s} cos (Im s · log n)`. -/
private lemma key_term {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ2 : χ ^ 2 = 1)
    (k : ℕ) (s : ℂ) {n : ℕ} (hn : n ≠ 0) :
    (LSeries.term (LSeries.logMul ^[k] (fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℂ))) s n).re
      + (LSeries.term (LSeries.logMul ^[k]
          (fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℂ) * (χ (m : ZMod q) : ℂ))) s n).re
      = (ArithmeticFunction.vonMangoldt n : ℝ) * (1 + (χ ((n : ℕ) : ZMod q)).re) *
        (Real.log n) ^ k * (n : ℝ) ^ (-s.re) * Real.cos (s.im * Real.log n) := by
  rw [reTermLogMulIterate k s hn, reTermLogMulIterate k s hn]
  have h0 : ((fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℂ)) n).im = 0 := by simp
  have h1 : ((fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℂ) *
      (χ (m : ZMod q) : ℂ)) n).im = 0 := by
    simp only [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, mul_zero, zero_mul, add_zero,
      imCharEqZero χ hχ2]
  rw [reMulCpowOfImEqZero h0 hn s, reMulCpowOfImEqZero h1 hn s]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- **The arithmetic side of the differentiated explicit formula, real form.** (module `Submission.Work.LinnikAreas.FarRepel.arithKthDeriv`; declare in `namespace Work.LinnikAreas.FarRepel`.)

For `χ` with `χ ≠ 1` and `χ ^ 2 = 1` (so every value of `χ` is real), `k ≥ 1` odd, and `1 < Re s`:

`Re ( ((logDeriv ζ)^{(k)})(s) + ((logDeriv L(·,χ))^{(k)})(s) )
  = ∑_n Λ(n) (1 + Re χ(n)) (log n)^k n^{-Re s} cos (Im s · log n)`.

This identifies the `k`-th derivative of the logarithmic derivative of `ζ·L(·,χ)` with a real
series of non-negative-modulus coefficients; it is the input to the positivity argument of the
Deuring–Heilbronn repulsion (Kadiri–Ng–Wong arXiv:1902.08640 §2).  Note `k` odd makes the sign
`(-1)^(k+1) = 1`.

PROOF ROUTE: (i) `logDeriv ζ(s) = -∑' n, Λ(n) n^{-s}` for `1 < Re s`
(`ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div`, or the workspace's
`Work.LinnikAreas.vonMangoldtTsum_eq_neg_zeta_logDeriv_re`), and `logDeriv (LFunction χ) s = -∑' n, Λ(n)χ(n) n^{-s}`
(`DirichletCharacter.LFunction_logDeriv_eq_neg_LSeries_vonMangoldt`, unconditional);
(ii) differentiate `k` times termwise inside a small disc around `s` contained in `Re > 1`, where
the termwise-differentiated series converges absolutely (`Work.ZeroFreeTables.P3.SummableVonMangoldtLogPow`,
or `LSeries` differentiability / `iteratedDeriv_tsum`), giving
`((logDeriv ζ)^{(k)})(s) = (-1)^(k+1) ∑' n, Λ(n)(log n)^k n^{-s}` and likewise for `L`;
(iii) take real parts (`Complex.re_tsum`), using `χ(n) ∈ {0, ±1} ⊂ ℝ` (from `χ^2 = 1`, cf. the proof
of `Work.LinnikAreas.DhK.one_add_re_nonneg`) and `n^{-s} = n^{-Re s}(cos(Im s log n) - i sin(Im s log n))`. -/
theorem arithKthDeriv {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hχ2 : χ ^ 2 = 1)
    (k : ℕ) (hk : 1 ≤ k) (hodd : k % 2 = 1) {s : ℂ} (hs : 1 < s.re) :
    (iteratedDeriv k (logDeriv riemannZeta) s +
        iteratedDeriv k (logDeriv (DirichletCharacter.LFunction χ)) s).re =
      ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * (1 + (χ ((n : ℕ) : ZMod q)).re) *
        (Real.log n) ^ k * (n : ℝ) ^ (-s.re) * Real.cos (s.im * Real.log n) := by
  have hk1 : (-1 : ℂ) ^ (k + 1) = 1 :=
    Even.neg_one_pow (Odd.add_one (Nat.odd_iff.mpr hodd))
  have hab0 : LSeries.abscissaOfAbsConv
      (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) ≤ 1 := abscissaVonMangoldtLeOne
  have hab1 : LSeries.abscissaOfAbsConv
      (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod q) : ℂ)) ≤ 1 :=
    abscissaVonMangoldtTwistLeOne χ
  have hz := iteratedDeriv_eq_neg_LSeries_iterate eqOn_zeta hab0 k hs
  have hl := iteratedDeriv_eq_neg_LSeries_iterate (eqOn_L χ) hab1 k hs
  have hsum0 : LSeriesSummable
      (LSeries.logMul ^[k] (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ))) s :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re (by
      rw [LSeries.absicssaOfAbsConv_logPowMul]
      exact lt_of_le_of_lt hab0 (EReal.coe_lt_coe_iff.mpr hs))
  have hsum1 : LSeriesSummable (LSeries.logMul ^[k]
      (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod q) : ℂ))) s :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re (by
      rw [LSeries.absicssaOfAbsConv_logPowMul]
      exact lt_of_le_of_lt hab1 (EReal.coe_lt_coe_iff.mpr hs))
  have hr0 : Summable (fun n : ℕ => (LSeries.term
      (LSeries.logMul ^[k] (fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℂ))) s n).re) :=
    (hsum0.map Complex.reCLM Complex.reCLM.continuous).congr (fun n => by simp)
  have hr1 : Summable (fun n : ℕ => (LSeries.term (LSeries.logMul ^[k]
      (fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℂ) * (χ (m : ZMod q) : ℂ))) s n).re) :=
    (hsum1.map Complex.reCLM Complex.reCLM.continuous).congr (fun n => by simp)
  have hre0 : (LSeries (LSeries.logMul ^[k]
      (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ))) s).re =
      ∑' n, (LSeries.term (LSeries.logMul ^[k]
        (fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℂ))) s n).re := Complex.re_tsum hsum0
  have hre1 : (LSeries (LSeries.logMul ^[k]
      (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod q) : ℂ))) s).re =
      ∑' n, (LSeries.term (LSeries.logMul ^[k]
        (fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℂ) * (χ (m : ZMod q) : ℂ))) s n).re :=
    Complex.re_tsum hsum1
  rw [hz, hl, hk1, one_mul, one_mul, Complex.add_re, hre0, hre1]
  rw [← Summable.tsum_add hr0 hr1]
  refine tsum_congr (fun n => ?_)
  rcases eq_or_ne n 0 with rfl | hn
  · simp [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr (not_isPrimePow_zero)]
  · exact key_term χ hχ2 k s hn

end Work.LinnikAreas.FarRepel

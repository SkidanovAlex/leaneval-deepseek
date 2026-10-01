import Mathlib
import Submission.Work.LinnikAreas.TuranOther.Defs
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_logDeriv_eq_neg_LSeries_vonMangoldt
import Submission.Work.LinnikAreas.FarRepel.abscissaVonMangoldtLeOne
import Submission.Work.LinnikAreas.FarRepel.abscissaVonMangoldtTwistLeOne
import Submission.Work.LinnikAreas.FarRepel.imCharEqZero
import Submission.Work.LinnikAreas.FarRepel.reMulCpowOfImEqZero
import Submission.Work.LinnikAreas.FarRepel.reTermLogMulIterate
import Submission.Work.LinnikAreas.TuranOther.chiCoeffPos
import Submission.Work.LinnikAreas.TuranOther.reIteratedDerivLogDeriv
import Submission.Work.LinnikAreas.TuranOther.summableLogMulTermRe
import Submission.Work.LinnikAreas.TuranOther.cpowShiftRe

/-!
# Turán-type positivity for the differentiated logarithmic derivatives

For `χ₀` of order dividing two (`χ₀ * χ₀ = 1`), an arbitrary character `χ` modulo `q`, real
`σ > 1`, real `γ` and odd `k = 2j-1`, the sum

  `(ζ′/ζ)^{(k)}(σ) + (L′/L(·,χ₀))^{(k)}(σ) + (L′/L(·,χ))^{(k)}(σ+iγ) + (L′/L(·,χ₀χ))^{(k)}(σ+iγ)`

has nonnegative real part.  This is the Turán/Landau positivity input for the Deuring–Heilbronn
repulsion in the other-character case.

The proof is the classical one: on `Re s > 1` each logarithmic derivative is minus an absolutely
convergent Dirichlet series, `(L′/L)(s,ψ) = − ∑_n Λ(n)ψ(n)n^{-s}`, and `LSeries_iteratedDeriv`
differentiates termwise.  Since `k` is odd, the `k`-th derivative of `(L′/L)(·,ψ)` is the
`k`-fold `log`-multiplied series, whose `n`-th real part is
`(log n)^k n^{-σ} Λ(n) Re(ψ(n) n^{-iγ})`; adding the four terms gives
`(log n)^k n^{-σ} Λ(n) (1+χ₀(n)) (1+Re(χ(n) n^{-iγ})) ≥ 0` termwise.
-/

open scoped LSeries.notation

namespace Work.LinnikAreas.TuranOther

/-! ## Helpers -/

/-- On `Re z > 1` the logarithmic derivative of `ζ` is minus the von Mangoldt `L`-series. -/
private lemma eqOn_logDeriv_zeta : Set.EqOn (logDeriv riemannZeta)
    (fun z : ℂ => - LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) z)
    {z : ℂ | 1 < z.re} := by
  intro z hz
  show deriv riemannZeta z / riemannZeta z
    = - LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) z
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (s := z) hz]
  ring

/-- On `Re z > 1` the logarithmic derivative of `L(·,χ)` is minus the twisted von Mangoldt
`L`-series. -/
private lemma eqOn_logDeriv_LFunction {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    Set.EqOn (logDeriv (DirichletCharacter.LFunction χ))
      (fun z : ℂ => - LSeries (fun n : ℕ =>
        (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod q) : ℂ)) z) {z : ℂ | 1 < z.re} := by
  intro z hz
  rw [Commons.NumberTheory.DirichletCharacter.LFunction_logDeriv_eq_neg_LSeries_vonMangoldt
    χ hz]

/-- Associating a sum of four absolutely convergent real series into a single series. -/
private lemma four_tsum_eq (a b c d : ℕ → ℝ) (ha : Summable a) (hb : Summable b)
    (hc : Summable c) (hd : Summable d) :
    (∑' n : ℕ, a n) + (∑' n : ℕ, b n) + (∑' n : ℕ, c n) + (∑' n : ℕ, d n)
      = ∑' n : ℕ, (((a n + b n) + c n) + d n) := by
  rw [← Summable.tsum_add ha hb, ← Summable.tsum_add (ha.add hb) hc,
    ← Summable.tsum_add ((ha.add hb).add hc) hd]

/-- **Termwise positivity.**  The sum of the four summands coming from the `k`-th derivatives of
the four logarithmic derivatives is nonnegative, because it factors as
`(log n)^k · Λ(n) · n^{-σ} · (1+χ₀(n)) · (1+Re(χ(n)n^{-iγ}))`. -/
private lemma termSum_nonneg {q : ℕ} [NeZero q] (χ₀ χ : DirichletCharacter ℂ q)
    (h₀sq : χ₀ * χ₀ = 1) (k : ℕ) (hk : 1 ≤ k) (σ γ : ℝ) (n : ℕ) :
    0 ≤ (Real.log n) ^ k
          * ((ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(σ : ℂ))).re
      + (Real.log n) ^ k
          * (((ArithmeticFunction.vonMangoldt n : ℂ) * (χ₀ (n : ZMod q) : ℂ))
              * (n : ℂ) ^ (-(σ : ℂ))).re
      + (Real.log n) ^ k
          * (((ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod q) : ℂ))
              * (n : ℂ) ^ (-((σ : ℂ) + Complex.I * (γ : ℂ)))).re
      + (Real.log n) ^ k
          * (((ArithmeticFunction.vonMangoldt n : ℂ) * ((χ₀ * χ) (n : ZMod q) : ℂ))
              * (n : ℂ) ^ (-((σ : ℂ) + Complex.I * (γ : ℂ)))).re := by
  have hχ₀im : (χ₀ (n : ZMod q)).im = 0 :=
    FarRepel.imCharEqZero χ₀ (by rw [pow_two]; exact h₀sq) (n : ZMod q)
  rcases eq_or_ne n 0 with rfl | hn
  · have hlog : (Real.log ((0 : ℕ) : ℝ)) ^ k = 0 := by
      rw [Nat.cast_zero, Real.log_zero, zero_pow (show k ≠ 0 by omega)]
    rw [hlog]
    simp
  · have hA : ((ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(σ : ℂ))).re
        = (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ) := by
      rw [FarRepel.reMulCpowOfImEqZero (c := (ArithmeticFunction.vonMangoldt n : ℂ))
        (by simp) hn (σ : ℂ)]
      simp
    have himB : (((ArithmeticFunction.vonMangoldt n : ℂ) * (χ₀ (n : ZMod q) : ℂ))).im = 0 := by
      rw [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, hχ₀im]
      ring
    have hB : (((ArithmeticFunction.vonMangoldt n : ℂ) * (χ₀ (n : ZMod q) : ℂ))
          * (n : ℂ) ^ (-(σ : ℂ))).re
        = (ArithmeticFunction.vonMangoldt n : ℝ) * (χ₀ (n : ZMod q)).re
            * (n : ℝ) ^ (-σ) := by
      rw [FarRepel.reMulCpowOfImEqZero (c := (ArithmeticFunction.vonMangoldt n : ℂ)
        * (χ₀ (n : ZMod q) : ℂ)) himB hn (σ : ℂ)]
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hχ₀im]
      simp
    have hC1 : (((ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod q) : ℂ))
          * (n : ℂ) ^ (-((σ : ℂ) + Complex.I * (γ : ℂ)))).re
        = (n : ℝ) ^ (-σ) * ((ArithmeticFunction.vonMangoldt n : ℂ)
            * ((χ (n : ZMod q) : ℂ) * (n : ℂ) ^ (-(Complex.I * (γ : ℂ))))).re := by
      rw [cpowShiftRe ((ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod q) : ℂ)) hn σ γ]
      congr 1
      rw [mul_assoc]
    have hC2 : ((ArithmeticFunction.vonMangoldt n : ℂ)
          * ((χ (n : ZMod q) : ℂ) * (n : ℂ) ^ (-(Complex.I * (γ : ℂ))))).re
        = (ArithmeticFunction.vonMangoldt n : ℝ)
            * ((χ (n : ZMod q) : ℂ) * (n : ℂ) ^ (-(Complex.I * (γ : ℂ)))).re := by
      rw [Complex.re_ofReal_mul]
    have hD1 : (((ArithmeticFunction.vonMangoldt n : ℂ) * ((χ₀ * χ) (n : ZMod q) : ℂ))
          * (n : ℂ) ^ (-((σ : ℂ) + Complex.I * (γ : ℂ)))).re
        = (n : ℝ) ^ (-σ) * ((ArithmeticFunction.vonMangoldt n : ℂ)
            * (((χ₀ * χ) (n : ZMod q) : ℂ) * (n : ℂ) ^ (-(Complex.I * (γ : ℂ))))).re := by
      rw [cpowShiftRe ((ArithmeticFunction.vonMangoldt n : ℂ) * ((χ₀ * χ) (n : ZMod q) : ℂ))
        hn σ γ]
      congr 1
      rw [mul_assoc]
    have hD2 : ((ArithmeticFunction.vonMangoldt n : ℂ)
          * (((χ₀ * χ) (n : ZMod q) : ℂ) * (n : ℂ) ^ (-(Complex.I * (γ : ℂ))))).re
        = (ArithmeticFunction.vonMangoldt n : ℝ)
            * (((χ₀ * χ) (n : ZMod q) : ℂ)
              * (n : ℂ) ^ (-(Complex.I * (γ : ℂ)))).re := by
      rw [Complex.re_ofReal_mul]
    have hD3 : (((χ₀ * χ) (n : ZMod q) : ℂ)
          * (n : ℂ) ^ (-(Complex.I * (γ : ℂ)))).re
        = (χ₀ (n : ZMod q)).re
            * ((χ (n : ZMod q) : ℂ) * (n : ℂ) ^ (-(Complex.I * (γ : ℂ)))).re := by
      rw [MulChar.mul_apply, mul_assoc, Complex.mul_re, hχ₀im, zero_mul, sub_zero]
    rw [hA, hB, hC1, hC2, hD1, hD2, hD3]
    have hfac : (Real.log n) ^ k * ((ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ))
          + (Real.log n) ^ k * ((ArithmeticFunction.vonMangoldt n : ℝ)
              * (χ₀ (n : ZMod q)).re * (n : ℝ) ^ (-σ))
          + (Real.log n) ^ k * ((n : ℝ) ^ (-σ) * ((ArithmeticFunction.vonMangoldt n : ℝ)
              * ((χ (n : ZMod q) : ℂ) * (n : ℂ) ^ (-(Complex.I * (γ : ℂ)))).re))
          + (Real.log n) ^ k * ((n : ℝ) ^ (-σ) * ((ArithmeticFunction.vonMangoldt n : ℝ)
              * ((χ₀ (n : ZMod q)).re
                * ((χ (n : ZMod q) : ℂ) * (n : ℂ) ^ (-(Complex.I * (γ : ℂ)))).re)))
        = (Real.log n) ^ k * ((ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ)
            * ((1 + (χ₀ (n : ZMod q)).re)
              * (1 + ((χ (n : ZMod q) : ℂ)
                  * (n : ℂ) ^ (-(Complex.I * (γ : ℂ)))).re))) := by
      ring
    rw [hfac]
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
    refine mul_nonneg (pow_nonneg (Real.log_nonneg hn1) k) ?_
    refine mul_nonneg (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)) ?_
    exact chiCoeffPos χ₀ χ h₀sq γ n

/-- **The `k`-th derivative positivity** with `k` an explicit parameter (odd, `≥ 1`). -/
private theorem positivityArith_aux {q : ℕ} [NeZero q] (χ₀ χ : DirichletCharacter ℂ q)
    (h₀sq : χ₀ * χ₀ = 1) {k : ℕ} (hk1 : 1 ≤ k) (hkodd : k % 2 = 1) (γ : ℝ) {σ : ℝ}
    (hσ : 1 < σ) :
    0 ≤ (iteratedDeriv k (logDeriv riemannZeta) (σ : ℂ)
        + iteratedDeriv k (logDeriv (DirichletCharacter.LFunction χ₀)) (σ : ℂ)
        + iteratedDeriv k (logDeriv (DirichletCharacter.LFunction χ))
            ((σ : ℂ) + Complex.I * (γ : ℂ))
        + iteratedDeriv k (logDeriv (DirichletCharacter.LFunction (χ₀ * χ)))
            ((σ : ℂ) + Complex.I * (γ : ℂ))).re := by
  have hσℂ : 1 < (σ : ℂ).re := by simpa using hσ
  have hσI : 1 < ((σ : ℂ) + Complex.I * (γ : ℂ)).re := by
    have : ((σ : ℂ) + Complex.I * (γ : ℂ)).re = σ := by simp
    rw [this]; exact hσ
  have e1 : (iteratedDeriv k (logDeriv riemannZeta) (σ : ℂ)).re
      = ∑' n : ℕ, (Real.log n) ^ k
          * ((ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(σ : ℂ))).re :=
    reIteratedDerivLogDeriv (F := logDeriv riemannZeta)
      (f := fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ))
      eqOn_logDeriv_zeta FarRepel.abscissaVonMangoldtLeOne hkodd hσℂ
  have e2 : (iteratedDeriv k (logDeriv (DirichletCharacter.LFunction χ₀)) (σ : ℂ)).re
      = ∑' n : ℕ, (Real.log n) ^ k
          * (((ArithmeticFunction.vonMangoldt n : ℂ) * (χ₀ (n : ZMod q) : ℂ))
              * (n : ℂ) ^ (-(σ : ℂ))).re :=
    reIteratedDerivLogDeriv (F := logDeriv (DirichletCharacter.LFunction χ₀))
      (f := fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) * (χ₀ (n : ZMod q) : ℂ))
      (eqOn_logDeriv_LFunction χ₀) (FarRepel.abscissaVonMangoldtTwistLeOne χ₀) hkodd hσℂ
  have e3 : (iteratedDeriv k (logDeriv (DirichletCharacter.LFunction χ))
        ((σ : ℂ) + Complex.I * (γ : ℂ))).re
      = ∑' n : ℕ, (Real.log n) ^ k
          * (((ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod q) : ℂ))
              * (n : ℂ) ^ (-((σ : ℂ) + Complex.I * (γ : ℂ)))).re :=
    reIteratedDerivLogDeriv (F := logDeriv (DirichletCharacter.LFunction χ))
      (f := fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod q) : ℂ))
      (eqOn_logDeriv_LFunction χ) (FarRepel.abscissaVonMangoldtTwistLeOne χ) hkodd hσI
  have e4 : (iteratedDeriv k (logDeriv (DirichletCharacter.LFunction (χ₀ * χ)))
        ((σ : ℂ) + Complex.I * (γ : ℂ))).re
      = ∑' n : ℕ, (Real.log n) ^ k
          * (((ArithmeticFunction.vonMangoldt n : ℂ) * ((χ₀ * χ) (n : ZMod q) : ℂ))
              * (n : ℂ) ^ (-((σ : ℂ) + Complex.I * (γ : ℂ)))).re :=
    reIteratedDerivLogDeriv (F := logDeriv (DirichletCharacter.LFunction (χ₀ * χ)))
      (f := fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) * ((χ₀ * χ) (n : ZMod q) : ℂ))
      (eqOn_logDeriv_LFunction (χ₀ * χ)) (FarRepel.abscissaVonMangoldtTwistLeOne (χ₀ * χ))
      hkodd hσI
  simp only [Complex.add_re]
  rw [e1, e2, e3, e4]
  let a : ℕ → ℝ := fun n => (Real.log n) ^ k
    * ((ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(σ : ℂ))).re
  let b : ℕ → ℝ := fun n => (Real.log n) ^ k
    * (((ArithmeticFunction.vonMangoldt n : ℂ) * (χ₀ (n : ZMod q) : ℂ))
        * (n : ℂ) ^ (-(σ : ℂ))).re
  let c : ℕ → ℝ := fun n => (Real.log n) ^ k
    * (((ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod q) : ℂ))
        * (n : ℂ) ^ (-((σ : ℂ) + Complex.I * (γ : ℂ)))).re
  let d : ℕ → ℝ := fun n => (Real.log n) ^ k
    * (((ArithmeticFunction.vonMangoldt n : ℂ) * ((χ₀ * χ) (n : ZMod q) : ℂ))
        * (n : ℂ) ^ (-((σ : ℂ) + Complex.I * (γ : ℂ)))).re
  have hAsm : Summable a :=
    summableLogMulTermRe (f := fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ))
      FarRepel.abscissaVonMangoldtLeOne hk1 hσℂ
  have hBsm : Summable b :=
    summableLogMulTermRe
      (f := fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) * (χ₀ (n : ZMod q) : ℂ))
      (FarRepel.abscissaVonMangoldtTwistLeOne χ₀) hk1 hσℂ
  have hCsm : Summable c :=
    summableLogMulTermRe
      (f := fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod q) : ℂ))
      (FarRepel.abscissaVonMangoldtTwistLeOne χ) hk1 hσI
  have hDsm : Summable d :=
    summableLogMulTermRe
      (f := fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) * ((χ₀ * χ) (n : ZMod q) : ℂ))
      (FarRepel.abscissaVonMangoldtTwistLeOne (χ₀ * χ)) hk1 hσI
  change 0 ≤ (∑' n : ℕ, a n) + (∑' n : ℕ, b n) + (∑' n : ℕ, c n) + (∑' n : ℕ, d n)
  rw [four_tsum_eq a b c d hAsm hBsm hCsm hDsm]
  exact tsum_nonneg (fun n => termSum_nonneg χ₀ χ h₀sq k hk1 σ γ n)

theorem positivityArith {q : ℕ} [NeZero q] (χ₀ χ : DirichletCharacter ℂ q) (h₀sq : χ₀ * χ₀ = 1)
    (j : ℕ) (hj : 1 ≤ j) (γ : ℝ) {σ : ℝ} (hσ : 1 < σ) :
    0 ≤ (iteratedDeriv (2 * j - 1) (logDeriv riemannZeta) (σ : ℂ)
        + iteratedDeriv (2 * j - 1) (logDeriv (DirichletCharacter.LFunction χ₀)) (σ : ℂ)
        + iteratedDeriv (2 * j - 1) (logDeriv (DirichletCharacter.LFunction χ))
            ((σ : ℂ) + Complex.I * (γ : ℂ))
        + iteratedDeriv (2 * j - 1) (logDeriv (DirichletCharacter.LFunction (χ₀ * χ)))
            ((σ : ℂ) + Complex.I * (γ : ℂ))).re :=
  positivityArith_aux χ₀ χ h₀sq (by omega) (by omega) γ hσ

end Work.LinnikAreas.TuranOther

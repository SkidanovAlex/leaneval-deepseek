import Mathlib
import Submission.Work.ZeroFreeTables.P9.SigmaP3LCoeffs
import Submission.Work.ZeroFreeTables.P9.iteratedDeriv_vonMangoldt
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_logDeriv_eq_neg_LSeries_vonMangoldt
import Submission.Work.ZeroFreeTables.P9.prim.summable_twisted_vonMangoldt_log
import Submission.Work.ZeroFreeTables.P9.prim.logDeriv_LFunction_eq_neg_tsum

open ArithmeticFunction

namespace Work.ZeroFreeTables.P9.prim

/-- The real part of one summand of the differentiated twisted von Mangoldt series. -/
lemma re_twisted_vonMangoldt_term {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ)
    (j n : ℕ) :
    (((ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod N) : ℂ) * (n : ℂ) ^ (-s) *
        (-(Real.log n : ℂ)) ^ j).re)
      = (ArithmeticFunction.vonMangoldt n : ℝ) * chiTwistRe χ s n *
          ((-1 : ℝ) ^ j * (Real.log n) ^ j) := by
  have h1 : (-(Real.log n : ℂ)) ^ j
      = (((-1 : ℝ) ^ j * (Real.log n) ^ j : ℝ) : ℂ) := by
    rw [← Complex.ofReal_neg, ← Complex.ofReal_pow, neg_pow]
  rw [h1]
  have h2 : (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod N) : ℂ) * (n : ℂ) ^ (-s)
      = (ArithmeticFunction.vonMangoldt n : ℂ) *
          ((χ (n : ZMod N) : ℂ) * (n : ℂ) ^ (-s)) := by
    ring
  rw [h2, Complex.re_mul_ofReal, Complex.re_ofReal_mul]
  rfl

/-- Real part of the differentiated twisted von Mangoldt series as the von Mangoldt moment. -/
lemma re_tsum_vonMangoldt_log {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 1 < s.re) (j : ℕ) :
    ((∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod N) : ℂ) *
        (n : ℂ) ^ (-s) * (-(Real.log n : ℂ)) ^ j).re)
      = (-1 : ℝ) ^ j * Work.ZeroFreeTables.vonMangoldtMoment χ s j := by
  have hsumm := summable_twisted_vonMangoldt_log χ hs j
  rw [Complex.re_tsum hsumm]
  have hterm : (fun n : ℕ =>
        (((ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod N) : ℂ) *
          (n : ℂ) ^ (-s) * (-(Real.log n : ℂ)) ^ j).re))
      = fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * chiTwistRe χ s n *
          (Real.log n) ^ j * ((-1 : ℝ) ^ j) := by
    funext n
    rw [re_twisted_vonMangoldt_term]
    ring
  rw [hterm, tsum_mul_right]
  simp only [Work.ZeroFreeTables.vonMangoldtMoment]
  ring

theorem iteratedDeriv_logDeriv_re {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (j : ℕ) {s : ℂ} (hs : 1 < s.re) : (iteratedDeriv j (logDeriv (DirichletCharacter.LFunction χ)) s).re = (-1) ^ (j + 1) * Work.ZeroFreeTables.vonMangoldtMoment χ s j := by
  set G : ℂ → ℂ := fun z => ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) *
      (χ (n : ZMod N) : ℂ) * (n : ℂ) ^ (-z) with hG
  have hopen : IsOpen {z : ℂ | 1 < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hfun : Set.EqOn (fun z : ℂ => logDeriv (DirichletCharacter.LFunction χ) z)
      (fun z : ℂ => -G z) {z : ℂ | 1 < z.re} := by
    intro z hz
    change logDeriv (DirichletCharacter.LFunction χ) z = -G z
    rw [logDeriv_LFunction_eq_neg_tsum χ hz, hG]
  have hder : iteratedDeriv j (logDeriv (DirichletCharacter.LFunction χ)) s
      = iteratedDeriv j (fun z : ℂ => -G z) s :=
    Set.EqOn.iteratedDeriv_of_isOpen hfun hopen j hs
  have hneg : iteratedDeriv j (fun z : ℂ => -G z) s = - iteratedDeriv j G s :=
    iteratedDeriv_fun_neg j G s
  have hGder : iteratedDeriv j G s = ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) *
      (χ (n : ZMod N) : ℂ) * (n : ℂ) ^ (-s) * (-(Real.log n : ℂ)) ^ j := by
    rw [hG]
    exact Work.ZeroFreeTables.P9.iteratedDeriv_vonMangoldt χ j hs
  rw [hder, hneg, hGder, Complex.neg_re, re_tsum_vonMangoldt_log χ hs j, pow_succ]
  ring

end Work.ZeroFreeTables.P9.prim

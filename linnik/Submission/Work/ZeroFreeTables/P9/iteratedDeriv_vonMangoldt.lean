/-
# ZeroFreeTables/P9/iteratedDeriv_vonMangoldt

Higher derivatives of the (character-twisted) von Mangoldt Dirichlet series.

The series
`Σ_χ(z) = ∑_n Λ(n) χ(n) n^{-z}`
is absolutely convergent on the half-plane `re z > 1`, so it is holomorphic there and may be
differentiated term by term: the `j`-th derivative is obtained by multiplying the `n`-th summand
by `(-log n)^j`.

The formalization is reduced to Mathlib's theory of `LSeries` (`LSeries_iteratedDeriv`), which
already contains the term-by-term differentiation theorem in the half-plane of absolute
convergence; the only bookkeeping needed here is

* the twisted von Mangoldt series is the `LSeries` of the coefficient sequence
  `n ↦ Λ(n) χ(n)`,
* its abscissa of absolute convergence is `≤ 1` (Mathlib: `LSeriesSummable_twist_vonMangoldt`),
* `logMul^[j] f n = (log n)^j * f n`, which converts the `j`-th derivative of the `LSeries`
  into the sum with the weight `(-log n)^j`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.P3.SummableVonMangoldtLogPow

namespace Work.ZeroFreeTables.P9

open LSeries ArithmeticFunction
open scoped LSeries.notation

/-- The `j`-fold iterate of `LSeries.logMul` multiplies the `n`-th coefficient by `(log n)^j`. -/
lemma logMul_iterate_apply (f : ℕ → ℂ) (j n : ℕ) :
    (logMul^[j] f) n = (Complex.log (n : ℂ)) ^ j * f n := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    show Complex.log (n : ℂ) * ((logMul^[j] f) n) = Complex.log (n : ℂ) ^ (j + 1) * f n
    rw [ih, pow_succ']
    ring

/-- **Term-by-term differentiation of a Dirichlet series.** If `f 0 = 0` and `re s` exceeds the
abscissa of absolute convergence of `f`, then the `j`-th derivative of
`z ↦ ∑' n, f n * n^{-z}` at `s` is `∑' n, f n * n^{-s} * (-log n)^j`. -/
lemma iteratedDeriv_LSeries_apply {f : ℕ → ℂ} (hf0 : f 0 = 0) (j : ℕ) {s : ℂ}
    (h : abscissaOfAbsConv f < s.re) :
    iteratedDeriv j (fun z : ℂ => ∑' n : ℕ, f n * (n : ℂ) ^ (-z)) s
      = ∑' n : ℕ, f n * (n : ℂ) ^ (-s) * (-(Real.log n : ℂ)) ^ j := by
  have hL : (fun z : ℂ => ∑' n : ℕ, f n * (n : ℂ) ^ (-z)) = LSeries f := by
    funext z
    rw [LSeries.eq_1]
    exact tsum_congr fun n => (LSeries.term_def₀ hf0 z n).symm
  rw [hL, LSeries_iteratedDeriv j h]
  have hiter0 : (logMul^[j] f) 0 = 0 := by
    rw [logMul_iterate_apply]; simp [hf0]
  have hLs : LSeries (logMul^[j] f) s
      = ∑' n : ℕ, (Complex.log (n : ℂ)) ^ j * f n * (n : ℂ) ^ (-s) := by
    rw [LSeries.eq_1]
    exact tsum_congr fun n => by
      rw [LSeries.term_def₀ hiter0, logMul_iterate_apply]
  rw [hLs, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [← Complex.natCast_log, neg_pow]
  ring

theorem iteratedDeriv_vonMangoldt {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (j : ℕ)
    {s : ℂ} (hs : 1 < s.re) :
    iteratedDeriv j (fun z : ℂ => ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) *
        (χ (n : ZMod N) : ℂ) * (n : ℂ) ^ (-z)) s
      = ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod N) : ℂ) *
          (n : ℂ) ^ (-s) * (-(Real.log n : ℂ)) ^ j := by
  set f : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod N) : ℂ) with hf
  have hf0 : f 0 = 0 := by
    rw [hf]; simp
  have habs : abscissaOfAbsConv f < s.re := by
    have hcongr : abscissaOfAbsConv f
        = abscissaOfAbsConv ((fun n : ℕ => (χ (n : ZMod N) : ℂ)) *
            fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) :=
      abscissaOfAbsConv_congr (fun {n} _ => by rw [hf]; simp [Pi.mul_apply, mul_comm])
    have hle : abscissaOfAbsConv f ≤ 1 := by
      rw [hcongr]
      exact abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
        DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ (by simpa using hy)
    exact lt_of_le_of_lt hle (EReal.coe_lt_coe_iff.mpr hs)
  have key := iteratedDeriv_LSeries_apply (f := f) hf0 j habs
  simpa only [hf] using key

end Work.ZeroFreeTables.P9

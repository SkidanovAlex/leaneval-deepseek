import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_logDeriv_eq_neg_LSeries_vonMangoldt

namespace Work.LinnikAreas.OtherCharRepel

open scoped LSeries.notation

/-- The `n`-th term of the L-series of `Λ · χ` at `σ > 1` has real part
`Λ(n) · Re χ(n) · n^{-σ}`. -/
private lemma re_LSeries_term_vonMangoldt_mul_char {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (σ : ℝ) (n : ℕ) :
    (LSeries.term (fun k : ℕ => (ArithmeticFunction.vonMangoldt k : ℂ) *
        (χ (k : ZMod N) : ℂ)) (σ : ℂ) n).re
      = (ArithmeticFunction.vonMangoldt n : ℝ) * (χ (n : ZMod N)).re * (n : ℝ) ^ (-σ) := by
  have hf : (fun k : ℕ => (ArithmeticFunction.vonMangoldt k : ℂ) *
      (χ (k : ZMod N) : ℂ)) 0 = 0 := by
    simp [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr not_isPrimePow_zero]
  rw [LSeries.term_def₀ hf]
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [Nat.cast_zero]
    rw [show (ArithmeticFunction.vonMangoldt 0 : ℝ) = 0 from by
      rw [ArithmeticFunction.vonMangoldt_eq_zero_iff]; exact not_isPrimePow_zero]
    simp
  · rw [show (-(σ : ℂ)) = ((-σ : ℝ) : ℂ) by simp]
    rw [← Complex.ofReal_natCast n, ← Complex.ofReal_cpow (Nat.cast_nonneg n) (-σ)]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    ring

/-- **The real part of `L'/L` on `Re s = σ > 1` is minus the twisted von Mangoldt series.**

Since `L'/L(·,χ)` is the negative of the absolutely convergent Dirichlet series
`∑_n Λ(n) χ(n) n^{-s}` on the half-plane `Re s > 1`, its real part is `−∑_n Λ(n) Re χ(n) n^{-σ}`. -/
theorem LFunctionLogDerivReEqTsum {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {σ : ℝ} (hσ : 1 < σ) :
    (logDeriv (DirichletCharacter.LFunction χ) (σ : ℂ)).re =
      -∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * (χ (n : ZMod N)).re *
        (n : ℝ) ^ (-σ) := by
  have hs : 1 < ((σ : ℂ)).re := by simpa using hσ
  -- absolute convergence of the twisted von Mangoldt series at `σ`
  have hsumm : LSeriesSummable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) *
      (χ (n : ZMod N) : ℂ)) (σ : ℂ) :=
    (LSeriesSummable_congr (σ : ℂ)
      (f := fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod N) : ℂ))
      (g := fun n : ℕ => (χ (n : ZMod N) : ℂ) * (ArithmeticFunction.vonMangoldt n : ℂ))
      (fun _ => mul_comm _ _)).mpr (DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hs)
  rw [Commons.NumberTheory.DirichletCharacter.LFunction_logDeriv_eq_neg_LSeries_vonMangoldt χ hs,
    Complex.neg_re, neg_inj]
  change (∑' n : ℕ, LSeries.term (fun k : ℕ => (ArithmeticFunction.vonMangoldt k : ℂ) *
    (χ (k : ZMod N) : ℂ)) (σ : ℂ) n).re = _
  rw [Complex.re_tsum hsumm]
  exact tsum_congr (fun n => re_LSeries_term_vonMangoldt_mul_char χ σ n)

end Work.LinnikAreas.OtherCharRepel

import Mathlib

namespace Work.LinnikAreas

/-- The `n`-th term of the (complex) Dirichlet series of `Λ` over `n ^ (-σ)`
has real part equal to `Λ(n) n^{-σ}` for every `n : ℕ` (including `0`). -/
lemma vonMangoldt_LSeries_term_re (n : ℕ) (σ : ℝ) :
    (LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) (σ : ℂ) n).re
      = (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [LSeries.term, ↓reduceIte, Complex.zero_re]
    rw [show (ArithmeticFunction.vonMangoldt 0 : ℝ) = 0 from by
      rw [ArithmeticFunction.vonMangoldt_eq_zero_iff]; exact not_isPrimePow_zero]
    simp
  · rw [LSeries.term, if_neg hn]
    rw [← Complex.ofReal_natCast n]
    rw [← Complex.ofReal_cpow (Nat.cast_nonneg n) σ]
    rw [← Complex.ofReal_div]
    rw [Complex.ofReal_re]
    rw [Real.rpow_neg (Nat.cast_nonneg n)]
    rw [div_eq_mul_inv]

theorem vonMangoldtTsum_eq_neg_zeta_logDeriv_re (σ : ℝ) (hσ : 1 < σ) :
    (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ))
      = (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re := by
  have hσℂ : 1 < ((σ : ℂ)).re := by simpa using hσ
  have hsum : Summable
      (LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) (σ : ℂ)) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hσℂ
  have hL := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
    (s := (σ : ℂ)) hσℂ
  have hcongr : (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ))
      = ∑' n : ℕ,
          (LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) (σ : ℂ) n).re :=
    tsum_congr (fun n => (vonMangoldt_LSeries_term_re n σ).symm)
  rw [hcongr, ← Complex.re_tsum hsum, ← hL]
  rfl

end Work.LinnikAreas

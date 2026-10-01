import Mathlib
import Submission.Work.LinnikAreas.szPrelude

open scoped LSeries.notation

namespace Work.LinnikAreas

/-!
# The real part of `L'/L` on the line `Re s = σ > 1`, bounded by the von Mangoldt sum

For `σ > 1` the logarithmic derivative of a Dirichlet `L`-function has the absolutely
convergent expansion

    (L'/L)(σ, χ) = − ∑_n Λ(n) χ(n) n^{−σ} ,

so its real part is at most `∑_n Λ(n) n^{−σ}` (indeed the real part is at most the modulus).
The latter series is the real von Mangoldt series, which is finite for `σ > 1`.

The proof goes through the (slightly stronger) norm estimate
`‖(L'/L)(σ,χ)‖ ≤ ∑_n Λ(n) n^{−σ}`, proved from the von Mangoldt expansion together with
`‖χ(n)‖ ≤ 1` and `Λ(n) ≥ 0`.
-/

/-- The real majorant `Λ(n)·n^{-σ}` is summable for `σ > 1`. -/
private lemma summable_vonMangoldt_mul_rpow_neg (σ : ℝ) (hσ : 1 < σ) :
    Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ)) := by
  have h := (ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (σ : ℂ))
    (by simpa using hσ)).norm
  refine h.congr (fun n => ?_)
  rw [LSeries.norm_term_eq]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [if_neg hn, Complex.ofReal_re,
      Complex.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
      Real.rpow_neg (Nat.cast_nonneg n) σ, div_eq_mul_inv]

/-- **Norm bound for the twisted von Mangoldt series.**  For `Re s > 1`,

    ‖ logDeriv (L(·,χ)) s ‖ ≤ ∑_n Λ(n) n^{-Re s}. -/
private lemma norm_logDeriv_LFunction_le_tsum {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    ‖logDeriv (DirichletCharacter.LFunction χ) s‖ ≤
      ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-s.re) := by
  rw [Commons.NumberTheory.DirichletCharacter.LFunction_logDeriv_eq_neg_LSeries_vonMangoldt χ hs,
    norm_neg]
  have hfsumm : LSeriesSummable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) *
      (χ (n : ZMod N) : ℂ)) s := by
    have hg : LSeriesSummable
        ((fun n : ℕ => (χ (n : ZMod N) : ℂ)) *
          fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) s :=
      DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hs
    refine (LSeriesSummable_congr s (f := fun n : ℕ =>
        (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod N) : ℂ))
      (g := (fun n : ℕ => (χ (n : ZMod N) : ℂ)) *
        fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) ?_).mpr hg
    intro n _
    simp only [Pi.mul_apply]
    ring
  have hsummN : Summable (fun n : ℕ =>
      ‖LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) *
        (χ (n : ZMod N) : ℂ)) s n‖) := hfsumm.norm
  have hterm : ∀ n : ℕ, ‖LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) *
        (χ (n : ZMod N) : ℂ)) s n‖ ≤
      (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-s.re) := by
    intro n
    rcases eq_or_ne n 0 with hn0 | hn0
    · subst hn0; simp [LSeries.term_zero]
    · rw [LSeries.norm_term_eq, if_neg hn0]
      have hnormχ : ‖(χ (n : ZMod N) : ℂ)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
      have hΛnn : (0 : ℝ) ≤ ArithmeticFunction.vonMangoldt n :=
        ArithmeticFunction.vonMangoldt_nonneg
      have hmul : ‖(ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod N) : ℂ)‖
          ≤ (ArithmeticFunction.vonMangoldt n : ℝ) := by
        rw [norm_mul, Complex.norm_of_nonneg hΛnn]
        exact mul_le_of_le_one_right hΛnn hnormχ
      have hpow : (0 : ℝ) ≤ (n : ℝ) ^ s.re := Real.rpow_nonneg (Nat.cast_nonneg n) _
      calc ‖(ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod N) : ℂ)‖ / (n : ℝ) ^ s.re
          ≤ (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ s.re :=
            div_le_div_of_nonneg_right hmul hpow
        _ = (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-s.re) := by
            rw [Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
  calc ‖LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) *
          (χ (n : ZMod N) : ℂ)) s‖
      ≤ ∑' n : ℕ, ‖LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) *
          (χ (n : ZMod N) : ℂ)) s n‖ := norm_tsum_le_tsum_norm hsummN
    _ ≤ ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-s.re) :=
        Summable.tsum_le_tsum hterm hsummN (summable_vonMangoldt_mul_rpow_neg s.re hs)

theorem re_logDeriv_LFunction_le_vonMangoldtTsum {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {σ : ℝ} (hσ : 1 < σ) :
    (logDeriv (DirichletCharacter.LFunction χ) (σ : ℂ)).re ≤
      ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ) := by
  have hs : 1 < ((σ : ℂ)).re := by simpa using hσ
  calc (logDeriv (DirichletCharacter.LFunction χ) (σ : ℂ)).re
      ≤ ‖logDeriv (DirichletCharacter.LFunction χ) (σ : ℂ)‖ := Complex.re_le_norm _
    _ ≤ ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-((σ : ℂ)).re) :=
        norm_logDeriv_LFunction_le_tsum χ hs
    _ = ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ) := by
        rw [Complex.ofReal_re]

end Work.LinnikAreas

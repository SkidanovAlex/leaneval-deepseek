import Mathlib
import Submission.Work.LinnikContract.Defs
import Submission.Work.LinnikAreas.OtherCharRepel.LFunctionLogDerivReEqTsum
import Submission.Work.LinnikAreas.OtherCharRepel.summableVonMangoldtReCharMulRpow
import Submission.Work.LinnikAreas.vonMangoldtTsum_eq_neg_zeta_logDeriv_re

/-!
# Landau positivity for three real characters and `ζ`

For two real (quadratic) Dirichlet characters `χ₀, χ₁` modulo `q` and every real `σ > 1`,

    Re (L′/L)(σ,χ₀) + Re (L′/L)(σ,χ₁) + Re (L′/L)(σ,χ₀χ₁) ≤ Re (−ζ′/ζ)(σ).

The proof is the classical one.  On `Re s = σ > 1` the logarithmic derivatives are the
negatives of absolutely convergent Dirichlet series,

    Re (L′/L)(σ,χ) = − ∑_n Λ(n)·Re(χ n)·n^{-σ},     Re (−ζ′/ζ)(σ) = ∑_n Λ(n)·n^{-σ},

so the inequality is equivalent to

    ∑_n Λ(n) n^{-σ} (1 + Re χ₀(n))(1 + Re χ₁(n)) ≥ 0,

which holds termwise: a quadratic character takes only the values `0, ±1`, hence
`1 + Re χ(n) ≥ 0` and `Re ((χ₀χ₁) n) = Re χ₀(n) · Re χ₁(n)`.

The exact form of the right-hand side requested here is the one supplied by
`Work.LinnikAreas.vonMangoldtTsum_eq_neg_zeta_logDeriv_re`,
`∑_n Λ(n) n^{-σ} = Re (−ζ′/ζ)(σ)`.
-/

namespace Work.LinnikAreas.OtherCharRepel

open DirichletCharacter

/-- A squaring-to-one Dirichlet character takes only the values `0`, `1`, `-1`. -/
private lemma threeCharPos_value {N : ℕ} (χ : DirichletCharacter ℂ N) (h : χ * χ = 1)
    (a : ZMod N) : χ a = 0 ∨ χ a = 1 ∨ χ a = -1 := by
  by_cases ha : IsUnit a
  · have hmul : χ a * χ a = (1 : DirichletCharacter ℂ N) a := by
      rw [← MulChar.mul_apply, h]
    rw [MulChar.one_apply ha, ← pow_two] at hmul
    rcases sq_eq_one_iff.mp hmul with h' | h'
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr h')
  · exact Or.inl (MulChar.map_nonunit χ ha)

/-- For such a character, `1 + Re (χ a) ≥ 0`. -/
private lemma threeCharPos_one_add_re_nonneg {N : ℕ} (χ : DirichletCharacter ℂ N)
    (h : χ * χ = 1) (a : ZMod N) : 0 ≤ 1 + (χ a).re := by
  rcases threeCharPos_value χ h a with h' | h' | h' <;> rw [h'] <;> norm_num

/-- For a product of two such characters, the real part multiplies. -/
private lemma threeCharPos_re_mul {N : ℕ} (χ₀ χ₁ : DirichletCharacter ℂ N)
    (h₀ : χ₀ * χ₀ = 1) (h₁ : χ₁ * χ₁ = 1) (a : ZMod N) :
    ((χ₀ * χ₁) a).re = (χ₀ a).re * (χ₁ a).re := by
  by_cases ha : IsUnit a
  · rw [MulChar.mul_apply]
    have v0 : χ₀ a = 1 ∨ χ₀ a = -1 := by
      have hmul : χ₀ a * χ₀ a = (1 : DirichletCharacter ℂ N) a := by
        rw [← MulChar.mul_apply, h₀]
      rw [MulChar.one_apply ha, ← pow_two] at hmul
      exact sq_eq_one_iff.mp hmul
    have v1 : χ₁ a = 1 ∨ χ₁ a = -1 := by
      have hmul : χ₁ a * χ₁ a = (1 : DirichletCharacter ℂ N) a := by
        rw [← MulChar.mul_apply, h₁]
      rw [MulChar.one_apply ha, ← pow_two] at hmul
      exact sq_eq_one_iff.mp hmul
    rcases v0 with h | h <;> rcases v1 with h' | h' <;> rw [h, h'] <;> norm_num
  · rw [MulChar.map_nonunit (χ₀ * χ₁) ha, MulChar.map_nonunit χ₀ ha]
    simp

/-- `Re (1 + χ₀ a + χ₁ a + (χ₀χ₁) a) = (1 + Re χ₀ a)(1 + Re χ₁ a) ≥ 0`. -/
private lemma threeCharPos_combined_nonneg {N : ℕ} (χ₀ χ₁ : DirichletCharacter ℂ N)
    (h₀ : χ₀ * χ₀ = 1) (h₁ : χ₁ * χ₁ = 1) (a : ZMod N) :
    0 ≤ 1 + (χ₀ a).re + (χ₁ a).re + ((χ₀ * χ₁) a).re := by
  rw [threeCharPos_re_mul χ₀ χ₁ h₀ h₁ a]
  have h0 := threeCharPos_one_add_re_nonneg χ₀ h₀ a
  have h1 := threeCharPos_one_add_re_nonneg χ₁ h₁ a
  have hfac : 1 + (χ₀ a).re + (χ₁ a).re + (χ₀ a).re * (χ₁ a).re
      = (1 + (χ₀ a).re) * (1 + (χ₁ a).re) := by ring
  rw [hfac]
  exact mul_nonneg h0 h1

/-- The real von Mangoldt series `∑ Λ(n) n^{-σ}` is summable for `σ > 1`, in `rpow` form. -/
private lemma threeCharPos_summable_zeta {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ)) := by
  refine (Commons.NumberTheory.Zeta.summable_vonMangoldt_div_rpow (σ := σ) hσ).congr
    (fun n => ?_)
  rw [Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]

/-- The same identity for `ζ`, in the exact form requested on the right-hand side. -/
private theorem threeCharPos_zeta_tsum (σ : ℝ) (hσ : 1 < σ) :
    (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ))
      = (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re :=
  Work.LinnikAreas.vonMangoldtTsum_eq_neg_zeta_logDeriv_re σ hσ

/-- Associating a sum of four absolutely convergent series into a single series. -/
private lemma threeCharPos_tsum_four_add {a b c d : ℕ → ℝ} (ha : Summable a) (hb : Summable b)
    (hc : Summable c) (hd : Summable d) :
    tsum a + tsum b + tsum c + tsum d = tsum (fun n : ℕ => ((a n + b n) + c n) + d n) := by
  rw [← Summable.tsum_add ha hb, ← Summable.tsum_add (ha.add hb) hc,
    ← Summable.tsum_add ((ha.add hb).add hc) hd]

/-- The `n`-th term of `∑ Λ(n) n^{-σ}(1 + χ₀(n))(1 + χ₁(n))` is nonnegative. -/
private lemma threeCharPos_termwise_nonneg {N : ℕ} (χ₀ χ₁ : DirichletCharacter ℂ N)
    (h₀ : χ₀ * χ₀ = 1) (h₁ : χ₁ * χ₁ = 1) {σ : ℝ} (_hσ : 1 < σ) (n : ℕ) :
    0 ≤ ((ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ)
          + (ArithmeticFunction.vonMangoldt n : ℝ) * (χ₀ (n : ZMod N)).re * (n : ℝ) ^ (-σ))
        + (ArithmeticFunction.vonMangoldt n : ℝ) * (χ₁ (n : ZMod N)).re * (n : ℝ) ^ (-σ)
        + (ArithmeticFunction.vonMangoldt n : ℝ) * ((χ₀ * χ₁) (n : ZMod N)).re
            * (n : ℝ) ^ (-σ) := by
  have hΛ : (0 : ℝ) ≤ (ArithmeticFunction.vonMangoldt n : ℝ) :=
    ArithmeticFunction.vonMangoldt_nonneg
  have hn : (0 : ℝ) ≤ (n : ℝ) ^ (-σ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hc := threeCharPos_combined_nonneg χ₀ χ₁ h₀ h₁ (n : ZMod N)
  have hfac : ((ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ)
        + (ArithmeticFunction.vonMangoldt n : ℝ) * (χ₀ (n : ZMod N)).re * (n : ℝ) ^ (-σ))
      + (ArithmeticFunction.vonMangoldt n : ℝ) * (χ₁ (n : ZMod N)).re * (n : ℝ) ^ (-σ)
      + (ArithmeticFunction.vonMangoldt n : ℝ) * ((χ₀ * χ₁) (n : ZMod N)).re * (n : ℝ) ^ (-σ)
      = (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ) *
        (1 + (χ₀ (n : ZMod N)).re + (χ₁ (n : ZMod N)).re + ((χ₀ * χ₁) (n : ZMod N)).re) := by
    ring
  rw [hfac]
  exact mul_nonneg (mul_nonneg hΛ hn) hc

/-- **Landau positivity for three real characters and `ζ`.**  For two real (quadratic) characters `χ₀, χ₁` modulo `q` and every real `σ > 1`, `Re(L'/L)(σ,χ₀) + Re(L'/L)(σ,χ₁) + Re(L'/L)(σ,χ₀χ₁) ≤ -Re(ζ'/ζ)(σ)`. (Ingredients already on disk: `Commons.NumberTheory.DirichletCharacter.LFunction_logDeriv_eq_neg_LSeries_vonMangoldt`, `Work.LinnikAreas.vonMangoldtTsum_eq_neg_zeta_logDeriv_re`; see also the sibling `Submission/Work/LinnikAreas/OtherCharRepel/threeCharLogDeriv.lean` and `OtherCharRepel/LFunctionLogDerivReEqTsum.lean`.) -/
theorem threeCharPositivity {q : ℕ} [NeZero q] (χ₀ χ₁ : DirichletCharacter ℂ q)
    (h₀ : χ₀ ^ 2 = 1) (h₁ : χ₁ ^ 2 = 1) :
    ∀ σ : ℝ, 1 < σ →
      (logDeriv (DirichletCharacter.LFunction χ₀) (σ : ℂ)).re
        + (logDeriv (DirichletCharacter.LFunction χ₁) (σ : ℂ)).re
        + (logDeriv (DirichletCharacter.LFunction (χ₀ * χ₁)) (σ : ℂ)).re
        ≤ (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re := by
  intro σ hσ
  -- replace `χ ^ 2 = 1` by the product form used by the termwise helpers
  have h0 : χ₀ * χ₀ = 1 := by simpa [pow_two] using h₀
  have h1 : χ₁ * χ₁ = 1 := by simpa [pow_two] using h₁
  -- rewrite all four logarithmic derivatives as von Mangoldt series
  rw [LFunctionLogDerivReEqTsum χ₀ hσ, LFunctionLogDerivReEqTsum χ₁ hσ,
    LFunctionLogDerivReEqTsum (χ₀ * χ₁) hσ,
    ← threeCharPos_zeta_tsum σ hσ]
  -- it remains to see that the total mass `∑ Λ(n)n^{-σ}(1+χ₀(n))(1+χ₁(n))` is nonnegative
  have hζ := threeCharPos_summable_zeta hσ
  have h0s := summableVonMangoldtReCharMulRpow χ₀ hσ
  have h1s := summableVonMangoldtReCharMulRpow χ₁ hσ
  have h01s := summableVonMangoldtReCharMulRpow (χ₀ * χ₁) hσ
  have key := threeCharPos_tsum_four_add hζ h0s h1s h01s
  have hnn : 0 ≤ tsum (fun n : ℕ =>
      ((ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ)
        + (ArithmeticFunction.vonMangoldt n : ℝ) * (χ₀ (n : ZMod q)).re * (n : ℝ) ^ (-σ))
      + (ArithmeticFunction.vonMangoldt n : ℝ) * (χ₁ (n : ZMod q)).re * (n : ℝ) ^ (-σ)
      + (ArithmeticFunction.vonMangoldt n : ℝ) * ((χ₀ * χ₁) (n : ZMod q)).re
          * (n : ℝ) ^ (-σ)) :=
    tsum_nonneg (fun n => threeCharPos_termwise_nonneg χ₀ χ₁ h0 h1 hσ n)
  linarith [key, hnn]

end Work.LinnikAreas.OtherCharRepel

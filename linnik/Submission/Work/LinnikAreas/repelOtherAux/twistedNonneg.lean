import Mathlib
import Submission.Work.LinnikAreas.OtherCharRepel.Prelude
import Submission.Work.LinnikAreas.OtherCharRepel.LFunctionLogDerivReEqTsum
import Submission.Work.LinnikAreas.OtherCharRepel.summableVonMangoldtReCharMulRpow

/-!
# The twisted Landau positivity for the other-character Deuring–Heilbronn problem

`Work.LinnikAreas.OtherCharAux.twistedNonneg` is the *positivity* which is the first step of any
Landau/Turán-type proof of the Deuring–Heilbronn repulsion for a character `χ ≠ χ₀` (the
"other character" case, Principle 2 of Heath-Brown (1992)): for a real character `χ₀`
(`χ₀ ^ 2 = 1`) and an *arbitrary* character `χ`, and real `σ > 1`, `γ`,

`(-ζ′/ζ)(σ) + (-L′/L)(σ,χ₀) + (-L′/L)(σ+iγ,χ) + (-L′/L)(σ+iγ,χ₀χ) ≥ 0`.

It is the exact analogue, in the twisted (complex-character, shifted) setting, of the proved
workspace statements `OtherCharRepel.threeCharPositivity` / `threeCharLogDeriv`, which handle
three *real* characters at a *real* point; the complex character at the shifted point is not
available anywhere in the workspace.

The content is the von Mangoldt expansion: for `Re s > 1` the logarithmic derivatives are the
absolutely convergent series `-ζ′/ζ(σ) = Σ Λ(n)n^{-σ}` and `-L′/L(s,ψ) = Σ Λ(n)·Re(ψ(n)n^{-s})`,
so the left-hand side is `Σ_n Λ(n) n^{-σ} (1 + χ₀(n)) (1 + Re(χ(n)n^{-iγ}))`, and both factors are
nonnegative termwise (`χ₀ ^ 2 = 1` gives `χ₀(n) ∈ {0, ±1}`, and `‖χ(n)‖ ≤ 1` gives
`1 + Re(χ(n)n^{-iγ}) ≥ 0`).  The file also provides the *complex-point* Λ-expansion
`LFunctionLogDerivReEqTsum_complex`, which the workspace only had at real points.
-/

namespace Work.LinnikAreas.OtherCharAux

open DirichletCharacter

open scoped LSeries.notation

/-- A squaring-to-one Dirichlet character takes only the values `0`, `1`, `-1`. -/
private lemma realChar_value {N : ℕ} (χ : DirichletCharacter ℂ N) (h : χ * χ = 1)
    (a : ZMod N) : χ a = 0 ∨ χ a = 1 ∨ χ a = -1 := by
  by_cases ha : IsUnit a
  · have hmul : χ a * χ a = (1 : DirichletCharacter ℂ N) a := by
      rw [← MulChar.mul_apply, h]
    rw [MulChar.one_apply ha, ← pow_two] at hmul
    rcases sq_eq_one_iff.mp hmul with h' | h'
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr h')
  · exact Or.inl (MulChar.map_nonunit χ ha)

/-- The `n`-th term of the twisted von Mangoldt `L`-series at a complex point, real part. -/
private lemma re_LSeries_term_vonMangoldt_mul_char {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (s : ℂ) (n : ℕ) :
    (LSeries.term (fun k : ℕ => (ArithmeticFunction.vonMangoldt k : ℂ) *
        (χ (k : ZMod N) : ℂ)) s n).re
      = (ArithmeticFunction.vonMangoldt n : ℝ) * (χ (n : ZMod N) * (n : ℂ) ^ (-s)).re := by
  have hf : (fun k : ℕ => (ArithmeticFunction.vonMangoldt k : ℂ) *
      (χ (k : ZMod N) : ℂ)) 0 = 0 := by
    simp [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr not_isPrimePow_zero]
  rw [LSeries.term_def₀ hf]
  rcases eq_or_ne n 0 with rfl | hn
  · rw [show (ArithmeticFunction.vonMangoldt 0 : ℝ) = 0 from by
      rw [ArithmeticFunction.vonMangoldt_eq_zero_iff]; exact not_isPrimePow_zero]
    simp
  · rw [mul_assoc, Complex.re_ofReal_mul]

/-- **The Λ-expansion of `L′/L` at a complex point.**  For `Re s > 1`,
`Re (-L′/L)(s,χ) = Σ_n Λ(n)·Re(χ(n)·n^{-s})`. -/
theorem LFunctionLogDerivReEqTsum_complex {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 1 < s.re) :
    (logDeriv (DirichletCharacter.LFunction χ) s).re =
      -∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * (χ (n : ZMod N) * (n : ℂ) ^ (-s)).re := by
  have hsumm : LSeriesSummable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) *
      (χ (n : ZMod N) : ℂ)) s :=
    (LSeriesSummable_congr s
      (f := fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod N) : ℂ))
      (g := fun n : ℕ => (χ (n : ZMod N) : ℂ) * (ArithmeticFunction.vonMangoldt n : ℂ))
      (fun _ => mul_comm _ _)).mpr (DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hs)
  rw [Commons.NumberTheory.DirichletCharacter.LFunction_logDeriv_eq_neg_LSeries_vonMangoldt χ hs,
    Complex.neg_re, neg_inj]
  change (∑' n : ℕ, LSeries.term (fun k : ℕ => (ArithmeticFunction.vonMangoldt k : ℂ) *
    (χ (k : ZMod N) : ℂ)) s n).re = _
  rw [Complex.re_tsum hsumm]
  exact tsum_congr (fun n => re_LSeries_term_vonMangoldt_mul_char χ s n)

/-- `Re (-ζ′/ζ)(σ)` is the von Mangoldt series (the `ζ` case of the expansion). -/
private theorem neg_zeta_logDeriv_re_eq_tsum (σ : ℝ) (hσ : 1 < σ) :
    -(logDeriv riemannZeta (σ : ℂ)).re
      = ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ) := by
  rw [logDeriv_apply]
  have h := Work.LinnikAreas.vonMangoldtTsum_eq_neg_zeta_logDeriv_re σ hσ
  rw [neg_div, Complex.neg_re] at h
  exact h.symm

/-- Associating a sum of four absolutely convergent series into a single series. -/
private lemma tsum_four_add {a b c d : ℕ → ℝ} (ha : Summable a) (hb : Summable b)
    (hc : Summable c) (hd : Summable d) :
    tsum a + tsum b + tsum c + tsum d = tsum (fun n : ℕ => ((a n + b n) + c n) + d n) := by
  rw [← Summable.tsum_add ha hb, ← Summable.tsum_add (ha.add hb) hc,
    ← Summable.tsum_add ((ha.add hb).add hc) hd]

/-- Summability of the twisted von Mangoldt series in real-part form. -/
private lemma summable_twisted {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) *
      (χ (n : ZMod N) * (n : ℂ) ^ (-s)).re) := by
  have hsm : Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) *
      (n : ℝ) ^ (-s.re)) := by
    refine (summable_congr (fun n => ?_)).mpr
      (Commons.NumberTheory.Zeta.summable_vonMangoldt_div_rpow hs)
    rw [Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
  refine Summable.of_norm_bounded hsm (fun n => ?_)
  have hΛ : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) := ArithmeticFunction.vonMangoldt_nonneg
  have hb : |(χ (n : ZMod N) * (n : ℂ) ^ (-s)).re| ≤ (n : ℝ) ^ (-s.re) := by
    have h1 : |(χ (n : ZMod N) * (n : ℂ) ^ (-s)).re| ≤ ‖χ (n : ZMod N) * (n : ℂ) ^ (-s)‖ :=
      Complex.abs_re_le_norm _
    have h2 : ‖χ (n : ZMod N) * (n : ℂ) ^ (-s)‖
        ≤ ‖χ (n : ZMod N)‖ * ‖(n : ℂ) ^ (-s)‖ := norm_mul_le _ _
    have h3 : ‖χ (n : ZMod N)‖ ≤ 1 := χ.norm_le_one _
    have h4 : ‖(n : ℂ) ^ (-s)‖ ≤ (n : ℝ) ^ (-s.re) := by
      rcases eq_or_ne n 0 with rfl | hn
      · have h0 : (0 : ℂ) ^ (-s) = 0 := Complex.zero_cpow (by
          intro h; have h2 := congrArg Complex.re h; simp at h2; linarith)
        rw [Nat.cast_zero, h0, norm_zero]
        exact Real.rpow_nonneg (Nat.cast_nonneg 0) _
      · have hpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
        have hnorm : ‖(((n : ℝ)) : ℂ) ^ (-s)‖ = (n : ℝ) ^ ((-s).re) :=
          Complex.norm_cpow_eq_rpow_re_of_pos hpos (-s)
        simpa using le_of_eq hnorm
    calc |(χ (n : ZMod N) * (n : ℂ) ^ (-s)).re|
        ≤ ‖χ (n : ZMod N) * (n : ℂ) ^ (-s)‖ := h1
      _ ≤ ‖χ (n : ZMod N)‖ * ‖(n : ℂ) ^ (-s)‖ := h2
      _ ≤ 1 * (n : ℝ) ^ (-s.re) := mul_le_mul h3 h4 (norm_nonneg _) (by positivity)
      _ = (n : ℝ) ^ (-s.re) := one_mul _
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hΛ]
  exact mul_le_mul_of_nonneg_left hb hΛ

/-- **The twisted Landau positivity** (the other-character positivity).  For a real character
`χ₀` (`χ₀ ^ 2 = 1`) and any character `χ` modulo `q`, and real `σ > 1`, `γ`,

`(-ζ′/ζ)(σ) + (-L′/L)(σ,χ₀) + (-L′/L)(σ+iγ,χ) + (-L′/L)(σ+iγ,χ₀χ) ≥ 0`.

This is the positivity input for the λ₁-uniform Deuring–Heilbronn repulsion in the
other-character case (Heath-Brown (1992), Principle 2). -/
theorem twistedNonneg {q : ℕ} [NeZero q] (χ₀ χ : DirichletCharacter ℂ q) (h₀ : χ₀ ^ 2 = 1)
    {σ γ : ℝ} (hσ : 1 < σ) :
    0 ≤ (-(logDeriv riemannZeta (σ : ℂ)).re)
      + (-(logDeriv (DirichletCharacter.LFunction χ₀) (σ : ℂ)).re)
      + (-(logDeriv (DirichletCharacter.LFunction χ)
          ((σ : ℂ) + Complex.I * (γ : ℂ))).re)
      + (-(logDeriv (DirichletCharacter.LFunction (χ₀ * χ))
          ((σ : ℂ) + Complex.I * (γ : ℂ))).re) := by
  have hsq : χ₀ * χ₀ = 1 := by rw [← pow_two]; exact h₀
  have hs1 : 1 < ((σ : ℂ) + Complex.I * (γ : ℂ)).re := by
    have h : ((σ : ℂ) + Complex.I * (γ : ℂ)).re = σ := by simp
    rw [h]; exact hσ
  have hz := neg_zeta_logDeriv_re_eq_tsum σ hσ
  have h0 := OtherCharRepel.LFunctionLogDerivReEqTsum χ₀ hσ
  have h1 := LFunctionLogDerivReEqTsum_complex χ (s := (σ : ℂ) + Complex.I * (γ : ℂ)) hs1
  have h2 := LFunctionLogDerivReEqTsum_complex (χ₀ * χ)
    (s := (σ : ℂ) + Complex.I * (γ : ℂ)) hs1
  set A : ℕ → ℝ := fun n => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ) with hA
  set B : ℕ → ℝ := fun n => (ArithmeticFunction.vonMangoldt n : ℝ) * (χ₀ (n : ZMod q)).re *
      (n : ℝ) ^ (-σ) with hB
  set C : ℕ → ℝ := fun n => (ArithmeticFunction.vonMangoldt n : ℝ) *
      (χ (n : ZMod q) * (n : ℂ) ^ (-((σ : ℂ) + Complex.I * (γ : ℂ)))).re with hC
  set D : ℕ → ℝ := fun n => (ArithmeticFunction.vonMangoldt n : ℝ) *
      ((χ₀ * χ) (n : ZMod q) * (n : ℂ) ^ (-((σ : ℂ) + Complex.I * (γ : ℂ)))).re with hD
  have hAsm : Summable A := by
    rw [hA]
    exact (summable_congr (fun n => by
      rw [Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv])).mpr
        (Commons.NumberTheory.Zeta.summable_vonMangoldt_div_rpow hσ)
  have hBsm : Summable B := by
    rw [hB]; exact OtherCharRepel.summableVonMangoldtReCharMulRpow χ₀ hσ
  have hCsm : Summable C := by rw [hC]; exact summable_twisted χ hs1
  have hDsm : Summable D := by rw [hD]; exact summable_twisted (χ₀ * χ) hs1
  have hAeq : -(logDeriv riemannZeta (σ : ℂ)).re = tsum A := by rw [hA, hz]
  have hBeq : -(logDeriv (DirichletCharacter.LFunction χ₀) (σ : ℂ)).re = tsum B := by
    rw [hB, h0, neg_neg]
  have hCeq : -(logDeriv (DirichletCharacter.LFunction χ)
      ((σ : ℂ) + Complex.I * (γ : ℂ))).re = tsum C := by
    rw [hC, h1, neg_neg]
  have hDeq : -(logDeriv (DirichletCharacter.LFunction (χ₀ * χ))
      ((σ : ℂ) + Complex.I * (γ : ℂ))).re = tsum D := by
    rw [hD, h2, neg_neg]
  rw [hAeq, hBeq, hCeq, hDeq, tsum_four_add hAsm hBsm hCsm hDsm]
  refine tsum_nonneg (fun n => ?_)
  have hΛ : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) := ArithmeticFunction.vonMangoldt_nonneg
  have hn : 0 ≤ (n : ℝ) ^ (-σ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have him0 : (χ₀ (n : ZMod q)).im = 0 := by
    rcases realChar_value χ₀ hsq (n : ZMod q) with hv | hv | hv <;> rw [hv] <;> simp
  have hre0 : -1 ≤ (χ₀ (n : ZMod q)).re := by
    rcases realChar_value χ₀ hsq (n : ZMod q) with hv | hv | hv <;> rw [hv] <;> norm_num
  have hsplit : (n : ℂ) ^ (-((σ : ℂ) + Complex.I * (γ : ℂ)))
      = Complex.ofReal ((n : ℝ) ^ (-σ)) * (n : ℂ) ^ (-(Complex.I * (γ : ℂ))) := by
    rcases eq_or_ne n 0 with rfl | hn0
    · have hz0 : -((σ : ℂ) + Complex.I * (γ : ℂ)) ≠ 0 := by
        intro h; have h2 := congrArg Complex.re h; simp at h2; linarith
      have hz1 : ((-σ : ℝ)) ≠ 0 := by linarith
      simp only [Nat.cast_zero, Complex.zero_cpow hz0, Real.zero_rpow hz1,
        Complex.ofReal_zero, zero_mul, eq_self_iff_true]
    · have hpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
      have hne : (n : ℂ) ≠ 0 := by
        rw [← Complex.ofReal_natCast]
        exact Complex.ofReal_ne_zero.mpr (ne_of_gt hpos)
      have hexp : -((σ : ℂ) + Complex.I * (γ : ℂ))
          = (-(σ : ℂ)) + (-(Complex.I * (γ : ℂ))) := by ring
      rw [hexp, Complex.cpow_add _ _ hne]
      congr 1
      rw [show (-(σ : ℂ)) = ((-σ : ℝ) : ℂ) by simp]
      exact (Complex.ofReal_cpow (le_of_lt hpos) (-σ)).symm
  have hAn : A n = (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ) := rfl
  have hBn : B n = (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ) *
      (χ₀ (n : ZMod q)).re := by rw [hB]; ring
  have hCn : C n = (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ) *
      (χ (n : ZMod q) * (n : ℂ) ^ (-(Complex.I * (γ : ℂ)))).re := by
    rw [hC]
    simp only []
    rw [hsplit]
    rw [show χ (n : ZMod q) * (Complex.ofReal ((n : ℝ) ^ (-σ)) *
          (n : ℂ) ^ (-(Complex.I * (γ : ℂ))))
        = Complex.ofReal ((n : ℝ) ^ (-σ)) *
          (χ (n : ZMod q) * (n : ℂ) ^ (-(Complex.I * (γ : ℂ)))) by ring]
    rw [Complex.re_ofReal_mul]
    ring
  have hDn : D n = (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ) *
      ((χ₀ (n : ZMod q)).re * (χ (n : ZMod q) * (n : ℂ) ^ (-(Complex.I * (γ : ℂ)))).re) := by
    rw [hD]
    simp only []
    rw [MulChar.mul_apply, hsplit]
    rw [show χ₀ (n : ZMod q) * χ (n : ZMod q) *
          (Complex.ofReal ((n : ℝ) ^ (-σ)) * (n : ℂ) ^ (-(Complex.I * (γ : ℂ))))
        = Complex.ofReal ((n : ℝ) ^ (-σ)) *
          (χ₀ (n : ZMod q) * (χ (n : ZMod q) * (n : ℂ) ^ (-(Complex.I * (γ : ℂ))))) by ring]
    rw [Complex.re_ofReal_mul, Complex.mul_re, him0]
    ring
  have hcomb : ((A n + B n) + C n) + D n
      = (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ) *
        (1 + (χ₀ (n : ZMod q)).re) *
        (1 + (χ (n : ZMod q) * (n : ℂ) ^ (-(Complex.I * (γ : ℂ)))).re) := by
    rw [hAn, hBn, hCn, hDn]; ring
  rw [hcomb]
  have hz1 : 0 ≤ 1 + (χ (n : ZMod q) * (n : ℂ) ^ (-(Complex.I * (γ : ℂ)))).re := by
    have hb : |(χ (n : ZMod q) * (n : ℂ) ^ (-(Complex.I * (γ : ℂ)))).re| ≤ 1 := by
      have h1' : |(χ (n : ZMod q) * (n : ℂ) ^ (-(Complex.I * (γ : ℂ)))).re|
          ≤ ‖χ (n : ZMod q) * (n : ℂ) ^ (-(Complex.I * (γ : ℂ)))‖ := Complex.abs_re_le_norm _
      have h2' : ‖χ (n : ZMod q) * (n : ℂ) ^ (-(Complex.I * (γ : ℂ)))‖
          ≤ ‖χ (n : ZMod q)‖ * ‖(n : ℂ) ^ (-(Complex.I * (γ : ℂ)))‖ := norm_mul_le _ _
      have h3' : ‖χ (n : ZMod q)‖ ≤ 1 := χ.norm_le_one _
      have h4' : ‖(n : ℂ) ^ (-(Complex.I * (γ : ℂ)))‖ ≤ 1 := by
        rcases eq_or_ne n 0 with rfl | hn0
        · rcases eq_or_ne (-(Complex.I * (γ : ℂ))) 0 with hw | hw
          · rw [Nat.cast_zero, hw]; norm_num
          · rw [Nat.cast_zero, Complex.zero_cpow hw, norm_zero]; norm_num
        · have hpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
          have hgoal : ‖(((n : ℝ)) : ℂ) ^ (-(Complex.I * (γ : ℂ)))‖ ≤ 1 := by
            rw [Complex.norm_cpow_eq_rpow_re_of_pos hpos (-(Complex.I * (γ : ℂ)))]
            have hzero : (-(Complex.I * (γ : ℂ))).re = 0 := by simp
            rw [hzero]; norm_num
          simpa using hgoal
      calc |(χ (n : ZMod q) * (n : ℂ) ^ (-(Complex.I * (γ : ℂ)))).re|
          ≤ ‖χ (n : ZMod q) * (n : ℂ) ^ (-(Complex.I * (γ : ℂ)))‖ := h1'
        _ ≤ ‖χ (n : ZMod q)‖ * ‖(n : ℂ) ^ (-(Complex.I * (γ : ℂ)))‖ := h2'
        _ ≤ 1 * 1 := mul_le_mul h3' h4' (norm_nonneg _) (by norm_num)
        _ = 1 := mul_one 1
    linarith [neg_le_of_abs_le hb]
  exact mul_nonneg (mul_nonneg (mul_nonneg hΛ hn) (by linarith)) hz1

end Work.LinnikAreas.OtherCharAux

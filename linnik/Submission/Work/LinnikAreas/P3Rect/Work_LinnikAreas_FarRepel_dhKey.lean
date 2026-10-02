import Mathlib
import Submission.Work.LinnikAreas.P3Rect.Work_LinnikAreas_FarRepel_multZ_explicit
import Submission.Work.LinnikAreas.P3Rect.Work_LinnikAreas_FarRepel_dhBasic
import Submission.Work.LinnikAreas.FarRepel.arithKthDeriv
import Submission.Work.ZeroFreeTables.P3.SummableVonMangoldtLogPow

namespace Work.LinnikAreas.FarRepel

noncomputable section

/-! ## Helper lemmas for the two-point Deuring--Heilbronn bound -/

/-- A Dirichlet character with `χ ^ 2 = 1` takes only values `0`, `1`, `-1`. -/
private lemma charValue_sq_one {q : ℕ} (χ : DirichletCharacter ℂ q) (h : χ ^ 2 = 1)
    (m : ZMod q) : χ m = 0 ∨ χ m = 1 ∨ χ m = -1 := by
  by_cases hm : IsUnit m
  · have hmul : χ m * χ m = 1 := by
      have hsq : χ * χ = 1 := by rw [← pow_two]; exact h
      rw [← MulChar.mul_apply, hsq, MulChar.one_apply hm]
    rw [← pow_two] at hmul
    rcases sq_eq_one_iff.mp hmul with h' | h'
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr h')
  · exact Or.inl (MulChar.map_nonunit χ hm)

/-- Real part of the coefficient `1/((2j-1)!)` acting on a complex number. -/
private lemma re_one_div_factorial_mul (n : ℕ) (z : ℂ) :
    (((1 : ℂ) / (n.factorial : ℂ)) * z).re = (1 / (n.factorial : ℝ)) * z.re := by
  have hcast : (((1 : ℝ) / (n.factorial : ℝ) : ℝ) : ℂ) = (1 : ℂ) / (n.factorial : ℂ) := by
    rw [Complex.ofReal_div, Complex.ofReal_one, ← Complex.ofReal_natCast n.factorial]
  rw [← hcast, Complex.re_ofReal_mul]

/-- `(1/((c:ℂ)-1)^(2j)).re = 1/(c-1)^(2j)`. -/
private lemma re_one_sub_pow (c : ℝ) (j : ℕ) :
    (1 / ((c : ℂ) - 1) ^ (2 * j)).re = 1 / (c - 1) ^ (2 * j) := by
  have hsub : (c : ℂ) - 1 = ((c - 1 : ℝ) : ℂ) := by push_cast; ring
  rw [hsub, one_div, ← Complex.ofReal_pow, ← Complex.ofReal_inv, Complex.ofReal_re, one_div]

private lemma re_add_I_mul_re (c γ' : ℝ) :
    (((c : ℂ) + Complex.I * (γ' : ℂ)).re) = c := by simp

private lemma re_add_I_mul_im (c γ' : ℝ) :
    (((c : ℂ) + Complex.I * (γ' : ℂ)).im) = γ' := by simp

/-- **The arithmetic side of the two-point Deuring--Heilbronn bound is non-negative.**
For `χ` with `χ ^ 2 = 1` (so `χ(n) ∈ {0, ±1}`), `j ≥ 1` and `1 < c`, the real parts of the
`(2j-1)`-st derivatives of `logDeriv ζ + logDeriv L(·,χ)` at the two points `c` and `c + iγ'`
add up to `≥ 0`. -/
private lemma arithTwoPoint_nonneg_aux {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (hχ2 : χ ^ 2 = 1) (j : ℕ) (hj : 1 ≤ j) {c γ' : ℝ} (hc : 1 < c) :
    0 ≤ (iteratedDeriv (2 * j - 1) (logDeriv riemannZeta) (c : ℂ)
          + iteratedDeriv (2 * j - 1) (logDeriv (DirichletCharacter.LFunction χ)) (c : ℂ)).re
      + (iteratedDeriv (2 * j - 1) (logDeriv riemannZeta) ((c : ℂ) + Complex.I * (γ' : ℂ))
          + iteratedDeriv (2 * j - 1) (logDeriv (DirichletCharacter.LFunction χ))
              ((c : ℂ) + Complex.I * (γ' : ℂ))).re := by
  have hk : 1 ≤ 2 * j - 1 := by omega
  have hodd : (2 * j - 1) % 2 = 1 := by
    have h : 2 * j - 1 = 2 * (j - 1) + 1 := by omega
    rw [h]; omega
  set A : ℕ → ℝ := fun n => (ArithmeticFunction.vonMangoldt n : ℝ)
      * (1 + (χ ((n : ℕ) : ZMod q)).re) * (Real.log (n : ℝ)) ^ (2 * j - 1)
      * (n : ℝ) ^ (-c) with hAdef
  set B : ℕ → ℝ := fun n => A n * Real.cos (γ' * Real.log (n : ℝ)) with hBdef
  have hAn : ∀ n : ℕ, A n = (ArithmeticFunction.vonMangoldt n : ℝ)
      * (1 + (χ ((n : ℕ) : ZMod q)).re) * (Real.log (n : ℝ)) ^ (2 * j - 1)
      * (n : ℝ) ^ (-c) := fun n => rfl
  have hBn : ∀ n : ℕ, B n = A n * Real.cos (γ' * Real.log (n : ℝ)) := fun n => rfl
  have hA' : (iteratedDeriv (2 * j - 1) (logDeriv riemannZeta) (c : ℂ)
        + iteratedDeriv (2 * j - 1) (logDeriv (DirichletCharacter.LFunction χ)) (c : ℂ)).re
      = ∑' n : ℕ, A n := by
    rw [arithKthDeriv χ hχ hχ2 (2 * j - 1) hk hodd (s := (c : ℂ)) (by simpa using hc)]
    refine tsum_congr (fun n => ?_)
    rw [Complex.ofReal_re, Complex.ofReal_im, zero_mul, Real.cos_zero, mul_one, hAn n]
  have hB' : (iteratedDeriv (2 * j - 1) (logDeriv riemannZeta) ((c : ℂ) + Complex.I * (γ' : ℂ))
        + iteratedDeriv (2 * j - 1) (logDeriv (DirichletCharacter.LFunction χ))
            ((c : ℂ) + Complex.I * (γ' : ℂ))).re
      = ∑' n : ℕ, B n := by
    have hsg : 1 < ((c : ℂ) + Complex.I * (γ' : ℂ)).re := by
      rw [re_add_I_mul_re]; exact hc
    rw [arithKthDeriv χ hχ hχ2 (2 * j - 1) hk hodd
      (s := (c : ℂ) + Complex.I * (γ' : ℂ)) hsg]
    refine tsum_congr (fun n => ?_)
    rw [re_add_I_mul_re, re_add_I_mul_im, hBn n, hAn n]
  have hD : Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ)
      * (Real.log (n : ℝ)) ^ (2 * j - 1) / (n : ℝ) ^ c) :=
    Work.ZeroFreeTables.P3.SummableVonMangoldtLogPow hc (2 * j - 1)
  have hbound : ∀ n : ℕ, ‖A n‖ ≤ 2 * ((ArithmeticFunction.vonMangoldt n : ℝ)
      * (Real.log (n : ℝ)) ^ (2 * j - 1) / (n : ℝ) ^ c) := by
    intro n
    have hΛ : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) :=
      ArithmeticFunction.vonMangoldt_nonneg
    have hlog : 0 ≤ (Real.log (n : ℝ)) ^ (2 * j - 1) :=
      pow_nonneg (Real.log_natCast_nonneg n) _
    have hrp : 0 ≤ (n : ℝ) ^ (-c) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    have hcoef : |1 + (χ ((n : ℕ) : ZMod q)).re| ≤ 2 := by
      rcases charValue_sq_one χ hχ2 ((n : ℕ) : ZMod q) with h | h | h <;> rw [h] <;> norm_num
    have h1 : ‖A n‖ = (ArithmeticFunction.vonMangoldt n : ℝ)
        * |1 + (χ ((n : ℕ) : ZMod q)).re|
        * (Real.log (n : ℝ)) ^ (2 * j - 1) * (n : ℝ) ^ (-c) := by
      rw [hAn n, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
        abs_of_nonneg hΛ, abs_of_nonneg hlog, abs_of_nonneg hrp]
    have h2 : (ArithmeticFunction.vonMangoldt n : ℝ) * |1 + (χ ((n : ℕ) : ZMod q)).re|
          * (Real.log (n : ℝ)) ^ (2 * j - 1) * (n : ℝ) ^ (-c)
        ≤ 2 * ((ArithmeticFunction.vonMangoldt n : ℝ) * (Real.log (n : ℝ)) ^ (2 * j - 1)
          / (n : ℝ) ^ c) := by
      have h3 : (ArithmeticFunction.vonMangoldt n : ℝ) * |1 + (χ ((n : ℕ) : ZMod q)).re|
            * (Real.log (n : ℝ)) ^ (2 * j - 1) * (n : ℝ) ^ (-c)
          ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * 2
            * (Real.log (n : ℝ)) ^ (2 * j - 1) * (n : ℝ) ^ (-c) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcoef hΛ) hlog) hrp
      have h4 : (ArithmeticFunction.vonMangoldt n : ℝ) * 2
            * (Real.log (n : ℝ)) ^ (2 * j - 1) * (n : ℝ) ^ (-c)
          = 2 * ((ArithmeticFunction.vonMangoldt n : ℝ) * (Real.log (n : ℝ)) ^ (2 * j - 1)
              / (n : ℝ) ^ c) := by
        rw [Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]; ring
      exact h3.trans (le_of_eq h4)
    rw [h1]
    exact h2
  have hAsm : Summable A := Summable.of_norm_bounded (hD.mul_left 2) hbound
  have hBsm : Summable B := by
    refine Summable.of_norm_bounded (hD.mul_left 2) (fun n => ?_)
    have hpos2 : 0 ≤ 2 * ((ArithmeticFunction.vonMangoldt n : ℝ)
        * (Real.log (n : ℝ)) ^ (2 * j - 1) / (n : ℝ) ^ c) := by
      have h1 : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * (Real.log (n : ℝ)) ^ (2 * j - 1)
          / (n : ℝ) ^ c := div_nonneg
        (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
          (pow_nonneg (Real.log_natCast_nonneg n) _))
        (Real.rpow_nonneg (Nat.cast_nonneg n) c)
      linarith only [h1]
    have h1 : ‖B n‖ = ‖A n‖ * |Real.cos (γ' * Real.log (n : ℝ))| := by
      simp only [hBn n, Real.norm_eq_abs, abs_mul]
    have h2 : ‖A n‖ * |Real.cos (γ' * Real.log (n : ℝ))|
        ≤ 2 * ((ArithmeticFunction.vonMangoldt n : ℝ) * (Real.log (n : ℝ)) ^ (2 * j - 1)
          / (n : ℝ) ^ c) :=
      (mul_le_mul (hbound n) (Real.abs_cos_le_one (γ' * Real.log (n : ℝ)))
        (abs_nonneg _) hpos2).trans (le_of_eq (by ring))
    rw [h1]
    exact h2
  have hsum : (iteratedDeriv (2 * j - 1) (logDeriv riemannZeta) (c : ℂ)
        + iteratedDeriv (2 * j - 1) (logDeriv (DirichletCharacter.LFunction χ)) (c : ℂ)).re
      + (iteratedDeriv (2 * j - 1) (logDeriv riemannZeta) ((c : ℂ) + Complex.I * (γ' : ℂ))
        + iteratedDeriv (2 * j - 1) (logDeriv (DirichletCharacter.LFunction χ))
            ((c : ℂ) + Complex.I * (γ' : ℂ))).re
      = ∑' n : ℕ, (A n + B n) := by
    rw [hA', hB', ← Summable.tsum_add hAsm hBsm]
  rw [hsum]
  refine tsum_nonneg (fun n => ?_)
  have hΛ : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) := ArithmeticFunction.vonMangoldt_nonneg
  have hlog : 0 ≤ (Real.log (n : ℝ)) ^ (2 * j - 1) :=
    pow_nonneg (Real.log_natCast_nonneg n) _
  have hrp : 0 ≤ (n : ℝ) ^ (-c) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have h1c : 0 ≤ 1 + (χ ((n : ℕ) : ZMod q)).re := by
    rcases charValue_sq_one χ hχ2 ((n : ℕ) : ZMod q) with h | h | h <;> rw [h] <;> norm_num
  have hcos : 0 ≤ 1 + Real.cos (γ' * Real.log (n : ℝ)) := by
    linarith only [Real.neg_one_le_cos (γ' * Real.log (n : ℝ))]
  rw [hBn n, hAn n]
  have hAB : (ArithmeticFunction.vonMangoldt n : ℝ) * (1 + (χ ((n : ℕ) : ZMod q)).re)
        * (Real.log (n : ℝ)) ^ (2 * j - 1) * (n : ℝ) ^ (-c)
      + (ArithmeticFunction.vonMangoldt n : ℝ) * (1 + (χ ((n : ℕ) : ZMod q)).re)
        * (Real.log (n : ℝ)) ^ (2 * j - 1) * (n : ℝ) ^ (-c)
        * Real.cos (γ' * Real.log (n : ℝ))
      = (ArithmeticFunction.vonMangoldt n : ℝ) * (1 + (χ ((n : ℕ) : ZMod q)).re)
        * (Real.log (n : ℝ)) ^ (2 * j - 1) * (n : ℝ) ^ (-c)
        * (1 + Real.cos (γ' * Real.log (n : ℝ))) := by ring
  rw [hAB]
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hΛ h1c) hlog) hrp) hcos

/-- (in namespace `Work.LinnikAreas.FarRepel`; module `Submission.Work.LinnikAreas.FarRepel.dhKey`)

**The two-point bound of the Deuring–Heilbronn inequality.**  Let `χ` be a non-principal primitive
real character (`χ ^ 2 = 1`) mod `q`, let `j ≥ 1`, let `a ∈ {0,1}` be the parity shift of `χ`
(`a = 0` if `χ` is even, `a = 1` if `χ` is odd), and let `1 < c`, `γ' ∈ ℝ`.
With `multZ χ u = analyticOrderNatAt completedRiemannZeta u + Work.LinnikContract.zeroMult χ u` the
multiplicity of `u` as a non-trivial zero of `ζ_K = ζ·L(·,χ)` and
`Wt c γ' j u = Re (1/(c-u)^{2j}) + Re (1/(c+iγ'-u)^{2j})`, the multiplicity-weighted two-point zero
sum is summable and bounded by the two pole contributions:

`(∑' u, (multZ χ u : ℝ)·Wt c γ' j u) ≤ 1/(c-1)^{2j} + Re (1/(c+iγ'-1)^{2j})`.

These are exactly the `hsumm` and `hkey` hypotheses of `Work.LinnikAreas.FarRepel.final_step`
(`dhBasic`); `β₁` does not enter, so `Work.LinnikAreas.FarRepel.dhDiffInequality` follows from this
together with `final_step`.  Equivalently this is the two-point real form of the combined
Lagarias–Montgomery–Odlyzko identity (p. 289; Kadiri–Ng–Wong arXiv:1902.08640 (2.5)–(2.6)).

PROOF.  Put `k := 2j-1` (odd, `k+1 = 2j`) and instantiate
`Work.LinnikAreas.FarRepel.multZ_explicit` (the combined `ζ_K` explicit formula) at the two points
`s = (c:ℂ)` and `s = (c:ℂ) + I*γ'` (both of real part `c > 1`); take real parts of both identities
and add them.  Then:
* the zero sums become `∑' u, (multZ χ u : ℝ)·Wt c γ' j u` via `re_tsum_multZ` and `Wt`;
* the pole side is `1/(c-1)^{2j} + Re (1/(c+iγ'-1)^{2j})` (`(c:ℂ) - 1 = ((c-1:ℝ):ℂ)` and
  `one_div_pow` for the second point);
* the trivial-zero side is minus a sum of four real parts, i.e. the `d = 2` part (for `ζ`, since
  `2(n+1) = 2 + 2n`) and the `d = a` part (for `L`); each of
  `(∑' n, (1/((c:ℂ)+(d+2n)))^{2j}).re + (∑' n, (1/((c:ℂ)+I*γ'+(d+2n)))^{2j}).re`
  is `≥ 0` by `trivSeries_nonneg` in `dhBasic`, so the trivial-zero contribution is `≤ 0`;
* the arithmetic side is `-(1/k!)·(A₀ + A₁)` where `A₀`, `A₁` are the real parts of
  `(logDeriv ζ)^(k) + (logDeriv L)^(k)` at `c` and `c+iγ'`; `A₀ + A₁ ≥ 0` is
  `arithTwoPoint_nonneg_aux` below (proved by `arithKthDeriv` plus the termwise inequality
  `Λ(n)(1+χ(n))(log n)^k n^{-c}(1 + cos(γ' log n)) ≥ 0`), so this contribution is `≤ 0`;
* hence the left-hand side is `≤` the pole side, which is the stated bound (`1/k! > 0`). -/
theorem dhKey {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) (hχ2 : χ ^ 2 = 1) (j : ℕ) (hj : 1 ≤ j)
    (a : ℕ) (ha0 : χ.Even → a = 0) (ha1 : χ.Odd → a = 1)
    {c γ' : ℝ} (hc : 1 < c) :
    Summable (fun u : ℂ => (multZ χ u : ℝ) * Wt c γ' j u) ∧
    (∑' u : ℂ, (multZ χ u : ℝ) * Wt c γ' j u)
      ≤ 1 / (c - 1) ^ (2 * j)
        + ((1 / ((c : ℂ) + Complex.I * (γ' : ℂ) - 1)) ^ (2 * j)).re := by
  have hc0 : 1 < (c : ℂ).re := by simpa using hc
  have hsg : 1 < ((c : ℂ) + Complex.I * (γ' : ℂ)).re := by
    rw [re_add_I_mul_re]; exact hc
  -- abbreviations for the two evaluation points
  set Zs0 : ℂ := ∑' u : ℂ, (multZ χ u : ℂ) * (1 / ((c : ℂ) - u)) ^ (2 * j) with hZs0
  set Zs1 : ℂ := ∑' u : ℂ,
    (multZ χ u : ℂ) * (1 / (((c : ℂ) + Complex.I * (γ' : ℂ)) - u)) ^ (2 * j) with hZs1
  set Tzs0 : ℂ := ∑' n : ℕ, (1 / ((c : ℂ) + ((2 * (n + 1) : ℕ) : ℂ))) ^ (2 * j) with hTzs0
  set Tls0 : ℂ := ∑' n : ℕ, (1 / ((c : ℂ) + ((a + 2 * n : ℕ) : ℂ))) ^ (2 * j) with hTls0
  set Tzs1 : ℂ := ∑' n : ℕ,
    (1 / (((c : ℂ) + Complex.I * (γ' : ℂ)) + ((2 * (n + 1) : ℕ) : ℂ))) ^ (2 * j) with hTzs1
  set Tls1 : ℂ := ∑' n : ℕ,
    (1 / (((c : ℂ) + Complex.I * (γ' : ℂ)) + ((a + 2 * n : ℕ) : ℂ))) ^ (2 * j) with hTls1
  set P0 : ℂ := 1 / ((c : ℂ) - 1) ^ (2 * j) with hP0
  set P1 : ℂ := 1 / ((c : ℂ) + Complex.I * (γ' : ℂ) - 1) ^ (2 * j) with hP1
  set A0 : ℂ := iteratedDeriv (2 * j - 1) (logDeriv riemannZeta) (c : ℂ)
      + iteratedDeriv (2 * j - 1) (logDeriv (DirichletCharacter.LFunction χ)) (c : ℂ) with hA0
  set A1 : ℂ := iteratedDeriv (2 * j - 1) (logDeriv riemannZeta) ((c : ℂ) + Complex.I * (γ' : ℂ))
      + iteratedDeriv (2 * j - 1) (logDeriv (DirichletCharacter.LFunction χ))
          ((c : ℂ) + Complex.I * (γ' : ℂ)) with hA1
  obtain ⟨hsum0, heq0⟩ := multZ_explicit χ hχ hprim j hj a ha0 ha1 (s := (c : ℂ)) hc0
  obtain ⟨hsum1, heq1⟩ := multZ_explicit χ hχ hprim j hj a ha0 ha1
      (s := (c : ℂ) + Complex.I * (γ' : ℂ)) hsg
  have heq0' : Zs0 + (Tzs0 + Tls0) = P0 - (1 / ((2 * j - 1).factorial : ℂ)) * A0 := heq0
  have heq1' : Zs1 + (Tzs1 + Tls1) = P1 - (1 / ((2 * j - 1).factorial : ℂ)) * A1 := heq1
  have h0raw : Zs0.re + (Tzs0.re + Tls0.re)
      = P0.re - (1 / ((2 * j - 1).factorial : ℝ)) * A0.re := by
    have h := congrArg Complex.re heq0'
    rw [Complex.add_re, Complex.add_re, Complex.sub_re, re_one_div_factorial_mul] at h
    exact h
  have h1raw : Zs1.re + (Tzs1.re + Tls1.re)
      = P1.re - (1 / ((2 * j - 1).factorial : ℝ)) * A1.re := by
    have h := congrArg Complex.re heq1'
    rw [Complex.add_re, Complex.add_re, Complex.sub_re, re_one_div_factorial_mul] at h
    exact h
  set U0 : ℝ := (1 / ((2 * j - 1).factorial : ℝ)) * A0.re with hU0
  set U1 : ℝ := (1 / ((2 * j - 1).factorial : ℝ)) * A1.re with hU1
  have h0 : Zs0.re + (Tzs0.re + Tls0.re) = P0.re - U0 := h0raw
  have h1 : Zs1.re + (Tzs1.re + Tls1.re) = P1.re - U1 := h1raw
  have hU : 0 ≤ U0 + U1 := by
    rw [hU0, hU1, ← mul_add]
    exact mul_nonneg (by positivity) (arithTwoPoint_nonneg_aux χ hχ hχ2 j hj hc)
  have htriv : 0 ≤ (Tzs0.re + Tls0.re) + (Tzs1.re + Tls1.re) := by
    have h2 := trivSeries_nonneg (c := c) (γ' := γ') (j := j) (by linarith only [hc] : 0 < c) hj 2
    have ha := trivSeries_nonneg (c := c) (γ' := γ') (j := j) (by linarith only [hc] : 0 < c) hj a
    have e0 : Tzs0.re
        = (∑' n : ℕ, (1 / ((c : ℂ) + ((2 + 2 * n : ℕ) : ℂ))) ^ (2 * j)).re := by
      rw [hTzs0]
      exact congrArg Complex.re (tsum_congr (fun n => by
        rw [show (2 * (n + 1) : ℕ) = 2 + 2 * n from by omega]))
    have e1 : Tzs1.re
        = (∑' n : ℕ, (1 / ((c : ℂ) + Complex.I * (γ' : ℂ)
            + ((2 + 2 * n : ℕ) : ℂ))) ^ (2 * j)).re := by
      rw [hTzs1]
      exact congrArg Complex.re (tsum_congr (fun n => by
        rw [show (2 * (n + 1) : ℕ) = 2 + 2 * n from by omega]))
    rw [e0, e1]
    linarith only [h2, ha]
  have hs0 : Summable (fun u : ℂ => (multZ χ u : ℝ) * ((1 / ((c : ℂ) - u)) ^ (2 * j)).re) := by
    refine (hsum0.map Complex.reCLM Complex.reCLM.continuous).congr (fun u => ?_)
    simp only [Function.comp_apply, Complex.reCLM_apply]
    simp [Complex.mul_re]
  have hs1 : Summable (fun u : ℂ =>
      (multZ χ u : ℝ) * ((1 / (((c : ℂ) + Complex.I * (γ' : ℂ)) - u)) ^ (2 * j)).re) := by
    refine (hsum1.map Complex.reCLM Complex.reCLM.continuous).congr (fun u => ?_)
    simp only [Function.comp_apply, Complex.reCLM_apply]
    simp [Complex.mul_re]
  have hZs0re : Zs0.re
      = ∑' u : ℂ, (multZ χ u : ℝ) * ((1 / ((c : ℂ) - u)) ^ (2 * j)).re :=
    re_tsum_multZ χ (s := (c : ℂ)) j hsum0
  have hZs1re : Zs1.re
      = ∑' u : ℂ, (multZ χ u : ℝ) *
          ((1 / (((c : ℂ) + Complex.I * (γ' : ℂ)) - u)) ^ (2 * j)).re :=
    re_tsum_multZ χ (s := (c : ℂ) + Complex.I * (γ' : ℂ)) j hsum1
  have hWt : (∑' u : ℂ, (multZ χ u : ℝ) * Wt c γ' j u) = Zs0.re + Zs1.re := by
    rw [hZs0re, hZs1re, ← Summable.tsum_add hs0 hs1]
    refine tsum_congr (fun u => ?_)
    rw [Wt]; ring
  have htotal : Summable (fun u : ℂ => (multZ χ u : ℝ) * Wt c γ' j u) := by
    refine (hs0.add hs1).congr (fun u => ?_)
    rw [Wt]; ring
  have hP0re : P0.re = 1 / (c - 1) ^ (2 * j) := re_one_sub_pow c j
  have hP1re : P1.re = ((1 / ((c : ℂ) + Complex.I * (γ' : ℂ) - 1)) ^ (2 * j)).re := by
    rw [hP1, one_div_pow]
  refine ⟨htotal, ?_⟩
  calc (∑' u : ℂ, (multZ χ u : ℝ) * Wt c γ' j u)
      = Zs0.re + Zs1.re := hWt
    _ = P0.re + P1.re - (U0 + U1) - ((Tzs0.re + Tls0.re) + (Tzs1.re + Tls1.re)) := by
        linarith only [h0, h1, h0raw, h1raw]
    _ ≤ P0.re + P1.re := by linarith only [hU, htriv]
    _ = 1 / (c - 1) ^ (2 * j)
          + ((1 / ((c : ℂ) + Complex.I * (γ' : ℂ) - 1)) ^ (2 * j)).re := by
        rw [hP0re, hP1re]

end

end Work.LinnikAreas.FarRepel

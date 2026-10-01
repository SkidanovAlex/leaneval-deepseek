import Mathlib

namespace Work.ZeroFreeTables

/-!
# The arithmetic core of the dyadic `exp(-L)` estimate (Heath-Brown 1992)

For a dyadic block `lam2 ∈ [2^j, 2^{j+1})` with `lam2 ≥ 15344/1000 = 15.344` and a
"Linnik length" `L ≥ lam2/(12/11 - ε')`, we need to show that

`exp(-L) < (1/2)^{j+1} · lam2^2 · exp(-(11/12 + 8εe + 2^{-j})·lam2)`

whenever `0 < εe`, `8εe ≤ ε'/2`, `0 < ε' ≤ 1/100`.

The proof is purely numerical.  Multiplying out, the two exponential factors
essentially cancel: the exponential gain `1/(12/11 - ε') - 11/12` of the
truncated weight more than compensates the losses `8εe` and `2^{-j}`, and what
remains is the single arithmetic inequality

`exp 2 · 2^{j+1} < lam2^2`,

which holds because either `j = 3` (and `lam2 > 15.344`, so `lam2^2 > 128 > 16e²`)
or `j ≥ 4` (and `lam2^2 ≥ 2^{2j} = 2^{j-1}·2^{j+1} ≥ 8·2^{j+1} > e²·2^{j+1}`).
-/

/-- `Real.exp 2 < 8`, from the rational bound `Real.exp 1 < 2.7182818286`. -/
private lemma hb88_exp_two_lt_eight : Real.exp 2 < 8 := by
  have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add, pow_two]
  rw [h2]
  nlinarith [h1, Real.exp_pos 1]

/-- The gain/loss inequality on the exponent: the loss `8εe` is dominated by the
gain `1/(12/11 - ε') - 11/12 ≥ 121ε'/144` coming from the truncated weight. -/
private lemma hb88_eps_bound (εe ε' : ℝ) (hεe0 : 0 < εe) (hεe1 : 8 * εe ≤ ε' / 2)
    (hε'0 : 0 < ε') (hε'1 : ε' ≤ 1 / 100) :
    11 / 12 + 8 * εe ≤ 1 / (12 / 11 - ε') := by
  have ht : 0 < 12 / 11 - ε' := by linarith
  rw [le_div_iff₀ ht]
  nlinarith [mul_le_mul_of_nonneg_right hεe1 (le_of_lt ht), hε'0]

/-- The single arithmetic inequality behind the dyadic core. -/
private lemma hb88_exp_two_mul_two_pow_lt_sq (lam2 : ℝ) (j : ℕ)
    (hj1 : (2 : ℝ) ^ j ≤ lam2) (hj2 : lam2 < (2 : ℝ) ^ (j + 1))
    (hbig : 15344 / 1000 ≤ lam2) :
    Real.exp 2 * (2 : ℝ) ^ (j + 1) < lam2 ^ 2 := by
  have hexp8 : Real.exp 2 < 8 := hb88_exp_two_lt_eight
  have hx_pos : 0 < lam2 := by linarith [hbig]
  -- the dyadic index is at least 3
  have hj3 : 3 ≤ j := by
    by_contra h
    have hle : j + 1 ≤ 3 := by omega
    have h3 : (2 : ℝ) ^ (j + 1) ≤ 8 := by
      calc (2 : ℝ) ^ (j + 1) ≤ (2 : ℝ) ^ 3 := pow_le_pow_right₀ (by norm_num) hle
        _ = 8 := by norm_num
    linarith
  by_cases hj4 : 4 ≤ j
  · -- `j ≥ 4`: `lam2^2 ≥ 2^{2j} = 2^{j-1}·2^{j+1} ≥ 8·2^{j+1} > e^2·2^{j+1}`
    have hsq : ((2 : ℝ) ^ j) ^ 2 ≤ lam2 ^ 2 :=
      pow_le_pow_left₀ (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) j) hj1 2
    have hpow_ge : (8 : ℝ) ≤ (2 : ℝ) ^ (j - 1) := by
      have h := pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) (show 3 ≤ j - 1 by omega)
      norm_num at h
      exact h
    have heq : (2 : ℝ) ^ (j - 1) * (2 : ℝ) ^ (j + 1) = ((2 : ℝ) ^ j) ^ 2 := by
      rw [← pow_add]
      have h2j : j - 1 + (j + 1) = 2 * j := by omega
      rw [h2j, pow_mul']
    calc Real.exp 2 * (2 : ℝ) ^ (j + 1) < 8 * (2 : ℝ) ^ (j + 1) :=
          mul_lt_mul_of_pos_right hexp8 (pow_pos (by norm_num : (0 : ℝ) < 2) (j + 1))
      _ ≤ (2 : ℝ) ^ (j - 1) * (2 : ℝ) ^ (j + 1) :=
          mul_le_mul_of_nonneg_right hpow_ge (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (j + 1))
      _ = ((2 : ℝ) ^ j) ^ 2 := heq
      _ ≤ lam2 ^ 2 := hsq
  · -- `j = 3`: `lam2 ≥ 15.344` gives `lam2^2 ≥ 235.4 > 128 = 8·2^4 > e^2·2^4`
    have hj_eq : j = 3 := by omega
    subst hj_eq
    have h4 : (15344 / 1000 : ℝ) ^ 2 ≤ lam2 ^ 2 :=
      pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 15344 / 1000) hbig 2
    have hlt : Real.exp 2 * (2 : ℝ) ^ (3 + 1) < 8 * (2 : ℝ) ^ (3 + 1) :=
      mul_lt_mul_of_pos_right hexp8 (by norm_num)
    have h128 : (8 : ℝ) * (2 : ℝ) ^ (3 + 1) = 128 := by norm_num
    have h235 : (128 : ℝ) < (15344 / 1000 : ℝ) ^ 2 := by norm_num
    linarith

theorem HB88DyadicArith (εe ε' L lam2 : ℝ) (j : ℕ)
    (hεe0 : 0 < εe) (hεe1 : 8 * εe ≤ ε' / 2) (hε'0 : 0 < ε') (hε'1 : ε' ≤ 1 / 100)
    (hL : 0 < L) (hLc : lam2 / (12 / 11 - ε') ≤ L)
    (hj1 : (2 : ℝ) ^ j ≤ lam2) (hj2 : lam2 < (2 : ℝ) ^ (j + 1))
    (hbig : 15344 / 1000 ≤ lam2) :
    Real.exp (-L) < 1 / (2 : ℝ) ^ (j + 1) * lam2 ^ 2 *
      Real.exp (-((11 / 12 + 8 * εe + 1 / (2 : ℝ) ^ j) * lam2)) := by
  have hx_pos : 0 < lam2 := by linarith [hbig]
  have hx2pos : 0 < lam2 ^ 2 := pow_pos hx_pos 2
  have h2jpos : 0 < (2 : ℝ) ^ j := pow_pos (by norm_num : (0 : ℝ) < 2) j
  have hnum : Real.exp 2 * (2 : ℝ) ^ (j + 1) < lam2 ^ 2 :=
    hb88_exp_two_mul_two_pow_lt_sq lam2 j hj1 hj2 hbig
  have hA : 11 / 12 + 8 * εe ≤ 1 / (12 / 11 - ε') :=
    hb88_eps_bound εe ε' hεe0 hεe1 hε'0 hε'1
  -- Step 1: the whole exponential factor is `< exp 2`.
  have hmain : Real.exp (-L) * Real.exp ((11 / 12 + 8 * εe + 1 / (2 : ℝ) ^ j) * lam2)
      < Real.exp 2 := by
    have hstep1 : Real.exp (-L) ≤ Real.exp (-(lam2 / (12 / 11 - ε'))) := by
      rw [Real.exp_le_exp]
      linarith
    have hc_le : (11 / 12 + 8 * εe + 1 / (2 : ℝ) ^ j) - 1 / (12 / 11 - ε')
        ≤ (1 / 2 : ℝ) ^ j := by
      have hp : (1 / 2 : ℝ) ^ j = 1 / (2 : ℝ) ^ j := by rw [one_div_pow]
      rw [hp]
      linarith
    calc Real.exp (-L) * Real.exp ((11 / 12 + 8 * εe + 1 / (2 : ℝ) ^ j) * lam2)
        ≤ Real.exp (-(lam2 / (12 / 11 - ε')))
            * Real.exp ((11 / 12 + 8 * εe + 1 / (2 : ℝ) ^ j) * lam2) :=
          mul_le_mul_of_nonneg_right hstep1 (Real.exp_pos _).le
      _ = Real.exp (-(lam2 / (12 / 11 - ε'))
            + (11 / 12 + 8 * εe + 1 / (2 : ℝ) ^ j) * lam2) :=
          (Real.exp_add _ _).symm
      _ = Real.exp (((11 / 12 + 8 * εe + 1 / (2 : ℝ) ^ j) - 1 / (12 / 11 - ε'))
            * lam2) := by
          congr 1
          ring
      _ ≤ Real.exp ((1 / 2 : ℝ) ^ j * lam2) := by
          rw [Real.exp_le_exp]
          exact mul_le_mul_of_nonneg_right hc_le (le_of_lt hx_pos)
      _ < Real.exp 2 := by
          rw [Real.exp_lt_exp]
          have h2jpow : (1 / 2 : ℝ) ^ j * lam2 = lam2 / (2 : ℝ) ^ j := by
            rw [one_div_pow, one_div, inv_mul_eq_div]
          rw [h2jpow, div_lt_iff₀ h2jpos]
          have hsucc : (2 : ℝ) ^ (j + 1) = 2 * (2 : ℝ) ^ j := by
            rw [pow_succ]
            ring
          linarith
  -- Step 2: divide by `lam2^2` and use the arithmetic inequality.
  have h5 : Real.exp 2 / lam2 ^ 2 < (1 / 2 : ℝ) ^ (j + 1) := by
    rw [one_div_pow]
    rw [div_lt_iff₀ hx2pos]
    rw [one_div, inv_mul_eq_div,
      lt_div_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) (j + 1))]
    exact hnum
  have h6 : Real.exp (-L) * Real.exp ((11 / 12 + 8 * εe + 1 / (2 : ℝ) ^ j) * lam2) / lam2 ^ 2
      < Real.exp 2 / lam2 ^ 2 := div_lt_div_of_pos_right hmain hx2pos
  have hfin : Real.exp (-L) * Real.exp ((11 / 12 + 8 * εe + 1 / (2 : ℝ) ^ j) * lam2) / lam2 ^ 2
      < (1 / 2 : ℝ) ^ (j + 1) := lt_trans h6 h5
  rw [one_div_pow] at hfin
  rw [div_lt_iff₀ hx2pos] at hfin
  -- Turn `< X * exp z` into `< X / exp z = X * exp(-z)`.
  have hzpos : 0 < Real.exp ((11 / 12 + 8 * εe + 1 / (2 : ℝ) ^ j) * lam2) :=
    Real.exp_pos _
  have hzeq : Real.exp (-((11 / 12 + 8 * εe + 1 / (2 : ℝ) ^ j) * lam2))
      = (Real.exp ((11 / 12 + 8 * εe + 1 / (2 : ℝ) ^ j) * lam2))⁻¹ := Real.exp_neg _
  rw [hzeq, ← div_eq_mul_inv]
  rw [lt_div_iff₀ hzpos]
  exact hfin

end Work.ZeroFreeTables

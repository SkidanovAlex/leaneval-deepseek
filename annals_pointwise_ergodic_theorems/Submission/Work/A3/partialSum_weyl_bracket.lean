import Mathlib

/-!
# The elementary Weyl-bracket inequality (Area A3)

Weyl's inequality for the polynomial exponential sum `S_N(θ)` under a Dirichlet approximation
`|θ - a/q| ≤ 1/q²` bounds `‖S_N(θ)‖` by

  `C · N^{1+ε} · (q⁻¹ + N⁻¹ + q·N^{-d})^{δ}`,   `δ = 2^{-(d-1)}`,  `d = deg Q`.

Off the major arcs the Dirichlet denominator satisfies `N ≤ q`, and the estimate used there is
that the *whole* factor `N^{1+δ/4} · (q⁻¹ + N⁻¹ + q·N^{-d})^{δ}` is at most `3 · q^{1-3δ/8}`:
the "`+δ/4`" on the power of `N` is exactly the slack that converts the crude bracket bound
`≪ max(N⁻¹, qN^{-d})` into a power of `q` alone.

This module proves that inequality (`Work.A3.partialSum_weyl_bracket`), together with the
general real-variable statement `Work.A3.weyl_bracket_core` from which it follows.
-/

namespace Work.A3

/-- For real numbers `1 ≤ x ≤ y` and exponents `e ≤ f` with `0 ≤ f`, one has `x^e ≤ y^f`.

If `e ≥ 0` this is monotonicity of the real power in the base, followed by monotonicity in the
exponent (the base `y` is `≥ 1`); if `e < 0` then `x^e ≤ 1` while `y^f ≥ 1`. -/
lemma weylBracket_rpow_le {x y e f : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) (hef : e ≤ f)
    (hf : 0 ≤ f) : x ^ e ≤ y ^ f := by
  rcases le_total 0 e with he | he
  · calc x ^ e ≤ y ^ e := Real.rpow_le_rpow (by linarith) hxy he
      _ ≤ y ^ f := Real.rpow_le_rpow_of_exponent_le (by linarith) hef
  · calc x ^ e ≤ x ^ 0 := Real.rpow_le_rpow_of_exponent_le hx he
      _ = 1 := Real.rpow_zero x
      _ ≤ y ^ f := Real.one_le_rpow (by linarith) hf

/-- **The Weyl bracket, `q`-form.**  For `0 < A ≤ 1/2`, `D ≥ 13/8` and `1 ≤ N ≤ q`,

  `N^{1+A/4} · (q⁻¹ + N⁻¹ + q·N^{-D})^A ≤ 3 · q^{1-3A/8}`.

The bracket is at most `3·max(N⁻¹, q·N^{-D})`; accordingly one splits on which of the two terms
dominates.  In the first case `N^{1+A/4}·(3N⁻¹)^A = 3^A·N^{1-3A/4} ≤ 3·q^{1-3A/8}`, using
`N ≤ q` and `0 ≤ 1-3A/4`.  In the second case
`N^{1+A/4}·(3qN^{-D})^A = 3^A·q^A·N^{1+A/4-DA}` and the hypothesis `D ≥ 13/8` gives
`1 + A/4 - DA ≤ 1 - 11A/8`, so `N^{1+A/4-DA} ≤ q^{1-11A/8}` and the conclusion follows from
`q^A · q^{1-11A/8} = q^{1-3A/8}` and `3^A ≤ 3`. -/
theorem weyl_bracket_core {A D N q : ℝ} (hD : 13 / 8 ≤ D) (hA0 : 0 < A) (hA : A ≤ 1 / 2)
    (hN : 1 ≤ N) (hNq : N ≤ q) (hq : 1 ≤ q) :
    N ^ (1 + A / 4) * (q⁻¹ + N⁻¹ + q * N ^ (-D)) ^ A ≤ 3 * q ^ (1 - 3 * A / 8) := by
  have hNpos : 0 < N := lt_of_lt_of_le one_pos hN
  have hqpos : 0 < q := lt_of_lt_of_le one_pos hq
  have hNnn : (0 : ℝ) ≤ N := hNpos.le
  have hqnn : (0 : ℝ) ≤ q := hqpos.le
  -- the universal factor `3^A ≤ 3`
  have h3A : (3 : ℝ) ^ A ≤ 3 := by
    have h := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 3 by norm_num)
      (show A ≤ 1 by linarith)
    simpa using h
  -- the bracket, and the basic facts used in both cases
  set X : ℝ := q⁻¹ + N⁻¹ + q * N ^ (-D) with hX
  have hXnn : 0 ≤ X := by
    rw [hX]
    have h1 : 0 ≤ q⁻¹ := inv_nonneg.mpr hqnn
    have h2 : 0 ≤ N⁻¹ := inv_nonneg.mpr hNnn
    have h3 : 0 ≤ q * N ^ (-D) := mul_nonneg hqnn (Real.rpow_nonneg hNnn _)
    linarith
  have hqinv : q⁻¹ ≤ N⁻¹ := (inv_le_inv₀ hqpos hNpos).mpr hNq
  rcases le_total (q * N ^ (-D)) N⁻¹ with hcase | hcase
  · -- ## case 1: the term `q·N^{-D}` is dominated by `N⁻¹`
    have hXle : X ≤ 3 * N⁻¹ := by
      rw [hX]
      linarith
    have hstep1 : X ^ A ≤ (3 * N⁻¹) ^ A := Real.rpow_le_rpow hXnn hXle hA0.le
    have hstep2 : (3 * N⁻¹) ^ A = 3 ^ A * N ^ (-A) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) (inv_nonneg.mpr hNnn),
        Real.inv_rpow hNnn A, ← Real.rpow_neg hNpos.le A]
    have hpow1 : N ^ (1 + A / 4) * N ^ (-A) = N ^ (1 - 3 * A / 4) := by
      rw [← Real.rpow_add hNpos]
      congr 1
      ring
    have hb : N ^ (1 - 3 * A / 4) ≤ q ^ (1 - 3 * A / 8) :=
      weylBracket_rpow_le hN hNq (by linarith) (by linarith)
    calc N ^ (1 + A / 4) * X ^ A
        ≤ N ^ (1 + A / 4) * (3 ^ A * N ^ (-A)) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hNnn _)
          rw [← hstep2]
          exact hstep1
      _ = 3 ^ A * (N ^ (1 + A / 4) * N ^ (-A)) := by ac_rfl
      _ = 3 ^ A * N ^ (1 - 3 * A / 4) := by rw [hpow1]
      _ ≤ 3 * q ^ (1 - 3 * A / 8) :=
          mul_le_mul h3A hb (Real.rpow_nonneg hNnn _) (by norm_num)
  · -- ## case 2: the term `q·N^{-D}` dominates `N⁻¹`
    have hbracketnn : 0 ≤ q * N ^ (-D) := mul_nonneg hqnn (Real.rpow_nonneg hNnn _)
    have hXle : X ≤ 3 * (q * N ^ (-D)) := by
      rw [hX]
      linarith
    have hstep1 : X ^ A ≤ (3 * (q * N ^ (-D))) ^ A := Real.rpow_le_rpow hXnn hXle hA0.le
    have hstep2 : (3 * (q * N ^ (-D))) ^ A = 3 ^ A * q ^ A * N ^ (-(D * A)) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) hbracketnn,
        Real.mul_rpow hqnn (Real.rpow_nonneg hNnn _), Real.rpow_neg hNpos.le D,
        Real.inv_rpow (Real.rpow_nonneg hNnn D) A, ← Real.rpow_mul hNpos.le D A,
        ← Real.rpow_neg hNpos.le (D * A)]
      rw [← mul_assoc]
    have hpow2 : N ^ (1 + A / 4) * N ^ (-(D * A)) = N ^ (1 + A / 4 - D * A) := by
      rw [← Real.rpow_add hNpos,
        show (1 + A / 4) + -(D * A) = 1 + A / 4 - D * A by ring]
    have hef : 1 + A / 4 - D * A ≤ 1 - 11 * A / 8 := by
      have h1 : (1 : ℝ) / 4 - D ≤ -11 / 8 := by linarith
      have h2 : A * ((1 : ℝ) / 4 - D) ≤ A * (-11 / 8) := mul_le_mul_of_nonneg_left h1 hA0.le
      nlinarith [h2]
    have hfnn : 0 ≤ 1 - 11 * A / 8 := by linarith
    have hbound : N ^ (1 + A / 4 - D * A) ≤ q ^ (1 - 11 * A / 8) :=
      weylBracket_rpow_le hN hNq hef hfnn
    have hcomb : q ^ A * q ^ (1 - 11 * A / 8) = q ^ (1 - 3 * A / 8) := by
      rw [← Real.rpow_add hqpos]
      congr 1
      ring
    have hfin : 3 ^ A * q ^ A * N ^ (1 + A / 4 - D * A) ≤ 3 * q ^ (1 - 3 * A / 8) := by
      have hstep : 3 ^ A * q ^ A * N ^ (1 + A / 4 - D * A)
          ≤ 3 ^ A * q ^ A * q ^ (1 - 11 * A / 8) :=
        mul_le_mul_of_nonneg_left hbound
          (mul_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _) (Real.rpow_nonneg hqnn _))
      calc 3 ^ A * q ^ A * N ^ (1 + A / 4 - D * A)
          ≤ 3 ^ A * q ^ A * q ^ (1 - 11 * A / 8) := hstep
        _ = 3 ^ A * (q ^ A * q ^ (1 - 11 * A / 8)) := by rw [mul_assoc]
        _ = 3 ^ A * q ^ (1 - 3 * A / 8) := by rw [hcomb]
        _ ≤ 3 * q ^ (1 - 3 * A / 8) :=
            mul_le_mul_of_nonneg_right h3A (Real.rpow_nonneg hqnn _)
    calc N ^ (1 + A / 4) * X ^ A
        ≤ N ^ (1 + A / 4) * (3 ^ A * q ^ A * N ^ (-(D * A))) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hNnn _)
          rw [← hstep2]
          exact hstep1
      _ = 3 ^ A * q ^ A * (N ^ (1 + A / 4) * N ^ (-(D * A))) := by ac_rfl
      _ = 3 ^ A * q ^ A * N ^ (1 + A / 4 - D * A) := by rw [hpow2]
      _ ≤ 3 * q ^ (1 - 3 * A / 8) := hfin

theorem partialSum_weyl_bracket (d : ℕ) (hd : 2 ≤ d) {N q : ℝ} (hN : 1 ≤ N) (hNq : N ≤ q) (hq : 1 ≤ q) :
    N ^ (1 + ((1 : ℝ) / (2 : ℝ) ^ (d - 1)) / 4) *
        (q⁻¹ + N⁻¹ + q * N ^ (-(d : ℝ))) ^ ((1 : ℝ) / (2 : ℝ) ^ (d - 1))
      ≤ 3 * q ^ (1 - 3 * ((1 : ℝ) / (2 : ℝ) ^ (d - 1)) / 8) := by
  -- the exponent `A = 2^{-(d-1)}` lies in `(0, 1/2]` because `d ≥ 2`
  have hd1 : 1 ≤ d - 1 := by omega
  have htwo : (2 : ℝ) ≤ (2 : ℝ) ^ (d - 1) := by
    simpa using pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) hd1
  have hA0 : 0 < (1 : ℝ) / (2 : ℝ) ^ (d - 1) := by positivity
  have hAle : (1 : ℝ) / (2 : ℝ) ^ (d - 1) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (show (0 : ℝ) < 2 by norm_num) htwo
  -- and `D = d ≥ 13/8`
  have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  exact weyl_bracket_core (A := (1 : ℝ) / (2 : ℝ) ^ (d - 1)) (D := (d : ℝ))
    (by linarith) hA0 hAle hN hNq hq

end Work.A3

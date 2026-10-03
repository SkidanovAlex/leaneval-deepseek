/-
# `Submission.Work.FIArea6Hecke.R.axisBadPoly_logDeriv_re_nonpos`

The real-axis logarithmic derivative of the bad-prime correction
`G_d(s) = ∏_{p ∣ 4d} (1 - p^{-s})(1 - χ₄(p) p^{-s})` has non-positive real part on `1 < σ`:

  `-Re(G_d'/G_d)(σ) ≤ 0`.

Each Euler factor `(1 - p^{-σ})(1 - χ₄(p) p^{-σ})` is a positive real number which is
strictly increasing in `σ`, hence its logarithmic derivative is real and positive; the
log-derivative of a finite product is the sum of the logarithmic derivatives.
-/
import Mathlib
import Submission.Work.FIArea6Hecke.R.AxisLogDefs
import Submission.Port.LogDerivCompat

set_option autoImplicit false

namespace Work.FIArea6Hecke.R

open scoped BigOperators

noncomputable section

/-! ## Elementary facts about `χ₄` -/

/-- `χ₄` takes only the values `0`, `1`, `-1`. -/
lemma axisChi4_eq_zero_or_one_or_neg_one (n : ℕ) :
    axisChi4 n = 0 ∨ axisChi4 n = 1 ∨ axisChi4 n = -1 := by
  rw [axisChi4_eq_if]
  split_ifs <;> simp

/-- `χ₄ n` is the coercion of its real part. -/
lemma axisChi4_eq_ofReal_re (n : ℕ) : axisChi4 n = ((axisChi4 n).re : ℂ) := by
  apply Complex.ext <;> simp [axisChi4]

/-! ## The individual Euler factor -/

/-- The second factor `1 - χ₄(p) p^{-σ}` is nonzero for `p > 1` and `σ > 1`. -/
lemma one_sub_axisChi4_mul_cpow_ne_zero {p : ℕ} (hp : 1 < p) {σ : ℝ} (hσ : 1 < σ) :
    (1 : ℂ) - axisChi4 p * (p : ℂ) ^ (-(σ : ℂ)) ≠ 0 := by
  have hp_nat : 0 < p := by omega
  have hppos : (0 : ℝ) < p := by exact_mod_cast hp_nat
  have hrpow_lt : (p : ℝ) ^ (-σ) < 1 := by
    rw [Real.rpow_lt_one_iff_of_pos hppos]
    exact Or.inl ⟨by exact_mod_cast hp, by linarith⟩
  have hnorm : ‖(p : ℂ) ^ (-(σ : ℂ))‖ = (p : ℝ) ^ (-σ) := by
    rw [Complex.norm_natCast_cpow_of_pos hp_nat (-(σ : ℂ)), Complex.neg_re, Complex.ofReal_re]
  rw [sub_ne_zero]
  intro h
  have h1 : ‖axisChi4 p * (p : ℂ) ^ (-(σ : ℂ))‖ = 1 := by rw [← h]; simp
  have hle : ‖axisChi4 p * (p : ℂ) ^ (-(σ : ℂ))‖ ≤ (p : ℝ) ^ (-σ) := by
    rw [norm_mul, hnorm]
    calc ‖axisChi4 p‖ * (p : ℝ) ^ (-σ) ≤ 1 * (p : ℝ) ^ (-σ) :=
          mul_le_mul_of_nonneg_right (axisChi4_norm_le_one p) (Real.rpow_pos_of_pos hppos _).le
      _ = (p : ℝ) ^ (-σ) := one_mul _
  linarith

/-- The Euler factor `(1 - p^{-s})(1 - χ₄(p) p^{-s})` is nonzero at a real point `σ > 1`. -/
lemma axisBadFactor_ne_zero {p : ℕ} (hp : 1 < p) {σ : ℝ} (hσ : 1 < σ) :
    (1 - (p : ℂ) ^ (-(σ : ℂ))) * (1 - axisChi4 p * (p : ℂ) ^ (-(σ : ℂ))) ≠ 0 :=
  mul_ne_zero (by
      rw [sub_ne_zero]
      exact (natCast_cpow_neg_ne_one hp (by rw [Complex.ofReal_re]; exact hσ)).symm)
    (one_sub_axisChi4_mul_cpow_ne_zero hp hσ)

/-- The Euler factor `(1 - p^{-s})(1 - χ₄(p) p^{-s})` is entire (for `p ≠ 0`). -/
lemma axisBadFactor_differentiableAt {p : ℕ} (hp0 : (p : ℂ) ≠ 0) (s : ℂ) :
    DifferentiableAt ℂ (fun s : ℂ => (1 - (p : ℂ) ^ (-s)) * (1 - axisChi4 p * (p : ℂ) ^ (-s))) s := by
  have hdu : DifferentiableAt ℂ (fun s : ℂ => (p : ℂ) ^ (-s)) s :=
    differentiableAt_cpow_neg_of_ne_zero (p : ℂ) hp0 s
  exact ((differentiableAt_const (1 : ℂ)).sub hdu).mul
    ((differentiableAt_const (1 : ℂ)).sub ((differentiableAt_const (axisChi4 p)).mul hdu))

/-- The logarithmic derivative of one Euler factor has non-negative real part on `σ > 1`. -/
lemma axisBadFactor_logDeriv_re_nonneg {p : ℕ} (hp : 1 < p) {σ : ℝ} (hσ : 1 < σ) :
    0 ≤ (logDeriv
        (fun s : ℂ => (1 - (p : ℂ) ^ (-s)) * (1 - axisChi4 p * (p : ℂ) ^ (-s)))
        (σ : ℂ)).re := by
  have hp_nat : 0 < p := by omega
  have hp0ℂ : (p : ℂ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  have hppos : (0 : ℝ) < p := by exact_mod_cast hp_nat
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  set ar : ℝ := (p : ℝ) ^ (-σ) with har
  set χr : ℝ := (axisChi4 p).re with hχr
  set Lp : ℝ := Real.log p with hLp
  have hpow : (p : ℂ) ^ (-(σ : ℂ)) = (ar : ℂ) := by
    have hexp : -(σ : ℂ) = ((-σ : ℝ) : ℂ) := by rw [Complex.ofReal_neg]
    rw [har, hexp, ← Complex.ofReal_natCast p, ← Complex.ofReal_cpow hppos.le (-σ)]
  have hlog : Complex.log (p : ℂ) = (Lp : ℂ) := by
    rw [hLp]
    exact (Complex.ofReal_log hppos.le).symm
  have hχ : axisChi4 p = (χr : ℂ) := by
    rw [hχr]; exact axisChi4_eq_ofReal_re p
  have har_pos : 0 < ar := by rw [har]; exact Real.rpow_pos_of_pos hppos (-σ)
  have har_lt_one : ar < 1 := by
    rw [har, Real.rpow_lt_one_iff_of_pos hppos]
    exact Or.inl ⟨hp1, by linarith⟩
  have hLp_nonneg : 0 ≤ Lp := by rw [hLp]; exact Real.log_nonneg hp1.le
  have hχval : χr = 0 ∨ χr = 1 ∨ χr = -1 := by
    rcases axisChi4_eq_zero_or_one_or_neg_one p with h | h | h
    · exact Or.inl (by simp [hχr, h])
    · exact Or.inr (Or.inl (by simp [hχr, h]))
    · exact Or.inr (Or.inr (by simp [hχr, h]))
  have hdu : DifferentiableAt ℂ (fun s : ℂ => (p : ℂ) ^ (-s)) (σ : ℂ) :=
    differentiableAt_cpow_neg_of_ne_zero (p : ℂ) hp0ℂ (σ : ℂ)
  have hd1 : DifferentiableAt ℂ (fun s : ℂ => 1 - (p : ℂ) ^ (-s)) (σ : ℂ) :=
    (differentiableAt_const (1 : ℂ)).sub hdu
  have hd2 : DifferentiableAt ℂ (fun s : ℂ => 1 - axisChi4 p * (p : ℂ) ^ (-s)) (σ : ℂ) :=
    (differentiableAt_const (1 : ℂ)).sub ((differentiableAt_const (axisChi4 p)).mul hdu)
  have hder_u : deriv (fun s : ℂ => (p : ℂ) ^ (-s)) (σ : ℂ)
      = -(Complex.log (p : ℂ) * (p : ℂ) ^ (-(σ : ℂ))) := by
    rw [Complex.deriv_const_cpow (f := fun s : ℂ => -s) (x := (σ : ℂ)) (by fun_prop) (p : ℂ),
      deriv_neg'']
    ring
  have hder_F1 : deriv (fun s : ℂ => 1 - (p : ℂ) ^ (-s)) (σ : ℂ)
      = Complex.log (p : ℂ) * (p : ℂ) ^ (-(σ : ℂ)) := by
    rw [deriv_const_sub, hder_u]; ring
  have hder_F2 : deriv (fun s : ℂ => 1 - axisChi4 p * (p : ℂ) ^ (-s)) (σ : ℂ)
      = axisChi4 p * (Complex.log (p : ℂ) * (p : ℂ) ^ (-(σ : ℂ))) := by
    rw [deriv_const_sub, deriv_const_mul (axisChi4 p) hdu, hder_u]; ring
  have hne1 : (1 : ℂ) - (p : ℂ) ^ (-(σ : ℂ)) ≠ 0 := by
    rw [sub_ne_zero]
    exact (natCast_cpow_neg_ne_one hp (by rw [Complex.ofReal_re]; exact hσ)).symm
  have hne2 : (1 : ℂ) - axisChi4 p * (p : ℂ) ^ (-(σ : ℂ)) ≠ 0 :=
    one_sub_axisChi4_mul_cpow_ne_zero hp hσ
  have hlogf : logDeriv
        (fun s : ℂ => (1 - (p : ℂ) ^ (-s)) * (1 - axisChi4 p * (p : ℂ) ^ (-s)))
        (σ : ℂ)
      = Complex.log (p : ℂ) * (p : ℂ) ^ (-(σ : ℂ)) / (1 - (p : ℂ) ^ (-(σ : ℂ)))
        + axisChi4 p * (Complex.log (p : ℂ) * (p : ℂ) ^ (-(σ : ℂ)))
            / (1 - axisChi4 p * (p : ℂ) ^ (-(σ : ℂ))) := by
    rw [Submission.Port.logDeriv_mul_fun (σ : ℂ) hne1 hne2 hd1 hd2, logDeriv_apply, logDeriv_apply,
      hder_F1, hder_F2]
  have hE : Complex.log (p : ℂ) * (p : ℂ) ^ (-(σ : ℂ)) / (1 - (p : ℂ) ^ (-(σ : ℂ)))
        + axisChi4 p * (Complex.log (p : ℂ) * (p : ℂ) ^ (-(σ : ℂ)))
            / (1 - axisChi4 p * (p : ℂ) ^ (-(σ : ℂ)))
      = (((Lp * ar) / (1 - ar) + (χr * (Lp * ar)) / (1 - χr * ar) : ℝ) : ℂ) := by
    rw [hlog, hpow, hχ,
      ← Complex.ofReal_mul, ← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_mul,
      ← Complex.ofReal_mul, ← Complex.ofReal_sub, ← Complex.ofReal_div, ← Complex.ofReal_div,
      ← Complex.ofReal_add]
  rw [hlogf, hE, Complex.ofReal_re]
  have hfac : Lp * ar / (1 - ar) + χr * (Lp * ar) / (1 - χr * ar)
      = Lp * ar * (1 / (1 - ar) + χr / (1 - χr * ar)) := by
    rw [div_eq_mul_inv]; ring
  have hbr : 0 ≤ 1 / (1 - ar) + χr / (1 - χr * ar) := by
    have h1m : 0 < 1 - ar := by linarith
    rcases hχval with h0 | h1 | hneg
    · rw [h0]; simp only [zero_mul, zero_div, add_zero]; positivity
    · rw [h1]; simp only [one_mul]; positivity
    · rw [hneg]
      have hEq : 1 / (1 - ar) + (-1) / (1 - (-1) * ar) = 2 * ar / ((1 - ar) * (1 + ar)) := by
        rw [show (1 : ℝ) - (-1) * ar = 1 + ar by ring, neg_div]
        have ha : (1 : ℝ) - ar ≠ 0 := by linarith
        have hb : (1 : ℝ) + ar ≠ 0 := by linarith
        field_simp
        ring
      rw [hEq]
      have h1p : 0 < 1 + ar := by linarith
      exact div_nonneg (by positivity) (mul_nonneg h1m.le h1p.le)
  rw [hfac]
  exact mul_nonneg (mul_nonneg hLp_nonneg har_pos.le) hbr

/-! ## The product -/

theorem axisBadPoly_logDeriv_re_nonpos (d : ℕ) (hd : 1 ≤ d) {σ : ℝ} (hσ : 1 < σ) :
    (-deriv (Work.FIArea6Hecke.R.axisBadPoly d) (σ : ℂ) /
      Work.FIArea6Hecke.R.axisBadPoly d (σ : ℂ)).re ≤ 0 := by
  have hlogprod : logDeriv (axisBadPoly d) (σ : ℂ)
      = ∑ p ∈ (4 * d).primeFactors,
          logDeriv (fun s : ℂ => (1 - (p : ℂ) ^ (-s)) * (1 - axisChi4 p * (p : ℂ) ^ (-s)))
            (σ : ℂ) := by
    have hunfold : axisBadPoly d
        = (fun s : ℂ => ∏ p ∈ (4 * d).primeFactors,
            (1 - (p : ℂ) ^ (-s)) * (1 - axisChi4 p * (p : ℂ) ^ (-s))) := by
      funext s
      rfl
    rw [hunfold]
    exact Submission.Port.logDeriv_prod_fun
      (fun p hp => axisBadFactor_ne_zero (Nat.prime_of_mem_primeFactors hp).one_lt hσ)
      (fun p hp => axisBadFactor_differentiableAt
        (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero) (σ : ℂ))
  have hmain : 0 ≤ (deriv (axisBadPoly d) (σ : ℂ) / axisBadPoly d (σ : ℂ)).re := by
    rw [← logDeriv_apply, hlogprod, Complex.re_sum]
    exact Finset.sum_nonneg fun p hp =>
      axisBadFactor_logDeriv_re_nonneg (Nat.prime_of_mem_primeFactors hp).one_lt hσ
  have hsplit : -deriv (axisBadPoly d) (σ : ℂ) / axisBadPoly d (σ : ℂ)
      = -(deriv (axisBadPoly d) (σ : ℂ) / axisBadPoly d (σ : ℂ)) := by rw [neg_div]
  rw [hsplit, Complex.neg_re]
  exact neg_nonpos.mpr hmain

end

end Work.FIArea6Hecke.R

/-
# `Work.FIArea6Hecke.R.badPolyAlt`

A copy of the local-factor (`𝔭 ∣ 4d`) logarithmic-derivative estimates of
`Submission.Work.FIArea6Hecke.R.PrincipalCharBadPoly`, with **every declaration renamed** by the
suffix `Alt`.

Reason for the copy: `PrincipalCharBadPoly` declares `norm_natCast_cpow_neg`, and
`Submission.Work.FIArea6Hecke.R.baseLowerNegTwo` declares a *different* lemma with the same name.
The two modules therefore **cannot be imported together** ("environment already contains
`Work.FIArea6Hecke.R.norm_natCast_cpow_neg`"), and the target
`Work.FIArea6Hecke.R.heckeLSeries_logDeriv_bound_re_gt_one` needs both chains:

* the exceptional ("Case B") bound for the principal strict character
  (`Work.FIArea6Hecke.R.heckeLSeries_logDeriv_principalCharAux`, in
  `R/logDerivPrincipalCharAlt.lean`, which uses `badPoly_logDeriv_re_le`), and
* the one-sided logarithmic-derivative bound `LogDerivReLower`, whose assembly
  `R/logDerivReLowerCapstone.lean` imports `R/baseLowerNegTwoUniform.lean` and hence
  `R/baseLowerNegTwo.lean`.

Keeping this renamed copy (and using it from `R/logDerivPrincipalCharAlt.lean`) removes the
collision: the closure of the target then contains `baseLowerNegTwo` but no longer
`PrincipalCharBadPoly`.
-/

/-
# `Submission.Work.FIArea6Hecke.R.PrincipalCharBadPoly`

The logarithmic derivative of the bad-prime correction
`badPoly d s = ∏_{p ∣ 4d}(1-p^{-s})(1-χ₄(p)p^{-s})` of `R/PrincipalCharAux.lean` is bounded,
for `re s > 1`, by `2 log(4d)`:

  `Re (G_d'(s)/G_d(s)) ≤ 2 log(4d)`.

This is the elementary finite-Euler-product input of the principal-character bound
`Work.FIArea6Hecke.R.heckeLSeries_logDeriv_principalChar`.  Each of the two factors at a prime `p`
contributes at most `log p/(p^{re s} - 1) ≤ log p`, and `∏_{p ∣ 4d} p ≤ 4d` bounds the total.
-/
import Mathlib
import Submission.Work.FIArea6Hecke.R.PrincipalCharAux
import Submission.Port.LogDerivCompat

set_option autoImplicit false

namespace Work.FIArea6Hecke.R

open scoped BigOperators

noncomputable section

/-! ## Norms of `p^{-s}` and its derivative -/

lemma norm_natCast_cpow_negAlt {p : ℕ} (hp : p ≠ 0) (s : ℂ) :
    ‖(p : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s.re) := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  have hpR : 0 < (p : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hp)
  calc ‖(p : ℂ) ^ (-s)‖ = ‖Complex.exp (Complex.log (p : ℂ) * (-s))‖ := by
        rw [Complex.cpow_def_of_ne_zero hpC]
    _ = ‖Complex.exp (((Real.log (p : ℝ) : ℂ)) * (-s))‖ := by rw [← Complex.natCast_log]
    _ = Real.exp ((((Real.log (p : ℝ) : ℂ)) * (-s)).re) := by rw [Complex.norm_exp]
    _ = Real.exp (Real.log (p : ℝ) * (-s.re)) := by rw [Complex.re_ofReal_mul, Complex.neg_re]
    _ = (p : ℝ) ^ (-s.re) := by rw [Real.rpow_def_of_pos hpR]

lemma norm_natCast_cpow_neg_lt_oneAlt {p : ℕ} (hp : 1 < p) {s : ℂ} (hs : 1 < s.re) :
    ‖(p : ℂ) ^ (-s)‖ < 1 := by
  rw [norm_natCast_cpow_negAlt (by omega)]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp) (by linarith)

lemma hasDerivAt_cpow_neg_natAlt {p : ℕ} (hp : p ≠ 0) (w : ℂ) :
    HasDerivAt (fun z : ℂ => (p : ℂ) ^ (-z))
      (-(((Real.log (p : ℝ)) : ℂ) * ((p : ℂ) ^ (-w)))) w := by
  have hc : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  have hlog : Complex.log ((p : ℂ)) = ((Real.log (p : ℝ) : ℂ)) := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_log (Nat.cast_nonneg _)]
  have h := (hasDerivAt_neg w).const_cpow (Or.inl hc)
  rw [hlog] at h
  convert h using 1
  ring

/-! ## A geometric-series estimate -/

lemma div_norm_one_sub_leAlt {z : ℂ} {q : ℝ} (hz : ‖z‖ ≤ q⁻¹) (hq : 1 < q) :
    ‖z‖ / ‖1 - z‖ ≤ (q - 1)⁻¹ := by
  have hqz : ‖z‖ < 1 := lt_of_le_of_lt hz (inv_lt_one_of_one_lt₀ hq)
  have hden : 1 - ‖z‖ ≤ ‖1 - z‖ := by
    have h := abs_norm_sub_norm_le (1 : ℂ) z
    rw [norm_one] at h
    exact le_trans (le_abs_self _) h
  have hdenpos : 0 < 1 - ‖z‖ := by linarith
  have h1 : ‖z‖ / ‖1 - z‖ ≤ ‖z‖ / (1 - ‖z‖) :=
    div_le_div_of_nonneg_left (norm_nonneg z) hdenpos hden
  have h3 : q⁻¹ / (1 - q⁻¹) = (q - 1)⁻¹ := by
    have hq0 : q ≠ 0 := by linarith
    have hq1 : q - 1 ≠ 0 := by linarith
    field_simp
  have h2 : ‖z‖ / (1 - ‖z‖) ≤ q⁻¹ / (1 - q⁻¹) := by
    rw [h3, div_le_iff₀ hdenpos]
    rw [show (q - 1)⁻¹ * (1 - ‖z‖) = (1 - ‖z‖) / (q - 1) by ring]
    rw [le_div_iff₀ (by linarith : (0:ℝ) < q - 1)]
    have hzq : ‖z‖ * q ≤ 1 := by
      calc ‖z‖ * q ≤ q⁻¹ * q := mul_le_mul_of_nonneg_right hz (by linarith)
        _ = 1 := by field_simp
    nlinarith [hzq, norm_nonneg z, hqz]
  linarith [h1, h2]

lemma norm_mul_div_one_sub_leAlt {z : ℂ} {q A : ℝ} (hz : ‖z‖ ≤ q⁻¹) (hq : 1 < q) (hA0 : 0 ≤ A) :
    ‖(A : ℂ) * z / (1 - z)‖ ≤ A * (q - 1)⁻¹ := by
  have hqz : ‖z‖ < 1 := lt_of_le_of_lt hz (inv_lt_one_of_one_lt₀ hq)
  have hne : (1 : ℂ) - z ≠ 0 := by
    intro h
    have : z = 1 := by linear_combination -h
    rw [this] at hqz
    simp at hqz
  rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hA0]
  rw [mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (div_norm_one_sub_leAlt hz hq) hA0

/-! ## The two local factors -/

lemma norm_logDeriv_one_sub_cpow_neg_leAlt {p : ℕ} (hp : 1 < p) {s : ℂ} (hs : 1 < s.re) :
    ‖deriv (fun s : ℂ => 1 - (p : ℂ) ^ (-s)) s / (1 - (p : ℂ) ^ (-s))‖
      ≤ Real.log p * (((p : ℝ) ^ s.re) - 1)⁻¹ := by
  have hp0 : p ≠ 0 := by omega
  have hlog0 : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp.le)
  have hderiv : deriv (fun s : ℂ => 1 - (p : ℂ) ^ (-s)) s
      = ((Real.log (p : ℝ)) : ℂ) * ((p : ℂ) ^ (-s)) := by
    have h := (hasDerivAt_const s (1 : ℂ)).sub (hasDerivAt_cpow_neg_natAlt hp0 s)
    exact h.deriv.trans (by ring)
  rw [hderiv]
  refine norm_mul_div_one_sub_leAlt ?_ ?_ hlog0
  · rw [norm_natCast_cpow_negAlt hp0, Real.rpow_neg (by positivity)]
  · exact Real.one_lt_rpow (by exact_mod_cast hp) (by linarith)

lemma norm_logDeriv_one_sub_chi4_mul_cpow_neg_leAlt {p : ℕ} (hp : 1 < p) {s : ℂ} (hs : 1 < s.re) :
    ‖deriv (fun s : ℂ => 1 - chi4fun p * (p : ℂ) ^ (-s)) s /
        (1 - chi4fun p * (p : ℂ) ^ (-s))‖
      ≤ Real.log p * (((p : ℝ) ^ s.re) - 1)⁻¹ := by
  have hp0 : p ≠ 0 := by omega
  have hlog0 : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp.le)
  have hderiv : deriv (fun s : ℂ => 1 - chi4fun p * (p : ℂ) ^ (-s)) s
      = ((Real.log (p : ℝ)) : ℂ) * (chi4fun p * (p : ℂ) ^ (-s)) := by
    have h := (hasDerivAt_const s (1 : ℂ)).sub
      ((hasDerivAt_cpow_neg_natAlt hp0 s).const_mul (chi4fun p))
    exact h.deriv.trans (by ring)
  rw [hderiv]
  refine norm_mul_div_one_sub_leAlt ?_ ?_ hlog0
  · rw [norm_mul]
    calc ‖chi4fun p‖ * ‖(p : ℂ) ^ (-s)‖ ≤ 1 * ((p : ℝ) ^ s.re)⁻¹ := by
          refine mul_le_mul (chi4fun_norm_le_one p) ?_ (norm_nonneg _) (by norm_num)
          rw [norm_natCast_cpow_negAlt hp0, Real.rpow_neg (by positivity)]
      _ = ((p : ℝ) ^ s.re)⁻¹ := one_mul _
  · exact Real.one_lt_rpow (by exact_mod_cast hp) (by linarith)

/-! ## Non-vanishing and the log-derivative identity -/

lemma one_sub_cpow_neg_ne_zeroAlt {p : ℕ} (hp : 1 < p) {s : ℂ} (hs : 1 < s.re) :
    (1 : ℂ) - (p : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have h1 : (p : ℂ) ^ (-s) = 1 := by linear_combination -h
  have h2 := norm_natCast_cpow_neg_lt_oneAlt hp hs
  rw [h1] at h2; simp at h2

lemma one_sub_chi4_mul_cpow_neg_ne_zeroAlt {p : ℕ} (hp : 1 < p) {s : ℂ} (hs : 1 < s.re) :
    (1 : ℂ) - chi4fun p * (p : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have h1 : chi4fun p * (p : ℂ) ^ (-s) = 1 := by linear_combination -h
  have h2 : ‖chi4fun p * (p : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_mul]
    calc ‖chi4fun p‖ * ‖(p : ℂ) ^ (-s)‖ ≤ 1 * ‖(p : ℂ) ^ (-s)‖ :=
          mul_le_mul_of_nonneg_right (chi4fun_norm_le_one p) (norm_nonneg _)
      _ = ‖(p : ℂ) ^ (-s)‖ := one_mul _
      _ < 1 := norm_natCast_cpow_neg_lt_oneAlt hp hs
  rw [h1] at h2; simp at h2

lemma badPoly_ne_zeroAlt {d : ℕ} (hd : 1 ≤ d) {s : ℂ} (hs : 1 < s.re) : badPoly d s ≠ 0 := by
  rw [badPoly]
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact mul_ne_zero (one_sub_cpow_neg_ne_zeroAlt (Nat.prime_of_mem_primeFactors hp).one_lt hs)
    (one_sub_chi4_mul_cpow_neg_ne_zeroAlt (Nat.prime_of_mem_primeFactors hp).one_lt hs)

lemma badPoly_logDeriv_eq_sumAlt {d : ℕ} {s : ℂ} (hs : 1 < s.re) :
    logDeriv (badPoly d) s
      = ∑ p ∈ (4 * d).primeFactors,
          (logDeriv (fun s : ℂ => 1 - (p : ℂ) ^ (-s)) s
            + logDeriv (fun s : ℂ => 1 - chi4fun p * (p : ℂ) ^ (-s)) s) := by
  rw [show badPoly d = (fun s : ℂ => ∏ p ∈ (4 * d).primeFactors,
        ((1 - (p : ℂ) ^ (-s)) * (1 - chi4fun p * (p : ℂ) ^ (-s)))) from rfl]
  rw [Submission.Port.logDeriv_prod_fun]
  · refine Finset.sum_congr rfl (fun p hp => ?_)
    have hp1 : 1 < p := (Nat.prime_of_mem_primeFactors hp).one_lt
    have hp0 : p ≠ 0 := by omega
    rw [Submission.Port.logDeriv_mul_fun]
    · exact one_sub_cpow_neg_ne_zeroAlt hp1 hs
    · exact one_sub_chi4_mul_cpow_neg_ne_zeroAlt hp1 hs
    · exact ((hasDerivAt_const s (1 : ℂ)).sub (hasDerivAt_cpow_neg_natAlt hp0 s)).differentiableAt
    · exact ((hasDerivAt_const s (1 : ℂ)).sub
        ((hasDerivAt_cpow_neg_natAlt hp0 s).const_mul (chi4fun p))).differentiableAt
  · intro p hp
    exact mul_ne_zero (one_sub_cpow_neg_ne_zeroAlt (Nat.prime_of_mem_primeFactors hp).one_lt hs)
      (one_sub_chi4_mul_cpow_neg_ne_zeroAlt (Nat.prime_of_mem_primeFactors hp).one_lt hs)
  · intro p hp
    have hp0 : p ≠ 0 := (Nat.prime_of_mem_primeFactors hp).ne_zero
    exact ((hasDerivAt_const s (1 : ℂ)).sub (hasDerivAt_cpow_neg_natAlt hp0 s)).differentiableAt.mul
      (((hasDerivAt_const s (1 : ℂ)).sub
        ((hasDerivAt_cpow_neg_natAlt hp0 s).const_mul (chi4fun p))).differentiableAt)

/-- `Re (G_d'/G_d)(s) ≤ 2 log(4d)` for `re s > 1`. -/
theorem badPoly_logDeriv_re_leAlt {d : ℕ} (hd : 1 ≤ d) {s : ℂ} (hs : 1 < s.re) :
    (logDeriv (badPoly d) s).re ≤ 2 * Real.log (4 * d) := by
  rw [badPoly_logDeriv_eq_sumAlt hs]
  refine le_trans (Complex.re_le_norm _) ?_
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ p ∈ (4 * d).primeFactors,
      ‖logDeriv (fun s : ℂ => 1 - (p : ℂ) ^ (-s)) s
        + logDeriv (fun s : ℂ => 1 - chi4fun p * (p : ℂ) ^ (-s)) s‖
      ≤ 2 * Real.log (p : ℝ) := by
    intro p hp
    have hp' : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hp1 : 1 < p := hp'.one_lt
    have hp2R : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp'.two_le
    have hσ1 : (1 : ℝ) ≤ s.re := le_of_lt hs
    have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp1.le)
    have hge : (p : ℝ) - 1 ≤ (p : ℝ) ^ s.re - 1 := by
      have h := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp1.le : (1:ℝ) ≤ (p:ℝ)) hσ1
      rw [Real.rpow_one] at h
      linarith
    have hposp : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have hinv : (((p : ℝ) ^ s.re) - 1)⁻¹ ≤ (((p : ℝ)) - 1)⁻¹ :=
      inv_anti₀ hposp hge
    have hinv1 : (((p : ℝ)) - 1)⁻¹ ≤ 1 := by
      apply inv_le_one_of_one_le₀
      linarith
    calc ‖logDeriv (fun s : ℂ => 1 - (p : ℂ) ^ (-s)) s
            + logDeriv (fun s : ℂ => 1 - chi4fun p * (p : ℂ) ^ (-s)) s‖
        ≤ ‖logDeriv (fun s : ℂ => 1 - (p : ℂ) ^ (-s)) s‖
            + ‖logDeriv (fun s : ℂ => 1 - chi4fun p * (p : ℂ) ^ (-s)) s‖ := norm_add_le _ _
      _ ≤ Real.log (p : ℝ) * (((p : ℝ) ^ s.re) - 1)⁻¹
            + Real.log (p : ℝ) * (((p : ℝ) ^ s.re) - 1)⁻¹ :=
          add_le_add (norm_logDeriv_one_sub_cpow_neg_leAlt hp1 hs)
            (norm_logDeriv_one_sub_chi4_mul_cpow_neg_leAlt hp1 hs)
      _ = 2 * Real.log (p : ℝ) * (((p : ℝ) ^ s.re) - 1)⁻¹ := by ring
      _ ≤ 2 * Real.log (p : ℝ) * (((p : ℝ)) - 1)⁻¹ :=
          mul_le_mul_of_nonneg_left hinv (by positivity)
      _ ≤ 2 * Real.log (p : ℝ) := by
          have h2p : 0 ≤ 2 * Real.log (p : ℝ) := by linarith
          calc 2 * Real.log (p : ℝ) * (((p : ℝ)) - 1)⁻¹ ≤ 2 * Real.log (p : ℝ) * 1 :=
                mul_le_mul_of_nonneg_left hinv1 h2p
            _ = 2 * Real.log (p : ℝ) := by ring
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  have hlogprod : Real.log (∏ p ∈ (4 * d).primeFactors, (p : ℝ))
      = ∑ p ∈ (4 * d).primeFactors, Real.log (p : ℝ) :=
    Real.log_prod (fun p hp => by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero)
  rw [← hlogprod]
  have hprodpos : (0 : ℝ) < ∏ p ∈ (4 * d).primeFactors, (p : ℝ) := by
    apply Finset.prod_pos
    intro p hp
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
  have hprodle : ∏ p ∈ (4 * d).primeFactors, (p : ℝ) ≤ 4 * (d : ℝ) := by
    have hdiv : ∏ p ∈ (4 * d).primeFactors, p ∣ 4 * d := Nat.prod_primeFactors_dvd _
    have hle : ∏ p ∈ (4 * d).primeFactors, p ≤ 4 * d := Nat.le_of_dvd (by omega) hdiv
    calc ∏ p ∈ (4 * d).primeFactors, (p : ℝ) = ((∏ p ∈ (4 * d).primeFactors, p : ℕ) : ℝ) := by
          push_cast; rfl
      _ ≤ ((4 * d : ℕ) : ℝ) := by exact_mod_cast hle
      _ = 4 * (d : ℝ) := by push_cast; ring
  exact mul_le_mul_of_nonneg_left (Real.log_le_log hprodpos hprodle) (by norm_num)


/-! ## Differentiability, and the elementary arithmetic final step -/

lemma LSeries_chi4fun_differentiableAtAlt {s : ℂ} (hs : 1 < s.re) :
    DifferentiableAt ℂ (LSeries chi4fun) s := by
  have hle : LSeries.abscissaOfAbsConv chi4fun ≤ (1 : EReal) :=
    LSeries.abscissaOfAbsConv_le_of_le_const ⟨1, fun n _ => chi4fun_norm_le_one n⟩
  have hlt : (1 : EReal) < (s.re : EReal) := EReal.coe_lt_coe_iff.mpr hs
  exact (LSeries_hasDerivAt (lt_of_le_of_lt hle hlt)).differentiableAt

lemma differentiableAt_badPolyAlt (d : ℕ) (s : ℂ) : DifferentiableAt ℂ (badPoly d) s := by
  have hfun : badPoly d = (∏ p ∈ (4 * d).primeFactors,
      fun w : ℂ => (1 - (p : ℂ) ^ (-w)) * (1 - chi4fun p * (p : ℂ) ^ (-w))) := by
    ext w
    simp only [badPoly, Finset.prod_apply]
  rw [hfun]
  refine DifferentiableAt.finsetProd (u := (4 * d).primeFactors)
    (f := fun p => fun w : ℂ => (1 - (p : ℂ) ^ (-w)) * (1 - chi4fun p * (p : ℂ) ^ (-w))) ?_
  intro p hp
  have hp0 : p ≠ 0 := (Nat.prime_of_mem_primeFactors hp).ne_zero
  exact (((hasDerivAt_const s (1 : ℂ)).sub (hasDerivAt_cpow_neg_natAlt hp0 s)).differentiableAt).mul
    (((hasDerivAt_const s (1 : ℂ)).sub
      ((hasDerivAt_cpow_neg_natAlt hp0 s).const_mul (chi4fun p))).differentiableAt)

/-- `2 log(4d) ≤ (2 log 4 + 2) d (log(|t|+3))²` for `d ≥ 1`. -/
lemma two_log_four_mul_d_leAlt {d : ℕ} (hd : 1 ≤ d) {t : ℝ} :
    2 * Real.log (4 * d) ≤ (2 * Real.log 4 + 2) * (d : ℝ) * (Real.log (|t| + 3)) ^ 2 := by
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < (d : ℝ) := by linarith
  have hM : (1 : ℝ) ≤ Real.log (|t| + 3) := by
    have h3 : Real.exp 1 ≤ |t| + 3 := by
      linarith [abs_nonneg t, Real.exp_one_lt_d9]
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log (|t| + 3) := Real.log_le_log (Real.exp_pos 1) h3
  have hM2 : (1 : ℝ) ≤ (Real.log (|t| + 3)) ^ (2 : ℕ) := by nlinarith [hM]
  have hlog4 : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
  have hlogd : Real.log (d : ℝ) ≤ (d : ℝ) := by
    have := Real.log_le_sub_one_of_pos hd0
    linarith
  rw [Real.log_mul (by norm_num) (ne_of_gt hd0)]
  have hlog4b : Real.log 4 ≤ Real.log 4 * (d : ℝ) := by nlinarith [hd1, hlog4]
  have hdlog : (d : ℝ) ≤ (d : ℝ) * (Real.log (|t| + 3)) ^ (2 : ℕ) := by
    nlinarith [hd1, hM2]
  have hlog4d : Real.log 4 * (d : ℝ) ≤ Real.log 4 * (d : ℝ) * (Real.log (|t| + 3)) ^ (2 : ℕ) := by
    nlinarith [hlog4b, hM2, hlog4, hd1]
  nlinarith [hlog4d, hdlog]

end

end Work.FIArea6Hecke.R

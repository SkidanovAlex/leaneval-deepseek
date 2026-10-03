/-
# `FIArea2/R6/BetaFacts6.lean` — the standing facts about a round-6 coefficient

Everything the §9/§10 assemblies need about a `Defs6.IsBetaCoeff6` coefficient and its `Params`:

* `one_le_log_x6`, `A'_pos6`, `theta_le_one6`, `theta_le_quarter6`,
  `two_pi_theta_le_pi_div_two6`, `vartheta_le_one6`, `tau_nonneg6` — the elementary
  `Params` arithmetic;
* `IsBetaCoeff6.norm_le_tau` — `‖β z‖ ≤ Pa.τ` (via `|μ| ≤ 1`, `q,p ≤ 1`, `|γ(n;C)| ≤ τ(n)` and the
  (5.9) cutoff carried in the support);
* `IsBetaCoeff6.gnorm_bounds`, `.isCoprime_star6`, `.delta_ne_zero6`, `.gamOf_bounds6` — the
  polar-box/primitivity facts of the support, and the (6.2) non-vanishing of `Δ`;
* `IsBetaCoeff6.haver_le6` — the (9.2) weight `Haver` against the uniform `sec9Usum` (the
  `Haver_le_uniform` comparison with the polar-box hypotheses discharged);
* `sec9Core6_eq_of` — the §9 pair weight `τ(Δ)³|Δ|⁻¹` on the support;
* `Gsum_zero_zero6` — the `h = 0` Poisson term is the corrected kernel `G0` (the (6.12) count).

This is the companion of `SixDefs` (the §9 objects) and `ExactMain` (the exact main term).
-/
import Mathlib
import Submission.Work.FIArea2.R6.SixDefs
import Submission.Work.FIArea2.Sec6Hzero
import Submission.Work.FITop4.Defs6

set_option autoImplicit false

namespace Work.FIArea2.R6

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. Elementary facts about `Params` -/

/-- `log x ≥ 1` (as `x ≥ 3 > e`). -/
theorem one_le_log_x6 (Pa : Work.FITop.Params) : 1 ≤ Real.log (Pa.x : ℝ) := by
  have hx3 : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
  have h := Real.log_lt_log (Real.exp_pos 1) (lt_of_lt_of_le Real.exp_one_lt_three hx3)
  rw [Real.log_exp] at h
  exact le_of_lt h

/-- The smoothing exponent `A'` of (4.15) is positive. -/
theorem A'_pos6 (Pa : Work.FITop.Params) : 0 < Pa.A' := by
  have h1 : (0 : ℝ) < 2 * Pa.A := by linarith [Pa.hA]
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (20 : ℕ) := by norm_num
  linarith [Pa.hA']

/-- `θ ≤ 1`. -/
theorem theta_le_one6 (Pa : Work.FITop.Params) : Pa.θ ≤ 1 := by
  rw [Pa.hθ]
  exact Real.rpow_le_one_of_one_le_of_nonpos (one_le_log_x6 Pa) (neg_nonpos.mpr (A'_pos6 Pa).le)

/-- `θ ≤ 1/4`, hence `2πθ ≤ π/2`: the polar box (5.14) has angular width at most `π/2`.

`θ = (log x)^{-A'}` with `A' ≥ 2^{20}`; since `log x ≥ log 3 > 1.098`, `(log x)^{A'} ≥ (1.098)^{16} > 4`,
so `θ ≤ 1/4`. -/
theorem theta_le_quarter6 (Pa : Work.FITop.Params) : Pa.θ ≤ 1 / 4 := by
  have hlog1 := one_le_log_x6 Pa
  have hlog9 : ((1098 : ℝ) / 1000) ≤ Real.log (Pa.x : ℝ) := by
    have hx3 : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 3) hx3
    have h9 : ((1098 : ℝ) / 1000) < Real.log 3 := by
      have hnum : ((1098 : ℝ) / 1000) < (10986122885 : ℝ) / 10000000000 := by norm_num
      have hd := Real.log_three_gt_d9
      rw [show (1.0986122885 : ℝ) = (10986122885 : ℝ) / 10000000000 by norm_num] at hd
      exact lt_trans hnum hd
    linarith
  have h16 : (16 : ℝ) ≤ Pa.A' := by
    have h : (2 : ℝ) ^ (20 : ℕ) ≤ Pa.A' := by linarith [Pa.hA', Pa.hA]
    have h2 : (16 : ℝ) ≤ (2 : ℝ) ^ (20 : ℕ) := by norm_num
    linarith
  have hpow : (4 : ℝ) ≤ (Real.log (Pa.x : ℝ)) ^ (16 : ℕ) := by
    calc (4 : ℝ) ≤ ((1098 : ℝ) / 1000) ^ 16 := by norm_num
      _ ≤ (Real.log (Pa.x : ℝ)) ^ (16 : ℕ) := pow_le_pow_left₀ (by norm_num) hlog9 16
  have hlogpos : (0 : ℝ) < Real.log (Pa.x : ℝ) := lt_of_lt_of_le (by norm_num) hlog1
  have hmain : (4 : ℝ) ≤ (Real.log (Pa.x : ℝ)) ^ Pa.A' := by
    calc (4 : ℝ) ≤ (Real.log (Pa.x : ℝ)) ^ (16 : ℕ) := hpow
      _ = (Real.log (Pa.x : ℝ)) ^ ((16 : ℕ) : ℝ) := (Real.rpow_natCast _ _).symm
      _ ≤ (Real.log (Pa.x : ℝ)) ^ Pa.A' := Real.rpow_le_rpow_of_exponent_le hlog1 h16
  rw [Pa.hθ, Real.rpow_neg hlogpos.le]
  have h4 : (0 : ℝ) < 4 := by norm_num
  have hfin := (inv_le_inv₀ (Real.rpow_pos_of_pos hlogpos Pa.A') h4).mpr hmain
  simpa using hfin

/-- `2πθ ≤ π/2` (the angular width of the polar box is at most a right angle). -/
theorem two_pi_theta_le_pi_div_two6 (Pa : Work.FITop.Params) :
    2 * Real.pi * Pa.θ ≤ Real.pi / 2 := by
  have h := theta_le_quarter6 Pa
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  nlinarith [h, hpi]

/-- `ϑ ≤ 1`. -/
theorem vartheta_le_one6 (Pa : Work.FITop.Params) : Pa.ϑ ≤ 1 := by
  rw [Pa.hϑ]
  exact Real.rpow_le_one_of_one_le_of_nonpos (one_le_log_x6 Pa) (neg_nonpos.mpr Pa.hA.le)

/-- `0 ≤ τ` (the (4.11) lower bound). -/
theorem tau_nonneg6 (Pa : Work.FITop.Params) : 0 ≤ Pa.τ := by
  have hlogpos : (0 : ℝ) < Real.log (Pa.x : ℝ) := lt_of_lt_of_le (by norm_num) (one_le_log_x6 Pa)
  have hpos : (0 : ℝ) < (Real.log (Pa.x : ℝ)) ^ (Pa.A + 124) := Real.rpow_pos_of_pos hlogpos _
  linarith [Pa.hτ1]

/-! ## 2. The coefficient facts -/

/-- **`‖β z‖ ≤ Pa.τ`** for a round-6 coefficient: on its support `β z = q·p·μ·γ` with
`|q|,|p|,|μ| ≤ 1`, `|γ(n;C)| ≤ τ(n)` and `τ(|z|²) ≤ Pa.τ` (the (5.9) cutoff). -/
theorem IsBetaCoeff6.norm_le_tau {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ} (h : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) (z : GaussianInt) :
    ‖β z‖ ≤ Pa.τ := by
  obtain ⟨q, p, -, -, hq0, hq1, -, -, hp0, hp1, -, -, hβ⟩ := h
  rw [hβ z]
  split_ifs with hz
  · have hqp : ‖((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hq0 _) (hp0 _))]
      calc q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) ≤ 1 * 1 :=
            mul_le_mul (hq1 _) (hp1 _) (hp0 _) (by norm_num)
        _ = 1 := by ring
    have hmu : ‖(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)‖ ≤ 1 := by
      have h1 := ArithmeticFunction.abs_moebius_le_one (n := Work.FIPlan.gnorm z)
      have h1' : ‖((ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ) : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs, ← Int.cast_abs]
        exact_mod_cast h1
      rwa [Complex.ofReal_intCast] at h1'
    have hg : ‖(Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℂ)‖
        ≤ (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact Work.FITop3.abs_gammaTrunc_le Pa.C (Work.FIPlan.gnorm z)
    calc ‖((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ) : ℂ)
            * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)
            * (Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℂ)‖
        = ‖((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ) : ℂ)‖
            * ‖(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)‖
            * ‖(Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℂ)‖ := by
          rw [norm_mul, norm_mul]
      _ ≤ 1 * 1 * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) :=
          mul_le_mul (mul_le_mul hqp hmu (norm_nonneg _) (by norm_num)) hg (norm_nonneg _)
            (by positivity)
      _ = (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) := by ring
      _ ≤ Pa.τ := hz.2.2.1
  · simp [tau_nonneg6 Pa]

/-- The polar-box bounds of a nonzero coefficient point. -/
theorem IsBetaCoeff6.gnorm_bounds {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ} (h : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) {z : GaussianInt}
    (hz : β z ≠ 0) :
    Pa.N < ((Work.FIPlan.gnorm z : ℕ) : ℝ) ∧
      ((Work.FIPlan.gnorm z : ℕ) : ℝ) ≤ (1 + Pa.θ) * Pa.N := by
  have hb := Work.FITop4.IsBetaCoeff6.support h hz
  exact ⟨hb.2.1, hb.2.2.1⟩

/-- The §9 pair weight on the support: `sec9Core6 Pa z₁ z₂ = τ(Δ)³|Δ|⁻¹`. -/
theorem sec9Core6_eq_of (Pa : Work.FITop.Params) {z1 z2 : GaussianInt}
    (hcop : Work.FIPlan.GaussCoprime z1 z2) (ha1 : Work.FITop4.IsAxisFree Pa z1)
    (ha2 : Work.FITop4.IsAxisFree Pa z2) :
    sec9Core6 Pa z1 z2
      = (((Work.FIPlan.absDelta z1 z2).divisors.card : ℝ) ^ 3
          / (Work.FIPlan.absDelta z1 z2 : ℝ)) := by
  unfold sec9Core6
  rw [if_pos ⟨hcop, ha1, ha2⟩]

/-- The `h = 0` Poisson term (6.10) is the corrected (6.12) count kernel `Work.FITop4.G0`. -/
theorem Gsum_zero_zero6 (z1 z2 : GaussianInt) :
    Work.FIArea2.Gsum z1 z2 0 0 = ((Work.FITop4.G0 z1 z2 : ℝ) : ℂ) := by
  rw [Work.FIArea2.Gsum_zero_zero]
  rfl

end

end Work.FIArea2.R6

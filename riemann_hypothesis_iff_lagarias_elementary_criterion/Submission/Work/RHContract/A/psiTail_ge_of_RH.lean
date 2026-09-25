import Mathlib
import Submission.Work.RHContract.Corpus
import Submission.Work.RHContract.Identity.TailInt.integrableOn_psi_sub_id_mul_kW
import Submission.Work.RHContract.A.zeroSum_tsum_bound
import Submission.Work.RHContract.A.ibp_psi
import Submission.Work.RHContract.A.lin_kernel_identity
import Submission.Work.RHContract.A.deriv_kW_eq

/-!
# `Work.RHContract.A.psiTail_ge_of_RH` — AREA A1 : the lower bound for `J = psiTail` under RH

ROUTE_LEAD §2.2, item **A1**: under RH, for every `x ≥ 1000`,

  `J(x) ≥ −u(x)·c_J(x)`,  `u(x) = 1/(√x log x)`,  `c_J(x) = β(5 + 7/L + 4/L²) + log(2π)/√x + 1/x`,
  `β = 2 + γ − log 4π`,  `L = log x`.

The proof uses the tilted explicit formula `Commons.NumberTheory.Zeta.psiIntegral_tilted_explicit`
for `∫_0^y ψ`, whose zero sum `Z(y) = Σ'_ρ m_ρ y^{ρ+1}/(ρ(ρ+1))` satisfies `‖Z(y)‖ ≤ β·y^{3/2} + 1/y`
under RH (`Work.RHContract.A.zeroSum_tsum_bound`).  Writing `Ψ₁(y) = ∫_0^y ψ − y²/2`, one has
`Ψ₁(y) = −y·log(2π) + c₀ + Σ_n Λ(n)/n² − Re Z(y)` and `Ψ₁' = ψ − id`, so integration by parts
(`Work.RHContract.A.ibp_psi`) gives

  `J(x) = −Ψ₁(x)·k(x) − ∫_x^∞ Ψ₁(t)·k'(t) dt`.

The affine part of `Ψ₁` contributes exactly `−log(2π)/(x log x)` (`lin_kernel_identity`) and the
`Z` part is dominated with `‖Z(t)‖ ≤ β t^{3/2} + 1/t`, which yields the numerical bound.
-/

namespace Work.RHContract.A

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

/-- `β = 2 + γ − log 4π`, the absolutely convergent zero-sum constant. -/
private def beta0 : ℝ := 2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi)

/-- The tilted zero sum `Z(y) = Σ'_ρ m_ρ y^{ρ+1}/(ρ(ρ+1))` of the explicit formula. -/
private def Zsum (y : ℝ) : ℂ :=
  ∑' ρ : ℂ, (Commons.NumberTheory.Zeta.zeta1Order ρ : ℂ) * (y : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1))

/-- The von Mangoldt series `Σ_n Λ(n)/n²` of the explicit formula. -/
private def Vsum : ℂ := ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (n : ℂ) ^ 2

/-- `Ψ₁(y) = ∫_0^y ψ − y²/2`, the antiderivative of `ψ − id`. -/
private def Psi1 (y : ℝ) : ℝ := (∫ t in (0:ℝ)..y, Chebyshev.psi t) - y ^ 2 / 2

/-- The constant `c₀ + Σ_n Λ(n)/n²` of the explicit formula. -/
private def cst : ℝ := Real.log (2 * Real.pi) - 1 + Real.eulerMascheroniConstant + Vsum.re

/-- `hk t = −k'(t) = (2 log²t + 3 log t + 2)/(t³ log³t)`, the positive kernel of the IBP. -/
private def hker (t : ℝ) : ℝ := (2 * (Real.log t) ^ 2 + 3 * Real.log t + 2) / (t ^ 3 * (Real.log t) ^ 3)

/-- `K(x) = 2/log x + 3/log²x + 2/log³x`, the constant in `hker t ≤ K(x)/t³`. -/
private def Kx (x : ℝ) : ℝ := 2 / Real.log x + 3 / (Real.log x) ^ 2 + 2 / (Real.log x) ^ 3

private lemma Zsum_apply (y : ℝ) : Zsum y =
    ∑' ρ : ℂ, (Commons.NumberTheory.Zeta.zeta1Order ρ : ℂ) * (y : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1)) := rfl

private lemma beta0_eq : beta0 = 2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi) := rfl

private lemma hker_eq_deriv {t : ℝ} (ht : 1 < t) :
    deriv Work.RHContract.kW t = -hker t := by
  rw [hker, deriv_kW_eq ht, neg_div]

private lemma Psi1_cont : Continuous Psi1 := by
  have h1 : Continuous fun b : ℝ => ∫ x in (0:ℝ)..b, Chebyshev.psi x :=
    intervalIntegral.continuous_primitive (fun a b => Chebyshev.psi_mono.intervalIntegrable) 0
  unfold Psi1
  exact h1.sub (by fun_prop)

private lemma Psi1_eq (h : RiemannHypothesis) {y : ℝ} (hy : 1 ≤ y) :
    Psi1 y = -y * Real.log (2 * Real.pi) + cst - (Zsum y).re := by
  have h1 := Commons.NumberTheory.Zeta.psiIntegral_tilted_explicit h y hy
  have h2 := congrArg Complex.re h1
  rw [intervalIntegral.integral_ofReal, Complex.ofReal_re] at h2
  have h3 : (y : ℂ) ^ 2 / 2 - (y : ℂ) * ((Real.log (2 * Real.pi) : ℝ) : ℂ)
        + ((Real.log (2 * Real.pi) - 1 + Real.eulerMascheroniConstant : ℝ) : ℂ) + Vsum - Zsum y
      = ((y ^ 2 / 2 - y * Real.log (2 * Real.pi)
          + (Real.log (2 * Real.pi) - 1 + Real.eulerMascheroniConstant) : ℝ) : ℂ) + Vsum - Zsum y := by
    push_cast
    ring
  simp only [Vsum, Zsum] at h3 ⊢
  rw [h3, Complex.sub_re, Complex.add_re, Complex.ofReal_re] at h2
  simp only [Psi1, cst, Vsum, Zsum]
  linarith


/-! ## Basic facts about the positive kernel `hk` -/

private lemma hker_nonneg {t : ℝ} (ht : 1 < t) : 0 ≤ hker t := by
  unfold hker
  have h0 : 0 < Real.log t := Real.log_pos ht
  positivity

private lemma hker_le {x t : ℝ} (hx : 1 < x) (ht : x ≤ t) :
    hker t ≤ (2 / Real.log x + 3 / (Real.log x) ^ 2 + 2 / (Real.log x) ^ 3) / t ^ 3 := by
  have hx0 : 0 < Real.log x := Real.log_pos hx
  have ht1 : 1 < t := lt_of_lt_of_le hx ht
  have ht0 : 0 < t := by linarith
  have hL : Real.log x ≤ Real.log t := Real.log_le_log (by linarith) ht
  have e1 : hker t = (2 / Real.log t + 3 / (Real.log t) ^ 2 + 2 / (Real.log t) ^ 3) / t ^ 3 := by
    unfold hker
    field_simp
  rw [e1, div_le_div_iff_of_pos_right (pow_pos ht0 3)]
  have h1 : 2 / Real.log t ≤ 2 / Real.log x :=
    div_le_div_of_nonneg_left (by norm_num) hx0 hL
  have h2 : 3 / (Real.log t) ^ 2 ≤ 3 / (Real.log x) ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (pow_pos hx0 2) (pow_le_pow_left₀ hx0.le hL 2)
  have h3 : 2 / (Real.log t) ^ 3 ≤ 2 / (Real.log x) ^ 3 :=
    div_le_div_of_nonneg_left (by norm_num) (pow_pos hx0 3) (pow_le_pow_left₀ hx0.le hL 3)
  linarith

private lemma hker_cont : ContinuousOn hker (Set.Ioi 1) := by
  unfold hker
  have hlog : ContinuousOn (fun t : ℝ => Real.log t) (Set.Ioi (1:ℝ)) :=
    Real.continuousOn_log.mono (fun t ht => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact ne_of_gt (lt_trans one_pos (Set.mem_Ioi.mp ht)))
  apply ContinuousOn.div
  · exact ((continuousOn_const.mul (hlog.pow 2)).add (continuousOn_const.mul hlog)).add
      continuousOn_const
  · exact (continuousOn_id.pow 3).mul (hlog.pow 3)
  · intro t ht
    have ht1 : 1 < t := ht
    have ht0 : t ≠ 0 := by linarith
    have hl : Real.log t ≠ 0 := (Real.log_pos ht1).ne'
    exact mul_ne_zero (pow_ne_zero 3 ht0) (pow_ne_zero 3 hl)

private lemma rpow_neg_natCast_inv (t : ℝ) (n : ℕ) (ht : 0 < t) :
    t ^ (-(n : ℝ)) = (t ^ n)⁻¹ := by
  rw [Real.rpow_neg ht.le (n : ℝ), Real.rpow_natCast]

private lemma rpow_three_halves {t : ℝ} (ht : 0 < t) : t ^ (3 / 2 : ℝ) = t * Real.sqrt t := by
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add ht, Real.rpow_one,
    Real.sqrt_eq_rpow]

/-- The zero-sum bound of `Work.RHContract.A.zeroSum_tsum_bound` in `rpow` form. -/
private lemma Zsum_bound (h : RiemannHypothesis) {t : ℝ} (ht : 2 ≤ t) :
    ‖Zsum t‖ ≤ beta0 * t ^ (3 / 2 : ℝ) + 1 / t := by
  have ht0 : 0 < t := by linarith
  have h1 := zeroSum_tsum_bound h t ht
  have h1' : ‖∑' ρ : ℂ, (Commons.NumberTheory.Zeta.zeta1Order ρ : ℂ) * (t : ℂ) ^ (ρ + 1)
        / (ρ * (ρ + 1))‖
      ≤ (2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) * t ^ (3 / 2 : ℝ) + 1 / t := by
    rwa [← rpow_three_halves ht0] at h1
  rw [Zsum_apply]
  exact h1'

/-! ## Integrability of `Ψ₁ · k'` on `(x, ∞)` -/

private lemma integrableOn_const_div_pow (x : ℝ) (hx : 0 < x) (n : ℕ) (hn : 1 < n) (C : ℝ) :
    IntegrableOn (fun t : ℝ => C / t ^ n) (Set.Ioi x) := by
  have hr : (-(n : ℝ)) < -1 := by
    have : (1 : ℝ) < n := by exact_mod_cast hn
    linarith
  have h : IntegrableOn (fun t : ℝ => t ^ (-(n : ℝ))) (Set.Ioi x) :=
    integrableOn_Ioi_rpow_of_lt hr hx
  have h2 : IntegrableOn (fun t : ℝ => (t ^ n)⁻¹) (Set.Ioi x) :=
    h.congr_fun (fun t ht => by
      have ht0 : 0 < t := lt_trans hx ht
      show t ^ (-(n : ℝ)) = (t ^ n)⁻¹
      rw [Real.rpow_neg ht0.le (n : ℝ), Real.rpow_natCast]) measurableSet_Ioi
  exact Integrable.const_mul h2 C

private lemma integrableOn_const_mul_rpow_div_cube (x : ℝ) (hx : 0 < x) (C : ℝ) :
    IntegrableOn (fun t : ℝ => C * (t ^ (3 / 2 : ℝ) / t ^ 3)) (Set.Ioi x) := by
  have h : IntegrableOn (fun t : ℝ => t ^ (-(3 / 2 : ℝ))) (Set.Ioi x) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hx
  have h2 : IntegrableOn (fun t : ℝ => t ^ (3 / 2 : ℝ) / t ^ 3) (Set.Ioi x) :=
    h.congr_fun (fun t ht => by
      have ht0 : 0 < t := lt_trans hx ht
      show t ^ (-(3 / 2 : ℝ)) = t ^ (3 / 2 : ℝ) / t ^ 3
      rw [← Real.rpow_ofNat t 3, ← Real.rpow_sub ht0 (3 / 2) 3]
      norm_num) measurableSet_Ioi
  exact h2.const_mul C

private lemma integrableOn_Psi1_mul_deriv_kW (h : RiemannHypothesis) {x : ℝ} (hx : 2 ≤ x) :
    IntegrableOn (fun t : ℝ => Psi1 t * deriv Work.RHContract.kW t) (Set.Ioi x) := by
  have hx1 : (1 : ℝ) < x := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  set K : ℝ := 2 / Real.log x + 3 / (Real.log x) ^ 2 + 2 / (Real.log x) ^ 3 with hK
  have hA0 : 0 ≤ Real.log (2 * Real.pi) :=
    Real.log_nonneg (by nlinarith [Real.pi_gt_three])
  have hβ0 : 0 ≤ beta0 := by
    rw [beta0]
    exact Commons.NumberTheory.Zeta.psiBeta_nonneg_of_rh h
  have hDint : IntegrableOn (fun t : ℝ => (Real.log (2 * Real.pi) * K) / t ^ 2
      + (|cst| * K) / t ^ 3 + (beta0 * K) * (t ^ (3 / 2 : ℝ) / t ^ 3) + K / t ^ 4)
      (Set.Ioi x) := by
    refine IntegrableOn.add (IntegrableOn.add (IntegrableOn.add ?_ ?_) ?_) ?_
    · exact integrableOn_const_div_pow x hx0 2 (by norm_num) _
    · exact integrableOn_const_div_pow x hx0 3 (by norm_num) _
    · exact integrableOn_const_mul_rpow_div_cube x hx0 _
    · exact integrableOn_const_div_pow x hx0 4 (by norm_num) _
  have key : ∀ t : ℝ, 0 < t →
      (Real.log (2 * Real.pi) * t + |cst| + beta0 * t ^ (3 / 2 : ℝ) + 1 / t) * (K / t ^ 3)
        = (Real.log (2 * Real.pi) * K) / t ^ 2 + (|cst| * K) / t ^ 3
          + (beta0 * K) * (t ^ (3 / 2 : ℝ) / t ^ 3) + K / t ^ 4 := by
    intro t ht0
    field_simp
  refine Integrable.mono' hDint ?_ ?_
  · refine (aestronglyMeasurable_congr ?_).mpr
      ((Psi1_cont.continuousOn.mul (hker_cont.mono (fun t ht => by
        simp only [Set.mem_Ioi] at ht ⊢; linarith)).neg).aestronglyMeasurable measurableSet_Ioi)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht1 : 1 < t := lt_of_lt_of_le hx1 (Set.mem_Ioi.mp ht).le
    show Psi1 t * deriv Work.RHContract.kW t = Psi1 t * (-hker t)
    rw [hker_eq_deriv ht1]
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htx : x < t := Set.mem_Ioi.mp ht
    have ht1 : 1 < t := lt_of_lt_of_le hx1 htx.le
    have ht2 : 2 ≤ t := le_trans hx htx.le
    have ht0 : 0 < t := by linarith
    have hZt : ‖Zsum t‖ ≤ beta0 * t ^ (3 / 2 : ℝ) + 1 / t := Zsum_bound h ht2
    have hZre : |(Zsum t).re| ≤ beta0 * t ^ (3 / 2 : ℝ) + 1 / t :=
      le_trans (Complex.abs_re_le_norm _) hZt
    have hPsi : |Psi1 t| ≤ Real.log (2 * Real.pi) * t + |cst| + |(Zsum t).re| := by
      have h1 := Psi1_eq h (le_of_lt ht1)
      have harg : -t * Real.log (2 * Real.pi) + cst - (Zsum t).re
          = -Real.log (2 * Real.pi) * t + cst - (Zsum t).re := by ring
      calc |Psi1 t| = |-Real.log (2 * Real.pi) * t + cst - (Zsum t).re| := by rw [h1, harg]
        _ ≤ |-Real.log (2 * Real.pi) * t + cst| + |(Zsum t).re| := by
            simpa using abs_sub_le (-Real.log (2 * Real.pi) * t + cst) 0 (Zsum t).re
        _ ≤ (|-Real.log (2 * Real.pi) * t| + |cst|) + |(Zsum t).re| :=
            add_le_add (abs_add_le _ _) le_rfl
        _ = Real.log (2 * Real.pi) * t + |cst| + |(Zsum t).re| := by
            rw [abs_mul, abs_neg, abs_of_nonneg hA0, abs_of_nonneg ht0.le]
    have hker0 : 0 ≤ hker t := hker_nonneg ht1
    have hkerb : hker t ≤ K / t ^ 3 := hker_le hx1 htx.le
    have hmain0 : 0 ≤ Real.log (2 * Real.pi) * t + |cst| + beta0 * t ^ (3 / 2 : ℝ) + 1 / t := by
      have ha : 0 ≤ beta0 * t ^ (3 / 2 : ℝ) := mul_nonneg hβ0 (Real.rpow_nonneg ht0.le _)
      have hb : 0 ≤ Real.log (2 * Real.pi) * t := mul_nonneg hA0 ht0.le
      have hc : 0 ≤ 1 / t := by positivity
      linarith [abs_nonneg cst]
    rw [hker_eq_deriv ht1, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_neg,
      abs_of_nonneg hker0]
    calc |Psi1 t| * hker t
        ≤ (Real.log (2 * Real.pi) * t + |cst| + beta0 * t ^ (3 / 2 : ℝ) + 1 / t) * hker t := by
          apply mul_le_mul_of_nonneg_right _ hker0
          linarith [hZre]
      _ ≤ (Real.log (2 * Real.pi) * t + |cst| + beta0 * t ^ (3 / 2 : ℝ) + 1 / t) * (K / t ^ 3) :=
          mul_le_mul_of_nonneg_left hkerb hmain0
      _ = _ := key t ht0

/-! ## The kernel bounds at infinity -/

private lemma half_le_log_of_two_le {Y : ℝ} (hY : 2 ≤ Y) : 1 / 2 ≤ Real.log Y := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have h : Real.exp (1 / 2 : ℝ) < 2 := by
    rw [show (1 / 2 : ℝ) = (1 : ℝ) / 2 by norm_num, Real.exp_half]
    nlinarith [Real.sq_sqrt (Real.exp_pos 1).le, Real.sqrt_nonneg (Real.exp 1),
      Real.exp_one_lt_d9]
  linarith

private lemma kW_eq (Y : ℝ) :
    Work.RHContract.kW Y = (Real.log Y + 1) / (Y ^ 2 * (Real.log Y) ^ 2) := rfl

private lemma kW_le_six_div_sq {Y : ℝ} (hY : 2 ≤ Y) : Work.RHContract.kW Y ≤ 6 / Y ^ 2 := by
  have hY0 : 0 < Y := by linarith
  have hL : 1 / 2 ≤ Real.log Y := half_le_log_of_two_le hY
  rw [kW_eq]
  have hden : 0 < Y ^ 2 * (Real.log Y) ^ 2 := by positivity
  rw [div_le_div_iff₀ hden (by positivity)]
  have h : Real.log Y + 1 ≤ 6 * (Real.log Y) ^ 2 := by nlinarith [hL]
  calc (Real.log Y + 1) * Y ^ 2 ≤ (6 * (Real.log Y) ^ 2) * Y ^ 2 :=
        mul_le_mul_of_nonneg_right h (by positivity)
    _ = 6 * (Y ^ 2 * (Real.log Y) ^ 2) := by ring

private lemma id_mul_kW_le_six {Y : ℝ} (hY : 2 ≤ Y) : Y * Work.RHContract.kW Y ≤ 6 / Y := by
  have hY0 : 0 < Y := by linarith
  have hL : 1 / 2 ≤ Real.log Y := half_le_log_of_two_le hY
  have e : Y * Work.RHContract.kW Y = (Real.log Y + 1) / (Y * (Real.log Y) ^ 2) := by
    rw [kW_eq]; field_simp
  rw [e, div_le_div_iff₀ (by positivity) hY0]
  have h : Real.log Y + 1 ≤ 6 * (Real.log Y) ^ 2 := by nlinarith [hL]
  calc (Real.log Y + 1) * Y ≤ (6 * (Real.log Y) ^ 2) * Y := mul_le_mul_of_nonneg_right h hY0.le
    _ = 6 * (Y * (Real.log Y) ^ 2) := by ring

private lemma rpow_mul_kW_le_six {Y : ℝ} (hY : 2 ≤ Y) :
    Y ^ (3 / 2 : ℝ) * Work.RHContract.kW Y ≤ 6 / Real.sqrt Y := by
  have hY0 : 0 < Y := by linarith
  have hL : 1 / 2 ≤ Real.log Y := half_le_log_of_two_le hY
  have hL0 : 0 < Real.log Y := by linarith
  have hs0 : 0 < Real.sqrt Y := Real.sqrt_pos.mpr hY0
  have hsq : Real.sqrt Y * Real.sqrt Y = Y := by
    rw [← pow_two]; exact Real.sq_sqrt hY0.le
  have h : Real.log Y + 1 ≤ 6 * (Real.log Y) ^ 2 := by nlinarith [hL]
  have e : Y ^ (3 / 2 : ℝ) * Work.RHContract.kW Y
      = (Real.log Y + 1) * Real.sqrt Y / (Y * (Real.log Y) ^ 2) := by
    rw [kW_eq, rpow_three_halves hY0]
    field_simp
  rw [e, div_le_div_iff₀ (by positivity) hs0]
  nlinarith [hsq, h, hL0, hY0, sq_nonneg (Real.log Y)]

private lemma inv_mul_kW_le_six {Y : ℝ} (hY : 2 ≤ Y) :
    (1 / Y) * Work.RHContract.kW Y ≤ 6 / Y ^ 3 := by
  have hY0 : 0 < Y := by linarith
  have hL : 1 / 2 ≤ Real.log Y := half_le_log_of_two_le hY
  have e : (1 / Y) * Work.RHContract.kW Y
      = (Real.log Y + 1) / (Y ^ 3 * (Real.log Y) ^ 2) := by
    rw [kW_eq]; field_simp
  rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
  have h : Real.log Y + 1 ≤ 6 * (Real.log Y) ^ 2 := by nlinarith [hL]
  calc (Real.log Y + 1) * Y ^ 3 ≤ (6 * (Real.log Y) ^ 2) * Y ^ 3 :=
        mul_le_mul_of_nonneg_right h (by positivity)
    _ = 6 * (Y ^ 3 * (Real.log Y) ^ 2) := by ring

private lemma tendsto_Psi1_mul_kW (h : RiemannHypothesis) :
    Filter.Tendsto (fun Y : ℝ => Psi1 Y * Work.RHContract.kW Y) Filter.atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  set C : ℝ := 6 * (Real.log (2 * Real.pi) + |cst| + beta0 + 1) with hC
  refine squeeze_zero' (g := fun Y : ℝ => C / Real.sqrt Y) ?_ ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with Y hY
    exact norm_nonneg _
  · filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with Y hY
    have hY0 : 0 < Y := by linarith
    have hY1 : 1 < Y := by linarith
    have hs0 : 0 < Real.sqrt Y := Real.sqrt_pos.mpr hY0
    have hYge1 : 1 ≤ Real.sqrt Y := Real.one_le_sqrt.mpr (by linarith)
    have hsq : Real.sqrt Y * Real.sqrt Y = Y := by
      rw [← pow_two]; exact Real.sq_sqrt hY0.le
    have hA0 : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by nlinarith [Real.pi_gt_three])
    have hβ0 : 0 ≤ beta0 := by
      rw [beta0]
      exact Commons.NumberTheory.Zeta.psiBeta_nonneg_of_rh h
    have hZ := Zsum_bound h hY
    have hkw0 : 0 ≤ Work.RHContract.kW Y := by
      have hL : 1 / 2 ≤ Real.log Y := half_le_log_of_two_le hY
      rw [kW_eq]
      exact div_nonneg (by linarith) (by positivity)
    have hPsi : |Psi1 Y| ≤ Real.log (2 * Real.pi) * Y + |cst| + beta0 * Y ^ (3 / 2 : ℝ) + 1 / Y := by
      have h1 := Psi1_eq h (le_of_lt hY1)
      have harg : -Y * Real.log (2 * Real.pi) + cst - (Zsum Y).re
          = -Real.log (2 * Real.pi) * Y + cst - (Zsum Y).re := by ring
      have hZre : |(Zsum Y).re| ≤ beta0 * Y ^ (3 / 2 : ℝ) + 1 / Y :=
        le_trans (Complex.abs_re_le_norm _) hZ
      calc |Psi1 Y| = |-Real.log (2 * Real.pi) * Y + cst - (Zsum Y).re| := by rw [h1, harg]
        _ ≤ |-Real.log (2 * Real.pi) * Y + cst| + |(Zsum Y).re| := by
            simpa using abs_sub_le (-Real.log (2 * Real.pi) * Y + cst) 0 (Zsum Y).re
        _ ≤ (|-Real.log (2 * Real.pi) * Y| + |cst|) + |(Zsum Y).re| :=
            add_le_add (abs_add_le _ _) le_rfl
        _ = Real.log (2 * Real.pi) * Y + |cst| + |(Zsum Y).re| := by
            rw [abs_mul, abs_neg, abs_of_nonneg hA0, abs_of_nonneg hY0.le]
        _ ≤ Real.log (2 * Real.pi) * Y + |cst| + (beta0 * Y ^ (3 / 2 : ℝ) + 1 / Y) := by
            linarith
        _ = Real.log (2 * Real.pi) * Y + |cst| + beta0 * Y ^ (3 / 2 : ℝ) + 1 / Y := by ring
    have hYg1 : 6 / Y ≤ 6 / Real.sqrt Y := by
      rw [div_le_div_iff₀ hY0 hs0]
      nlinarith [hsq, hYge1]
    have hYg2 : 6 / Y ^ 2 ≤ 6 / Real.sqrt Y := by
      rw [div_le_div_iff₀ (by positivity) hs0]
      nlinarith [hsq, hYge1, hY0]
    have hYg3 : 6 / Y ^ 3 ≤ 6 / Real.sqrt Y := by
      rw [div_le_div_iff₀ (by positivity) hs0]
      nlinarith [hsq, hYge1, hY0]
    have step1 : Real.log (2 * Real.pi) * (Y * Work.RHContract.kW Y)
        ≤ Real.log (2 * Real.pi) * (6 / Real.sqrt Y) :=
      mul_le_mul_of_nonneg_left (le_trans (id_mul_kW_le_six hY) hYg1) hA0
    have step2 : |cst| * Work.RHContract.kW Y ≤ |cst| * (6 / Real.sqrt Y) :=
      mul_le_mul_of_nonneg_left (le_trans (kW_le_six_div_sq hY) hYg2) (abs_nonneg cst)
    have step3 : beta0 * (Y ^ (3 / 2 : ℝ) * Work.RHContract.kW Y)
        ≤ beta0 * (6 / Real.sqrt Y) :=
      mul_le_mul_of_nonneg_left (rpow_mul_kW_le_six hY) hβ0
    have step4 : (1 / Y) * Work.RHContract.kW Y ≤ 1 * (6 / Real.sqrt Y) := by
      have h4 := inv_mul_kW_le_six hY
      simp only [one_mul]
      linarith
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hkw0]
    calc |Psi1 Y| * Work.RHContract.kW Y
        ≤ (Real.log (2 * Real.pi) * Y + |cst| + beta0 * Y ^ (3 / 2 : ℝ) + 1 / Y)
            * Work.RHContract.kW Y := mul_le_mul_of_nonneg_right hPsi hkw0
      _ = Real.log (2 * Real.pi) * (Y * Work.RHContract.kW Y) + |cst| * Work.RHContract.kW Y
            + beta0 * (Y ^ (3 / 2 : ℝ) * Work.RHContract.kW Y)
            + (1 / Y) * Work.RHContract.kW Y := by ring
      _ ≤ Real.log (2 * Real.pi) * (6 / Real.sqrt Y) + |cst| * (6 / Real.sqrt Y)
            + beta0 * (6 / Real.sqrt Y) + 1 * (6 / Real.sqrt Y) := by
          linarith [step1, step2, step3, step4]
      _ = C / Real.sqrt Y := by rw [hC]; ring_nf
  · have h : Filter.Tendsto (fun Y : ℝ => C * (Real.sqrt Y)⁻¹) Filter.atTop (nhds 0) := by
      simpa using Real.tendsto_sqrt_atTop.inv_tendsto_atTop.const_mul C
    refine h.congr (fun Y => ?_)
    rw [div_eq_mul_inv]

/-! ## The integral identity for `psiTail` -/

private lemma psiTail_eq (h : RiemannHypothesis) {x : ℝ} (hx : 2 ≤ x) :
    Work.RHContract.psiTail x = -Psi1 x * Work.RHContract.kW x
      - ∫ t in Set.Ioi x, Psi1 t * deriv Work.RHContract.kW t := by
  have hx1 : (1 : ℝ) < x := by linarith
  have hint1 := Work.RHContract.Identity.TailInt.integrableOn_psi_sub_id_mul_kW hx
  have hint2 := integrableOn_Psi1_mul_deriv_kW h hx
  have hlim1 : Filter.Tendsto
      (fun Y : ℝ => ∫ t in x..Y, (Chebyshev.psi t - t) * Work.RHContract.kW t)
      Filter.atTop (nhds (Work.RHContract.psiTail x)) := by
    unfold Work.RHContract.psiTail
    exact MeasureTheory.intervalIntegral_tendsto_integral_Ioi x hint1 Filter.tendsto_id
  have hlim2 : Filter.Tendsto (fun Y : ℝ => ∫ t in x..Y, Psi1 t * deriv Work.RHContract.kW t)
      Filter.atTop (nhds (∫ t in Set.Ioi x, Psi1 t * deriv Work.RHContract.kW t)) :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi x hint2 Filter.tendsto_id
  have hlim3 := tendsto_Psi1_mul_kW h
  have heq : (fun Y : ℝ => ∫ t in x..Y, (Chebyshev.psi t - t) * Work.RHContract.kW t)
      =ᶠ[Filter.atTop] (fun Y : ℝ => Psi1 Y * Work.RHContract.kW Y
        - Psi1 x * Work.RHContract.kW x
        - ∫ t in x..Y, Psi1 t * deriv Work.RHContract.kW t) := by
    filter_upwards [Filter.eventually_ge_atTop x] with Y hY
    exact ibp_psi x Y hx1 hY
  have hlim : Filter.Tendsto (fun Y : ℝ => Psi1 Y * Work.RHContract.kW Y
        - Psi1 x * Work.RHContract.kW x
        - ∫ t in x..Y, Psi1 t * deriv Work.RHContract.kW t) Filter.atTop
      (nhds (0 - Psi1 x * Work.RHContract.kW x
        - ∫ t in Set.Ioi x, Psi1 t * deriv Work.RHContract.kW t)) :=
    (hlim3.sub_const _).sub hlim2
  have hkey := tendsto_nhds_unique hlim1 (hlim.congr' heq.symm)
  linarith [hkey]

/-! ## Integrability of the split pieces -/

/-- `(β t^{3/2} + 1/t)·(K/t³)` in the two-term form used for the integral bounds. -/
private lemma Zbound_mul_eq {K t : ℝ} (ht : 0 < t) :
    (beta0 * t ^ (3 / 2 : ℝ) + 1 / t) * (K / t ^ 3)
      = (beta0 * K) * (t ^ (3 / 2 : ℝ) / t ^ 3) + K / t ^ 4 := by
  field_simp

private lemma integrableOn_mul_hker_of (h : RiemannHypothesis) {x : ℝ} (hx : 2 ≤ x)
    (f g : ℝ → ℝ) (hae : f =ᵐ[volume.restrict (Set.Ioi x)] g)
    (hg : ContinuousOn g (Set.Ioi x))
    (hf : ∀ t : ℝ, 2 ≤ t → |f t| ≤ beta0 * t ^ (3 / 2 : ℝ) + 1 / t) :
    IntegrableOn (fun t : ℝ => f t * hker t) (Set.Ioi x) := by
  have hx1 : (1 : ℝ) < x := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  have hβ0 : 0 ≤ beta0 := by
    rw [beta0]
    exact Commons.NumberTheory.Zeta.psiBeta_nonneg_of_rh h
  have hDint : IntegrableOn
      (fun t : ℝ => (beta0 * Kx x) * (t ^ (3 / 2 : ℝ) / t ^ 3) + Kx x / t ^ 4) (Set.Ioi x) :=
    (integrableOn_const_mul_rpow_div_cube x hx0 (beta0 * Kx x)).add
      (integrableOn_const_div_pow x hx0 4 (by norm_num) (Kx x))
  refine Integrable.mono' hDint ?_ ?_
  · refine (aestronglyMeasurable_congr ?_).mpr
      ((hg.mul (hker_cont.mono (fun t ht => by
        simp only [Set.mem_Ioi] at ht ⊢; linarith))).aestronglyMeasurable measurableSet_Ioi)
    filter_upwards [hae] with t ht
    show f t * hker t = g t * hker t
    rw [ht]
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htx : x < t := Set.mem_Ioi.mp ht
    have ht1 : 1 < t := lt_of_lt_of_le hx1 htx.le
    have ht2 : 2 ≤ t := le_trans hx htx.le
    have ht0 : 0 < t := by linarith
    have hker0 : 0 ≤ hker t := hker_nonneg ht1
    have hkerb : hker t ≤ Kx x / t ^ 3 := by
      have := hker_le hx1 htx.le
      simpa only [Kx] using this
    have hb : |f t| ≤ beta0 * t ^ (3 / 2 : ℝ) + 1 / t := hf t ht2
    have hβt : 0 ≤ beta0 * t ^ (3 / 2 : ℝ) + 1 / t := by
      have h1 : 0 ≤ beta0 * t ^ (3 / 2 : ℝ) := mul_nonneg hβ0 (Real.rpow_nonneg ht0.le _)
      have h2 : 0 ≤ 1 / t := by positivity
      linarith
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hker0]
    calc |f t| * hker t ≤ (beta0 * t ^ (3 / 2 : ℝ) + 1 / t) * hker t :=
          mul_le_mul_of_nonneg_right hb hker0
      _ ≤ (beta0 * t ^ (3 / 2 : ℝ) + 1 / t) * (Kx x / t ^ 3) :=
          mul_le_mul_of_nonneg_left hkerb hβt
      _ = _ := Zbound_mul_eq ht0

private lemma integrableOn_lin_hker {x : ℝ} (hx : 2 ≤ x) :
    IntegrableOn (fun t : ℝ => (-Real.log (2 * Real.pi) * t + cst) * hker t) (Set.Ioi x) := by
  have hx1 : (1 : ℝ) < x := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  have hA0 : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by nlinarith [Real.pi_gt_three])
  have hDint : IntegrableOn
      (fun t : ℝ => Real.log (2 * Real.pi) * Kx x / t ^ 2 + |cst| * Kx x / t ^ 3) (Set.Ioi x) :=
    (integrableOn_const_div_pow x hx0 2 (by norm_num) (Real.log (2 * Real.pi) * Kx x)).add
      (integrableOn_const_div_pow x hx0 3 (by norm_num) (|cst| * Kx x))
  refine Integrable.mono' hDint ?_ ?_
  · have hc : ContinuousOn (fun t : ℝ => -Real.log (2 * Real.pi) * t + cst) (Set.Ioi x) := by
      fun_prop
    exact (hc.mul (hker_cont.mono (fun t ht => by
      simp only [Set.mem_Ioi] at ht ⊢; linarith))).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htx : x < t := Set.mem_Ioi.mp ht
    have ht1 : 1 < t := lt_of_lt_of_le hx1 htx.le
    have ht0 : 0 < t := by linarith
    have hker0 : 0 ≤ hker t := hker_nonneg ht1
    have hkerb : hker t ≤ Kx x / t ^ 3 := by
      have := hker_le hx1 htx.le
      simpa only [Kx] using this
    have hb : |-Real.log (2 * Real.pi) * t + cst| ≤ Real.log (2 * Real.pi) * t + |cst| := by
      calc |-Real.log (2 * Real.pi) * t + cst| ≤ |-Real.log (2 * Real.pi) * t| + |cst| :=
            abs_add_le _ _
        _ = Real.log (2 * Real.pi) * t + |cst| := by
            rw [abs_mul, abs_neg, abs_of_nonneg hA0, abs_of_nonneg ht0.le]
    have h2 : 0 ≤ Real.log (2 * Real.pi) * t + |cst| := by
      have h3 : 0 ≤ Real.log (2 * Real.pi) * t := mul_nonneg hA0 ht0.le
      linarith [abs_nonneg cst]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hker0]
    calc |-Real.log (2 * Real.pi) * t + cst| * hker t
        ≤ (Real.log (2 * Real.pi) * t + |cst|) * hker t := mul_le_mul_of_nonneg_right hb hker0
      _ ≤ (Real.log (2 * Real.pi) * t + |cst|) * (Kx x / t ^ 3) := mul_le_mul_of_nonneg_left hkerb h2
      _ = Real.log (2 * Real.pi) * Kx x / t ^ 2 + |cst| * Kx x / t ^ 3 := by field_simp

private lemma integrableOn_ReZ_hker (h : RiemannHypothesis) {x : ℝ} (hx : 2 ≤ x) :
    IntegrableOn (fun t : ℝ => (Zsum t).re * hker t) (Set.Ioi x) := by
  have hx1 : (1 : ℝ) < x := by linarith
  refine integrableOn_mul_hker_of h hx (fun t => (Zsum t).re)
    (fun t => -Real.log (2 * Real.pi) * t + cst - Psi1 t) ?_ ?_ ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht1 : 1 < t := lt_of_lt_of_le hx1 (Set.mem_Ioi.mp ht).le
    have h1 := Psi1_eq h (le_of_lt ht1)
    linarith [h1]
  · exact (((continuousOn_const.mul continuousOn_id).add continuousOn_const).sub
      Psi1_cont.continuousOn)
  · intro t ht
    exact le_trans (Complex.abs_re_le_norm _) (Zsum_bound h ht)

private lemma integrableOn_Zbound_hker (h : RiemannHypothesis) {x : ℝ} (hx : 2 ≤ x) :
    IntegrableOn (fun t : ℝ => (beta0 * t ^ (3 / 2 : ℝ) + 1 / t) * hker t) (Set.Ioi x) := by
  have hx1 : (1 : ℝ) < x := by linarith
  have hβ0 : 0 ≤ beta0 := by
    rw [beta0]
    exact Commons.NumberTheory.Zeta.psiBeta_nonneg_of_rh h
  refine integrableOn_mul_hker_of h hx (fun t => beta0 * t ^ (3 / 2 : ℝ) + 1 / t)
    (fun t => beta0 * (t * Real.sqrt t) + 1 / t) ?_ ?_ ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := by linarith [Set.mem_Ioi.mp ht, (by linarith : (0:ℝ) < x)]
    rw [rpow_three_halves ht0]
  · exact (continuousOn_const.mul (continuousOn_id.mul Real.continuous_sqrt.continuousOn)).add
      (continuousOn_const.div continuousOn_id (fun t ht => by
        exact ne_of_gt (by linarith [Set.mem_Ioi.mp ht, (by linarith : (0:ℝ) < x)])))
  · intro t ht
    have ht0 : 0 < t := by linarith
    rw [abs_of_nonneg (by
      have h1 : 0 ≤ beta0 * t ^ (3 / 2 : ℝ) := mul_nonneg hβ0 (Real.rpow_nonneg ht0.le _)
      have h2 : 0 ≤ 1 / t := by positivity
      linarith)]

/-! ## The elementary integrals -/

private lemma integral_Ioi_rpow_neg_three_halves (x : ℝ) (hx : 0 < x) :
    ∫ t in Set.Ioi x, t ^ (-(3 / 2 : ℝ)) = 2 / Real.sqrt x := by
  rw [integral_Ioi_rpow_of_lt (by norm_num : (-(3 / 2 : ℝ)) < -1) hx]
  have h1 : x ^ (-(3 / 2 : ℝ) + 1) = (Real.sqrt x)⁻¹ := by
    rw [show (-(3 / 2 : ℝ) + 1) = -(1 / 2 : ℝ) by norm_num, Real.rpow_neg hx.le (1 / 2 : ℝ),
      ← Real.sqrt_eq_rpow]
  rw [h1, show (-(3 / 2 : ℝ) + 1) = -(1 / 2 : ℝ) by norm_num]
  field_simp

private lemma integral_Ioi_rpow_neg_four (x : ℝ) (hx : 0 < x) :
    ∫ t in Set.Ioi x, t ^ (-(4 : ℝ)) = 1 / (3 * x ^ 3) := by
  rw [integral_Ioi_rpow_of_lt (by norm_num : (-(4 : ℝ)) < -1) hx]
  have h1 : x ^ (-(4 : ℝ) + 1) = (x ^ 3)⁻¹ := by
    rw [show (-(4 : ℝ) + 1) = -(3 : ℝ) by norm_num, Real.rpow_neg hx.le (3 : ℝ),
      Real.rpow_ofNat]
  rw [h1, show (-(4 : ℝ) + 1) = -(3 : ℝ) by norm_num]
  field_simp

private lemma integral_Ioi_rpow_div_cube (x : ℝ) (hx : 0 < x) :
    ∫ t in Set.Ioi x, t ^ (3 / 2 : ℝ) / t ^ 3 = 2 / Real.sqrt x := by
  trans ∫ t in Set.Ioi x, t ^ (-(3 / 2 : ℝ))
  · apply MeasureTheory.integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := lt_trans hx ht
    show t ^ (3 / 2 : ℝ) / t ^ 3 = t ^ (-(3 / 2 : ℝ))
    rw [← Real.rpow_ofNat t 3, ← Real.rpow_sub ht0 (3 / 2) 3]
    norm_num
  · exact integral_Ioi_rpow_neg_three_halves x hx

private lemma integral_Ioi_inv_four (x : ℝ) (hx : 0 < x) :
    ∫ t in Set.Ioi x, 1 / t ^ 4 = 1 / (3 * x ^ 3) := by
  trans ∫ t in Set.Ioi x, t ^ (-(4 : ℝ))
  · apply MeasureTheory.integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := lt_trans hx ht
    show 1 / t ^ 4 = t ^ (-(4 : ℝ))
    rw [one_div, ← Real.rpow_ofNat t 4, ← Real.rpow_neg ht0.le (4 : ℝ)]
  · exact integral_Ioi_rpow_neg_four x hx

private lemma integral_Zbound_hker {x : ℝ} (hx : 2 ≤ x) :
    ∫ t in Set.Ioi x, (beta0 * t ^ (3 / 2 : ℝ) + 1 / t) * (Kx x / t ^ 3)
      = Kx x * (beta0 * (2 / Real.sqrt x) + 1 / (3 * x ^ 3)) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hcongr : ∫ t in Set.Ioi x, (beta0 * t ^ (3 / 2 : ℝ) + 1 / t) * (Kx x / t ^ 3)
      = ∫ t in Set.Ioi x, (beta0 * Kx x) * (t ^ (3 / 2 : ℝ) / t ^ 3) + Kx x / t ^ 4 := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := lt_trans hx0 ht
    exact Zbound_mul_eq ht0
  rw [hcongr, MeasureTheory.integral_add
      (integrableOn_const_mul_rpow_div_cube x hx0 (beta0 * Kx x))
      (integrableOn_const_div_pow x hx0 4 (by norm_num) (Kx x))]
  have h2 : ∫ t in Set.Ioi x, Kx x / t ^ 4 = Kx x * (1 / (3 * x ^ 3)) := by
    rw [show (fun t : ℝ => Kx x / t ^ 4) = fun t => Kx x * (1 / t ^ 4) from by funext t; ring,
      MeasureTheory.integral_const_mul, integral_Ioi_inv_four x hx0]
  rw [show (∫ t in Set.Ioi x, beta0 * Kx x * (t ^ (3 / 2 : ℝ) / t ^ 3))
      = (beta0 * Kx x) * (2 / Real.sqrt x) from by
    rw [MeasureTheory.integral_const_mul, integral_Ioi_rpow_div_cube x hx0], h2]
  ring

/-! ## The split identity and the two bounds -/

private lemma psiTail_split (h : RiemannHypothesis) {x : ℝ} (hx : 2 ≤ x) :
    Work.RHContract.psiTail x = -Real.log (2 * Real.pi) / (x * Real.log x)
      + (Zsum x).re * Work.RHContract.kW x - ∫ t in Set.Ioi x, (Zsum t).re * hker t := by
  have hx1 : (1 : ℝ) < x := by linarith
  have hIlin := integrableOn_lin_hker hx
  have hIre := integrableOn_ReZ_hker h hx
  have hIhker : IntegrableOn (fun t : ℝ => Psi1 t * hker t) (Set.Ioi x) := by
    have h1 : (fun t : ℝ => Psi1 t * hker t)
        =ᵐ[volume.restrict (Set.Ioi x)]
          (fun t => (-Real.log (2 * Real.pi) * t + cst) * hker t - (Zsum t).re * hker t) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht1 : 1 < t := lt_of_lt_of_le hx1 (Set.mem_Ioi.mp ht).le
      have h2 := Psi1_eq h (le_of_lt ht1)
      have harg : -t * Real.log (2 * Real.pi) + cst - (Zsum t).re
          = -Real.log (2 * Real.pi) * t + cst - (Zsum t).re := by ring
      rw [h2, harg]
      ring
    exact (hIlin.sub hIre).congr h1.symm
  have hlin := lin_kernel_identity (Real.log (2 * Real.pi)) cst x hx1
  -- the three facts about the four integrals
  have hJ2_eq : ∫ t in Set.Ioi x, (-Real.log (2 * Real.pi) * t + cst) * hker t
      = (-Real.log (2 * Real.pi) * x + cst) * Work.RHContract.kW x
        - Real.log (2 * Real.pi) / (x * Real.log x) := by
    have hcongr : ∫ t in Set.Ioi x, (-Real.log (2 * Real.pi) * t + cst) * hker t
        = ∫ t in Set.Ioi x, (-Real.log (2 * Real.pi) * t + cst) * (-deriv Work.RHContract.kW t) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht1 : 1 < t := lt_of_lt_of_le hx1 (Set.mem_Ioi.mp ht).le
      rw [hker_eq_deriv ht1, neg_neg]
    rw [hcongr]
    linarith [hlin]
  have hJ_eq : ∫ t in Set.Ioi x, Psi1 t * deriv Work.RHContract.kW t
      = -∫ t in Set.Ioi x, Psi1 t * hker t := by
    have hcongr : ∫ t in Set.Ioi x, Psi1 t * deriv Work.RHContract.kW t
        = ∫ t in Set.Ioi x, -(Psi1 t * hker t) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht1 : 1 < t := lt_of_lt_of_le hx1 (Set.mem_Ioi.mp ht).le
      rw [hker_eq_deriv ht1]
      ring
    rw [hcongr]
    exact MeasureTheory.integral_neg (f := fun t : ℝ => Psi1 t * hker t)
  have hJ1_eq : ∫ t in Set.Ioi x, Psi1 t * hker t
      = (∫ t in Set.Ioi x, (-Real.log (2 * Real.pi) * t + cst) * hker t)
        - ∫ t in Set.Ioi x, (Zsum t).re * hker t := by
    have hcongr : ∫ t in Set.Ioi x, Psi1 t * hker t
        = ∫ t in Set.Ioi x, ((-Real.log (2 * Real.pi) * t + cst) * hker t
            - (Zsum t).re * hker t) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht1 : 1 < t := lt_of_lt_of_le hx1 (Set.mem_Ioi.mp ht).le
      have h2 := Psi1_eq h (le_of_lt ht1)
      have harg : -t * Real.log (2 * Real.pi) + cst - (Zsum t).re
          = -Real.log (2 * Real.pi) * t + cst - (Zsum t).re := by ring
      rw [h2, harg]
      ring
    rw [hcongr]
    exact MeasureTheory.integral_sub
      (f := fun t : ℝ => (-Real.log (2 * Real.pi) * t + cst) * hker t)
      (g := fun t : ℝ => (Zsum t).re * hker t) hIlin hIre
  rw [psiTail_eq h hx, hJ_eq, hJ1_eq, hJ2_eq]
  have h2 := Psi1_eq h (le_of_lt hx1)
  have harg : -x * Real.log (2 * Real.pi) + cst - (Zsum x).re
      = -Real.log (2 * Real.pi) * x + cst - (Zsum x).re := by ring
  rw [h2, harg]
  ring

private lemma ReZ_mul_kW_ge (h : RiemannHypothesis) {x : ℝ} (hx : 1000 ≤ x) :
    -beta0 * (1 / (Real.sqrt x * Real.log x)) * (1 + 1 / Real.log x)
        - (Real.log x + 1) / (x ^ 3 * (Real.log x) ^ 2)
      ≤ (Zsum x).re * Work.RHContract.kW x := by
  have hx2 : 2 ≤ x := by linarith
  have hx1 : (1 : ℝ) < x := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  have hβ0 : 0 ≤ beta0 := by
    rw [beta0]
    exact Commons.NumberTheory.Zeta.psiBeta_nonneg_of_rh h
  have hZ := Zsum_bound h hx2
  have hkw0 : 0 ≤ Work.RHContract.kW x := by
    have hL : 1 / 2 ≤ Real.log x := half_le_log_of_two_le hx2
    rw [kW_eq]
    exact div_nonneg (by linarith) (by positivity)
  have hkeyA1 : x ^ (3 / 2 : ℝ) * Work.RHContract.kW x
      = (1 / (Real.sqrt x * Real.log x)) * (1 + 1 / Real.log x) := by
    have hL : Real.log x ≠ 0 := (Real.log_pos hx1).ne'
    have hs : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx0).ne'
    rw [kW_eq, rpow_three_halves hx0]
    field_simp
    rw [Real.sq_sqrt hx0.le]
  have hkeyA2 : (1 / x) * Work.RHContract.kW x
      = (Real.log x + 1) / (x ^ 3 * (Real.log x) ^ 2) := by
    rw [kW_eq]; field_simp
  have hkey : (beta0 * x ^ (3 / 2 : ℝ) + 1 / x) * Work.RHContract.kW x
      = beta0 * (1 / (Real.sqrt x * Real.log x)) * (1 + 1 / Real.log x)
        + (Real.log x + 1) / (x ^ 3 * (Real.log x) ^ 2) := by
    rw [show (beta0 * x ^ (3 / 2 : ℝ) + 1 / x) * Work.RHContract.kW x
        = beta0 * (x ^ (3 / 2 : ℝ) * Work.RHContract.kW x)
          + (1 / x) * Work.RHContract.kW x from by ring, hkeyA1, hkeyA2]
    ring
  calc (Zsum x).re * Work.RHContract.kW x
      ≥ -‖Zsum x‖ * Work.RHContract.kW x := by
        apply mul_le_mul_of_nonneg_right _ hkw0
        have h1 := Complex.abs_re_le_norm (Zsum x)
        linarith [neg_abs_le (Zsum x).re]
    _ ≥ -(beta0 * x ^ (3 / 2 : ℝ) + 1 / x) * Work.RHContract.kW x := by
        apply mul_le_mul_of_nonneg_right _ hkw0
        linarith [hZ]
    _ = _ := by
        rw [show -(beta0 * x ^ (3 / 2 : ℝ) + 1 / x) * Work.RHContract.kW x
            = -((beta0 * x ^ (3 / 2 : ℝ) + 1 / x) * Work.RHContract.kW x) from by ring,
          hkey]
        ring_nf

private lemma Zint_le (h : RiemannHypothesis) {x : ℝ} (hx : 1000 ≤ x) :
    ∫ t in Set.Ioi x, (Zsum t).re * hker t
      ≤ beta0 * (1 / (Real.sqrt x * Real.log x)) * (4 + 6 / Real.log x + 4 / (Real.log x) ^ 2)
        + Kx x / (3 * x ^ 3) := by
  have hx2 : 2 ≤ x := by linarith
  have hx1 : (1 : ℝ) < x := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  have hβ0 : 0 ≤ beta0 := by
    rw [beta0]
    exact Commons.NumberTheory.Zeta.psiBeta_nonneg_of_rh h
  have hIre := integrableOn_ReZ_hker h hx2
  have hIzb := integrableOn_Zbound_hker h hx2
  have hint3 : IntegrableOn
      (fun t : ℝ => (beta0 * t ^ (3 / 2 : ℝ) + 1 / t) * (Kx x / t ^ 3)) (Set.Ioi x) :=
    ((integrableOn_const_mul_rpow_div_cube x hx0 (beta0 * Kx x)).add
      (integrableOn_const_div_pow x hx0 4 (by norm_num) (Kx x))).congr (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht0 : 0 < t := lt_trans hx0 (Set.mem_Ioi.mp ht)
        exact (Zbound_mul_eq ht0).symm)
  have hstep1 : ∫ t in Set.Ioi x, (Zsum t).re * hker t
      ≤ ∫ t in Set.Ioi x, (beta0 * t ^ (3 / 2 : ℝ) + 1 / t) * hker t := by
    apply MeasureTheory.integral_mono_ae hIre hIzb
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htx : x < t := Set.mem_Ioi.mp ht
    have ht1 : 1 < t := lt_of_lt_of_le hx1 htx.le
    have ht2 : 2 ≤ t := le_trans hx2 htx.le
    have hker0 : 0 ≤ hker t := hker_nonneg ht1
    have hZre : |(Zsum t).re| ≤ beta0 * t ^ (3 / 2 : ℝ) + 1 / t :=
      le_trans (Complex.abs_re_le_norm _) (Zsum_bound h ht2)
    have hb : (Zsum t).re ≤ beta0 * t ^ (3 / 2 : ℝ) + 1 / t := le_trans (le_abs_self _) hZre
    exact mul_le_mul_of_nonneg_right hb hker0
  have hstep2 : ∫ t in Set.Ioi x, (beta0 * t ^ (3 / 2 : ℝ) + 1 / t) * hker t
      ≤ ∫ t in Set.Ioi x, (beta0 * t ^ (3 / 2 : ℝ) + 1 / t) * (Kx x / t ^ 3) := by
    apply MeasureTheory.integral_mono_ae hIzb hint3
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htx : x < t := Set.mem_Ioi.mp ht
    have ht1 : 1 < t := lt_of_lt_of_le hx1 htx.le
    have ht0 : 0 < t := by linarith
    have hkerb : hker t ≤ Kx x / t ^ 3 := by
      have := hker_le hx1 htx.le
      simpa only [Kx] using this
    have h0 : 0 ≤ beta0 * t ^ (3 / 2 : ℝ) + 1 / t := by
      have h1 : 0 ≤ beta0 * t ^ (3 / 2 : ℝ) := mul_nonneg hβ0 (Real.rpow_nonneg ht0.le _)
      have h2 : 0 ≤ 1 / t := by positivity
      linarith
    exact mul_le_mul_of_nonneg_left hkerb h0
  have hstep3 : (∫ t in Set.Ioi x, (beta0 * t ^ (3 / 2 : ℝ) + 1 / t) * (Kx x / t ^ 3))
      = Kx x * (beta0 * (2 / Real.sqrt x) + 1 / (3 * x ^ 3)) := integral_Zbound_hker hx2
  have hfin : Kx x * (beta0 * (2 / Real.sqrt x) + 1 / (3 * x ^ 3))
      = beta0 * (1 / (Real.sqrt x * Real.log x)) * (4 + 6 / Real.log x + 4 / (Real.log x) ^ 2)
        + Kx x / (3 * x ^ 3) := by
    have hfin1 : Kx x * (2 / Real.sqrt x)
        = (1 / (Real.sqrt x * Real.log x)) * (4 + 6 / Real.log x + 4 / (Real.log x) ^ 2) := by
      have hL : Real.log x ≠ 0 := (Real.log_pos hx1).ne'
      have hs : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx0).ne'
      rw [Kx]
      field_simp
      ring
    rw [show Kx x * (beta0 * (2 / Real.sqrt x) + 1 / (3 * x ^ 3))
        = beta0 * (Kx x * (2 / Real.sqrt x)) + Kx x / (3 * x ^ 3) from by ring, hfin1]
    ring
  linarith [hstep1, hstep2, hstep3, hfin.le, hfin.ge]

private lemma Kx_arith {x : ℝ} (hx : 1000 ≤ x) :
    (Real.log x + 1) / (x ^ 3 * (Real.log x) ^ 2) + Kx x / (3 * x ^ 3)
      ≤ (1 / (Real.sqrt x * Real.log x)) / x := by
  have hx0 : (0 : ℝ) < x := by linarith
  set L : ℝ := Real.log x with hL
  have hL1 : 1 ≤ L := by
    rw [hL, Real.le_log_iff_exp_le hx0]
    have h := Real.exp_one_lt_d9
    linarith
  have hL0 : 0 < L := lt_of_lt_of_le one_pos hL1
  have hKx : Kx x = 2 / L + 3 / L ^ 2 + 2 / L ^ 3 := by rw [Kx, hL]
  have hx32 : (13 : ℝ) / 3 ≤ x ^ (3 / 2 : ℝ) := by
    have h6 : (31 : ℝ) ≤ Real.sqrt x := by
      have h7 : (961 : ℝ) ≤ x := by linarith
      nlinarith [Real.sqrt_nonneg x, Real.sq_sqrt hx0.le, Real.sqrt_le_sqrt h7]
    rw [rpow_three_halves hx0]
    nlinarith
  have hnum : (L + 1) + Kx x * L ^ 2 / 3 ≤ x ^ (3 / 2 : ℝ) * L := by
    have h1 : Kx x * L ^ 2 / 3 = (2 * L + 3 + 2 / L) / 3 := by
      rw [hKx]; field_simp
    have h2 : 2 / L ≤ 2 := by rw [div_le_iff₀ hL0]; linarith
    have h5 : (2 * L + 3 + 2 / L) / 3 ≤ 7 * L / 3 := by linarith
    calc (L + 1) + Kx x * L ^ 2 / 3 = (L + 1) + (2 * L + 3 + 2 / L) / 3 := by rw [h1]
      _ ≤ 2 * L + 7 * L / 3 := by linarith
      _ = (13 / 3) * L := by ring
      _ ≤ x ^ (3 / 2 : ℝ) * L := mul_le_mul_of_nonneg_right hx32 hL0.le
  have hstep : (L + 1) / (x ^ 3 * L ^ 2) + Kx x / (3 * x ^ 3)
      = ((L + 1) + Kx x * L ^ 2 / 3) / (x ^ 3 * L ^ 2) := by
    field_simp
  have hstep2 : ((L + 1) + Kx x * L ^ 2 / 3) / (x ^ 3 * L ^ 2)
      ≤ (x ^ (3 / 2 : ℝ) * L) / (x ^ 3 * L ^ 2) :=
    div_le_div_of_nonneg_right hnum (by positivity)
  have hstep3 : (x ^ (3 / 2 : ℝ) * L) / (x ^ 3 * L ^ 2) = (1 / (Real.sqrt x * L)) / x := by
    rw [rpow_three_halves hx0]
    field_simp
    exact Real.sq_sqrt hx0.le
  rw [hL] at hstep hstep2 hstep3
  rw [hL]
  linarith [hstep.le, hstep.ge, hstep2, hstep3.le, hstep3.ge]

/-- **AREA A1**: under RH, `J(x) = psiTail x` is bounded below for all `x ≥ 1000`. -/
theorem psiTail_ge_of_RH (h : RiemannHypothesis) (x : ℝ) (hx : 1000 ≤ x) :
    -((2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) * (5 + 7 / Real.log x + 4 / (Real.log x) ^ 2)
        + Real.log (2 * Real.pi) / Real.sqrt x + 1 / x) / (Real.sqrt x * Real.log x)
      ≤ Work.RHContract.psiTail x := by
  have hx2 : 2 ≤ x := by linarith
  have hx1 : (1 : ℝ) < x := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  have hL0 : 0 < Real.log x := Real.log_pos hx1
  have hs : Real.sqrt x * Real.sqrt x = x := by rw [← pow_two]; exact Real.sq_sqrt hx0.le
  set u : ℝ := 1 / (Real.sqrt x * Real.log x) with hu
  have hsqrt_inv : (1 : ℝ) / (Real.sqrt x * Real.log x) / Real.sqrt x
      = 1 / (x * Real.log x) := by
    rw [div_div]
    congr 1
    linear_combination Real.log x * hs
  have hsplit := psiTail_split h hx2
  have hAeq : Real.log (2 * Real.pi) / (x * Real.log x)
      = Real.log (2 * Real.pi) * u / Real.sqrt x := by
    rw [hu]
    rw [show Real.log (2 * Real.pi) * (1 / (Real.sqrt x * Real.log x)) / Real.sqrt x
        = Real.log (2 * Real.pi) * ((1 / (Real.sqrt x * Real.log x)) / Real.sqrt x) from by ring,
      hsqrt_inv]
    ring
  have hb1 : (Zsum x).re * Work.RHContract.kW x
      ≥ -beta0 * u * (1 + 1 / Real.log x) - (Real.log x + 1) / (x ^ 3 * (Real.log x) ^ 2) := by
    have h1 := ReZ_mul_kW_ge h hx
    rw [hu]
    exact h1
  have hb2 : (∫ t in Set.Ioi x, (Zsum t).re * hker t)
      ≤ beta0 * u * (4 + 6 / Real.log x + 4 / (Real.log x) ^ 2) + Kx x / (3 * x ^ 3) := by
    have h2 := Zint_le h hx
    rw [hu]
    exact h2
  have hb3 : (Real.log x + 1) / (x ^ 3 * (Real.log x) ^ 2) + Kx x / (3 * x ^ 3) ≤ u / x := by
    have h3 := Kx_arith hx
    rw [hu]
    exact h3
  have hgrp : beta0 * u * (1 + 1 / Real.log x)
        + beta0 * u * (4 + 6 / Real.log x + 4 / (Real.log x) ^ 2)
      = beta0 * u * (5 + 7 / Real.log x + 4 / (Real.log x) ^ 2) := by ring
  have hmain : -beta0 * u * (5 + 7 / Real.log x + 4 / (Real.log x) ^ 2)
      - Real.log (2 * Real.pi) * u / Real.sqrt x - u / x ≤ Work.RHContract.psiTail x := by
    rw [hsplit]
    have hA' : -Real.log (2 * Real.pi) / (x * Real.log x)
        = -(Real.log (2 * Real.pi) * u / Real.sqrt x) := by
      rw [show -Real.log (2 * Real.pi) / (x * Real.log x)
          = -(Real.log (2 * Real.pi) / (x * Real.log x)) from neg_div _ _]
      rw [hAeq]
    have hZ' : (Zsum x).re * Work.RHContract.kW x
        ≥ -(beta0 * u * (1 + 1 / Real.log x)
            + (Real.log x + 1) / (x ^ 3 * (Real.log x) ^ 2)) := by
      linarith [hb1]
    have hI' : -(∫ t in Set.Ioi x, (Zsum t).re * hker t)
        ≥ -(beta0 * u * (4 + 6 / Real.log x + 4 / (Real.log x) ^ 2) + Kx x / (3 * x ^ 3)) := by
      linarith [hb2]
    have h4 : -Real.log (2 * Real.pi) / (x * Real.log x) + (Zsum x).re * Work.RHContract.kW x
          - ∫ t in Set.Ioi x, (Zsum t).re * hker t
        ≥ -(Real.log (2 * Real.pi) * u / Real.sqrt x)
          - (beta0 * u * (1 + 1 / Real.log x)
            + (Real.log x + 1) / (x ^ 3 * (Real.log x) ^ 2))
          - (beta0 * u * (4 + 6 / Real.log x + 4 / (Real.log x) ^ 2)
            + Kx x / (3 * x ^ 3)) := by
      linarith [hA', hZ', hI']
    refine le_trans ?_ h4
    have hb3' : (Real.log x + 1) / (x ^ 3 * (Real.log x) ^ 2) + Kx x / (3 * x ^ 3) ≤ u / x := hb3
    calc -beta0 * u * (5 + 7 / Real.log x + 4 / (Real.log x) ^ 2)
          - Real.log (2 * Real.pi) * u / Real.sqrt x - u / x
        = -(Real.log (2 * Real.pi) * u / Real.sqrt x)
          - (beta0 * u * (1 + 1 / Real.log x)
            + beta0 * u * (4 + 6 / Real.log x + 4 / (Real.log x) ^ 2)) - u / x := by
          rw [hgrp]; ring_nf
      _ ≤ -(Real.log (2 * Real.pi) * u / Real.sqrt x)
          - (beta0 * u * (1 + 1 / Real.log x)
            + beta0 * u * (4 + 6 / Real.log x + 4 / (Real.log x) ^ 2))
          - ((Real.log x + 1) / (x ^ 3 * (Real.log x) ^ 2) + Kx x / (3 * x ^ 3)) :=
          sub_le_sub_left hb3' _
      _ = -(Real.log (2 * Real.pi) * u / Real.sqrt x)
          - (beta0 * u * (1 + 1 / Real.log x)
            + (Real.log x + 1) / (x ^ 3 * (Real.log x) ^ 2))
          - (beta0 * u * (4 + 6 / Real.log x + 4 / (Real.log x) ^ 2)
            + Kx x / (3 * x ^ 3)) := by ring_nf
  have hgoal : -((2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi))
        * (5 + 7 / Real.log x + 4 / (Real.log x) ^ 2)
        + Real.log (2 * Real.pi) / Real.sqrt x + 1 / x) / (Real.sqrt x * Real.log x)
      = -beta0 * u * (5 + 7 / Real.log x + 4 / (Real.log x) ^ 2)
        - Real.log (2 * Real.pi) * u / Real.sqrt x - u / x := by
    rw [beta0, hu]
    have hsq' : (Real.log (2 * Real.pi) / Real.sqrt x) / (Real.sqrt x * Real.log x)
        = Real.log (2 * Real.pi) / (x * Real.log x) := by
      rw [div_div, show Real.sqrt x * (Real.sqrt x * Real.log x) = x * Real.log x from by
        rw [← mul_assoc, hs]]
    have hsplit : ((2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi))
          * (5 + 7 / Real.log x + 4 / (Real.log x) ^ 2)
        + Real.log (2 * Real.pi) / Real.sqrt x + 1 / x) / (Real.sqrt x * Real.log x)
        = (2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi))
            * (5 + 7 / Real.log x + 4 / (Real.log x) ^ 2) / (Real.sqrt x * Real.log x)
          + (Real.log (2 * Real.pi) / Real.sqrt x) / (Real.sqrt x * Real.log x)
          + (1 / x) / (Real.sqrt x * Real.log x) := by
      ring
    have hlog : Real.log (2 * Real.pi) * (1 / (Real.sqrt x * Real.log x)) / Real.sqrt x
        = Real.log (2 * Real.pi) / (x * Real.log x) := by
      rw [show Real.log (2 * Real.pi) * (1 / (Real.sqrt x * Real.log x)) / Real.sqrt x
          = (Real.log (2 * Real.pi) / Real.sqrt x) / (Real.sqrt x * Real.log x) from by ring,
        hsq']
    rw [show -((2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi))
          * (5 + 7 / Real.log x + 4 / (Real.log x) ^ 2)
        + Real.log (2 * Real.pi) / Real.sqrt x + 1 / x) / (Real.sqrt x * Real.log x)
        = -(((2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi))
          * (5 + 7 / Real.log x + 4 / (Real.log x) ^ 2)
        + Real.log (2 * Real.pi) / Real.sqrt x + 1 / x) / (Real.sqrt x * Real.log x)) from by
      ring, hsplit, hsq', hlog]
    ring
  rw [hgoal]
  exact hmain

end

end Work.RHContract.A

import Submission.FUP.PSHToFourier5

open FractalUncertainty MeasureTheory FourierTransform Metric Filter Set
open scoped ENNReal BigOperators Topology

set_option autoImplicit false
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)
local notation "ℂᵈ" => (Fin d → ℂ)

namespace Submission.FUP

lemma continuous_toCpx : Continuous (fun x : ℝᵈ => toCpx x) := by
  rw [continuous_pi_iff]
  intro i
  exact Complex.continuous_ofReal.comp (by fun_prop : Continuous (fun x : ℝᵈ => x i))

/-! ### The decay estimate on `ℝᵈ`

The paper's proof of `prop:psh_to_bounded_fourier` obtains, along `ℝᵈ`, the bound
`|f(x)| ≤ C e^{u(x)} e^{(1/2)c_dρω₀(x)}`; since `u ≤ 0` and `ω₀ ≤ 0` decays, this both gives
estimate (iii) (on dropping the last, `≤ 1`, factor) and the `L²` integrability of `f|_ℝᵈ`.
The lemma below produces the *sharpened* form directly: with `c₀ = ρλ/4`,

  `‖F (toCpx x)‖ ≤ D * exp (-(c₀ * χ(‖x‖) * ‖x‖ / (log (2+‖x‖))²))`

where `D` dominates the two constants `A₂ e^{c₀(5+√d)}` (small `x`) and
`√(((πr²)^d)⁻¹ KF) e^{B₂/2+B₃}` (large `x`). -/

lemma norm_F_decay (hd : 1 ≤ d) {ρ CLip lam B3 KF Kg D : ℝ} (hρ : 0 < ρ) (hlam : 0 < lam)
    (hCLip : 0 ≤ CLip)
    (hD1 : (1 + Real.sqrt (((Real.pi * rr d ^ 2) ^ d)⁻¹ * Real.exp (Bsmall ρ CLip d) * Kg))
      * Real.exp ((ρ * lam / 4) * (5 + Real.sqrt d)) ≤ D)
    (hD2 : Real.sqrt (((Real.pi * rr d ^ 2) ^ d)⁻¹ * KF)
      * Real.exp (Bsmall2 ρ CLip d / 2 + B3) ≤ D)
    {u u0 : ℂᵈ → ℝ} {F g : ℂᵈ → ℂ}
    (hunonpos : ∀ x : ℝᵈ, u (toCpx x) ≤ 0)
    (hulip : ∀ x₁ x₂ : ℝᵈ, |u (toCpx x₁) - u (toCpx x₂)| ≤ CLip * ‖x₁ - x₂‖)
    (hugrowth : ∀ z : ℂᵈ, u (toCpx (reVec z)) ≤ u z ∧
      u z ≤ u (toCpx (reVec z)) + ρ * ‖imVec z‖)
    (hu0nonpos : ∀ x : ℝᵈ, u0 (toCpx x) ≤ 0)
    (hu0lip : ∀ x₁ x₂ : ℝᵈ, |u0 (toCpx x₁) - u0 (toCpx x₂)| ≤ 1 * ‖x₁ - x₂‖)
    (hu0growth : ∀ z : ℂᵈ, u0 (toCpx (reVec z)) ≤ u0 z ∧
      u0 z ≤ u0 (toCpx (reVec z)) + (1 / 2) * ‖imVec z‖)
    (hu0le : ∀ x : ℝᵈ, u0 (toCpx x) ≤ lam * omega0 x)
    (habs3 : ∀ t : ℝ, 0 ≤ t → 10 * (d : ℝ) * Real.log (1 + t)
      - (1 / 4) * ρ * lam * (Real.smoothTransition (t / 5 - 1) *
          (t / (Real.log (2 + t)) ^ 2)) ≤ B3)
    (hFana : AnalyticOnNhd ℂ F Set.univ)
    (hg_ana : AnalyticOnNhd ℂ g (Metric.ball (0 : ℂᵈ) (1 / 2)))
    (hFeq : ∀ z, F z = bumpC (d := d) z - g z)
    (hMF : ∫⁻ z in U5, ENNReal.ofReal (‖F z‖ ^ 2 * Real.exp (-(section5Phi ρ u u0 z)))
      ≤ ENNReal.ofReal KF)
    (hKF : 0 < KF)
    (hMg : ∫⁻ z, ENNReal.ofReal (‖g z‖ ^ 2 * Real.exp (-(section5Phi ρ u u0 z)))
      ≤ ENNReal.ofReal Kg)
    (hKg : 0 < Kg) :
    ∀ x : ℝᵈ, ‖F (toCpx x)‖ ≤ D * Real.exp (-((ρ * lam / 4) *
      (Real.smoothTransition (‖x‖ / 5 - 1) * (‖x‖ / (Real.log (2 + ‖x‖)) ^ 2)))) := by
  have hs : (0 : ℝ) < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  intro x
  set χ : ℝ := Real.smoothTransition (‖x‖ / 5 - 1) * (‖x‖ / (Real.log (2 + ‖x‖)) ^ 2) with hχ
  have hA2nn : 0 ≤ 1 + Real.sqrt (((Real.pi * rr d ^ 2) ^ d)⁻¹ * Real.exp (Bsmall ρ CLip d) * Kg) := by
    have h := Real.sqrt_nonneg (((Real.pi * rr d ^ 2) ^ d)⁻¹ * Real.exp (Bsmall ρ CLip d) * Kg)
    linarith
  rcases lt_or_ge ‖toCpx x‖ (1 / 4) with hx | hx
  · -- case `‖x‖` small: `‖F‖ ≤ A₂` and the decay factor is `≥ e^{-c₀(5+√d)}`
    have h1 : ‖F (toCpx x)‖ ≤ 1 + Real.sqrt (((Real.pi * rr d ^ 2) ^ d)⁻¹
        * Real.exp (Bsmall ρ CLip d) * Kg) := by
      have h2 : ‖g (toCpx x)‖ ≤ Real.sqrt (((Real.pi * rr d ^ 2) ^ d)⁻¹
          * Real.exp (Bsmall ρ CLip d) * Kg) :=
        Real.le_sqrt_of_sq_le (norm_g_sq_le_le_quarter (d := d) hρ hCLip hKg hunonpos hugrowth
          hu0nonpos hu0growth hg_ana hMg hd hx.le)
      calc ‖F (toCpx x)‖ = ‖bumpC (d := d) (toCpx x) - g (toCpx x)‖ := by rw [hFeq]
        _ ≤ ‖bumpC (d := d) (toCpx x)‖ + ‖g (toCpx x)‖ := norm_sub_le _ _
        _ ≤ 1 + Real.sqrt (((Real.pi * rr d ^ 2) ^ d)⁻¹ * Real.exp (Bsmall ρ CLip d) * Kg) :=
            add_le_add (norm_bumpC_le_one _) h2
    have hxle : ‖x‖ ≤ Real.sqrt d / 4 := by
      have h := norm_toCpx_ge x
      nlinarith [norm_nonneg (toCpx x), h, hs]
    have hχle : χ ≤ 5 + Real.sqrt d := by
      rw [hχ]
      rcases le_or_gt ‖x‖ 5 with h5 | h5
      · rw [Real.smoothTransition.zero_of_nonpos (by linarith : ‖x‖ / 5 - 1 ≤ 0), zero_mul]
        linarith [Real.sqrt_nonneg d]
      · have hlog1 : (1 : ℝ) ≤ Real.log (2 + ‖x‖) := by
          rw [← Real.log_exp 1]
          exact Real.log_le_log (Real.exp_pos 1)
            (by have := Real.exp_one_lt_three; linarith)
        have hsq1 : (1 : ℝ) ≤ (Real.log (2 + ‖x‖)) ^ 2 := by nlinarith
        have hdiv : ‖x‖ / (Real.log (2 + ‖x‖)) ^ 2 ≤ ‖x‖ := by
          rw [div_le_iff₀ (by positivity)]
          nlinarith [norm_nonneg x]
        calc Real.smoothTransition (‖x‖ / 5 - 1) * (‖x‖ / (Real.log (2 + ‖x‖)) ^ 2)
            ≤ 1 * (‖x‖ / (Real.log (2 + ‖x‖)) ^ 2) :=
              mul_le_mul_of_nonneg_right (Real.smoothTransition.le_one _)
                (div_nonneg (norm_nonneg _) (sq_nonneg _))
          _ = ‖x‖ / (Real.log (2 + ‖x‖)) ^ 2 := one_mul _
          _ ≤ ‖x‖ := hdiv
          _ ≤ 5 + Real.sqrt d := by linarith [Real.sqrt_nonneg d]
    have hge : (1 : ℝ) ≤ Real.exp ((ρ * lam / 4) * (5 + Real.sqrt d))
        * Real.exp (-((ρ * lam / 4) * χ)) := by
      have hcl : (0 : ℝ) ≤ ρ * lam / 4 := by positivity
      have hmono : Real.exp (-((ρ * lam / 4) * (5 + Real.sqrt d)))
          ≤ Real.exp (-((ρ * lam / 4) * χ)) := Real.exp_le_exp.mpr (by nlinarith)
      have hone : Real.exp ((ρ * lam / 4) * (5 + Real.sqrt d))
          * Real.exp (-((ρ * lam / 4) * (5 + Real.sqrt d))) = 1 := by
        rw [← Real.exp_add]
        have : (ρ * lam / 4) * (5 + Real.sqrt d) + -((ρ * lam / 4) * (5 + Real.sqrt d)) = 0 := by
          ring
        rw [this, Real.exp_zero]
      calc (1 : ℝ) = Real.exp ((ρ * lam / 4) * (5 + Real.sqrt d))
            * Real.exp (-((ρ * lam / 4) * (5 + Real.sqrt d))) := hone.symm
        _ ≤ Real.exp ((ρ * lam / 4) * (5 + Real.sqrt d))
            * Real.exp (-((ρ * lam / 4) * χ)) :=
            mul_le_mul_of_nonneg_left hmono (Real.exp_pos _).le
    calc ‖F (toCpx x)‖ ≤ 1 + Real.sqrt (((Real.pi * rr d ^ 2) ^ d)⁻¹
          * Real.exp (Bsmall ρ CLip d) * Kg) := h1
      _ = (1 + Real.sqrt (((Real.pi * rr d ^ 2) ^ d)⁻¹ * Real.exp (Bsmall ρ CLip d) * Kg)) * 1 :=
          (mul_one _).symm
      _ ≤ (1 + Real.sqrt (((Real.pi * rr d ^ 2) ^ d)⁻¹ * Real.exp (Bsmall ρ CLip d) * Kg))
            * (Real.exp ((ρ * lam / 4) * (5 + Real.sqrt d)) * Real.exp (-((ρ * lam / 4) * χ))) :=
          mul_le_mul_of_nonneg_left hge hA2nn
      _ = (1 + Real.sqrt (((Real.pi * rr d ^ 2) ^ d)⁻¹ * Real.exp (Bsmall ρ CLip d) * Kg))
            * Real.exp ((ρ * lam / 4) * (5 + Real.sqrt d)) * Real.exp (-((ρ * lam / 4) * χ)) := by
          ring
      _ ≤ D * Real.exp (-((ρ * lam / 4) * χ)) :=
          mul_le_mul_of_nonneg_right hD1 (Real.exp_pos _).le
  · -- case `‖x‖` large
    have h1 := @norm_F_sq_le_quarter d ρ CLip KF hρ hCLip hd u u0 F hunonpos hulip hugrowth
      hu0lip hu0growth hFana hMF hKF x hx
    have h2 : ρ * u0 (toCpx x) + 20 * (d : ℝ) * Real.log (1 + ‖x‖)
        ≤ 2 * B3 - 2 * ((ρ * lam / 4) * χ) := by
      have h3 := habs3 ‖x‖ (norm_nonneg x)
      rw [show Real.smoothTransition (‖x‖ / 5 - 1) * (‖x‖ / (Real.log (2 + ‖x‖)) ^ 2) = χ from hχ.symm]
        at h3
      have h4 : ρ * u0 (toCpx x) ≤ ρ * (lam * omega0 x) := mul_le_mul_of_nonneg_left (hu0le x) hρ.le
      have h5 : ρ * (lam * omega0 x) = -(4 * ((ρ * lam / 4) * χ)) := by
        rw [hχ, omega0]; ring
      linarith
    have h2u : 2 * u (toCpx x) ≤ 0 := by have := hunonpos x; linarith
    have h7 : ‖F (toCpx x)‖ ^ 2 ≤ (((Real.pi * rr d ^ 2) ^ d)⁻¹ * KF)
        * Real.exp (2 * B3 + Bsmall2 ρ CLip d) * Real.exp (-(2 * ((ρ * lam / 4) * χ))) := by
      have hexp : Real.exp (2 * u (toCpx x) + ρ * u0 (toCpx x) + 20 * (d : ℝ) * Real.log (1 + ‖x‖)
            + Bsmall2 ρ CLip d)
          ≤ Real.exp (2 * B3 + Bsmall2 ρ CLip d) * Real.exp (-(2 * ((ρ * lam / 4) * χ))) := by
        have harg : 2 * u (toCpx x) + ρ * u0 (toCpx x) + 20 * (d : ℝ) * Real.log (1 + ‖x‖)
            + Bsmall2 ρ CLip d ≤ (2 * B3 + Bsmall2 ρ CLip d) + (-(2 * ((ρ * lam / 4) * χ))) := by
          linarith
        calc Real.exp (2 * u (toCpx x) + ρ * u0 (toCpx x) + 20 * (d : ℝ) * Real.log (1 + ‖x‖)
              + Bsmall2 ρ CLip d)
            ≤ Real.exp ((2 * B3 + Bsmall2 ρ CLip d) + (-(2 * ((ρ * lam / 4) * χ)))) :=
              Real.exp_le_exp.mpr harg
          _ = Real.exp (2 * B3 + Bsmall2 ρ CLip d) * Real.exp (-(2 * ((ρ * lam / 4) * χ))) :=
              Real.exp_add _ _
      calc ‖F (toCpx x)‖ ^ 2 ≤ ((Real.pi * rr d ^ 2) ^ d)⁻¹
            * Real.exp (2 * u (toCpx x) + ρ * u0 (toCpx x) + 20 * (d : ℝ) * Real.log (1 + ‖x‖)
                + Bsmall2 ρ CLip d) * KF := h1
        _ ≤ (((Real.pi * rr d ^ 2) ^ d)⁻¹
            * (Real.exp (2 * B3 + Bsmall2 ρ CLip d) * Real.exp (-(2 * ((ρ * lam / 4) * χ)))) * KF) := by
            have hA : (0 : ℝ) ≤ ((Real.pi * rr d ^ 2) ^ d)⁻¹ := by
              have h1 : (0 : ℝ) < Real.pi * rr d ^ 2 := by
                refine mul_pos Real.pi_pos (pow_pos ?_ 2)
                rw [rr]; positivity
              exact inv_nonneg.mpr (pow_nonneg h1.le d)
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp hA) hKF.le
        _ = (((Real.pi * rr d ^ 2) ^ d)⁻¹ * KF)
            * Real.exp (2 * B3 + Bsmall2 ρ CLip d) * Real.exp (-(2 * ((ρ * lam / 4) * χ))) := by
            ring
    have h8 : ‖F (toCpx x)‖ ≤ Real.sqrt (((Real.pi * rr d ^ 2) ^ d)⁻¹ * KF)
        * Real.exp (Bsmall2 ρ CLip d / 2 + B3) * Real.exp (-((ρ * lam / 4) * χ)) := by
      refine le_trans (Real.le_sqrt_of_sq_le h7) (le_of_eq ?_)
      have hA : (0 : ℝ) ≤ ((Real.pi * rr d ^ 2) ^ d)⁻¹ * KF := by
        have h1 : (0 : ℝ) < Real.pi * rr d ^ 2 := by
          refine mul_pos Real.pi_pos (pow_pos ?_ 2)
          rw [rr]; positivity
        exact mul_nonneg (inv_nonneg.mpr (pow_nonneg h1.le d)) hKF.le
      have e1 : (2 * B3 + Bsmall2 ρ CLip d) / 2 = Bsmall2 ρ CLip d / 2 + B3 := by ring
      have e2 : (-(2 * ((ρ * lam / 4) * χ))) / 2 = -((ρ * lam / 4) * χ) := by ring
      rw [Real.sqrt_mul (mul_nonneg hA (Real.exp_pos _).le), Real.sqrt_mul hA, sqrt_exp, sqrt_exp,
        e1, e2]
    calc ‖F (toCpx x)‖ ≤ Real.sqrt (((Real.pi * rr d ^ 2) ^ d)⁻¹ * KF)
          * Real.exp (Bsmall2 ρ CLip d / 2 + B3) * Real.exp (-((ρ * lam / 4) * χ)) := h8
      _ ≤ D * Real.exp (-((ρ * lam / 4) * χ)) :=
          mul_le_mul_of_nonneg_right hD2 (Real.exp_pos _).le

end Submission.FUP

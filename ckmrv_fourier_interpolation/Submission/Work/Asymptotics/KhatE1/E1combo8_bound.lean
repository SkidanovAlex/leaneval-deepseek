import Mathlib
import Submission.Work.Asymptotics.KhatE1Defs
import Submission.Work.Residues.ThetaDecay
import Submission.Work.Residues.ThetaAux
import Submission.Work.Residues.KMinusClear_T
import Submission.Work.Kernels.TildeFacts.theta_quartic
import Submission.Work.FunnelNumerics.Lamb_funnel_bound
import Submission.Work.Asymptotics.E4Fun_sub_one_explicit
import Submission.Work.Asymptotics.KhatE1.E1logf_bound
import Submission.Work.Asymptotics.KhatE1.E1LS_eq_log
import Submission.Work.Asymptotics.KhatE1.E1funnel_UW_bounds

set_option maxHeartbeats 2000000

namespace Work.Asymptotics.KhatE1

open UpperHalfPlane

noncomputable section

/-!
## The exact expression of `24 Δ E¹` in terms of the theta quartics

Multiplying `E1combo8 = j (ψ₄ - ψ₂ E₆/E₄) + 576 (2E₄ - ψ₄)` by `24 Δ` clears the
denominator `Δ` of `j = E₄³/Δ`; the resulting expression is polynomial in the theta
quartics `U = θ₀₀⁴`, `V = θ₁₀⁴`, `W = θ₀₁⁴` and in `𝓛`, `𝓛_S`.
-/

private lemma e1combo8_clear (ℓ : Work.Kernels.LogLambdaData) (τ : UpperHalfPlane)
    (hE4 : Work.Kernels.E4Fun τ ≠ 0) (hΔ : Work.Kernels.DeltaFun τ ≠ 0) :
    24 * Work.Asymptotics.E1combo8 ℓ τ * Work.Kernels.DeltaFun τ
      = 24 * (Work.Kernels.E4Fun τ)^3 * Work.Kernels.psi4 ℓ τ
        - 24 * (Work.Kernels.E4Fun τ)^2 * Work.Kernels.E6Fun τ * Work.Kernels.psi2 ℓ τ
        + 13824 * Work.Kernels.DeltaFun τ
            * (2 * Work.Kernels.E4Fun τ - Work.Kernels.psi4 ℓ τ) := by
  have hj : Work.Kernels.jInvariantFun τ
      = Work.Kernels.E4Fun τ^3 / Work.Kernels.DeltaFun τ := rfl
  rw [Work.Asymptotics.E1combo8, hj]
  field_simp
  ring

private lemma e1combo8_theta (ℓ : Work.Kernels.LogLambdaData) (τ : UpperHalfPlane) :
    24 * (Work.Kernels.E4Fun τ)^3 * Work.Kernels.psi4 ℓ τ
        - 24 * (Work.Kernels.E4Fun τ)^2 * Work.Kernels.E6Fun τ * Work.Kernels.psi2 ℓ τ
        + 13824 * Work.Kernels.DeltaFun τ
            * (2 * Work.Kernels.E4Fun τ - Work.Kernels.psi4 ℓ τ)
      = (270 * (Work.Kernels.UFun τ)^4 * (Work.Kernels.VFun τ)^4
         - 540 * (Work.Kernels.UFun τ)^3 * (Work.Kernels.VFun τ)^5
         + 378 * (Work.Kernels.UFun τ)^2 * (Work.Kernels.VFun τ)^6
         - 108 * Work.Kernels.UFun τ * (Work.Kernels.VFun τ)^7) * ℓ.L τ
        + (108 * (Work.Kernels.UFun τ)^7 * Work.Kernels.VFun τ
           - 378 * (Work.Kernels.UFun τ)^6 * (Work.Kernels.VFun τ)^2
           + 540 * (Work.Kernels.UFun τ)^5 * (Work.Kernels.VFun τ)^3
           - 540 * (Work.Kernels.UFun τ)^4 * (Work.Kernels.VFun τ)^4
           + 540 * (Work.Kernels.UFun τ)^3 * (Work.Kernels.VFun τ)^5
           - 378 * (Work.Kernels.UFun τ)^2 * (Work.Kernels.VFun τ)^6
           + 108 * Work.Kernels.UFun τ * (Work.Kernels.VFun τ)^7) * ℓ.L_S τ
        + 27648 * Work.Kernels.DeltaFun τ * Work.Kernels.E4Fun τ := by
  have hψ4 : Work.Kernels.psi4 ℓ τ
      = ((Work.Kernels.UFun τ)^2 + (Work.Kernels.WFun τ)^2
            - 2*(Work.Kernels.VFun τ)^2) * ℓ.L τ
        + ((Work.Kernels.UFun τ)^2 + (Work.Kernels.VFun τ)^2
            - 2*(Work.Kernels.WFun τ)^2) * ℓ.L_S τ := by
    unfold Work.Kernels.psi4 Work.Kernels.xi4Fun
    rw [Work.Residues.xi4Fun_slash_S_apply τ]
  have hψ2 : Work.Kernels.psi2 ℓ τ
      = ((Work.Kernels.UFun τ) + (Work.Kernels.WFun τ)) * ℓ.L τ
        - ((Work.Kernels.UFun τ) + (Work.Kernels.VFun τ)) * ℓ.L_S τ := by
    unfold Work.Kernels.psi2 Work.Kernels.xi2Fun
    rw [Work.Residues.xi2Fun_slash_S_apply τ]
    ring
  rw [hψ4, hψ2, Work.Residues.KMinusT_E4Fun_eq_theta τ,
    Work.Residues.KMinusT_E6Fun_eq_theta τ, Work.Residues.KMinusT_DeltaFun_eq_theta τ,
    Work.Kernels.TildeFacts.theta_quartic τ]
  ring

/-- The exact identity for `24 Δ · E1combo8`. -/
private lemma e1combo8_key (ℓ : Work.Kernels.LogLambdaData) (τ : UpperHalfPlane)
    (hE4 : Work.Kernels.E4Fun τ ≠ 0) (hΔ : Work.Kernels.DeltaFun τ ≠ 0) :
    24 * Work.Asymptotics.E1combo8 ℓ τ * Work.Kernels.DeltaFun τ
      = (270 * (Work.Kernels.UFun τ)^4 * (Work.Kernels.VFun τ)^4
         - 540 * (Work.Kernels.UFun τ)^3 * (Work.Kernels.VFun τ)^5
         + 378 * (Work.Kernels.UFun τ)^2 * (Work.Kernels.VFun τ)^6
         - 108 * Work.Kernels.UFun τ * (Work.Kernels.VFun τ)^7) * ℓ.L τ
        + (108 * (Work.Kernels.UFun τ)^7 * Work.Kernels.VFun τ
           - 378 * (Work.Kernels.UFun τ)^6 * (Work.Kernels.VFun τ)^2
           + 540 * (Work.Kernels.UFun τ)^5 * (Work.Kernels.VFun τ)^3
           - 540 * (Work.Kernels.UFun τ)^4 * (Work.Kernels.VFun τ)^4
           + 540 * (Work.Kernels.UFun τ)^3 * (Work.Kernels.VFun τ)^5
           - 378 * (Work.Kernels.UFun τ)^2 * (Work.Kernels.VFun τ)^6
           + 108 * Work.Kernels.UFun τ * (Work.Kernels.VFun τ)^7) * ℓ.L_S τ
        + 27648 * Work.Kernels.DeltaFun τ * Work.Kernels.E4Fun τ := by
  rw [e1combo8_clear ℓ τ hE4 hΔ, e1combo8_theta ℓ τ]

/-- The polynomial factor `m` of the fourth-order vanishing combination. -/
private noncomputable def e1m (z : ℂ) : ℂ :=
  ((9:ℂ)/2)*z - ((63:ℂ)/4)*z^2 + ((45:ℂ)/2)*z^3 - ((45:ℂ)/2)*z^4
      + ((45:ℂ)/2)*z^5 - ((63:ℂ)/4)*z^6 + ((9:ℂ)/2)*z^7

/-- The polynomial `(9/2) z² (1-z)² (1-z+z²)` of the fourth-order vanishing combination. -/
private noncomputable def e1g (z : ℂ) : ℂ :=
  ((9:ℂ)/2)*z^2*(1-z)^2*(1-z+z^2)

/-- The fourth-order vanishing combination appearing in `E1logf_bound`, as a function
of `z = V/U`. -/
private noncomputable def e1f (z : ℂ) : ℂ := e1m z * Complex.log (1 - z) + e1g z

/-- `24 U⁸ m(V/U)` is the explicit polynomial of `e1combo8_theta`. -/
private lemma u8_m (U V : ℂ) (hU : U ≠ 0) :
    (24:ℂ) * U^8 * e1m (V/U)
      = 108*U^7*V - 378*U^6*V^2 + 540*U^5*V^3 - 540*U^4*V^4
        + 540*U^3*V^5 - 378*U^2*V^6 + 108*U*V^7 := by
  unfold e1m
  field_simp
  ring

/-- `24 U⁸ g(V/U)` for `g(z) = (9/2)z²(1-z)²(1-z+z²)`. -/
private lemma u8_g (U V : ℂ) (hU : U ≠ 0) :
    (24:ℂ) * U^8 * e1g (V/U)
      = 108 * U^2 * V^2 * (U - V)^2 * (U^2 - U*V + V^2) := by
  unfold e1g
  field_simp
  ring

/-! ## Numerical facts on the funnel -/

/-- `e^{-2π} ≤ 1/350`. -/
private lemma exp_neg_two_pi_le : Real.exp (-(2 * Real.pi)) ≤ 1 / 350 := by
  have h6 : (6:ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  have h1 : Real.exp 6 ≤ Real.exp (2 * Real.pi) := Real.exp_le_exp.mpr h6
  have h2 : Real.exp 6 = (Real.exp 1)^6 := by
    rw [show (6:ℝ) = ((6:ℕ):ℝ) * 1 by norm_num, Real.exp_nat_mul]
  have h3 : (2.7:ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h4 : (2.7:ℝ)^6 ≤ (Real.exp 1)^6 := pow_le_pow_left₀ (by norm_num) h3.le 6
  have h5 : (350:ℝ) ≤ Real.exp (2 * Real.pi) := by
    rw [h2] at h1
    nlinarith [h1, h4, (by norm_num : (350:ℝ) ≤ 2.7^6)]
  rw [Real.exp_neg, inv_eq_one_div]
  exact one_div_le_one_div_of_le (by norm_num) h5

/-- On the funnel, `tpar τ = e^{-π Im τ} ≤ 1/350`. -/
private lemma tpar_funnel_le (τ : UpperHalfPlane) (hτ : Work.Asymptotics.Funnel τ) :
    Work.Residues.tpar τ ≤ 1 / 350 := by
  have him : (2:ℝ) ≤ τ.im := hτ.2
  have h : Real.exp (-(Real.pi * τ.im)) ≤ Real.exp (-(2 * Real.pi)) :=
    Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, him])
  exact le_trans h exp_neg_two_pi_le

/-- `‖U - 1‖`, `‖W - 1‖ ≤ 40 tpar` and `‖V‖ ≤ 80 tpar` on the funnel. -/
private lemma funnel_theta_bounds (τ : UpperHalfPlane) (hτ : Work.Asymptotics.Funnel τ) :
    ‖Work.Kernels.UFun τ - 1‖ ≤ 40 * Work.Residues.tpar τ ∧
    ‖Work.Kernels.WFun τ - 1‖ ≤ 40 * Work.Residues.tpar τ ∧
    ‖Work.Kernels.VFun τ‖ ≤ 80 * Work.Residues.tpar τ := by
  obtain ⟨hU, hW⟩ := E1funnel_UW_bounds τ hτ
  refine ⟨hU, hW, ?_⟩
  have hVeq : Work.Kernels.VFun τ
      = Work.Kernels.UFun τ - Work.Kernels.WFun τ := by
    have h := Work.Kernels.TildeFacts.theta_quartic τ
    rw [h]; ring
  rw [hVeq]
  calc ‖Work.Kernels.UFun τ - Work.Kernels.WFun τ‖
      ≤ ‖Work.Kernels.UFun τ - 1‖ + ‖Work.Kernels.WFun τ - 1‖ := by
        have he : Work.Kernels.UFun τ - Work.Kernels.WFun τ
            = (Work.Kernels.UFun τ - 1) - (Work.Kernels.WFun τ - 1) := by ring
        rw [he]; exact norm_sub_le _ _
    _ ≤ 40 * Work.Residues.tpar τ + 40 * Work.Residues.tpar τ := add_le_add hU hW
    _ = 80 * Work.Residues.tpar τ := by ring

/-- `1/2 ≤ ‖U‖ ≤ 2` on the funnel. -/
private lemma funnel_U_norm (τ : UpperHalfPlane) (hτ : Work.Asymptotics.Funnel τ) :
    ‖Work.Kernels.UFun τ‖ ≤ 2 ∧ (1/2:ℝ) ≤ ‖Work.Kernels.UFun τ‖ := by
  have hU := (funnel_theta_bounds τ hτ).1
  have ht := tpar_funnel_le τ hτ
  have h40 : (40:ℝ) * Work.Residues.tpar τ ≤ 4/35 := by
    nlinarith [ht, Work.Residues.tpar_pos τ]
  have hle : ‖Work.Kernels.UFun τ - 1‖ ≤ 4/35 := le_trans hU h40
  constructor
  · have h := norm_add_le (Work.Kernels.UFun τ - 1) (1:ℂ)
    rw [sub_add_cancel, norm_one] at h
    linarith
  · have h := norm_add_le ((1:ℂ) - Work.Kernels.UFun τ) (Work.Kernels.UFun τ)
    rw [sub_add_cancel, norm_one] at h
    have h2 : ‖(1:ℂ) - Work.Kernels.UFun τ‖ = ‖Work.Kernels.UFun τ - 1‖ := by
      rw [show (1:ℂ) - Work.Kernels.UFun τ = -(Work.Kernels.UFun τ - 1) by ring, norm_neg]
    rw [h2] at h
    linarith

/-- `‖V/U‖ ≤ 1/2` on the funnel. -/
private lemma funnel_lambda (τ : UpperHalfPlane) (hτ : Work.Asymptotics.Funnel τ) :
    ‖Work.Kernels.VFun τ / Work.Kernels.UFun τ‖ ≤ 1/2 := by
  obtain ⟨_, _, hV⟩ := funnel_theta_bounds τ hτ
  obtain ⟨_, hUlb⟩ := funnel_U_norm τ hτ
  have ht := tpar_funnel_le τ hτ
  have h80 : (80:ℝ) * Work.Residues.tpar τ ≤ 8/35 := by
    nlinarith [ht, Work.Residues.tpar_pos τ]
  have hV' : ‖Work.Kernels.VFun τ‖ ≤ 8/35 := le_trans hV h80
  rw [norm_div]
  have hdenpos : 0 < ‖Work.Kernels.UFun τ‖ := by linarith
  rw [div_le_iff₀ hdenpos]
  nlinarith

/-! ## A polynomial bound for the leading `q`-coefficient -/

private lemma n1_poly_bound (U V : ℂ) (hU : ‖U‖ ≤ 2) (hV : ‖V‖ ≤ 1) :
    ‖(270:ℂ)*U^4*V^4 - (540:ℂ)*U^3*V^5 + (378:ℂ)*U^2*V^6 - (108:ℂ)*U*V^7‖
      ≤ 10368 * ‖V‖^4 := by
  have hU0 : (0:ℝ) ≤ ‖U‖ := norm_nonneg U
  have hV0 : (0:ℝ) ≤ ‖V‖ := norm_nonneg V
  have hkey : (270:ℂ)*U^4*V^4 - (540:ℂ)*U^3*V^5 + (378:ℂ)*U^2*V^6
        - (108:ℂ)*U*V^7
      = V^4 * ((270:ℂ)*U^4 - (540:ℂ)*U^3*V + (378:ℂ)*U^2*V^2
          - (108:ℂ)*U*V^3) := by ring
  rw [hkey, norm_mul, norm_pow]
  have hb1 : ‖(270:ℂ)*U^4‖ ≤ 4320 := by
    rw [norm_mul, norm_pow]; norm_num
    have := pow_le_pow_left₀ hU0 hU 4
    nlinarith
  have hb2 : ‖(540:ℂ)*U^3*V‖ ≤ 4320 := by
    rw [norm_mul, norm_mul, norm_pow]; norm_num
    have h1 := pow_le_pow_left₀ hU0 hU 3
    nlinarith
  have hb3 : ‖(378:ℂ)*U^2*V^2‖ ≤ 1512 := by
    rw [norm_mul, norm_mul, norm_pow, norm_pow]; norm_num
    have h1 := pow_le_pow_left₀ hU0 hU 2
    have h2 := pow_le_pow_left₀ hV0 hV 2
    nlinarith
  have hb4 : ‖(108:ℂ)*U*V^3‖ ≤ 216 := by
    rw [norm_mul, norm_mul, norm_pow]; norm_num
    have h2 := pow_le_pow_left₀ hV0 hV 3
    nlinarith
  have hsum : ‖(270:ℂ)*U^4 - (540:ℂ)*U^3*V + (378:ℂ)*U^2*V^2 - (108:ℂ)*U*V^3‖
      ≤ 10368 := by
    have h1 := norm_sub_le ((270:ℂ)*U^4 - (540:ℂ)*U^3*V + (378:ℂ)*U^2*V^2)
      ((108:ℂ)*U*V^3)
    have h2 := norm_add_le ((270:ℂ)*U^4 - (540:ℂ)*U^3*V) ((378:ℂ)*U^2*V^2)
    have h3 := norm_sub_le ((270:ℂ)*U^4) ((540:ℂ)*U^3*V)
    linarith
  calc ‖V‖^4 * ‖(270:ℂ)*U^4 - (540:ℂ)*U^3*V + (378:ℂ)*U^2*V^2
        - (108:ℂ)*U*V^3‖ ≤ ‖V‖^4 * 10368 :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 10368 * ‖V‖^4 := by ring

/-! ## The main theorem -/

/-- **Refined near-identity, dimension 8.** -/
theorem E1combo8_bound (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ : UpperHalfPlane, Work.Asymptotics.Funnel τ →
      ‖Work.Asymptotics.E1combo8 ℓ τ‖
        ≤ C * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun τ‖ := by
  obtain ⟨c, hc, hΔlow⟩ := Work.Asymptotics.exists_Delta_Funnel_lower
  obtain ⟨CL, NL, hCL, hNL, hL⟩ := Work.FunnelNumerics.L_scale_bound ℓ
  obtain ⟨Cf, hCf, hf⟩ := E1logf_bound
  refine ⟨((80:ℝ)^4 / c) * (10368*CL + 384*Cf) + 1, NL, by positivity, hNL, ?_⟩
  intro τ hτ
  -- basic funnel facts
  have ht_le : Work.Residues.tpar τ ≤ 1/350 := tpar_funnel_le τ hτ
  have ht_pos : 0 < Work.Residues.tpar τ := Work.Residues.tpar_pos τ
  obtain ⟨hU1, hW1, hVb⟩ := funnel_theta_bounds τ hτ
  obtain ⟨hUub, hUlb⟩ := funnel_U_norm τ hτ
  have hlam : ‖Work.Kernels.VFun τ / Work.Kernels.UFun τ‖ ≤ 1/2 := funnel_lambda τ hτ
  have hU0 : Work.Kernels.UFun τ ≠ 0 := by
    intro h
    have hz : ‖Work.Kernels.UFun τ‖ = 0 := by rw [h]; simp
    linarith [hUlb, hz]
  have hUpos : 0 < ‖Work.Kernels.UFun τ‖ := lt_of_lt_of_le (by norm_num) hUlb
  have hVle1 : ‖Work.Kernels.VFun τ‖ ≤ 1 := by
    have h : (80:ℝ) * Work.Residues.tpar τ ≤ 1 := by nlinarith [ht_le]
    linarith [hVb, h]
  -- lower bound for Δ
  have hΔlow' : c * Work.Residues.tpar τ ^ 2 ≤ ‖Work.Kernels.DeltaFun τ‖ := by
    have h := hΔlow τ hτ
    rwa [← Work.Residues.tpar_pow_two] at h
  have hΔpos : 0 < ‖Work.Kernels.DeltaFun τ‖ := lt_of_lt_of_le (by positivity) hΔlow'
  have hΔne : Work.Kernels.DeltaFun τ ≠ 0 := by
    intro h
    have hz : ‖Work.Kernels.DeltaFun τ‖ = 0 := by rw [h]; simp
    linarith [hΔpos, hz]
  -- E₄ ≠ 0 on the funnel
  have hE4b : ‖Work.Kernels.E4Fun τ - 1‖ ≤ 1/2 := by
    have h := Work.Asymptotics.E4Fun_sub_one_explicit (w := τ) (by linarith [hτ.2])
    have hq : ‖Work.Kernels.qParamFun τ‖ = Work.Residues.tpar τ ^ 2 := by
      rw [Work.Asymptotics.norm_qParamFun, ← Work.Residues.tpar_pow_two]
    rw [hq] at h
    have ht2 : Work.Residues.tpar τ ^ 2 ≤ (1/350)^2 :=
      pow_le_pow_left₀ ht_pos.le ht_le 2
    calc ‖Work.Kernels.E4Fun τ - 1‖ ≤ 20000 * Work.Residues.tpar τ ^ 2 := h
      _ ≤ 20000 * (1/350)^2 := by nlinarith [ht2]
      _ ≤ 1/2 := by norm_num
  have hE4ne : Work.Kernels.E4Fun τ ≠ 0 := by
    intro h
    have hz : ‖Work.Kernels.E4Fun τ - 1‖ = 1 := by rw [h]; norm_num
    rw [hz] at hE4b
    norm_num at hE4b
  -- the logarithm identity
  have hLS : ℓ.L_S τ = Complex.log (1 - Work.Kernels.VFun τ / Work.Kernels.UFun τ) := by
    have hWU : Work.Kernels.WFun τ / Work.Kernels.UFun τ
        = 1 - Work.Kernels.VFun τ / Work.Kernels.UFun τ := by
      have hVeq : Work.Kernels.VFun τ
          = Work.Kernels.UFun τ - Work.Kernels.WFun τ := by
        have h := Work.Kernels.TildeFacts.theta_quartic τ
        rw [h]; ring
      rw [hVeq, sub_div, div_self hU0]
      ring
    rw [E1LS_eq_log ℓ τ hτ, hWU]
  -- the identity for `24 Δ E¹`
  have hkey := e1combo8_key ℓ τ hE4ne hΔne
  have hN2eq : (108 * (Work.Kernels.UFun τ)^7 * Work.Kernels.VFun τ
           - 378 * (Work.Kernels.UFun τ)^6 * (Work.Kernels.VFun τ)^2
           + 540 * (Work.Kernels.UFun τ)^5 * (Work.Kernels.VFun τ)^3
           - 540 * (Work.Kernels.UFun τ)^4 * (Work.Kernels.VFun τ)^4
           + 540 * (Work.Kernels.UFun τ)^3 * (Work.Kernels.VFun τ)^5
           - 378 * (Work.Kernels.UFun τ)^2 * (Work.Kernels.VFun τ)^6
           + 108 * Work.Kernels.UFun τ * (Work.Kernels.VFun τ)^7)
      = 24 * (Work.Kernels.UFun τ)^8
          * e1m (Work.Kernels.VFun τ / Work.Kernels.UFun τ) := by
    rw [u8_m (Work.Kernels.UFun τ) (Work.Kernels.VFun τ) hU0]
  have hΔE4eq : 27648 * Work.Kernels.DeltaFun τ * Work.Kernels.E4Fun τ
      = 24 * (Work.Kernels.UFun τ)^8
          * e1g (Work.Kernels.VFun τ / Work.Kernels.UFun τ) := by
    rw [u8_g (Work.Kernels.UFun τ) (Work.Kernels.VFun τ) hU0]
    have hW : Work.Kernels.WFun τ
        = Work.Kernels.UFun τ - Work.Kernels.VFun τ := by
      have h := Work.Kernels.TildeFacts.theta_quartic τ
      rw [h]; ring
    rw [Work.Residues.KMinusT_DeltaFun_eq_theta τ,
      Work.Residues.KMinusT_E4Fun_eq_theta τ, hW]
    ring
  have hsplit : (108 * (Work.Kernels.UFun τ)^7 * Work.Kernels.VFun τ
           - 378 * (Work.Kernels.UFun τ)^6 * (Work.Kernels.VFun τ)^2
           + 540 * (Work.Kernels.UFun τ)^5 * (Work.Kernels.VFun τ)^3
           - 540 * (Work.Kernels.UFun τ)^4 * (Work.Kernels.VFun τ)^4
           + 540 * (Work.Kernels.UFun τ)^3 * (Work.Kernels.VFun τ)^5
           - 378 * (Work.Kernels.UFun τ)^2 * (Work.Kernels.VFun τ)^6
           + 108 * Work.Kernels.UFun τ * (Work.Kernels.VFun τ)^7) * ℓ.L_S τ
        + 27648 * Work.Kernels.DeltaFun τ * Work.Kernels.E4Fun τ
      = 24 * (Work.Kernels.UFun τ)^8 *
          e1f (Work.Kernels.VFun τ / Work.Kernels.UFun τ) := by
    rw [hN2eq, hΔE4eq, hLS]
    unfold e1f
    ring
  have hmain : 24 * Work.Asymptotics.E1combo8 ℓ τ * Work.Kernels.DeltaFun τ
      = (270 * (Work.Kernels.UFun τ)^4 * (Work.Kernels.VFun τ)^4
         - 540 * (Work.Kernels.UFun τ)^3 * (Work.Kernels.VFun τ)^5
         + 378 * (Work.Kernels.UFun τ)^2 * (Work.Kernels.VFun τ)^6
         - 108 * Work.Kernels.UFun τ * (Work.Kernels.VFun τ)^7) * ℓ.L τ
        + 24 * (Work.Kernels.UFun τ)^8 *
            e1f (Work.Kernels.VFun τ / Work.Kernels.UFun τ) := by
    rw [hkey, add_assoc, hsplit]
  -- bounds
  have hfl : ‖e1f (Work.Kernels.VFun τ / Work.Kernels.UFun τ)‖
      ≤ Cf * ‖Work.Kernels.VFun τ / Work.Kernels.UFun τ‖^4 := hf _ hlam
  have hN1b : ‖(270 * (Work.Kernels.UFun τ)^4 * (Work.Kernels.VFun τ)^4
         - 540 * (Work.Kernels.UFun τ)^3 * (Work.Kernels.VFun τ)^5
         + 378 * (Work.Kernels.UFun τ)^2 * (Work.Kernels.VFun τ)^6
         - 108 * Work.Kernels.UFun τ * (Work.Kernels.VFun τ)^7)‖
      ≤ 10368 * ‖Work.Kernels.VFun τ‖^4 := n1_poly_bound _ _ hUub hVle1
  have hU4 : ‖Work.Kernels.UFun τ‖^4 ≤ 16 := by
    have h : ‖Work.Kernels.UFun τ‖^4 ≤ (2:ℝ)^4 := pow_le_pow_left₀ (norm_nonneg _) hUub 4
    have h2 : (2:ℝ)^4 = 16 := by norm_num
    rwa [h2] at h
  have hcomb : ‖Work.Kernels.UFun τ‖^8
        * ‖Work.Kernels.VFun τ / Work.Kernels.UFun τ‖^4
      = ‖Work.Kernels.UFun τ‖^4 * ‖Work.Kernels.VFun τ‖^4 := by
    rw [norm_div, div_pow]
    field_simp
  have hstep2 : 24 * ‖Work.Kernels.UFun τ‖^8
        * (Cf * ‖Work.Kernels.VFun τ / Work.Kernels.UFun τ‖^4)
      ≤ 384 * Cf * ‖Work.Kernels.VFun τ‖^4 := by
    have hV0 : (0:ℝ) ≤ ‖Work.Kernels.VFun τ‖^4 := by positivity
    calc 24 * ‖Work.Kernels.UFun τ‖^8
          * (Cf * ‖Work.Kernels.VFun τ / Work.Kernels.UFun τ‖^4)
        = 24 * Cf * (‖Work.Kernels.UFun τ‖^8
            * ‖Work.Kernels.VFun τ / Work.Kernels.UFun τ‖^4) := by ring
      _ = 24 * Cf * (‖Work.Kernels.UFun τ‖^4 * ‖Work.Kernels.VFun τ‖^4) := by
            rw [hcomb]
      _ ≤ 24 * Cf * (16 * ‖Work.Kernels.VFun τ‖^4) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul_of_nonneg_right hU4 hV0
      _ = 384 * Cf * ‖Work.Kernels.VFun τ‖^4 := by ring
  have hfinal : ‖24 * Work.Asymptotics.E1combo8 ℓ τ * Work.Kernels.DeltaFun τ‖
      ≤ (10368 * ‖ℓ.L τ‖ + 384 * Cf) * ‖Work.Kernels.VFun τ‖^4 := by
    rw [hmain]
    have h1 : ‖(270 * (Work.Kernels.UFun τ)^4 * (Work.Kernels.VFun τ)^4
         - 540 * (Work.Kernels.UFun τ)^3 * (Work.Kernels.VFun τ)^5
         + 378 * (Work.Kernels.UFun τ)^2 * (Work.Kernels.VFun τ)^6
         - 108 * Work.Kernels.UFun τ * (Work.Kernels.VFun τ)^7) * ℓ.L τ‖
        ≤ 10368 * ‖Work.Kernels.VFun τ‖^4 * ‖ℓ.L τ‖ := by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_right hN1b (norm_nonneg _)
    have h2 : ‖(24:ℂ) * (Work.Kernels.UFun τ)^8 *
          e1f (Work.Kernels.VFun τ / Work.Kernels.UFun τ)‖
        ≤ 384 * Cf * ‖Work.Kernels.VFun τ‖^4 := by
      calc ‖(24:ℂ) * (Work.Kernels.UFun τ)^8 *
            e1f (Work.Kernels.VFun τ / Work.Kernels.UFun τ)‖
          = 24 * ‖(Work.Kernels.UFun τ)^8‖
              * ‖e1f (Work.Kernels.VFun τ / Work.Kernels.UFun τ)‖ := by
            rw [norm_mul, norm_mul]; norm_num
        _ = 24 * ‖Work.Kernels.UFun τ‖^8
              * ‖e1f (Work.Kernels.VFun τ / Work.Kernels.UFun τ)‖ := by rw [norm_pow]
        _ ≤ 24 * ‖Work.Kernels.UFun τ‖^8
              * (Cf * ‖Work.Kernels.VFun τ / Work.Kernels.UFun τ‖^4) :=
            mul_le_mul_of_nonneg_left hfl (by positivity)
        _ ≤ 384 * Cf * ‖Work.Kernels.VFun τ‖^4 := hstep2
    calc ‖(270 * (Work.Kernels.UFun τ)^4 * (Work.Kernels.VFun τ)^4
         - 540 * (Work.Kernels.UFun τ)^3 * (Work.Kernels.VFun τ)^5
         + 378 * (Work.Kernels.UFun τ)^2 * (Work.Kernels.VFun τ)^6
         - 108 * Work.Kernels.UFun τ * (Work.Kernels.VFun τ)^7) * ℓ.L τ
        + (24:ℂ) * (Work.Kernels.UFun τ)^8 *
            e1f (Work.Kernels.VFun τ / Work.Kernels.UFun τ)‖
        ≤ ‖(270 * (Work.Kernels.UFun τ)^4 * (Work.Kernels.VFun τ)^4
         - 540 * (Work.Kernels.UFun τ)^3 * (Work.Kernels.VFun τ)^5
         + 378 * (Work.Kernels.UFun τ)^2 * (Work.Kernels.VFun τ)^6
         - 108 * Work.Kernels.UFun τ * (Work.Kernels.VFun τ)^7) * ℓ.L τ‖
          + ‖(24:ℂ) * (Work.Kernels.UFun τ)^8 *
            e1f (Work.Kernels.VFun τ / Work.Kernels.UFun τ)‖ := norm_add_le _ _
      _ ≤ 10368 * ‖Work.Kernels.VFun τ‖^4 * ‖ℓ.L τ‖
            + 384 * Cf * ‖Work.Kernels.VFun τ‖^4 := add_le_add h1 h2
      _ = (10368 * ‖ℓ.L τ‖ + 384 * Cf) * ‖Work.Kernels.VFun τ‖^4 := by ring
  -- put everything together
  have hbV : ‖Work.Kernels.VFun τ‖^4
      ≤ (80 * Work.Residues.tpar τ)^4 :=
    pow_le_pow_left₀ (norm_nonneg _) hVb 4
  have hbL : ‖ℓ.L τ‖ ≤ CL * Work.Kernels.scale τ ^ NL := hL τ
  have hs1 : (1:ℝ) ≤ Work.Kernels.scale τ ^ NL :=
    Real.one_le_rpow (Work.Kernels.one_le_scale τ) hNL
  have hs0 : (0:ℝ) ≤ Work.Kernels.scale τ ^ NL :=
    Real.rpow_nonneg (Work.Kernels.scale_pos τ).le NL
  have hstep3 : ‖24 * Work.Asymptotics.E1combo8 ℓ τ‖ * (c * Work.Residues.tpar τ^2)
      ≤ (80 * Work.Residues.tpar τ)^4
          * ((10368*CL) * Work.Kernels.scale τ^NL + 384*Cf) := by
    calc ‖24 * Work.Asymptotics.E1combo8 ℓ τ‖ * (c * Work.Residues.tpar τ^2)
        ≤ ‖24 * Work.Asymptotics.E1combo8 ℓ τ‖ * ‖Work.Kernels.DeltaFun τ‖ :=
          mul_le_mul_of_nonneg_left hΔlow' (norm_nonneg _)
      _ = ‖24 * Work.Asymptotics.E1combo8 ℓ τ * Work.Kernels.DeltaFun τ‖ :=
          (norm_mul _ _).symm
      _ ≤ (10368 * ‖ℓ.L τ‖ + 384 * Cf) * ‖Work.Kernels.VFun τ‖^4 := hfinal
      _ ≤ (10368 * (CL * Work.Kernels.scale τ^NL) + 384 * Cf)
            * (80 * Work.Residues.tpar τ)^4 := by
          apply mul_le_mul
          · nlinarith [hbL, hCL.le]
          · exact hbV
          · positivity
          · nlinarith [hs0, hCL.le, hCf.le]
      _ = (80 * Work.Residues.tpar τ)^4
            * ((10368*CL) * Work.Kernels.scale τ^NL + 384*Cf) := by ring
  have hstep3b : ‖24 * Work.Asymptotics.E1combo8 ℓ τ‖
      ≤ (80 * Work.Residues.tpar τ)^4
          * ((10368*CL) * Work.Kernels.scale τ^NL + 384*Cf)
        / (c * Work.Residues.tpar τ^2) := by
    rw [le_div_iff₀ (by positivity)]
    exact hstep3
  have hstep5 : (80 * Work.Residues.tpar τ)^4
          * ((10368*CL) * Work.Kernels.scale τ^NL + 384*Cf)
        / (c * Work.Residues.tpar τ^2)
      ≤ ((80:ℝ)^4/c*(10368*CL + 384*Cf)) * Work.Kernels.scale τ^NL
          * Work.Residues.tpar τ^2 := by
    rw [div_le_iff₀ (by positivity)]
    have hmid : (10368*CL) * Work.Kernels.scale τ^NL + 384*Cf
        ≤ (10368*CL + 384*Cf) * Work.Kernels.scale τ^NL := by
      nlinarith [hs1, hCL.le, hCf.le, hs0]
    calc (80 * Work.Residues.tpar τ)^4
          * ((10368*CL) * Work.Kernels.scale τ^NL + 384*Cf)
        ≤ (80 * Work.Residues.tpar τ)^4
            * ((10368*CL + 384*Cf) * Work.Kernels.scale τ^NL) :=
          mul_le_mul_of_nonneg_left hmid (by positivity)
      _ = ((80:ℝ)^4/c*(10368*CL + 384*Cf)) * Work.Kernels.scale τ^NL
            * Work.Residues.tpar τ^2 * (c * Work.Residues.tpar τ^2) := by
          field_simp
  have hstep6 : ((80:ℝ)^4/c*(10368*CL + 384*Cf)) * Work.Kernels.scale τ^NL
        * Work.Residues.tpar τ^2
      ≤ ((80:ℝ)^4/c*(10368*CL + 384*Cf)) * Work.Kernels.scale τ^NL
        * ‖Work.Kernels.qParamFun τ‖ := by
    rw [show Work.Residues.tpar τ ^ 2 = ‖Work.Kernels.qParamFun τ‖ by
      rw [Work.Residues.tpar_pow_two, Work.Asymptotics.norm_qParamFun]]
  have hC : ‖Work.Asymptotics.E1combo8 ℓ τ‖
      ≤ ((80:ℝ)^4/c*(10368*CL + 384*Cf)) * Work.Kernels.scale τ^NL
        * ‖Work.Kernels.qParamFun τ‖ := by
    have hb : ‖24 * Work.Asymptotics.E1combo8 ℓ τ‖
        ≤ ((80:ℝ)^4/c*(10368*CL + 384*Cf)) * Work.Kernels.scale τ^NL
          * ‖Work.Kernels.qParamFun τ‖ := le_trans hstep3b (le_trans hstep5 hstep6)
    rw [norm_mul] at hb
    norm_num at hb
    have h24 : ‖Work.Asymptotics.E1combo8 ℓ τ‖
        ≤ 24 * ‖Work.Asymptotics.E1combo8 ℓ τ‖ := by
      nlinarith [norm_nonneg (Work.Asymptotics.E1combo8 ℓ τ)]
    linarith [h24, hb]
  calc ‖Work.Asymptotics.E1combo8 ℓ τ‖
      ≤ ((80:ℝ)^4/c*(10368*CL + 384*Cf)) * Work.Kernels.scale τ^NL
        * ‖Work.Kernels.qParamFun τ‖ := hC
    _ ≤ (((80:ℝ)^4/c*(10368*CL + 384*Cf)) + 1) * Work.Kernels.scale τ^NL
        * ‖Work.Kernels.qParamFun τ‖ := by
          have hq0 : (0:ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ := norm_nonneg _
          have hK0 : (0:ℝ) ≤ (80:ℝ)^4/c*(10368*CL + 384*Cf) := by positivity
          nlinarith [hs0, hq0, hK0]

end

end Work.Asymptotics.KhatE1

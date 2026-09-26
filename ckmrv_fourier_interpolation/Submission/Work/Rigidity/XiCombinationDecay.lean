import Mathlib
import Submission.Work.Kernels.Classical
import Submission.Work.Kernels.LogLambda.ThetaLaws
import Submission.Work.Modular.E4_qExpansion_coeff
import Submission.Work.Modular.E6_qExpansion_coeff
import Submission.Work.Modular.ThetaFuncs
import Submission.Work.Modular.theta2_at_cusp
import Submission.Work.Modular.E4_tendsto_atImInfty
import Submission.Work.Kernels.TildeFacts.theta_quartic
import Submission.Work.Kernels.TildeFacts.E6Fun_eq_theta
import Submission.Work.Residues.KMinusClear_T

/-!
# The rigidity of the weight-twelve combination `ξ₄E₄²`, `ξ₂E₄E₆`

This file proves that no nontrivial linear combination `c₁ξ₄E₄² + c₂ξ₂E₄E₆` can decay
faster than `e^{-2π Im τ}` at the cusp: if its modulus times `e^{2π Im τ}` tends to `0` as
`Im τ → ∞`, then `c₁ = c₂ = 0`.

The mathematics is the following.  Writing `U = θ₀₀⁴`, `V = θ₁₀⁴`, `W = θ₀₁⁴` and
`ξ₂ = U + W`, `ξ₄ = U² + W² - 2V²`, the classical theta identities give
`E₄ = (U²+V²+W²)/2`, `E₆ = -U³ + (3/2)U²W + (3/2)UW² - W³` and `U = W + V`, whence the
combination factors as

  `ξ₄E₄² - ξ₂E₄E₆ = (9/2)·U·V²·W·E₄`.

Together with `Δ = U²V²W²/256` this gives `(ξ₄E₄² - ξ₂E₄E₆)·U·W = 1152·Δ·E₄`, so the
quotient by `q` tends to `1152·(Δ/q)·E₄/(UW) → 1152·1·1 = 1152 ≠ 0`.  On the other hand
`ξ₄E₄² → 2` and `ξ₂E₄E₆ → 2`, so `c₁ + c₂ = 0` is forced by the decay; writing
`c₂ = -c₁` the same decay applied to `c₁(ξ₄E₄² - ξ₂E₄E₆)` forces `c₁ = 0`.
-/

namespace Work.Rigidity

open Filter UpperHalfPlane
open scoped Real Topology

/-! ## Limits of the classical objects at the cusp -/

private lemma tendsto_UFun : Tendsto Work.Kernels.UFun atImInfty (nhds (1 : ℂ)) := by
  change Tendsto (fun τ : ℍ => Work.Modular.theta3 τ ^ 4) atImInfty (nhds 1)
  have h := Work.Modular.tendsto_theta3_atImInfty.pow 4
  simpa using h

private lemma tendsto_WFun : Tendsto Work.Kernels.WFun atImInfty (nhds (1 : ℂ)) := by
  change Tendsto (fun τ : ℍ => Work.Modular.theta4 τ ^ 4) atImInfty (nhds 1)
  have h := Work.Modular.tendsto_theta4_atImInfty.pow 4
  simpa using h

private lemma tendsto_VFun : Tendsto Work.Kernels.VFun atImInfty (nhds (0 : ℂ)) := by
  change Tendsto (fun τ : ℍ => Work.Modular.theta2 τ ^ 4) atImInfty (nhds 0)
  have h := Work.Modular.theta2_at_cusp.pow 4
  simpa using h

private lemma tendsto_E4Fun : Tendsto Work.Kernels.E4Fun atImInfty (nhds (1 : ℂ)) := by
  simpa using Work.Modular.E4_tendsto_atImInfty

private lemma tendsto_E6Fun : Tendsto Work.Kernels.E6Fun atImInfty (nhds (1 : ℂ)) := by
  have key : (fun τ : ℍ => (Work.Kernels.WFun τ - Work.Kernels.VFun τ) *
      (Work.Kernels.VFun τ ^ 2 + Work.Kernels.WFun τ ^ 2
        + (5 / 2) * (Work.Kernels.VFun τ * Work.Kernels.WFun τ))) = Work.Kernels.E6Fun := by
    funext τ; rw [Work.Kernels.TildeFacts.E6Fun_eq_theta]; ring
  rw [← key]
  have hm := ((tendsto_WFun.sub tendsto_VFun).mul
    (((tendsto_VFun.pow 2).add (tendsto_WFun.pow 2)).add
      ((tendsto_VFun.mul tendsto_WFun).const_mul (5 / 2))))
  simpa using hm

private lemma tendsto_xi2Fun : Tendsto Work.Kernels.xi2Fun atImInfty (nhds (2 : ℂ)) := by
  change Tendsto (fun τ : ℍ => Work.Kernels.UFun τ + Work.Kernels.WFun τ) atImInfty (nhds 2)
  have hm : Tendsto (fun τ : ℍ => Work.Kernels.UFun τ + Work.Kernels.WFun τ) atImInfty
      (nhds ((1 : ℂ) + 1)) := tendsto_UFun.add tendsto_WFun
  rw [show ((1 : ℂ) + 1) = 2 from by norm_num] at hm
  exact hm

private lemma tendsto_xi4Fun : Tendsto Work.Kernels.xi4Fun atImInfty (nhds (2 : ℂ)) := by
  change Tendsto (fun τ : ℍ => Work.Kernels.UFun τ ^ 2 + Work.Kernels.WFun τ ^ 2
    - 2 * Work.Kernels.VFun τ ^ 2) atImInfty (nhds 2)
  have hm : Tendsto (fun τ : ℍ => Work.Kernels.UFun τ ^ 2 + Work.Kernels.WFun τ ^ 2
      - 2 * Work.Kernels.VFun τ ^ 2) atImInfty
      (nhds ((1 : ℂ) ^ 2 + (1 : ℂ) ^ 2 - 2 * (0 : ℂ) ^ 2)) :=
    ((tendsto_UFun.pow 2).add (tendsto_WFun.pow 2)).sub ((tendsto_VFun.pow 2).const_mul 2)
  rw [show ((1 : ℂ) ^ 2 + (1 : ℂ) ^ 2 - 2 * (0 : ℂ) ^ 2) = 2 from by norm_num] at hm
  exact hm

/-! ## The quotient `Δ/q` tends to `1` -/

private lemma qParamFun_ne_zero (τ : ℍ) : Work.Kernels.qParamFun τ ≠ 0 := by
  simp [Work.Kernels.qParamFun]

private lemma qParamFun_norm_inv (τ : ℍ) :
    (‖Work.Kernels.qParamFun τ‖)⁻¹ = Real.exp (2 * Real.pi * τ.im) := by
  have hnorm : ‖Work.Kernels.qParamFun τ‖ = Real.exp (-(2 * Real.pi * τ.im)) := by
    rw [show Work.Kernels.qParamFun τ = Function.Periodic.qParam 1 (τ : ℂ) from by
      simp [Work.Kernels.qParamFun, Function.Periodic.qParam]]
    rw [Function.Periodic.norm_qParam]
    congr 1
    rw [UpperHalfPlane.coe_im]; ring
  rw [hnorm, ← Real.exp_neg]
  congr 1; ring

private lemma tendsto_DeltaFun_div_qParamFun :
    Tendsto (fun τ : ℍ => Work.Kernels.DeltaFun τ / Work.Kernels.qParamFun τ)
      atImInfty (nhds (1 : ℂ)) := by
  have hfun : (fun τ : ℍ => Work.Kernels.DeltaFun τ / Work.Kernels.qParamFun τ)
      = (fun τ : ℍ => ∏' n, (1 - ModularForm.eta_q n (τ : ℂ)) ^ 24) := by
    funext τ
    rw [show Work.Kernels.DeltaFun τ = ModularForm.discriminant τ from by
          rw [show Work.Kernels.DeltaFun = ⇑CuspForm.discriminant from rfl,
            CuspForm.coe_discriminant]]
    rw [ModularForm.discriminant_eq_q_prod]
    rw [show Work.Kernels.qParamFun τ = Function.Periodic.qParam 1 (τ : ℂ) from by
          simp [Work.Kernels.qParamFun, Function.Periodic.qParam]]
    rw [mul_div_cancel_left₀ _ (Function.Periodic.qParam_ne_zero (τ : ℂ))]
  rw [hfun]
  exact ModularForm.tendsto_atImInfty_tprod_one_sub_eta_q_pow

/-! ## The algebraic identity and the nonvanishing of `U·W` -/

/-- The weight-twelve combination `ξ₄E₄² − ξ₂E₄E₆`. -/
private noncomputable abbrev xiComb : ℍ → ℂ :=
  fun τ => Work.Kernels.xi4Fun τ * Work.Kernels.E4Fun τ ^ 2
    - Work.Kernels.xi2Fun τ * Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ

private lemma xiComb_identity (τ : ℍ) :
    xiComb τ = (9 / 2) * (Work.Kernels.UFun τ * Work.Kernels.VFun τ ^ 2
      * Work.Kernels.WFun τ * Work.Kernels.E4Fun τ) := by
  simp only [xiComb, Work.Kernels.xi4Fun, Work.Kernels.xi2Fun]
  rw [Work.Residues.KMinusT_E4Fun_eq_theta τ, Work.Residues.KMinusT_E6Fun_eq_theta τ,
      Work.Kernels.TildeFacts.theta_quartic τ]
  ring

private lemma UFun_mul_WFun_ne_zero (τ : ℍ) :
    Work.Kernels.UFun τ * Work.Kernels.WFun τ ≠ 0 := by
  intro h0
  have h := Work.Residues.KMinusT_DeltaFun_eq_theta τ
  apply Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ
  rw [h]
  have hsq : Work.Kernels.UFun τ ^ 2 * Work.Kernels.VFun τ ^ 2
      * Work.Kernels.WFun τ ^ 2 = 0 := by
    rw [show Work.Kernels.UFun τ ^ 2 * Work.Kernels.VFun τ ^ 2
          * Work.Kernels.WFun τ ^ 2
        = (Work.Kernels.UFun τ * Work.Kernels.WFun τ) ^ 2
          * Work.Kernels.VFun τ ^ 2 by ring, h0]
    ring
  rw [hsq]; ring

/-! ## The main theorem -/

theorem XiCombinationDecay (c1 c2 : Complex)
    (h : Filter.Tendsto (fun τ : UpperHalfPlane =>
            ‖c1 * Work.Kernels.xi4Fun τ * Work.Kernels.E4Fun τ ^ 2
              + c2 * Work.Kernels.xi2Fun τ * Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ‖
            * Real.exp (2 * Real.pi * τ.im)) UpperHalfPlane.atImInfty (nhds 0)) :
    c1 = 0 ∧ c2 = 0 := by
  -- Step 1: the combination tends to `2 (c1 + c2)` at the cusp.
  have hL : Tendsto (fun τ : ℍ =>
        c1 * Work.Kernels.xi4Fun τ * Work.Kernels.E4Fun τ ^ 2
          + c2 * Work.Kernels.xi2Fun τ * Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ)
      atImInfty (nhds (2 * (c1 + c2))) := by
    have h1 : Tendsto (fun τ : ℍ => c1 * Work.Kernels.xi4Fun τ * Work.Kernels.E4Fun τ ^ 2)
        atImInfty (nhds ((c1 * 2) * (1 : ℂ) ^ 2)) :=
      (tendsto_const_nhds.mul tendsto_xi4Fun).mul (tendsto_E4Fun.pow 2)
    have h2 : Tendsto (fun τ : ℍ =>
          c2 * Work.Kernels.xi2Fun τ * Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ)
        atImInfty (nhds (((c2 * 2) * 1) * 1)) :=
      ((tendsto_const_nhds.mul tendsto_xi2Fun).mul tendsto_E4Fun).mul tendsto_E6Fun
    have h3 := h1.add h2
    rw [show ((c1 * 2) * (1 : ℂ) ^ 2 + ((c2 * 2) * 1) * 1) = 2 * (c1 + c2) from by ring] at h3
    exact h3
  -- Step 2: the decay forces `c1 + c2 = 0`.
  have hg : Tendsto (fun τ : ℍ => Real.exp (2 * Real.pi * τ.im)) atImInfty atTop := by
    have him : Tendsto (fun τ : ℍ => τ.im) atImInfty atTop := by
      simpa only [atImInfty, UpperHalfPlane.coe_im] using
        tendsto_comap (f := UpperHalfPlane.im) (x := atTop)
    have h2 : Tendsto (fun τ : ℍ => 2 * Real.pi * τ.im) atImInfty atTop :=
      him.const_mul_atTop (by positivity)
    exact Real.tendsto_exp_atTop.comp h2
  have hsum : c1 + c2 = 0 := by
    by_contra hne
    have hpos : 0 < ‖(2 : ℂ) * (c1 + c2)‖ := by
      rw [norm_mul]
      exact mul_pos (by norm_num) (norm_pos_iff.mpr hne)
    set δ : ℝ := ‖(2 : ℂ) * (c1 + c2)‖ / 2 with hδdef
    have hδpos : 0 < δ := by rw [hδdef]; linarith
    have hδlt : δ < ‖(2 : ℂ) * (c1 + c2)‖ := by rw [hδdef]; linarith
    have hLnorm : Tendsto (fun τ : ℍ => ‖c1 * Work.Kernels.xi4Fun τ
          * Work.Kernels.E4Fun τ ^ 2
          + c2 * Work.Kernels.xi2Fun τ * Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ‖)
        atImInfty (nhds ‖(2 : ℂ) * (c1 + c2)‖) := hL.norm
    have ev1 : ∀ᶠ τ : ℍ in atImInfty, δ < ‖c1 * Work.Kernels.xi4Fun τ
          * Work.Kernels.E4Fun τ ^ 2
          + c2 * Work.Kernels.xi2Fun τ * Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ‖ := by
      filter_upwards [hLnorm.eventually (isOpen_Ioi.mem_nhds hδlt)] with τ hτ
      exact hτ
    have ev2 : ∀ᶠ τ : ℍ in atImInfty, 1 < δ * Real.exp (2 * Real.pi * τ.im) := by
      have hδg : Tendsto (fun τ : ℍ => δ * Real.exp (2 * Real.pi * τ.im)) atImInfty atTop :=
        hg.const_mul_atTop hδpos
      exact hδg.eventually (eventually_gt_atTop 1)
    have ev3 : ∀ᶠ τ : ℍ in atImInfty, ‖c1 * Work.Kernels.xi4Fun τ
          * Work.Kernels.E4Fun τ ^ 2
          + c2 * Work.Kernels.xi2Fun τ * Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ‖
          * Real.exp (2 * Real.pi * τ.im) < 1 :=
      h.eventually (Iio_mem_nhds one_pos)
    obtain ⟨τ, hτ1, hτ2, hτ3⟩ := (ev1.and (ev2.and ev3)).exists
    have hstep := mul_lt_mul_of_pos_right hτ1 (Real.exp_pos (2 * Real.pi * τ.im))
    linarith
  -- Step 3: with `c2 = -c1`, the quotient `(ξ₄E₄² - ξ₂E₄E₆)/q` tends to `1152 ≠ 0`.
  have hc2 : c2 = -c1 := by linear_combination hsum
  rw [hc2] at h ⊢
  have hHq : Tendsto (fun τ : ℍ => xiComb τ / Work.Kernels.qParamFun τ)
      atImInfty (nhds (1152 : ℂ)) := by
    have key : ∀ τ : ℍ, xiComb τ / Work.Kernels.qParamFun τ
        = 1152 * (Work.Kernels.DeltaFun τ / Work.Kernels.qParamFun τ)
            * (Work.Kernels.E4Fun τ / (Work.Kernels.UFun τ * Work.Kernels.WFun τ)) := by
      intro τ
      rw [xiComb_identity τ, Work.Residues.KMinusT_DeltaFun_eq_theta τ]
      field_simp [UFun_mul_WFun_ne_zero τ, qParamFun_ne_zero τ]
      ring
    have hRHS : Tendsto (fun τ : ℍ => 1152 * (Work.Kernels.DeltaFun τ
          / Work.Kernels.qParamFun τ)
        * (Work.Kernels.E4Fun τ / (Work.Kernels.UFun τ * Work.Kernels.WFun τ)))
        atImInfty (nhds (1152 : ℂ)) := by
      have h1 : Tendsto (fun τ : ℍ => (1152 : ℂ)
            * (Work.Kernels.DeltaFun τ / Work.Kernels.qParamFun τ))
          atImInfty (nhds ((1152 : ℂ) * 1)) :=
        tendsto_const_nhds.mul tendsto_DeltaFun_div_qParamFun
      have hUW : Tendsto (fun τ : ℍ => Work.Kernels.UFun τ * Work.Kernels.WFun τ)
          atImInfty (nhds (1 : ℂ)) := by
        have h := tendsto_UFun.mul tendsto_WFun
        rwa [show ((1 : ℂ) * 1) = 1 from by norm_num] at h
      have h2 : Tendsto (fun τ : ℍ => Work.Kernels.E4Fun τ
            / (Work.Kernels.UFun τ * Work.Kernels.WFun τ))
          atImInfty (nhds ((1 : ℂ) / 1)) :=
        tendsto_E4Fun.div hUW one_ne_zero
      have h3 := h1.mul h2
      rw [show ((1152 : ℂ) * 1) * (1 / 1) = 1152 from by ring] at h3
      exact h3
    exact hRHS.congr (fun τ => (key τ).symm)
  have hHdecay : Tendsto (fun τ : ℍ => ‖xiComb τ‖ * Real.exp (2 * Real.pi * τ.im))
      atImInfty (nhds (1152 : ℝ)) := by
    have hnorm : Tendsto (fun τ : ℍ => ‖xiComb τ / Work.Kernels.qParamFun τ‖)
        atImInfty (nhds (1152 : ℝ)) := by
      have h' := hHq.norm
      simpa using h'
    exact hnorm.congr (fun τ => by rw [norm_div, div_eq_mul_inv, qParamFun_norm_inv])
  have hc1lim : Tendsto (fun τ : ℍ => ‖c1‖ * (‖xiComb τ‖
        * Real.exp (2 * Real.pi * τ.im))) atImInfty (nhds (‖c1‖ * 1152)) :=
    hHdecay.const_mul ‖c1‖
  have hzero : Tendsto (fun τ : ℍ => ‖c1‖ * (‖xiComb τ‖
        * Real.exp (2 * Real.pi * τ.im))) atImInfty (nhds 0) := by
    refine h.congr (fun τ => ?_)
    rw [show c1 * Work.Kernels.xi4Fun τ * Work.Kernels.E4Fun τ ^ 2
          + -c1 * Work.Kernels.xi2Fun τ * Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ
          = c1 * xiComb τ from by simp only [xiComb]; ring]
    rw [norm_mul]
    ring
  have huniq : ‖c1‖ * 1152 = 0 := tendsto_nhds_unique hc1lim hzero
  have hc1 : c1 = 0 := by
    refine norm_eq_zero.mp ?_
    exact (mul_eq_zero.mp huniq).resolve_right (by norm_num)
  exact ⟨hc1, by rw [hc1]; ring⟩

end Work.Rigidity

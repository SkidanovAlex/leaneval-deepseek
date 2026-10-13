import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.RPFresh.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.RPFresh

open MeasureTheory Set intervalIntegral
open scoped Real Topology

set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem sg_eq_lam : sg = fun θ : ℝ => (Real.sin (2*θ))^(-(Work.Spaces.eta)) := rfl

/-- `(cot(2θ))' = -2 sin(2θ)^{-2}` on `(0,π/2)`. -/
theorem hasDerivAt_cot_two {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi/2)) :
    HasDerivAt (fun t : ℝ => Real.cot (2*t)) (-(2:ℝ) * (Real.sin (2*θ))^(-(2:ℝ))) θ := by
  have hsin : (0:ℝ) < Real.sin (2*θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hcos : HasDerivAt (fun t : ℝ => Real.cos (2*t)) (-(2:ℝ) * Real.sin (2*θ)) θ := by
    have h : HasDerivAt (fun t : ℝ => 2*t) 2 θ := by
      simpa using (hasDerivAt_id θ).const_mul (2:ℝ)
    have h2 := (Real.hasDerivAt_cos (2*θ)).comp θ h
    simpa [Function.comp_def, mul_comm] using h2
  have hsin' : HasDerivAt (fun t : ℝ => Real.sin (2*t)) ((2:ℝ) * Real.cos (2*θ)) θ := by
    have h : HasDerivAt (fun t : ℝ => 2*t) 2 θ := by
      simpa using (hasDerivAt_id θ).const_mul (2:ℝ)
    have h2 := (Real.hasDerivAt_sin (2*θ)).comp θ h
    simpa [Function.comp_def, mul_comm] using h2
  have hquot : HasDerivAt (fun t : ℝ => Real.cos (2*t) / Real.sin (2*t))
      (((-(2:ℝ) * Real.sin (2*θ)) * Real.sin (2*θ) - Real.cos (2*θ) * ((2:ℝ) * Real.cos (2*θ)))
        / (Real.sin (2*θ))^2) θ :=
    hcos.div hsin' hsin.ne'
  have hfun : (fun t : ℝ => Real.cot (2*t)) = fun t : ℝ => Real.cos (2*t) / Real.sin (2*t) := by
    funext t; rw [Real.cot_eq_cos_div_sin]
  rw [hfun]
  refine hquot.congr_deriv ?_
  have key : (Real.sin (2*θ))^(-(2:ℝ)) = 1/(Real.sin (2*θ))^2 := by
    rw [← Real.rpow_two, Real.rpow_neg hsin.le, one_div]
  rw [key]
  field_simp
  nlinarith [Real.sin_sq_add_cos_sq (2*θ)]

/-- Continuity of `σ` on the sub-interval. -/
theorem cont_sg_Icc {δ : ℝ} (hδ : 0 < δ) (hδ4 : δ < Real.pi/4) :
    ContinuousOn sg (Set.Icc δ (Real.pi/2-δ)) := by
  have hfun : sg = fun θ : ℝ => (Real.sin (2*θ))^(-(Work.Spaces.eta)) := sg_eq_lam
  rw [hfun]
  refine ContinuousOn.rpow_const
    ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn) ?_
  intro θ hθ
  exact Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
    (by linarith [hθ.2, Real.pi_pos])))

theorem cont_cot_Icc {δ : ℝ} (hδ : 0 < δ) (hδ4 : δ < Real.pi/4) :
    ContinuousOn (fun θ : ℝ => Real.cot (2*θ)) (Set.Icc δ (Real.pi/2-δ)) := by
  have hfun : (fun θ : ℝ => Real.cot (2*θ)) = fun θ : ℝ => Real.cos (2*θ)/Real.sin (2*θ) := by
    funext θ; rw [Real.cot_eq_cos_div_sin]
  rw [hfun]
  refine ContinuousOn.div ?_ ?_ ?_
  · exact (Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn
  · exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  · intro θ hθ
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos]))

theorem cont_csc2_Icc {δ : ℝ} (hδ : 0 < δ) (hδ4 : δ < Real.pi/4) :
    ContinuousOn (fun θ : ℝ => (Real.sin (2*θ))^(-(2:ℝ))) (Set.Icc δ (Real.pi/2-δ)) := by
  refine ContinuousOn.rpow_const
    ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn) ?_
  intro θ hθ
  exact Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
    (by linarith [hθ.2, Real.pi_pos])))

theorem cont_g_Icc {g : ℝ → ℝ} (hg : ContDiffOn ℝ 2 g (Set.Ioo 0 (Real.pi/2)))
    {δ : ℝ} (hδ : 0 < δ) (hδ4 : δ < Real.pi/4) :
    ContinuousOn g (Set.Icc δ (Real.pi/2-δ)) :=
  hg.continuousOn.mono fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩

theorem cont_dg_Icc {g : ℝ → ℝ} (hg : ContDiffOn ℝ 2 g (Set.Ioo 0 (Real.pi/2)))
    {δ : ℝ} (hδ : 0 < δ) (hδ4 : δ < Real.pi/4) :
    ContinuousOn (deriv g) (Set.Icc δ (Real.pi/2-δ)) :=
  ((hg.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)).continuousOn).mono
    fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩

/-- **The cot identity on a sub-interval.** -/
theorem ang_T_id_sub {g : ℝ → ℝ} (hg : ContDiffOn ℝ 2 g (Set.Ioo 0 (Real.pi/2)))
    {δ : ℝ} (hδ : 0 < δ) (hδ4 : δ < Real.pi/4) :
    (∫ θ in δ..(Real.pi/2-δ), sg θ * Real.cot (2*θ) * g θ * deriv g θ)
      = (sg (Real.pi/2-δ) * Real.cot (2*(Real.pi/2-δ)) * g (Real.pi/2-δ)^2
          - sg δ * Real.cot (2*δ) * g δ^2)/2
        + (∫ θ in δ..(Real.pi/2-δ),
            sg θ * (Work.Spaces.eta * (Real.cot (2*θ))^2 + (Real.sin (2*θ))^(-(2:ℝ))) * g θ^2) := by
  have hle : δ ≤ Real.pi/2 - δ := by linarith
  have hsub : Set.Icc δ (Real.pi/2-δ) ⊆ Set.Ioo (0:ℝ) (Real.pi/2) :=
    fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  -- work with `g θ * g θ` to keep the `HasDerivAt` shapes aligned
  have hgI : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2), HasDerivAt g (deriv g θ) θ :=
    fun θ hθ => (hg.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioo.mem_nhds hθ) |>.hasDerivAt
  set F : ℝ → ℝ := fun θ => sg θ * Real.cot (2*θ) * (g θ * g θ) with hFdef
  set F' : ℝ → ℝ := fun θ => 2 * (sg θ * Real.cot (2*θ) * (g θ * deriv g θ))
      - 2 * (sg θ * (Work.Spaces.eta * (Real.cot (2*θ))^2 + (Real.sin (2*θ))^(-(2:ℝ)))
        * (g θ * g θ)) with hF'def
  have hderiv : ∀ θ ∈ Set.Ioo δ (Real.pi/2-δ), HasDerivAt F (F' θ) θ := by
    intro θ hθ
    have hθ' : θ ∈ Set.Ioo (0:ℝ) (Real.pi/2) := hsub (Set.Ioo_subset_Icc_self hθ)
    have h1 := hgI θ hθ'
    have hprod : HasDerivAt (fun θ : ℝ => (sg θ * Real.cot (2*θ)) * (g θ * g θ))
        ((-(2*Work.Spaces.eta) * (Real.cot (2*θ) * sg θ) * Real.cot (2*θ)
            + sg θ * (-(2:ℝ) * (Real.sin (2*θ))^(-(2:ℝ)))) * (g θ * g θ)
          + (sg θ * Real.cot (2*θ)) * (deriv g θ * g θ + g θ * deriv g θ)) θ :=
      ((hasDerivAt_sg hθ').mul (hasDerivAt_cot_two hθ')).mul (h1.mul h1)
    have hfun : F = fun θ : ℝ => (sg θ * Real.cot (2*θ)) * (g θ * g θ) := rfl
    rw [hfun]
    refine hprod.congr_deriv ?_
    rw [hF'def]; ring_nf
  have hcot2c : ContinuousOn (fun θ : ℝ => Work.Spaces.eta * (Real.cot (2*θ))^2
      + (Real.sin (2*θ))^(-(2:ℝ))) (Set.Icc δ (Real.pi/2-δ)) :=
    (((cont_cot_Icc hδ hδ4).pow 2).const_mul _).add (cont_csc2_Icc hδ hδ4)
  have hAc : ContinuousOn (fun θ : ℝ => sg θ * Real.cot (2*θ) * (g θ * deriv g θ))
      (Set.Icc δ (Real.pi/2-δ)) :=
    ((cont_sg_Icc hδ hδ4).mul (cont_cot_Icc hδ hδ4)).mul
      ((cont_g_Icc hg hδ hδ4).mul (cont_dg_Icc hg hδ hδ4))
  have hBc : ContinuousOn (fun θ : ℝ => sg θ * (Work.Spaces.eta * (Real.cot (2*θ))^2
      + (Real.sin (2*θ))^(-(2:ℝ))) * (g θ * g θ)) (Set.Icc δ (Real.pi/2-δ)) :=
    ((cont_sg_Icc hδ hδ4).mul hcot2c).mul ((cont_g_Icc hg hδ hδ4).mul (cont_g_Icc hg hδ hδ4))
  have hcont : ContinuousOn F (Set.Icc δ (Real.pi/2-δ)) :=
    ((cont_sg_Icc hδ hδ4).mul (cont_cot_Icc hδ hδ4)).mul
      ((cont_g_Icc hg hδ hδ4).mul (cont_g_Icc hg hδ hδ4))
  have hF'cont : ContinuousOn F' (Set.Icc δ (Real.pi/2-δ)) := by
    have h1 : ContinuousOn (fun θ : ℝ => 2 * (sg θ * Real.cot (2*θ) * (g θ * deriv g θ)))
        (Set.Icc δ (Real.pi/2-δ)) := hAc.const_mul 2
    have h2 : ContinuousOn (fun θ : ℝ => 2 * (sg θ * (Work.Spaces.eta * (Real.cot (2*θ))^2
        + (Real.sin (2*θ))^(-(2:ℝ))) * (g θ * g θ))) (Set.Icc δ (Real.pi/2-δ)) := hBc.const_mul 2
    have h := h1.sub h2
    rw [hF'def]
    exact h
  have hint : IntervalIntegrable F' volume δ (Real.pi/2-δ) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hle]; exact hF'cont
  have hFTC : (∫ θ in δ..(Real.pi/2-δ), F' θ) = F (Real.pi/2-δ) - F δ :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hle hcont hderiv hint
  have hI1 : IntervalIntegrable (fun θ : ℝ => sg θ * Real.cot (2*θ) * (g θ * deriv g θ))
      volume δ (Real.pi/2-δ) :=
    ContinuousOn.intervalIntegrable (by rw [Set.uIcc_of_le hle]; exact hAc)
  have hI2 : IntervalIntegrable (fun θ : ℝ => sg θ * (Work.Spaces.eta * (Real.cot (2*θ))^2
      + (Real.sin (2*θ))^(-(2:ℝ))) * (g θ * g θ)) volume δ (Real.pi/2-δ) :=
    ContinuousOn.intervalIntegrable (by rw [Set.uIcc_of_le hle]; exact hBc)
  have hexp : (∫ θ in δ..(Real.pi/2-δ), F' θ)
      = 2 * (∫ θ in δ..(Real.pi/2-δ), sg θ * Real.cot (2*θ) * (g θ * deriv g θ))
        - 2 * (∫ θ in δ..(Real.pi/2-δ), sg θ * (Work.Spaces.eta * (Real.cot (2*θ))^2
            + (Real.sin (2*θ))^(-(2:ℝ))) * (g θ * g θ)) := by
    have h2 := hI2.const_mul (2:ℝ)
    have h1 := hI1.const_mul (2:ℝ)
    rw [hF'def, intervalIntegral.integral_sub (by simpa using h1) (by simpa using h2)]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hFend : F (Real.pi/2-δ)
      = sg (Real.pi/2-δ) * Real.cot (2*(Real.pi/2-δ)) * (g (Real.pi/2-δ) * g (Real.pi/2-δ)) := rfl
  have hFδ : F δ = sg δ * Real.cot (2*δ) * (g δ * g δ) := rfl
  rw [hexp] at hFTC
  rw [hFend, hFδ] at hFTC
  have hgoal : (∫ θ in δ..(Real.pi/2-δ), sg θ * Real.cot (2*θ) * (g θ * deriv g θ))
      = (sg (Real.pi/2-δ) * Real.cot (2*(Real.pi/2-δ)) * (g (Real.pi/2-δ) * g (Real.pi/2-δ))
          - sg δ * Real.cot (2*δ) * (g δ * g δ))/2
        + (∫ θ in δ..(Real.pi/2-δ), sg θ * (Work.Spaces.eta * (Real.cot (2*θ))^2
            + (Real.sin (2*θ))^(-(2:ℝ))) * (g θ * g θ)) := by linarith
  have hL : (∫ θ in δ..(Real.pi/2-δ), sg θ * Real.cot (2*θ) * g θ * deriv g θ)
      = (∫ θ in δ..(Real.pi/2-δ), sg θ * Real.cot (2*θ) * (g θ * deriv g θ)) := by
    refine intervalIntegral.integral_congr ?_
    intro θ _; ring
  have hR : (∫ θ in δ..(Real.pi/2-δ), sg θ * (Work.Spaces.eta * (Real.cot (2*θ))^2
        + (Real.sin (2*θ))^(-(2:ℝ))) * g θ^2)
      = (∫ θ in δ..(Real.pi/2-δ), sg θ * (Work.Spaces.eta * (Real.cot (2*θ))^2
        + (Real.sin (2*θ))^(-(2:ℝ))) * (g θ * g θ)) := by
    refine intervalIntegral.integral_congr ?_
    intro θ _; ring
  rw [hL, hR]
  have he1 : g (Real.pi/2-δ)^2 = g (Real.pi/2-δ) * g (Real.pi/2-δ) := by ring
  have he2 : g δ^2 = g δ * g δ := by ring
  rw [he1, he2]
  exact hgoal

/-- **The angular integration by parts on a sub-interval.** -/
theorem ang_ibp_sub {g : ℝ → ℝ} (hg : ContDiffOn ℝ 2 g (Set.Ioo 0 (Real.pi/2)))
    {δ : ℝ} (hδ : 0 < δ) (hδ4 : δ < Real.pi/4) :
    (∫ θ in δ..(Real.pi/2-δ), sg θ * (deriv g θ)^2)
      = sg (Real.pi/2-δ) * g (Real.pi/2-δ) * deriv g (Real.pi/2-δ)
        - sg δ * g δ * deriv g δ
        + 2*Work.Spaces.eta * (∫ θ in δ..(Real.pi/2-δ),
            sg θ * Real.cot (2*θ) * g θ * deriv g θ)
        - (∫ θ in δ..(Real.pi/2-δ), sg θ * g θ * deriv (deriv g) θ) := by
  have hle : δ ≤ Real.pi/2 - δ := by linarith
  have hsub : Set.Icc δ (Real.pi/2-δ) ⊆ Set.Ioo (0:ℝ) (Real.pi/2) :=
    fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hg1 : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2), HasDerivAt g (deriv g θ) θ :=
    fun θ hθ => (hg.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioo.mem_nhds hθ) |>.hasDerivAt
  have hg2 : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2), HasDerivAt (deriv g) (deriv (deriv g) θ) θ :=
    fun θ hθ => (((hg.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)).differentiableOn
      (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds hθ)) |>.hasDerivAt
  set F : ℝ → ℝ := fun θ => (sg θ * g θ) * deriv g θ with hFdef
  set F' : ℝ → ℝ := fun θ => -(2*Work.Spaces.eta) * (sg θ * (Real.cot (2*θ) * g θ) * deriv g θ)
      + (sg θ * deriv g θ * deriv g θ) + (sg θ * g θ * deriv (deriv g) θ) with hF'def
  have hderiv : ∀ θ ∈ Set.Ioo δ (Real.pi/2-δ), HasDerivAt F (F' θ) θ := by
    intro θ hθ
    have hθ' : θ ∈ Set.Ioo (0:ℝ) (Real.pi/2) := hsub (Set.Ioo_subset_Icc_self hθ)
    have hprod : HasDerivAt (fun θ : ℝ => (sg θ * g θ) * deriv g θ)
        ((-(2*Work.Spaces.eta) * (Real.cot (2*θ) * sg θ) * g θ + sg θ * deriv g θ) * deriv g θ
          + (sg θ * g θ) * deriv (deriv g) θ) θ :=
      ((hasDerivAt_sg hθ').mul (hg1 θ hθ')).mul (hg2 θ hθ')
    have hfun : F = fun θ : ℝ => (sg θ * g θ) * deriv g θ := rfl
    rw [hfun]
    refine hprod.congr_deriv ?_
    rw [hF'def]; ring
  have hAc : ContinuousOn (fun θ : ℝ => sg θ * (Real.cot (2*θ) * g θ) * deriv g θ)
      (Set.Icc δ (Real.pi/2-δ)) :=
    ((cont_sg_Icc hδ hδ4).mul ((cont_cot_Icc hδ hδ4).mul (cont_g_Icc hg hδ hδ4))).mul
      (cont_dg_Icc hg hδ hδ4)
  have hBc : ContinuousOn (fun θ : ℝ => sg θ * deriv g θ * deriv g θ) (Set.Icc δ (Real.pi/2-δ)) :=
    ((cont_sg_Icc hδ hδ4).mul (cont_dg_Icc hg hδ hδ4)).mul (cont_dg_Icc hg hδ hδ4)
  have hddg : ContinuousOn (deriv (deriv g)) (Set.Icc δ (Real.pi/2-δ)) :=
    ((hg.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)).continuousOn_deriv_of_isOpen
      isOpen_Ioo (le_refl 1)).mono (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩)
  have hCc : ContinuousOn (fun θ : ℝ => sg θ * g θ * deriv (deriv g) θ) (Set.Icc δ (Real.pi/2-δ)) :=
    ((cont_sg_Icc hδ hδ4).mul (cont_g_Icc hg hδ hδ4)).mul hddg
  have hcont : ContinuousOn F (Set.Icc δ (Real.pi/2-δ)) :=
    ((cont_sg_Icc hδ hδ4).mul (cont_g_Icc hg hδ hδ4)).mul (cont_dg_Icc hg hδ hδ4)
  have hF'cont : ContinuousOn F' (Set.Icc δ (Real.pi/2-δ)) := by
    have h1 : ContinuousOn (fun θ : ℝ => -(2*Work.Spaces.eta)
        * (sg θ * (Real.cot (2*θ) * g θ) * deriv g θ)) (Set.Icc δ (Real.pi/2-δ)) :=
      hAc.const_mul _
    have h12 := h1.add hBc
    have h := h12.add hCc
    rw [hF'def]
    exact h
  have hint : IntervalIntegrable F' volume δ (Real.pi/2-δ) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hle]; exact hF'cont
  have hFTC : (∫ θ in δ..(Real.pi/2-δ), F' θ) = F (Real.pi/2-δ) - F δ :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hle hcont hderiv hint
  have hI1 : IntervalIntegrable (fun θ : ℝ => sg θ * (Real.cot (2*θ) * g θ) * deriv g θ)
      volume δ (Real.pi/2-δ) :=
    ContinuousOn.intervalIntegrable (by rw [Set.uIcc_of_le hle]; exact hAc)
  have hI2 : IntervalIntegrable (fun θ : ℝ => sg θ * deriv g θ * deriv g θ)
      volume δ (Real.pi/2-δ) :=
    ContinuousOn.intervalIntegrable (by rw [Set.uIcc_of_le hle]; exact hBc)
  have hI3 : IntervalIntegrable (fun θ : ℝ => sg θ * g θ * deriv (deriv g) θ)
      volume δ (Real.pi/2-δ) :=
    ContinuousOn.intervalIntegrable (by rw [Set.uIcc_of_le hle]; exact hCc)
  have hexp : (∫ θ in δ..(Real.pi/2-δ), F' θ)
      = -(2*Work.Spaces.eta) * (∫ θ in δ..(Real.pi/2-δ), sg θ * (Real.cot (2*θ) * g θ) * deriv g θ)
        + (∫ θ in δ..(Real.pi/2-δ), sg θ * deriv g θ * deriv g θ)
        + (∫ θ in δ..(Real.pi/2-δ), sg θ * g θ * deriv (deriv g) θ) := by
    have h1 := hI1.const_mul (-(2*Work.Spaces.eta))
    have h12 : IntervalIntegrable (fun θ : ℝ => -(2*Work.Spaces.eta)
        * (sg θ * (Real.cot (2*θ) * g θ) * deriv g θ)
        + sg θ * deriv g θ * deriv g θ) volume δ (Real.pi/2-δ) := h1.add hI2
    rw [hF'def, intervalIntegral.integral_add h12 hI3]
    rw [intervalIntegral.integral_add h1 hI2, intervalIntegral.integral_const_mul]
  have hFend : F (Real.pi/2-δ)
      = sg (Real.pi/2-δ) * g (Real.pi/2-δ) * deriv g (Real.pi/2-δ) := rfl
  have hFδ : F δ = sg δ * g δ * deriv g δ := rfl
  rw [hexp] at hFTC
  rw [hFend, hFδ] at hFTC
  have hL : (∫ θ in δ..(Real.pi/2-δ), sg θ * (deriv g θ)^2)
      = (∫ θ in δ..(Real.pi/2-δ), sg θ * deriv g θ * deriv g θ) := by
    refine intervalIntegral.integral_congr ?_
    intro θ _; ring
  have hM : (∫ θ in δ..(Real.pi/2-δ), sg θ * Real.cot (2*θ) * g θ * deriv g θ)
      = (∫ θ in δ..(Real.pi/2-δ), sg θ * (Real.cot (2*θ) * g θ) * deriv g θ) := by
    refine intervalIntegral.integral_congr ?_
    intro θ _; ring
  have hN : (∫ θ in δ..(Real.pi/2-δ), sg θ * g θ * deriv (deriv g) θ)
      = (∫ θ in δ..(Real.pi/2-δ), sg θ * g θ * deriv (deriv g) θ) := rfl
  rw [hL, hM, hN]
  linarith

end Work.FTS.EllipticEst.RPFresh

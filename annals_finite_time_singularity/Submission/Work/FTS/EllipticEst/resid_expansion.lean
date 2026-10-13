import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.trig_resid
import Submission.Work.FTS.EllipticEst.ibp_contdiffon

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real
open MeasureTheory
open Set

namespace Work.FTS.EllipticEst

/-- If two functions agree on the open interval `uIoo a b`, they agree almost everywhere for the
measure restricted to `uIoc a b` (the endpoints have measure zero). -/
private lemma ae_eq_of_eqOn_uIoo {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (h : EqOn f g (Set.uIoo a b)) :
    f =ᵐ[volume.restrict (Set.uIoc a b)] g := by
  rw [Set.uIoc_of_le hab, ← restrict_Ioo_eq_restrict_Ioc]
  refine ae_restrict_of_forall_mem measurableSet_Ioo ?_
  intro x hx
  exact h (by rwa [Set.uIoo_of_le hab])

/-- **Residual expansion for the first sine mode on `[0, π/2]`.**

For `f ∈ C²` on `[0, π/2]` vanishing at both endpoints, the projection
`a = (4/π) ∫ f sin(2θ)` onto the mode `sin(2θ)` is exactly the `L²`-orthogonal one: the residual
`g = f - a sin(2θ)` is `L²`-orthogonal to `sin(2θ)` and to `2cos(2θ)` (its derivative), and the
`L²`-norms of `f`, `f'` decompose as `∫f² = (π/4)a² + ∫g²` and `∫(f')² = π a² + ∫(g')²`. -/
theorem resid_expansion (f : ℝ → ℝ) (hf : ContDiffOn ℝ 2 f (Set.Icc 0 (π / 2)))
    (h0 : f 0 = 0) (h1 : f (π / 2) = 0) :
    let a := (4 / π) * ∫ θ in (0:ℝ)..(π / 2), f θ * Real.sin (2 * θ)
    let g := fun θ => f θ - a * Real.sin (2 * θ)
    (∫ θ in (0:ℝ)..(π / 2), g θ * Real.sin (2 * θ) = 0) ∧
    (∫ θ in (0:ℝ)..(π / 2), deriv g θ * (2 * Real.cos (2 * θ)) = 0) ∧
    (∫ θ in (0:ℝ)..(π / 2), (f θ) ^ 2
        = (π / 4) * a ^ 2 + ∫ θ in (0:ℝ)..(π / 2), (g θ) ^ 2) ∧
    (∫ θ in (0:ℝ)..(π / 2), (deriv f θ) ^ 2
        = π * a ^ 2 + ∫ θ in (0:ℝ)..(π / 2), (deriv g θ) ^ 2) := by
  obtain ⟨T1, T2, T3, Dsin, Dcos⟩ := trig_resid
  set a : ℝ := (4 / π) * ∫ θ in (0:ℝ)..(π / 2), f θ * Real.sin (2 * θ) with ha_def
  set g : ℝ → ℝ := fun θ => f θ - a * Real.sin (2 * θ) with hg_def
  have hpi : (0:ℝ) < π/2 := by positivity
  have hpi_le : (0:ℝ) ≤ π/2 := hpi.le
  have hgpt : ∀ θ, g θ = f θ - a * Real.sin (2 * θ) := fun θ => by simp only [hg_def]
  have hsin2_CD : ContDiff ℝ 2 (fun θ : ℝ => Real.sin (2 * θ)) := by fun_prop
  have hpsi_CD : ContDiff ℝ 2 (fun θ : ℝ => 2 * Real.cos (2 * θ)) := by fun_prop
  have hgCD0 : ContDiffOn ℝ 2 (fun θ : ℝ => f θ - a * Real.sin (2 * θ)) (Set.Icc 0 (π/2)) :=
    hf.sub (ContDiffOn.const_smul a hsin2_CD.contDiffOn)
  have hgCD : ContDiffOn ℝ 2 g (Set.Icc 0 (π/2)) := hgCD0.congr (fun θ _ => hgpt θ)
  have hcont_f : ContinuousOn f (Set.uIcc 0 (π/2)) := by
    rw [Set.uIcc_of_le hpi_le]; exact hf.continuousOn
  have hcont_g : ContinuousOn g (Set.uIcc 0 (π/2)) := by
    rw [Set.uIcc_of_le hpi_le]; exact hgCD.continuousOn
  have hcont_sin2 : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.uIcc 0 (π/2)) := by fun_prop
  have hg0 : g 0 = 0 := by
    rw [hgpt 0, h0, show (2:ℝ)*0 = 0 by ring, Real.sin_zero, mul_zero, sub_zero]
  have hg1 : g (π/2) = 0 := by
    rw [hgpt (π/2), h1, show (2:ℝ)*(π/2) = π by ring, Real.sin_pi, mul_zero, sub_zero]
  have hcdg : ContinuousOn (derivWithin g (Set.Icc 0 (π/2))) (Set.uIcc 0 (π/2)) := by
    rw [Set.uIcc_of_le hpi_le]
    exact hgCD.continuousOn_derivWithin (uniqueDiffOn_Icc hpi) (by norm_num)
  ----------------------------------------------------------------
  -- (1) orthogonality of the residual to sin(2θ)
  have hInt_fs : IntervalIntegrable (fun θ : ℝ => f θ * Real.sin (2*θ)) volume 0 (π/2) :=
    (hcont_f.mul hcont_sin2).intervalIntegrable
  have ha_pi4 : a * (π/4) = ∫ θ in (0:ℝ)..(π/2), f θ * Real.sin (2*θ) := by
    rw [ha_def]
    field_simp
  have h1main : ∫ θ in (0:ℝ)..(π/2), g θ * Real.sin (2*θ) = 0 := by
    have hc : ∫ θ in (0:ℝ)..(π/2), g θ * Real.sin (2*θ)
        = ∫ θ in (0:ℝ)..(π/2), f θ * Real.sin (2*θ) - a * (Real.sin (2*θ))^2 := by
      apply intervalIntegral.integral_congr
      intro θ _
      dsimp only
      rw [hgpt θ]; ring
    have hInt_a : IntervalIntegrable (fun θ : ℝ => a * (Real.sin (2*θ))^2) volume 0 (π/2) := by
      have hc2 : ContinuousOn (fun θ : ℝ => a * (Real.sin (2*θ))^2) (Set.uIcc 0 (π/2)) := by fun_prop
      exact hc2.intervalIntegrable
    rw [hc, intervalIntegral.integral_sub hInt_fs hInt_a, intervalIntegral.integral_const_mul,
      T1, ha_pi4]
    ring
  ----------------------------------------------------------------
  -- (2) orthogonality of d/dθ residual to 2cos(2θ)
  have hpsi_pi : (2:ℝ) * Real.cos (2*(π/2)) = -2 := by
    rw [show (2:ℝ)*(π/2) = π by ring, Real.cos_pi]; ring
  have hpsi_0 : (2:ℝ) * Real.cos (2*0) = 2 := by
    rw [show (2:ℝ)*0 = 0 by ring, Real.cos_zero]; ring
  have hderivpsi : deriv (fun θ : ℝ => 2 * Real.cos (2*θ)) = fun θ => -4 * Real.sin (2*θ) := by
    funext θ; exact Dcos θ
  have h2main : ∫ θ in (0:ℝ)..(π/2), deriv g θ * (2 * Real.cos (2*θ)) = 0 := by
    have hIBP := ibp_contdiffon hpi hgCD hpsi_CD
    have hcross : ∫ x in (0:ℝ)..(π/2), g x * (-4 * Real.sin (2*x)) = 0 := by
      rw [show (∫ x in (0:ℝ)..(π/2), g x * (-4 * Real.sin (2*x)))
          = ∫ x in (0:ℝ)..(π/2), (-4) * (g x * Real.sin (2*x)) by
        apply intervalIntegral.integral_congr; intro x _; dsimp only; ring]
      rw [intervalIntegral.integral_const_mul, h1main]
      ring
    rw [hIBP, hderivpsi]
    dsimp only
    rw [hpsi_pi, hpsi_0, hg1, hg0, hcross]
    ring
  ----------------------------------------------------------------
  -- (3) L² decomposition of f
  have h3main : ∫ θ in (0:ℝ)..(π/2), (f θ)^2
      = (π/4) * a^2 + ∫ θ in (0:ℝ)..(π/2), (g θ)^2 := by
    have hexp : ∫ θ in (0:ℝ)..(π/2), (f θ)^2
        = ∫ θ in (0:ℝ)..(π/2), (g θ)^2 + 2*a*(g θ * Real.sin (2*θ)) + a^2*(Real.sin (2*θ))^2 := by
      apply intervalIntegral.integral_congr
      intro θ _
      dsimp only
      rw [show f θ = g θ + a * Real.sin (2*θ) by rw [hgpt θ]; ring]
      ring
    have hX : IntervalIntegrable (fun θ : ℝ => (g θ)^2) volume 0 (π/2) :=
      (hcont_g.pow 2).intervalIntegrable
    have hY : IntervalIntegrable (fun θ : ℝ => 2*a*(g θ * Real.sin (2*θ))) volume 0 (π/2) := by
      have hc2 : ContinuousOn (fun θ : ℝ => 2*a*(g θ * Real.sin (2*θ))) (Set.uIcc 0 (π/2)) := by fun_prop
      exact hc2.intervalIntegrable
    have hZ : IntervalIntegrable (fun θ : ℝ => a^2*(Real.sin (2*θ))^2) volume 0 (π/2) := by
      have hc2 : ContinuousOn (fun θ : ℝ => a^2*(Real.sin (2*θ))^2) (Set.uIcc 0 (π/2)) := by fun_prop
      exact hc2.intervalIntegrable
    rw [hexp, intervalIntegral.integral_add (hX.add hY) hZ, intervalIntegral.integral_add hX hY,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, T1, h1main]
    ring
  ----------------------------------------------------------------
  -- (4) L² decomposition of the derivative
  have hderiv_pt : ∀ θ ∈ Set.Ioo (0:ℝ) (π/2),
      deriv f θ = deriv g θ + 2*a*Real.cos (2*θ) := by
    intro θ hθ
    have hfeq : f = fun θ : ℝ => g θ + a * Real.sin (2 * θ) := by
      funext x; rw [hgpt x]; ring
    have hgd : DifferentiableAt ℝ g θ :=
      (hgCD.contDiffAt (Icc_mem_nhds hθ.1 hθ.2)).differentiableAt (by norm_num)
    have hsd : DifferentiableAt ℝ (fun θ : ℝ => a * Real.sin (2*θ)) θ := by fun_prop
    have hsd' : DifferentiableAt ℝ (fun θ : ℝ => Real.sin (2*θ)) θ := by fun_prop
    rw [hfeq]
    change deriv (g + fun θ : ℝ => a * Real.sin (2*θ)) θ = deriv g θ + 2*a*Real.cos (2*θ)
    rw [deriv_add hgd hsd, deriv_const_mul a hsd', Dsin θ]
    ring
  have hU : ∫ θ in (0:ℝ)..(π/2), (derivWithin g (Set.Icc 0 (π/2)) θ)^2
      = ∫ θ in (0:ℝ)..(π/2), (deriv g θ)^2 := by
    apply intervalIntegral.integral_congr_ae_restrict
    refine ae_eq_of_eqOn_uIoo hpi_le ?_
    intro x hx
    rw [Set.uIoo_of_le hpi_le] at hx
    dsimp only
    rw [derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)]
  have h1_4 : ∫ θ in (0:ℝ)..(π/2), (deriv f θ)^2
      = ∫ θ in (0:ℝ)..(π/2), (deriv g θ + 2*a*Real.cos (2*θ))^2 := by
    apply intervalIntegral.integral_congr_ae_restrict
    refine ae_eq_of_eqOn_uIoo hpi_le ?_
    intro x hx
    rw [Set.uIoo_of_le hpi_le] at hx
    dsimp only
    rw [hderiv_pt x hx]
  have h2_4 : ∫ θ in (0:ℝ)..(π/2), (deriv g θ + 2*a*Real.cos (2*θ))^2
      = ∫ θ in (0:ℝ)..(π/2), (derivWithin g (Set.Icc 0 (π/2)) θ + 2*a*Real.cos (2*θ))^2 := by
    apply intervalIntegral.integral_congr_ae_restrict
    refine ae_eq_of_eqOn_uIoo hpi_le ?_
    intro x hx
    rw [Set.uIoo_of_le hpi_le] at hx
    dsimp only
    rw [derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)]
  have hzero : ∫ θ in (0:ℝ)..(π/2), (derivWithin g (Set.Icc 0 (π/2)) θ) * (2*Real.cos (2*θ)) = 0 := by
    have hc : ∫ θ in (0:ℝ)..(π/2), (derivWithin g (Set.Icc 0 (π/2)) θ) * (2*Real.cos (2*θ))
        = ∫ θ in (0:ℝ)..(π/2), deriv g θ * (2*Real.cos (2*θ)) := by
      apply intervalIntegral.integral_congr_ae_restrict
      refine ae_eq_of_eqOn_uIoo hpi_le ?_
      intro x hx
      rw [Set.uIoo_of_le hpi_le] at hx
      dsimp only
      rw [derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)]
    rw [hc, h2main]
  have hexp4 : ∫ θ in (0:ℝ)..(π/2), (derivWithin g (Set.Icc 0 (π/2)) θ + 2*a*Real.cos (2*θ))^2
      = ∫ θ in (0:ℝ)..(π/2), (derivWithin g (Set.Icc 0 (π/2)) θ)^2
          + 2*a*((derivWithin g (Set.Icc 0 (π/2)) θ) * (2*Real.cos (2*θ)))
          + a^2*(2*Real.cos (2*θ))^2 := by
    apply intervalIntegral.integral_congr
    intro θ _
    dsimp only
    ring
  have h4main : ∫ θ in (0:ℝ)..(π/2), (deriv f θ)^2 = π*a^2 + ∫ θ in (0:ℝ)..(π/2), (deriv g θ)^2 := by
    have hIU : IntervalIntegrable
        (fun θ : ℝ => (derivWithin g (Set.Icc 0 (π/2)) θ)^2) volume 0 (π/2) :=
      (hcdg.pow 2).intervalIntegrable
    have hIY : IntervalIntegrable
        (fun θ : ℝ => 2*a*((derivWithin g (Set.Icc 0 (π/2)) θ) * (2*Real.cos (2*θ)))) volume 0 (π/2) := by
      have hc2 : ContinuousOn
          (fun θ : ℝ => 2*a*((derivWithin g (Set.Icc 0 (π/2)) θ) * (2*Real.cos (2*θ))))
          (Set.uIcc 0 (π/2)) := by fun_prop
      exact hc2.intervalIntegrable
    have hIZ : IntervalIntegrable (fun θ : ℝ => a^2*(2*Real.cos (2*θ))^2) volume 0 (π/2) := by
      have hc2 : ContinuousOn (fun θ : ℝ => a^2*(2*Real.cos (2*θ))^2) (Set.uIcc 0 (π/2)) := by fun_prop
      exact hc2.intervalIntegrable
    rw [h1_4, h2_4, hexp4, intervalIntegral.integral_add (hIU.add hIY) hIZ,
      intervalIntegral.integral_add hIU hIY, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, hzero, T3, hU]
    ring
  exact ⟨h1main, h2main, h3main, h4main⟩

end Work.FTS.EllipticEst

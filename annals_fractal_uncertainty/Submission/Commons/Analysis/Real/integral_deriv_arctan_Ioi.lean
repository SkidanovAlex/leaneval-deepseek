import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

namespace Commons.Analysis.Real

open MeasureTheory

/-- For positive `σ` and `u`, `π/2 - arctan (u/σ) = arctan (σ/u)`. -/
lemma arctan_sigma_div {σ u : ℝ} (hσ : 0 < σ) (hu : 0 < u) :
    Real.pi / 2 - Real.arctan (u / σ) = Real.arctan (σ / u) := by
  rw [← Real.arctan_inv_of_pos (show (0:ℝ) < u / σ by positivity), inv_div]

theorem integral_deriv_arctan_Ioi {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) (hs : HasCompactSupport g)
    {σ : ℝ} (hσ : 0 < σ) :
    ∫ u in Set.Ioi (0:ℝ), deriv g u * Real.arctan (σ / u)
      = -(Real.pi / 2) * g 0 + σ * ∫ u in Set.Ioi (0:ℝ), g u / (σ^2 + u^2) := by
  set ψ : ℝ → ℝ := fun u => Real.pi / 2 - Real.arctan (u / σ) with hψdef
  have hψderiv : ∀ u, HasDerivAt ψ (-σ / (σ ^ 2 + u ^ 2)) u := by
    intro u
    rw [hψdef]
    have hinner : HasDerivAt (fun u : ℝ => u / σ) (1 / σ) u := by
      simpa using (hasDerivAt_id u).div_const σ
    have hcomp : HasDerivAt (fun u : ℝ => Real.arctan (u / σ))
        ((1 / (1 + (u / σ) ^ 2)) * (1 / σ)) u := by
      have h0 := (Real.hasDerivAt_arctan (u / σ)).comp u hinner
      simpa only [Function.comp_def] using h0
    have h := (hasDerivAt_const u (Real.pi / 2)).sub hcomp
    have heq : (-σ / (σ ^ 2 + u ^ 2)) = 0 - (1 / (1 + (u / σ) ^ 2)) * (1 / σ) := by
      field_simp
      ring
    rw [heq]
    exact h
  have hψcont : Continuous ψ := by rw [hψdef]; fun_prop
  have hψcd : ContDiff ℝ 1 ψ := by
    rw [hψdef]
    exact contDiff_const.sub ((Real.contDiff_arctan (n := 1)).comp (contDiff_id.div_const σ))
  have hderivψ : deriv ψ = fun u => -σ / (σ ^ 2 + u ^ 2) := by
    funext u; exact (hψderiv u).deriv
  have hcont_r : Continuous (fun u : ℝ => -σ / (σ ^ 2 + u ^ 2)) := by
    rw [← hderivψ]; exact hψcd.continuous_deriv le_rfl
  set F : ℝ → ℝ := fun u => g u * ψ u with hFdef
  have hFcd : ContDiff ℝ 1 F := by rw [hFdef]; exact hg.mul hψcd
  have hFsupp : HasCompactSupport F := by rw [hFdef]; exact hs.mul_right
  have hIntF : ∫ u in Set.Ioi (0:ℝ), deriv F u = -(Real.pi / 2) * g 0 := by
    rw [hFsupp.integral_Ioi_deriv_eq hFcd 0]
    simp only [hFdef, hψdef]
    norm_num
    ring
  have hderivF_eq : ∀ u, deriv F u = deriv g u * ψ u + g u * (-σ / (σ ^ 2 + u ^ 2)) := by
    intro u
    have hg' : HasDerivAt g (deriv g u) u :=
      (hg.differentiable one_ne_zero).differentiableAt.hasDerivAt
    have hprod' : HasDerivAt (fun u : ℝ => g u * ψ u)
        (deriv g u * ψ u + g u * (-σ / (σ ^ 2 + u ^ 2))) u := hg'.mul (hψderiv u)
    rw [hFdef]
    exact hprod'.deriv
  have integ1 : Integrable (fun u => deriv g u * ψ u) volume :=
    Continuous.integrable_of_hasCompactSupport
      ((hg.continuous_deriv le_rfl).mul hψcont) hs.deriv.mul_right
  have integ2 : Integrable (fun u => g u * (-σ / (σ ^ 2 + u ^ 2))) volume :=
    Continuous.integrable_of_hasCompactSupport (hg.continuous.mul hcont_r) hs.mul_right
  have stepA : ∫ u in Set.Ioi (0:ℝ), deriv F u
      = (∫ u in Set.Ioi (0:ℝ), deriv g u * ψ u)
        + (∫ u in Set.Ioi (0:ℝ), g u * (-σ / (σ ^ 2 + u ^ 2))) := by
    rw [show ∫ u in Set.Ioi (0:ℝ), deriv F u
          = ∫ u in Set.Ioi (0:ℝ), (deriv g u * ψ u + g u * (-σ / (σ ^ 2 + u ^ 2))) from
        setIntegral_congr_fun measurableSet_Ioi (fun u _ => hderivF_eq u)]
    exact integral_add (integ1.integrableOn (s := Set.Ioi 0)) (integ2.integrableOn (s := Set.Ioi 0))
  have eqA : ∫ u in Set.Ioi (0:ℝ), deriv g u * ψ u
      = ∫ u in Set.Ioi (0:ℝ), deriv g u * Real.arctan (σ / u) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_)
    show deriv g u * ψ u = deriv g u * Real.arctan (σ / u)
    have : ψ u = Real.arctan (σ / u) := by
      simpa only [hψdef] using arctan_sigma_div hσ (Set.mem_Ioi.mp hu)
    rw [this]
  have stepC : ∫ u in Set.Ioi (0:ℝ), g u * (-σ / (σ ^ 2 + u ^ 2))
      = -σ * ∫ u in Set.Ioi (0:ℝ), g u / (σ ^ 2 + u ^ 2) := by
    rw [show ∫ u in Set.Ioi (0:ℝ), g u * (-σ / (σ ^ 2 + u ^ 2))
          = ∫ u in Set.Ioi (0:ℝ), (-σ) * (g u / (σ ^ 2 + u ^ 2)) from
        setIntegral_congr_fun measurableSet_Ioi (fun u _ => by ring)]
    rw [integral_const_mul]
  have hmain : ∫ u in Set.Ioi (0:ℝ), deriv g u * ψ u
      = -(Real.pi / 2) * g 0 + σ * ∫ u in Set.Ioi (0:ℝ), g u / (σ ^ 2 + u ^ 2) := by
    rw [← hIntF, stepA, stepC]
    ring
  rw [← eqA]
  exact hmain

end Commons.Analysis.Real
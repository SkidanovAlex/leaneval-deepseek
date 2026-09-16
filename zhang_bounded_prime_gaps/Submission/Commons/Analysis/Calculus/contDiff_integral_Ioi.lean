import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace Commons.Analysis.Calculus

open MeasureTheory intervalIntegral Set Filter
open scoped ContDiff Topology

/-- The primitive `x ↦ ∫ s in a..x, f s` of a smooth function with values in a complete
normed space is smooth. -/
theorem contDiff_intervalIntegral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : ℝ → E) (a : ℝ) (hsm : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun x => ∫ s in a..x, f s) := by
  have hcont : Continuous f := hsm.continuous
  have hderiv : deriv (fun u => ∫ s in a..u, f s) = f := by
    funext x
    exact intervalIntegral.deriv_integral_right (hcont.intervalIntegrable a x)
      (hcont.stronglyMeasurableAtFilter volume (𝓝 x)) hcont.continuousAt
  have hdiff : Differentiable ℝ (fun u => ∫ s in a..u, f s) :=
    intervalIntegral.differentiable_integral_of_continuous hcont
  rw [contDiff_infty_iff_deriv]
  exact ⟨hdiff, by rw [hderiv]; exact hsm⟩

/-- Smoothness of the tail integral of a smooth compactly supported function. -/
theorem contDiff_integral_Ioi (f : ℝ → ℝ) (hcs : HasCompactSupport f)
    (hsm : ContDiff ℝ (↑(⊤ : ℕ∞)) f) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => ∫ s in Set.Ioi x, f s) := by
  have hcont : Continuous f := hsm.continuous
  have hint : Integrable f volume := hcont.integrable_of_hasCompactSupport hcs
  have hψ : ContDiff ℝ ∞ (fun u => ∫ s in (0:ℝ)..u, f s) :=
    contDiff_intervalIntegral f 0 hsm
  have hrel : ∀ x, ∫ s in Set.Ioi x, f s = (∫ s in Set.Ioi (0:ℝ), f s) - ∫ s in (0:ℝ)..x, f s := by
    intro x
    have h1 : IntegrableOn f (Set.Ioi (0:ℝ)) volume := hint.integrableOn
    have h2 : IntegrableOn f (Set.Ioi x) volume := hint.integrableOn
    have := intervalIntegral.integral_interval_add_Ioi h1 h2
    linarith
  have hfun : (fun x => ∫ s in Set.Ioi x, f s)
      = (fun _ : ℝ => ∫ s in Set.Ioi (0:ℝ), f s) - (fun u => ∫ s in (0:ℝ)..u, f s) := by
    funext x; rw [Pi.sub_apply]; exact hrel x
  rw [hfun]
  exact ContDiff.sub contDiff_const hψ

end Commons.Analysis.Calculus
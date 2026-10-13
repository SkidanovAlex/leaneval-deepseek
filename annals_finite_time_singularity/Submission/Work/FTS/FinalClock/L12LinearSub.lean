import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Construction.Defs
import Submission.Work.FM.Core
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace Work.FTS.FinalClock

/-- `L₁₂`-density of a pointwise negation is the negation of the density.  The angular integral is
`MeasureTheory.integral_neg`, which needs no integrability (the Bochner integral is total). -/
theorem L12dens_neg' {K : ℝ → ℝ} {f : ℝ → ℝ → ℝ} {s : ℝ} :
    Work.FM.L12dens K (fun s' θ => -f s' θ) s = -(Work.FM.L12dens K f s) := by
  have h : (fun θ : ℝ => K θ * (-f s θ) / s) = fun θ : ℝ => -(K θ * f s θ / s) := by
    funext θ
    ring
  rw [Work.FM.L12dens, Work.FM.L12dens, h]
  exact MeasureTheory.integral_neg (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    (f := fun θ : ℝ => K θ * f s θ / s)

/-- `L₁₂` of a pointwise negation is the negation of `L₁₂`. -/
theorem L12_neg' {K : ℝ → ℝ} {f : ℝ → ℝ → ℝ} {z : ℝ} :
    Work.FM.L12 K (fun s θ => -f s θ) z = -(Work.FM.L12 K f z) := by
  rw [Work.FM.L12, Work.FM.L12]
  simp only [L12dens_neg']
  exact MeasureTheory.integral_neg (μ := MeasureTheory.volume.restrict (Set.Ioi z))
    (f := fun s : ℝ => Work.FM.L12dens K f s)

theorem L12LinearSub {f₁ f₂ : ℝ → ℝ → ℝ} {z : ℝ}
    (h1 : ∀ s : ℝ, MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Spaces.K θ * f₁ s θ / s) Work.Spaces.Iθ)
    (h2 : ∀ s : ℝ, MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Spaces.K θ * f₂ s θ / s) Work.Spaces.Iθ)
    (hF1 : MeasureTheory.IntegrableOn (Work.FM.L12dens Work.Spaces.K f₁) (Set.Ioi z))
    (hF2 : MeasureTheory.IntegrableOn (Work.FM.L12dens Work.Spaces.K f₂) (Set.Ioi z)) :
    Work.Construction.L12 f₁ z - Work.Construction.L12 f₂ z
      = Work.Construction.L12 (fun s θ => f₁ s θ - f₂ s θ) z := by
  have h2' : ∀ s : ℝ,
      MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Spaces.K θ * (-f₂ s θ) / s) Work.Spaces.Iθ := by
    intro s
    refine ((h2 s).neg).congr ?_
    filter_upwards with θ
    rw [Pi.neg_apply]
    ring
  have hF2' : MeasureTheory.IntegrableOn
      (Work.FM.L12dens Work.Spaces.K (fun s θ => -f₂ s θ)) (Set.Ioi z) := by
    refine (MeasureTheory.IntegrableOn.neg hF2).congr ?_
    filter_upwards with s
    exact (L12dens_neg' (K := Work.Spaces.K) (f := f₂) (s := s)).symm
  have hadd := Work.FM.L12_add (K := Work.Spaces.K) (f := f₁)
    (g := fun s θ => -f₂ s θ) h1 h2' hF1 hF2'
  rw [Work.Construction.L12, Work.Construction.L12, Work.Construction.L12]
  have hsub : (fun s θ => f₁ s θ - f₂ s θ) = fun s θ => f₁ s θ + -f₂ s θ := rfl
  rw [hsub, hadd, L12_neg']
  ring

end Work.FTS.FinalClock

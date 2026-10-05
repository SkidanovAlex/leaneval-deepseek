import Mathlib
import Submission.Work.RPB1a.Defs

namespace Work.RPB1a

open Complex Set Metric
open scoped ContDiff Real
open Work.RPB1a

/-- The annulus `ρ < |w| < ρ⁻¹` is an open subset of `ℂ`. -/
private theorem annulus_isOpen (ρ : ℝ) : IsOpen (annulus ρ) := by
  have h1 : IsOpen {w : ℂ | ρ < ‖w‖} := isOpen_lt continuous_const continuous_norm
  have h2 : IsOpen {w : ℂ | ‖w‖ < ρ⁻¹} := isOpen_lt continuous_norm continuous_const
  have h : annulus ρ = {w : ℂ | ρ < ‖w‖} ∩ {w : ℂ | ‖w‖ < ρ⁻¹} := rfl
  rw [h]; exact h1.inter h2

/-- `w ↦ w⁻¹` preserves the inversion-symmetric annulus `annulus ρ`. -/
private theorem inv_mapsTo_annulus {ρ : ℝ} (hρ : 0 < ρ) :
    MapsTo (fun w : ℂ => w⁻¹) (annulus ρ) (annulus ρ) := by
  intro w hw
  obtain ⟨h1, h2⟩ := hw
  have hwpos : 0 < ‖w‖ := lt_trans hρ h1
  have hrhop : 0 < ρ⁻¹ := inv_pos.mpr hρ
  rw [annulus, Set.mem_ofPred_eq, norm_inv]
  refine ⟨?_, ?_⟩
  · have : (ρ⁻¹)⁻¹ < ‖w‖⁻¹ := (inv_lt_inv₀ hrhop hwpos).mpr h2
    simpa using this
  · exact (inv_lt_inv₀ hwpos hρ).mpr h1

/-- The flip `w ↦ w⁻¹` of a collar map `Γ`, on whose collar `Γ` is injective with
non-vanishing derivative, is again injective with non-vanishing derivative. -/
theorem flip_collar_data {Γ : ℂ → ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hΓd : DifferentiableOn ℂ Γ (annulus ρ)) (hΓi : InjOn Γ (annulus ρ))
    (hΓ' : ∀ w ∈ annulus ρ, deriv Γ w ≠ 0) :
    DifferentiableOn ℂ (fun w : ℂ => Γ w⁻¹) (annulus ρ) ∧
      InjOn (fun w : ℂ => Γ w⁻¹) (annulus ρ) ∧
      (∀ w ∈ annulus ρ, deriv (fun w : ℂ => Γ w⁻¹) w ≠ 0) := by
  have hmaps : MapsTo (fun w : ℂ => w⁻¹) (annulus ρ) (annulus ρ) := inv_mapsTo_annulus hρ
  have hopen : IsOpen (annulus ρ) := annulus_isOpen ρ
  refine ⟨?_, ?_, ?_⟩
  · -- differentiability of the flip: chain rule with `w ↦ w⁻¹` on the collar
    have hinv : DifferentiableOn ℂ (fun w : ℂ => w⁻¹) (annulus ρ) :=
      differentiableOn_inv.mono (fun x hx => by
        rw [annulus, Set.mem_ofPred_eq] at hx
        intro h
        have : ‖x‖ = 0 := by rw [h]; simp
        linarith [hρ, hx.1])
    have hcomp := hΓd.comp hinv hmaps
    simpa [Function.comp_def] using hcomp
  · -- injectivity: `Γ` injective on the collar and `w ↦ w⁻¹` injective
    intro a ha b hb hab
    have ha' : a⁻¹ ∈ annulus ρ := hmaps ha
    have hb' : b⁻¹ ∈ annulus ρ := hmaps hb
    exact inv_inj.mp (hΓi ha' hb' hab)
  · -- non-vanishing derivative: chain rule and `deriv Γ ≠ 0` on the collar
    intro w hw
    have hwne : w ≠ 0 := by
      rw [annulus, Set.mem_ofPred_eq] at hw
      intro h
      have : ‖w‖ = 0 := by rw [h]; simp
      linarith [hρ, hw.1]
    have hwa : w⁻¹ ∈ annulus ρ := hmaps hw
    have hΓat : DifferentiableAt ℂ Γ (w⁻¹) := hΓd.differentiableAt (hopen.mem_nhds hwa)
    have hinvat : DifferentiableAt ℂ (fun z : ℂ => z⁻¹) w := differentiableAt_inv hwne
    have hcomp : deriv (fun w : ℂ => Γ w⁻¹) w
        = deriv Γ (w⁻¹) * deriv (fun z : ℂ => z⁻¹) w := by
      have := deriv_comp w hΓat hinvat
      simpa [Function.comp_def] using this
    rw [hcomp, deriv_inv]
    exact mul_ne_zero (hΓ' (w⁻¹) hwa) (by simp [hwne])

end Work.RPB1a

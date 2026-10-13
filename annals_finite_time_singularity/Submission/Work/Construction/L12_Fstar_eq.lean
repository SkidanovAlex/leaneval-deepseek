import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Construction.Defs
import Submission.Work.FM.Core
import Submission.Work.Spaces.c_bounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `L₁₂(F_*) = 2α/(1+z)`

For the profile `F_*(z,θ) = α (Γ(θ)/c(α)) 2z/(1+z)²` of Elgindi's paper the integral
operator `L₁₂` collapses to the elementary function `2α/(1+z)`.  The proof separates
variables (`F_* = g(z) Γ(θ)` with `g = α · 2z/(1+z)²/c(α)`), uses
`∫₀^{π/2} K Γ = c(α) ≠ 0` and the improper integral `∫_z^∞ F_*(s)/s ds = 2/(1+z)`
(`Work.FM.integral_Ioi_Fstar_div`).
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Construction

/-- The angular density of `L₁₂` at the profile `F_*` is `α · F_*(s)/s`; the angular
integral contributes `∫₀^{π/2} K(θ)Γ(θ) dθ = c(α)` against the normalisation `1/c(α)` of
`F_*`. -/
theorem L12dens_Fstar {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (s : ℝ) :
    L12dens (Fstar α) s = α * (Work.FM.Fstar s / s) := by
  have hc : Work.Spaces.c α ≠ 0 := by
    have h := (Work.Spaces.c_bounds α hα hα1).1
    intro h0
    rw [h0] at h
    norm_num at h
  rw [L12dens, Work.FM.L12dens]
  have hpoint : ∀ θ : ℝ, Work.Spaces.K θ * Fstar α s θ / s
      = (α * (Work.Spaces.Gam α θ * Work.Spaces.K θ) / Work.Spaces.c α)
          * (Work.FM.Fstar s / s) := by
    intro θ
    simp only [Fstar]
    ring
  rw [setIntegral_congr_fun (s := Set.Icc 0 (Real.pi / 2)) measurableSet_Icc
        (fun θ _ => hpoint θ)]
  rw [integral_mul_const]
  have hcint : (∫ θ in Set.Icc 0 (Real.pi / 2),
        α * (Work.Spaces.Gam α θ * Work.Spaces.K θ) / Work.Spaces.c α) = α := by
    rw [integral_div, integral_const_mul]
    have hval : (∫ θ in Set.Icc 0 (Real.pi / 2),
        Work.Spaces.Gam α θ * Work.Spaces.K θ) = Work.Spaces.c α := rfl
    rw [hval, mul_div_assoc, div_self hc, mul_one]
  rw [hcint]

theorem L12_Fstar_eq {α z : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hz : 0 ≤ z) :
    Work.Construction.L12 (Work.Construction.Fstar α) z = 2 * α / (1 + z) := by
  rw [L12, Work.FM.L12]
  rw [setIntegral_congr_fun (s := Set.Ioi z) measurableSet_Ioi
        (fun s _ => show Work.FM.L12dens Work.Spaces.K (Fstar α) s
            = α * (Work.FM.Fstar s / s) from L12dens_Fstar hα hα1 s)]
  rw [integral_const_mul, Work.FM.integral_Ioi_Fstar_div z hz]
  ring

end Work.Construction

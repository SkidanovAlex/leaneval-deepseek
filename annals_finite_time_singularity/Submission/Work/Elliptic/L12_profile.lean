/-
Copyright: work module for the Elgindi finite-time singularity project.

# `L₁₂` of the fundamental profile: `L₁₂(F_*) = 2α/(1+z)`

Elgindi, Annals 194 (3) 2021, §'Elliptic Regularity Estimates' / §'Some useful facts':
with `Γ(θ) = (sin θ cos²θ)^{α/3}`, `c = ∫_0^{π/2} Γ K` and `F_*(z) = 2z/(1+z)²`, the profile

  `F_*^{(paper)}(z,θ) = α (Γ(θ)/c) F_*(z)`

satisfies `L₁₂(F_*) (z) = 2α/(1+z)`.  This is the identity used at tex 1176
(`Proposition PhiStarRegularity`) and in §Modulation (tex 1385: `L₁₂(F_*) = 2α/(1+z)`), and it is
what makes `L₁₂(F_*) ∈ 𝒲^{5,∞}` with norm `O(α)`.

The proof is immediate from the definitions: `K = 3 sinθcos²θ`, so the angular integral of the
profile against `K` is `α F_*(z)` (the normalisation `c = ∫ΓK` cancels), and

  `∫_z^∞ F_*(s)/s ds = ∫_z^∞ 2/(1+s)² ds = 2/(1+z)`
-/
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.Interval.Basic
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.c_bounds
import Submission.Work.FM.Defs
import Submission.Work.FM.Core

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false

/-- `L₁₂` of the fundamental profile `α (Γ(θ)/c) F_*(z)` equals `2α/(1+z)`. -/
theorem L12_profile (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (z : ℝ) (hz : 0 ≤ z) :
    L12 (fun w θ => α * (Work.Spaces.Gam α θ / Work.Spaces.c α) * Work.FM.Fstar w) z
      = 2 * α / (1 + z) := by
  have hc : Work.Spaces.c α ≠ 0 := by
    have h := (Work.Spaces.c_bounds α hα hα1).1
    intro h0; rw [h0] at h; norm_num at h
  -- the angular density is `α F_*(w)/w`
  have hdens : ∀ w : ℝ,
      L12dens (fun w θ => α * (Work.Spaces.Gam α θ / Work.Spaces.c α) * Work.FM.Fstar w) w
        = α * Work.FM.Fstar w / w := by
    intro w
    rw [L12dens]
    have hpt : (fun θ : ℝ => Ktheta θ
          * (α * (Work.Spaces.Gam α θ / Work.Spaces.c α) * Work.FM.Fstar w) / w)
        = fun θ : ℝ =>
          (α * Work.FM.Fstar w / (Work.Spaces.c α * w)) * (Work.Spaces.K θ * Work.Spaces.Gam α θ) := by
      funext θ
      simp only [Ktheta_eq_K]
      ring
    rw [hpt, MeasureTheory.integral_const_mul]
    have hcint : (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.Spaces.Gam α θ)
        = Work.Spaces.c α := by
      have h : Work.Spaces.c α = ∫ θ in Work.Spaces.Iθ, Work.Spaces.Gam α θ * Work.Spaces.K θ := rfl
      rw [h]
      exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)
    rw [hcint]
    rcases eq_or_ne w 0 with hw | hw
    · subst hw; simp
    · field_simp
  rw [L12]
  simp only [hdens]
  have hfun : (fun r : ℝ => α * Work.FM.Fstar r / r)
      = fun r : ℝ => α * (Work.FM.Fstar r / r) := by
    funext r; ring
  rw [hfun, MeasureTheory.integral_const_mul, Work.FM.integral_Ioi_Fstar_div z hz]
  ring

end Work.Elliptic

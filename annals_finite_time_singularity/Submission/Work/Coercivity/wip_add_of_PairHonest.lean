/-
# Additivity of `wip` in its first argument under the honest-pairing hypothesis

If the two pairing integrands `A₁·B·ρ` and `A₂·B·ρ` have honest iterated integrals over
the quadrant `[0,∞) × [0,π/2]` — i.e. every angular slice is integrable and the resulting
function of `z` is integrable, which is exactly the hypothesis `PairHonest ρ Aᵢ B` — then
the pairing with `A₁ + A₂` is honest as well and `wip` is additive:

  `wip ρ (A₁ + A₂) B = wip ρ A₁ B + wip ρ A₂ B`.

Nothing beyond the two honesty hypotheses is needed, because additivity is proved *inside*
the iterated integral: for each `z ∈ Iz` the additivity of the Bochner integral on the
angular slice gives the pointwise identity, and the resulting two functions of `z` are
integrable by hypothesis, so the outer integrals add as well.  No joint integrability of
the product integrands over the quadrant is required.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Coercivity.H1IPAddDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

theorem wip_add_of_PairHonest (ρ A₁ A₂ B : ℝ → ℝ → ℝ)
    (h₁ : PairHonest ρ A₁ B) (h₂ : PairHonest ρ A₂ B) :
    wip ρ (A₁ + A₂) B = wip ρ A₁ B + wip ρ A₂ B := by
  simp only [PairHonest, I2Mem] at h₁ h₂
  obtain ⟨hs₁, hi₁⟩ := h₁
  obtain ⟨hs₂, hi₂⟩ := h₂
  simp only [wip]
  have hpt : ∀ z ∈ Spaces.Iz,
      (∫ θ in Spaces.Iθ, (A₁ z θ + A₂ z θ) * B z θ * ρ z θ)
        = (∫ θ in Spaces.Iθ, A₁ z θ * B z θ * ρ z θ)
            + ∫ θ in Spaces.Iθ, A₂ z θ * B z θ * ρ z θ := by
    intro z hz
    have hcongr : (fun θ => (A₁ z θ + A₂ z θ) * B z θ * ρ z θ)
        = (fun θ => A₁ z θ * B z θ * ρ z θ + A₂ z θ * B z θ * ρ z θ) := by
      funext θ; ring
    rw [hcongr]
    exact integral_add (hs₁ z hz) (hs₂ z hz)
  rw [show (∫ z in Spaces.Iz, ∫ θ in Spaces.Iθ, (A₁ + A₂) z θ * B z θ * ρ z θ)
        = ∫ z in Spaces.Iz, ((∫ θ in Spaces.Iθ, A₁ z θ * B z θ * ρ z θ)
            + ∫ θ in Spaces.Iθ, A₂ z θ * B z θ * ρ z θ) from by
      refine integral_congr_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_Ici] with z hz
      exact hpt z hz]
  rw [integral_add hi₁ hi₂]

end Work.Coercivity

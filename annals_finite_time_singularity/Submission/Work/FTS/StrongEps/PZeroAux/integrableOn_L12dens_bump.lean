/-
Copyright: work module for the Elgindi finite-time singularity project.

# Integrability of the `L₁₂`-density of the correction profile `bump`

The target of this file is

`IntegrableOn (fun s => ∫ θ in Iθ, K θ * bump s θ / s) (Ioi 0)`,

i.e. the *angular density* `s ↦ ∫_0^{π/2} K(θ) bump(s,θ)/s dθ` of the profile `bump` is
integrable on `(0,∞)`.

The density is `Work.Construction.L12dens bump = Work.FM.L12dens Work.Spaces.K bump`, whose
integrability on `(0,∞)` is already proved (as `PzNormAux.integrableOn_L12dens` inside
`PZeroAux/pzNorm_pos.lean`, where it is used to show `pzNorm > 0`).  The only mathematical
content here is the identification of the two integral expressions: by definition

`Work.FM.L12dens K f s = ∫ θ in Iθ, K θ * f s θ / s`

(`Work.FM.L12dens`), and the two bodies are *definitionally* the same through
`PzNormAux.KB`, so the bridge is `PzNormAux.L12dens_eq` (which rewrites `L12dens` as the
full-line integral of `KB`) together with the vanishing of `KB s` off `Iθ`
(`PzNormAux.KB_eq_zero_of_not_mem_Iθ`).
-/
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.PZero
import Submission.Work.FTS.StrongEps.BumpDefs
import Submission.Work.FTS.StrongEps.PZeroAux.pzNorm_pos

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.PZeroAux

open MeasureTheory

/-- The angular density of `bump`, `s ↦ ∫_θ K θ · bump s θ / s`, is integrable on `(0, ∞)`.

Equivalently: `L₁₂(bump)` is absolutely convergent, so that `L₁₂` is an honest integral of
`bump` and the projection `Pz` is linear on `bump` (`pzNorm_pos`,
`PZeroAux/PzNormPos.lean`). -/
theorem integrableOn_L12dens_bump :
    MeasureTheory.IntegrableOn
      (fun s : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.FTS.StrongEps.bump s θ / s)
      (Set.Ioi 0) := by
  -- The two integrands agree pointwise: `L12dens K bump s = ∫_θ KB s θ` and the set integral
  -- over `Iθ` involves the same body (`KB`), which vanishes off `Iθ`.
  have hfun : (fun s : ℝ => ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.K θ * Work.FTS.StrongEps.bump s θ / s)
      = fun s : ℝ => Work.FM.L12dens Work.Spaces.K Work.FTS.StrongEps.bump s := by
    funext s
    rw [PzNormAux.L12dens_eq s]
    rw [show (fun θ : ℝ => Work.Spaces.K θ * Work.FTS.StrongEps.bump s θ / s)
        = (fun θ : ℝ => PzNormAux.KB s θ) from rfl]
    exact setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun θ hθ => PzNormAux.KB_eq_zero_of_not_mem_Iθ hθ)
  rw [hfun]
  exact PzNormAux.integrableOn_L12dens

end Work.FTS.StrongEps.PZeroAux
